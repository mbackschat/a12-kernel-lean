import A12Kernel.Semantics.StringPattern

/-! # A12Kernel.Proofs.StringPattern — resolved pattern laws

These laws concern consumption of an already-admitted whole-value matcher. Java pattern compilation and the kernel's bounded admission gate remain outside this proof boundary.
-/

namespace A12Kernel

/-- Forgetting the computation's retained poison cause yields the same resolved pattern verdict. -/
theorem stringPattern_evalComputation_bridge (op : StringPatternOp)
    (matcher : String → Bool) (operand : SimpleComparisonOperand String) :
    (match op.evalComputationResolved matcher operand with
      | .holds => Verdict.fired .value
      | .notTrue => .notFired
      | .poison _ => .unknown) = op.evalResolved matcher operand := by
  cases operand with
  | notEvaluated => rfl
  | unknown cause => rfl
  | value actual given =>
      cases outcome : op.acceptsMatchResult (matcher actual) <;>
        simp [StringPatternOp.evalComputationResolved, StringPatternOp.evalResolved, outcome]

theorem stringPattern_evalComputation_poison_iff (op : StringPatternOp)
    (matcher : String → Bool) (operand : SimpleComparisonOperand String) (cause : FormalCause) :
    op.evalComputationResolved matcher operand = .poison cause ↔ operand = .unknown cause := by
  cases operand with
  | notEvaluated => simp [StringPatternOp.evalComputationResolved]
  | unknown actual => simp [StringPatternOp.evalComputationResolved]
  | value actual given =>
      cases outcome : op.acceptsMatchResult (matcher actual) <;>
        simp [StringPatternOp.evalComputationResolved, outcome]

@[simp]
theorem stringPattern_evalResolved_notEvaluated
    (op : StringPatternOp) (wholeValueMatches : String → Bool) :
    op.evalResolved wholeValueMatches (.notEvaluated) = .notFired := by
  rfl

@[simp]
theorem stringPattern_evalResolved_unknown
    (op : StringPatternOp) (wholeValueMatches : String → Bool)
    (cause : FormalCause) :
    op.evalResolved wholeValueMatches (.unknown cause) = .unknown := by
  rfl

/-- On every present String, `PatternMatched` and `PatternViolated` are exact firing complements. -/
theorem stringPattern_evalResolved_value_complement
    (wholeValueMatches : String → Bool) (actual : String) (given : Bool) :
    if wholeValueMatches actual then
      StringPatternOp.matched.evalResolved wholeValueMatches (.value actual given) =
          .fired .value ∧
        StringPatternOp.violated.evalResolved wholeValueMatches (.value actual given) =
          .notFired
  else
      StringPatternOp.matched.evalResolved wholeValueMatches (.value actual given) =
          .notFired ∧
        StringPatternOp.violated.evalResolved wholeValueMatches (.value actual given) =
          .fired .value := by
  cases matchResult : wholeValueMatches actual <;>
    simp [StringPatternOp.evalResolved, StringPatternOp.acceptsMatchResult, matchResult]

/-- Pattern conditions never emit omission polarity: missing input is suppressed before matching. -/
theorem stringPattern_evalResolved_fired_is_value
    (op : StringPatternOp) (wholeValueMatches : String → Bool)
    (operand : SimpleComparisonOperand String) (polarity : Polarity)
    (fired : op.evalResolved wholeValueMatches operand = .fired polarity) :
  polarity = .value := by
  cases operand with
  | value actual given =>
      cases matchResult : wholeValueMatches actual <;> cases op <;>
        simp_all [StringPatternOp.evalResolved, StringPatternOp.acceptsMatchResult]
  | notEvaluated => cases op <;> simp_all [StringPatternOp.evalResolved]
  | unknown cause => cases op <;> simp_all [StringPatternOp.evalResolved]

/-- The flat integration gives the matcher exactly the normalized checked String cached by formal checking. -/
theorem resolvedStringPattern_readsNormalized (context : FlatContext)
    (field : FlatStringField) (text : String) (op : StringPatternOp)
    (wholeValueMatches : String → Bool)
    (read : context.read field.id =
      formalCheck { kind := .string } (.parsed (.str text)))
    (nonempty : (normalizeEvaluatedString text).isEmpty = false) :
    context.evalResolvedStringPattern op field wholeValueMatches =
      op.evalResolved wholeValueMatches
        (.value (normalizeEvaluatedString text) true) := by
  simp [FlatContext.evalResolvedStringPattern,
    FlatContext.resolveDirectStringComparisonOperand,
    FlatContext.resolveStringComparisonOperandAt,
    read, formalCheck, nonempty, observeCell]

end A12Kernel
