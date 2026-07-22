import A12Kernel.Semantics.StringPattern

/-! # A12Kernel.Proofs.StringPattern — resolved pattern laws

These laws concern consumption of an already-admitted whole-value matcher. Java pattern compilation and the kernel's bounded admission gate remain outside this proof boundary.
-/

namespace A12Kernel

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
  cases op <;> cases operand <;>
    simp_all [StringPatternOp.evalResolved, StringPatternOp.acceptsMatchResult] <;>
    split at fired <;> simp_all

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
    FlatContext.observeValidationAt, read, formalCheck, nonempty, observeCell]

end A12Kernel
