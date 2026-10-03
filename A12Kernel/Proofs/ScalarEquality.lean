import A12Kernel.Semantics.ScalarEquality

/-! # Shared symmetric scalar-comparison laws -/

namespace A12Kernel

/-- Formal unavailability dominates every right operand, including a valueless one. -/
theorem evalSymmetricComparison_unknown_left (holds : α → α → Bool)
    (cause : FormalCause) (right : SimpleComparisonOperand α) :
    evalSymmetricComparison holds (.unknown cause) right = .unknown := by
  cases right <;> rfl

/-- A valueless left operand makes a comparison with a present value not fire. -/
theorem evalSymmetricComparison_noValue_left (holds : α → α → Bool)
    (right : α) (rightGiven : Bool) :
    evalSymmetricComparison holds .notEvaluated (.value right rightGiven) =
      .notFired := by
  rfl

/-- A true comparison over fixed present operands fires with VALUE polarity. -/
theorem evalSymmetricComparison_fixed_firing (holds : α → α → Bool)
    (left right : α) (truth : holds left right = true) :
    evalSymmetricComparison holds (.value left true) (.value right true) =
      .fired .value := by
  simp [evalSymmetricComparison, truth]

/-- Missing provenance on either present operand makes a true comparison omission-typed. -/
theorem evalSymmetricComparison_missing_firing (holds : α → α → Bool)
    (left right : α) (leftGiven rightGiven : Bool)
    (missing : (leftGiven && rightGiven) = false)
    (truth : holds left right = true) :
    evalSymmetricComparison holds (.value left leftGiven) (.value right rightGiven) =
      .fired .omission := by
  simp [evalSymmetricComparison, truth, missing]

/-- Exchanging operands and a correspondingly reversed truth predicate preserves the complete classified verdict and polarity. -/
theorem evalSymmetricComparison_swapped
    (holds reversed : α → α → Bool)
    (reverseHolds : ∀ left right, reversed left right = holds right left)
    (left right : SimpleComparisonOperand α) :
    evalSymmetricComparison reversed left right =
      evalSymmetricComparison holds right left := by
  cases left <;> cases right <;>
    simp [evalSymmetricComparison, reverseHolds, Bool.and_comm]

namespace EqualityOp

/-- Equality and inequality over a symmetric equivalence relation are invariant under exchanging the classified operands. -/
theorem evalSymmetric_swapped (op : EqualityOp)
    (equivalent : α → α → Bool)
    (symmetric : ∀ left right, equivalent left right = equivalent right left)
    (left right : SimpleComparisonOperand α) :
    op.evalSymmetric equivalent left right =
      op.evalSymmetric equivalent right left := by
  cases op <;> cases left <;> cases right <;>
    simp [EqualityOp.evalSymmetric, evalSymmetricComparison,
      symmetric, Bool.and_comm]

end EqualityOp

/-- A reached formal error suppresses the entire right read, including its runtime failure. -/
theorem computationComparisonExcept_leftPoison
    (holds : α → α → Bool) (cause : FormalCause)
    (right : Unit → Except Error (SimpleComparisonOperand α)) :
    evalComputationComparisonExcept holds (.ok (.unknown cause)) right = .ok (.poison cause) := rfl

/-- Empty is not an abort: the right reader can still fail. -/
theorem computationComparisonExcept_emptyLeft_error
    (holds : α → α → Bool) (error : Error) :
    evalComputationComparisonExcept holds (.ok .notEvaluated)
      (fun _ => .error error) = .error error := rfl

/-- Successful reads reduce to the same pure comparison used by Boolean and token guards. -/
theorem computationComparisonExcept_pure
    (holds : α → α → Bool) (left right : SimpleComparisonOperand α) :
    evalComputationComparisonExcept (Error := Error) holds (.ok left) (fun _ => .ok right) =
      .ok (evalComputationComparison holds left right) := by
  cases left <;> rfl

end A12Kernel
