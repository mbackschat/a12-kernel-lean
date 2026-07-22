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

end A12Kernel
