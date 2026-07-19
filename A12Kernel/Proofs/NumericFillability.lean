import A12Kernel.Semantics.NumericFillability

/-! # A12Kernel.Proofs.NumericFillability — arithmetic direction laws -/

namespace A12Kernel

theorem numericArithmetic_fixed_fillability (op : NumericArithmeticOp) (left right : Rat) :
    op.fillability left .fixed right .fixed = .fixed := by
  cases op with
  | add => rfl
  | subtract => rfl
  | multiply =>
      simp only [NumericArithmeticOp.fillability]
      generalize NumericSign.ofRat left = leftSign
      generalize NumericSign.ofRat right = rightSign
      cases leftSign <;> cases rightSign <;> rfl

theorem numericFillability_add_comm (left right : NumericFillability) :
    left.add right = right.add left := by
  cases left
  cases right
  simp [NumericFillability.add, Bool.or_comm]

theorem numericFillability_subtract_eq_add_swapped (left right : NumericFillability) :
    left.subtract right = left.add right.swapDirections := by
  rfl

theorem numericFillability_subtract_fixed_right (fillability : NumericFillability) :
    fillability.subtract .fixed = fillability := by
  cases fillability
  simp [NumericFillability.subtract, NumericFillability.fixed]

theorem numericFillability_fixed_subtract (fillability : NumericFillability) :
    NumericFillability.fixed.subtract fillability = fillability.swapDirections := by
  cases fillability
  simp [NumericFillability.subtract, NumericFillability.fixed,
    NumericFillability.swapDirections]

theorem numericFillability_multiply_comm (left right : NumericFillability)
    (leftSign rightSign : NumericSign) :
    left.multiply leftSign right rightSign =
      right.multiply rightSign left leftSign := by
  rcases left with ⟨leftGrow, leftShrink⟩
  rcases right with ⟨rightGrow, rightShrink⟩
  cases leftGrow <;> cases leftShrink <;>
    cases rightGrow <;> cases rightShrink <;>
    cases leftSign <;> cases rightSign <;> rfl

theorem numericFillability_multiply_fixed_positive
    (fillability : NumericFillability) (sign : NumericSign) :
    fillability.multiply sign .fixed .positive = fillability := by
  rcases fillability with ⟨canGrow, canShrink⟩
  cases canGrow <;> cases canShrink <;> cases sign <;> rfl

theorem numericFillability_multiply_fixed_negative
    (fillability : NumericFillability) (sign : NumericSign) :
    fillability.multiply sign .fixed .negative = fillability.swapDirections := by
  rcases fillability with ⟨canGrow, canShrink⟩
  cases canGrow <;> cases canShrink <;> cases sign <;> rfl

theorem numericFillability_multiply_fixed_zero
    (fillability : NumericFillability) (sign : NumericSign) :
    fillability.multiply sign .fixed .zero = .fixed := by
  rcases fillability with ⟨canGrow, canShrink⟩
  cases canGrow <;> cases canShrink <;> cases sign <;> rfl

end A12Kernel
