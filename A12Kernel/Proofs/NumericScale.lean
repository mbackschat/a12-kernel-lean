import A12Kernel.Elaboration.NumericScale

/-! # Static numeric-scale laws -/

namespace A12Kernel

theorem scaleInfo_maxExact_comm (left right : ScaleInfo) :
    left.maxExact right = right.maxExact left := by
  cases left <;> cases right <;> simp [ScaleInfo.maxExact, Int.max_comm]

theorem scaleInfo_addExact_comm (left right : ScaleInfo) :
    left.addExact right = right.addExact left := by
  cases left <;> cases right <;> simp [ScaleInfo.addExact, Int.add_comm]

theorem numericScale_union_comm (left right : NumericScaleSummary) :
    left.union right = right.union left := by
  cases left
  cases right
  simp [NumericScaleSummary.union, scaleInfo_maxExact_comm, Bool.and_comm]

/-- Static binary summaries are operand-order independent, including subtraction because only its scale/capability abstraction is summarized here. -/
theorem numericScale_binary_comm (op : NumericScaleBinaryOp)
    (left right : NumericScaleSummary) :
    NumericScaleSummary.binary op left right =
      NumericScaleSummary.binary op right left := by
  cases op <;>
    simp [NumericScaleSummary.binary, numericScale_union_comm,
      scaleInfo_addExact_comm, Bool.or_comm]

/-- Although scale expansion is locally directional, swapping both operands preserves exact-comparison acceptance. -/
theorem exactNumericScaleComparisonAllowed_comm
    (left right : NumericScaleSummary) :
    exactNumericScaleComparisonAllowed left right =
      exactNumericScaleComparisonAllowed right left := by
  cases left with
  | mk leftScale leftCanExpand =>
      cases right with
      | mk rightScale rightCanExpand =>
          cases leftScale <;> cases rightScale <;>
            simp [exactNumericScaleComparisonAllowed, Bool.or_comm,
              Bool.or_left_comm, Bool.or_assoc, BEq.comm]

theorem exactNumericScaleComparisonAllowed_same
    (scale : Int) (leftCanExpand rightCanExpand : Bool) :
    exactNumericScaleComparisonAllowed
      { scale := .exact scale, canExpandScale := leftCanExpand }
      { scale := .exact scale, canExpandScale := rightCanExpand } = true := by
  simp [exactNumericScaleComparisonAllowed]

/-- When the left scale is smaller, the left capability is the complete acceptance condition. -/
theorem exactNumericScaleComparisonAllowed_of_left_lt
    (leftScale rightScale : Int) (leftCanExpand rightCanExpand : Bool)
    (lower : leftScale < rightScale) :
    exactNumericScaleComparisonAllowed
      { scale := .exact leftScale, canExpandScale := leftCanExpand }
      { scale := .exact rightScale, canExpandScale := rightCanExpand } =
        leftCanExpand := by
  have different : leftScale ≠ rightScale := Int.ne_of_lt lower
  have notReverse : ¬ rightScale < leftScale := Int.lt_asymm lower
  simp [exactNumericScaleComparisonAllowed, different, lower, notReverse]

/-- Field-only exact comparison reduces to equality of the two declared nonnegative scales. -/
theorem exactNumericScaleComparisonAllowed_fields (left right : Nat) :
    exactNumericScaleComparisonAllowed
      (NumericScaleSummary.field left) (NumericScaleSummary.field right) = true ↔
        left = right := by
  simp [exactNumericScaleComparisonAllowed, NumericScaleSummary.field,
    Int.ofNat_inj]

theorem exactNumericScaleComparisonAllowed_unknown_left
    (canExpand : Bool) (right : NumericScaleSummary) :
    exactNumericScaleComparisonAllowed
      { scale := .unknown, canExpandScale := canExpand } right = false := by
  cases right with
  | mk rightScale rightCanExpand =>
      cases rightScale <;> rfl

theorem exactNumericScaleComparisonAllowed_unknown_right
    (left : NumericScaleSummary) (canExpand : Bool) :
    exactNumericScaleComparisonAllowed left
      { scale := .unknown, canExpandScale := canExpand } = false := by
  cases left with
  | mk leftScale leftCanExpand =>
      cases leftScale <;> rfl

end A12Kernel
