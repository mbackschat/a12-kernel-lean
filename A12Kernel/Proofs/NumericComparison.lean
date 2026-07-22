import A12Kernel.Semantics.NumericComparison

/-! # A12Kernel.Proofs.NumericComparison — directional-polarity laws -/

namespace A12Kernel

/-- Every symmetric temporal numeric consumer maps an empty typed observation to bidirectionally fillable zero. -/
theorem symmetricValidationNumericOperand_empty
    (project : α → Rat) :
    symmetricValidationNumericOperand project (.empty : CellObservation α) =
      .value 0 .both := by
  rfl

/-- Every present value projected through the symmetric temporal numeric seam is fixed. -/
theorem symmetricValidationNumericOperand_value
    (project : α → Rat) (value : α) :
    symmetricValidationNumericOperand project (.value value) =
      .value (project value) .fixed := by
  rfl

/-- The symmetric temporal numeric seam preserves the exact formal-unavailability cause. -/
theorem symmetricValidationNumericOperand_unknown
    (project : α → Rat) (cause : FormalCause) :
    symmetricValidationNumericOperand project
        (.unknown cause : CellObservation α) = .unknown cause := by
  rfl

/-- Whenever substituted symmetric zero satisfies a fixed-right comparison, either filling direction can break the result and the verdict is omission-typed. -/
theorem symmetricValidationNumericOperand_true_comparison_omission
    (project : α → Rat) (op : NumericComparisonOp) (expected : Rat)
    (holds : op.holds 0 expected = true) :
    op.evalFixedRight
        (symmetricValidationNumericOperand project
          (.empty : CellObservation α)) expected = .fired .omission := by
  cases op <;>
    simp_all [symmetricValidationNumericOperand,
      NumericComparisonOp.evalFixedRight, NumericComparisonOp.eval,
      NumericComparisonOp.fillCanBreak, numericDifferenceFillCanClose,
      NumericFillability.both]

/-- A value transformation cannot hide or replace the exact invalid operand cause. -/
theorem numericOperand_mapValue_unknown
    (cause : FormalCause)
    (transform : Rat → NumericFillability → Rat × NumericFillability) :
    (NumericOperand.unknown cause).mapValue transform = .unknown cause := by
  rfl

theorem numericDifferenceFillCanClose_comm_of_ne (left right : Rat)
    (leftFill rightFill : NumericFillability)
    (different :
      normalizedComparisonValue left ≠ normalizedComparisonValue right) :
    numericDifferenceFillCanClose left right leftFill rightFill =
      numericDifferenceFillCanClose right left rightFill leftFill := by
  by_cases below :
      normalizedComparisonValue left < normalizedComparisonValue right
  · have notAbove :
        ¬normalizedComparisonValue right < normalizedComparisonValue left :=
      Rat.not_lt.mpr (Rat.le_of_lt below)
    simp [numericDifferenceFillCanClose, below, notAbove, Bool.or_comm]
  · have above :
        normalizedComparisonValue right < normalizedComparisonValue left :=
      Rat.lt_of_le_of_ne (Rat.not_lt.mp below) different.symm
    simp [numericDifferenceFillCanClose, above, below, Bool.or_comm]

/-- The reduced fixed-right entry point is exactly the two-sided evaluator with a fixed literal operand. -/
theorem numericEval_fixedRight (op : NumericComparisonOp)
    (left : NumericOperand) (right : Rat) :
    op.evalFixedRight left right = op.eval left (.value right .fixed) := by
  rfl

private theorem numericNotEqual_holds_comm (left right : Rat) :
    NumericComparisonOp.notEqual.holds left right =
      NumericComparisonOp.notEqual.holds right left := by
  exact congrArg (!·) Bool.beq_comm

/-- Swapping both operands preserves the complete equality verdict. -/
theorem numericEqual_eval_comm (left right : NumericOperand) :
    NumericComparisonOp.equal.eval left right =
      NumericComparisonOp.equal.eval right left := by
  cases left <;> cases right <;>
    simp [NumericComparisonOp.eval, NumericComparisonOp.holds,
      NumericComparisonOp.fillCanBreak, Bool.beq_comm,
      Bool.or_comm, Bool.or_left_comm]

/-- Swapping both operands preserves the complete directional-inequality verdict. -/
theorem numericNotEqual_eval_comm (left right : NumericOperand) :
    NumericComparisonOp.notEqual.eval left right =
      NumericComparisonOp.notEqual.eval right left := by
  cases left with
  | unknown leftCause =>
      cases right <;> rfl
  | value leftAmount leftFill =>
      cases right with
      | unknown rightCause => rfl
      | value rightAmount rightFill =>
          cases holds :
              NumericComparisonOp.notEqual.holds leftAmount rightAmount with
          | false =>
              have swapped :
                  NumericComparisonOp.notEqual.holds rightAmount leftAmount = false := by
                rw [← numericNotEqual_holds_comm leftAmount rightAmount]
                exact holds
              simp [NumericComparisonOp.eval, holds, swapped]
          | true =>
              have swapped :
                  NumericComparisonOp.notEqual.holds rightAmount leftAmount = true := by
                rw [← numericNotEqual_holds_comm leftAmount rightAmount]
                exact holds
              have different :
                  normalizedComparisonValue leftAmount ≠
                    normalizedComparisonValue rightAmount := by
                intro equal
                simp [NumericComparisonOp.holds, equal] at holds
              have closes := numericDifferenceFillCanClose_comm_of_ne
                leftAmount rightAmount leftFill rightFill different
              simp [NumericComparisonOp.eval, holds, swapped,
                NumericComparisonOp.fillCanBreak, closes]

/-- A fixed numeric operand that satisfies its comparison always produces a value firing. -/
theorem fixedNumericFiring_is_value (op : NumericComparisonOp) (actual expected : Rat)
    (holds : op.holds actual expected = true) :
    op.evalFixedRight (.value actual .fixed) expected = .fired .value := by
  cases op <;> simp_all [NumericComparisonOp.evalFixedRight,
    NumericComparisonOp.eval, NumericComparisonOp.fillCanBreak,
    numericDifferenceFillCanClose, NumericFillability.fixed]

/-- A grow-only result cannot be repaired by filling when a greater-or-equal condition already fires. -/
theorem growOnlyGreaterEqualFiring_is_value (actual expected : Rat)
    (holds : NumericComparisonOp.greaterEqual.holds actual expected = true) :
    NumericComparisonOp.greaterEqual.evalFixedRight (.value actual .growOnly) expected =
      .fired .value := by
  simp [NumericComparisonOp.evalFixedRight, NumericComparisonOp.eval, holds,
    NumericComparisonOp.fillCanBreak, NumericFillability.growOnly,
    NumericFillability.fixed]

/-- The mirror direction remains omission-typed: filling a grow-only result can clear a true less-than condition. -/
theorem growOnlyLessFiring_is_omission (actual expected : Rat)
    (holds : NumericComparisonOp.less.holds actual expected = true) :
    NumericComparisonOp.less.evalFixedRight (.value actual .growOnly) expected =
      .fired .omission := by
  simp [NumericComparisonOp.evalFixedRight, NumericComparisonOp.eval, holds,
    NumericComparisonOp.fillCanBreak, NumericFillability.growOnly]

/-- Filling either an unsigned or signed empty Number can grow its substituted zero, so a true direct less-than condition is omission-typed. -/
theorem emptyNumberLessFiring_is_omission (signed : Bool) (expected : Rat)
    (holds : NumericComparisonOp.less.holds 0 expected = true) :
    NumericComparisonOp.less.evalFixedRight (.value 0 (.emptyNumber signed)) expected =
      .fired .omission := by
  simp [NumericComparisonOp.evalFixedRight, NumericComparisonOp.eval, holds,
    NumericComparisonOp.fillCanBreak, NumericFillability.emptyNumber]

/-- Inclusive upper bounds share the same grow-direction repair for either empty Number signedness. -/
theorem emptyNumberLessEqualFiring_is_omission (signed : Bool) (expected : Rat)
    (holds : NumericComparisonOp.lessEqual.holds 0 expected = true) :
    NumericComparisonOp.lessEqual.evalFixedRight
        (.value 0 (.emptyNumber signed)) expected = .fired .omission := by
  simp [NumericComparisonOp.evalFixedRight, NumericComparisonOp.eval, holds,
    NumericComparisonOp.fillCanBreak, NumericFillability.emptyNumber]

/-- For a true strict lower bound over an empty Number, only a signed field can later shrink far enough to repair it. -/
theorem emptyNumberGreaterFiring_polarity (signed : Bool) (expected : Rat)
    (holds : NumericComparisonOp.greater.holds 0 expected = true) :
    NumericComparisonOp.greater.evalFixedRight
        (.value 0 (.emptyNumber signed)) expected =
      .fired (if signed then .omission else .value) := by
  cases signed <;>
    simp [NumericComparisonOp.evalFixedRight, NumericComparisonOp.eval, holds,
      NumericComparisonOp.fillCanBreak, NumericFillability.emptyNumber,
      NumericFillability.fixed]

/-- For a true greater-or-equal condition over an empty Number, only a signed field can later shrink below the fixed literal. -/
theorem emptyNumberGreaterEqualFiring_polarity (signed : Bool) (expected : Rat)
    (holds : NumericComparisonOp.greaterEqual.holds 0 expected = true) :
    NumericComparisonOp.greaterEqual.evalFixedRight
        (.value 0 (.emptyNumber signed)) expected =
      .fired (if signed then .omission else .value) := by
  cases signed <;>
    simp [NumericComparisonOp.evalFixedRight, NumericComparisonOp.eval, holds,
      NumericComparisonOp.fillCanBreak, NumericFillability.emptyNumber,
      NumericFillability.fixed]

/-- A grow-only operand that already differs from a literal at or below it fires as VALUE: filling cannot move the operand downward to repair the inequality. Empty unsigned zero versus a negative literal is the captured instance. -/
theorem growOnlyNotEqualWhenLeftNotBelow_is_value (actual expected : Rat)
    (holds : NumericComparisonOp.notEqual.holds actual expected = true)
    (notBelow : ¬ normalizedComparisonValue actual < normalizedComparisonValue expected) :
    NumericComparisonOp.notEqual.evalFixedRight (.value actual .growOnly) expected =
      .fired .value := by
  simp [NumericComparisonOp.evalFixedRight, NumericComparisonOp.eval, holds,
    NumericComparisonOp.fillCanBreak, numericDifferenceFillCanClose,
    NumericFillability.growOnly, NumericFillability.fixed, notBelow]

/-- A grow-only right operand can falsify a true greater-or-equal comparison by growing. -/
theorem growOnlyRightGreaterEqualFiring_is_omission (left right : Rat)
    (holds : NumericComparisonOp.greaterEqual.holds left right = true) :
    NumericComparisonOp.greaterEqual.eval
        (.value left .fixed) (.value right .growOnly) =
      .fired .omission := by
  simp [NumericComparisonOp.eval, holds, NumericComparisonOp.fillCanBreak,
    NumericFillability.fixed, NumericFillability.growOnly]

/-- Merely growing the right side cannot falsify a true less-than comparison. -/
theorem growOnlyRightLessFiring_is_value (left right : Rat)
    (holds : NumericComparisonOp.less.holds left right = true) :
    NumericComparisonOp.less.eval
        (.value left .fixed) (.value right .growOnly) =
      .fired .value := by
  simp [NumericComparisonOp.eval, holds, NumericComparisonOp.fillCanBreak,
    NumericFillability.fixed, NumericFillability.growOnly]

/-- Shrinking the right side can falsify a true less-than comparison. -/
theorem shrinkOnlyRightLessFiring_is_omission (left right : Rat)
    (holds : NumericComparisonOp.less.holds left right = true) :
    NumericComparisonOp.less.eval
        (.value left .fixed) (.value right .shrinkOnly) =
      .fired .omission := by
  simp [NumericComparisonOp.eval, holds, NumericComparisonOp.fillCanBreak,
    NumericFillability.fixed, NumericFillability.shrinkOnly]

end A12Kernel
