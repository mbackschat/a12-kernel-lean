import A12Kernel.Semantics.NumericComparison

/-! # A12Kernel.Proofs.NumericComparison — directional-polarity laws -/

namespace A12Kernel

/-- A fixed numeric operand that satisfies its comparison always produces a value firing. -/
theorem fixedNumericFiring_is_value (op : NumericComparisonOp) (actual expected : Rat)
    (holds : op.holds actual expected = true) :
    op.evalFixedRight (.value actual .fixed) expected = .fired .value := by
  cases op <;> simp_all [NumericComparisonOp.evalFixedRight,
    NumericComparisonOp.leftFillCanBreak, numericDifferenceFillCanClose,
    NumericFillability.fixed]

/-- A grow-only result cannot be repaired by filling when a greater-or-equal condition already fires. -/
theorem growOnlyGreaterEqualFiring_is_value (actual expected : Rat)
    (holds : NumericComparisonOp.greaterEqual.holds actual expected = true) :
    NumericComparisonOp.greaterEqual.evalFixedRight (.value actual .growOnly) expected =
      .fired .value := by
  simp [NumericComparisonOp.evalFixedRight, holds,
    NumericComparisonOp.leftFillCanBreak, NumericFillability.growOnly]

/-- The mirror direction remains omission-typed: filling a grow-only result can clear a true less-than condition. -/
theorem growOnlyLessFiring_is_omission (actual expected : Rat)
    (holds : NumericComparisonOp.less.holds actual expected = true) :
    NumericComparisonOp.less.evalFixedRight (.value actual .growOnly) expected =
      .fired .omission := by
  simp [NumericComparisonOp.evalFixedRight, holds,
    NumericComparisonOp.leftFillCanBreak, NumericFillability.growOnly]

/-- Filling either an unsigned or signed empty Number can grow its substituted zero, so a true direct less-than condition is omission-typed. -/
theorem emptyNumberLessFiring_is_omission (signed : Bool) (expected : Rat)
    (holds : NumericComparisonOp.less.holds 0 expected = true) :
    NumericComparisonOp.less.evalFixedRight (.value 0 (.emptyNumber signed)) expected =
      .fired .omission := by
  simp [NumericComparisonOp.evalFixedRight, holds,
    NumericComparisonOp.leftFillCanBreak, NumericFillability.emptyNumber]

/-- For a true greater-or-equal condition over an empty Number, only a signed field can later shrink below the fixed literal. -/
theorem emptyNumberGreaterEqualFiring_polarity (signed : Bool) (expected : Rat)
    (holds : NumericComparisonOp.greaterEqual.holds 0 expected = true) :
    NumericComparisonOp.greaterEqual.evalFixedRight
        (.value 0 (.emptyNumber signed)) expected =
      .fired (if signed then .omission else .value) := by
  cases signed <;>
    simp [NumericComparisonOp.evalFixedRight, holds,
      NumericComparisonOp.leftFillCanBreak, NumericFillability.emptyNumber]

/-- A grow-only operand that already differs from a literal at or below it fires as VALUE: filling cannot move the operand downward to repair the inequality. Empty unsigned zero versus a negative literal is the captured instance. -/
theorem growOnlyNotEqualWhenLeftNotBelow_is_value (actual expected : Rat)
    (holds : NumericComparisonOp.notEqual.holds actual expected = true)
    (notBelow : ¬ normalizedComparisonValue actual < normalizedComparisonValue expected) :
    NumericComparisonOp.notEqual.evalFixedRight (.value actual .growOnly) expected =
      .fired .value := by
  simp [NumericComparisonOp.evalFixedRight, holds,
    NumericComparisonOp.leftFillCanBreak, numericDifferenceFillCanClose,
    NumericFillability.growOnly, NumericFillability.fixed, notBelow]

end A12Kernel
