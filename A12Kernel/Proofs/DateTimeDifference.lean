import A12Kernel.Semantics.DateTimeDifference

/-! # A12Kernel.Proofs.DateTimeDifference — resolved instant-difference laws

These laws characterize the total sub-day difference core over exact instants. They do not claim parsing, zone resolution, operand formal checking, result admission, or external kernel equivalence.
-/

namespace A12Kernel

/-- Every closed DateTime-difference unit has a strictly positive divisor. -/
theorem dateTimeDifferenceUnit_unitSeconds_pos
    (unit : DateTimeDifferenceUnit) :
    0 < unit.unitSeconds := by
  cases unit <;> decide

/-- Equal instants have zero difference in every admitted unit. -/
theorem instant_difference_self
    (instant : Instant) (unit : DateTimeDifferenceUnit) :
    instant.difference unit instant = 0 := by
  simp [Instant.difference]

/-- Swapping authored operands negates the truncated result; truncation toward zero is sign-symmetric. -/
theorem instant_difference_swap
    (first second : Instant) (unit : DateTimeDifferenceUnit) :
    second.difference unit first = -(first.difference unit second) := by
  have negated :
      first.epochMillis - second.epochMillis =
        -(second.epochMillis - first.epochMillis) := by
    omega
  simp only [Instant.difference, negated, Int.neg_tdiv]

/-- Seconds divide the exact authored-order millisecond subtraction and truncate toward zero. -/
theorem instant_difference_seconds
    (first second : Instant) :
    first.difference .seconds second =
      (second.epochMillis - first.epochMillis).tdiv 1000 := by
  simp [Instant.difference, DateTimeDifferenceUnit.unitSeconds]

/-- Advancing by an exact whole number of selected units recovers that signed amount. -/
theorem instant_difference_exactUnits
    (instant : Instant) (unit : DateTimeDifferenceUnit) (amount : Int) :
    instant.difference unit
        { epochMillis :=
            instant.epochMillis + amount * (unit.unitSeconds * 1000) } =
      amount := by
  simp only [Instant.difference]
  have difference :
      instant.epochMillis + amount * (unit.unitSeconds * 1000) -
          instant.epochMillis =
        amount * (unit.unitSeconds * 1000) := by
    omega
  rw [difference, Int.mul_tdiv_cancel amount]
  have positive := dateTimeDifferenceUnit_unitSeconds_pos unit
  omega

/-- The existing whole-hour shift is an exact inverse input for the hours difference core. -/
theorem instant_difference_shiftHours
    (instant : Instant) (hours : Int) :
    instant.difference .hours (instant.shiftHours hours) = hours := by
  exact instant_difference_exactUnits instant .hours hours

/-- A left formal cause wins before sub-day empty substitution or exact-instant evaluation. -/
theorem dateTimeDifferenceOperand_unavailable_left
    (unit : DateTimeDifferenceUnit) (cause : FormalCause)
    (right : DateTimeDifferenceOperand) :
    DateTimeDifferenceOperand.evaluate unit (.unavailable cause) right =
      .unknown cause := by
  rfl

/-- Either empty DateTime operand supplies the symmetric scale-0 value with both fill directions. -/
theorem dateTimeDifferenceOperand_empty_left
    (unit : DateTimeDifferenceUnit) (right : Instant) :
    DateTimeDifferenceOperand.evaluate unit .empty (.value right) =
      .value 0 .both := by
  rfl

/-- Two exact DateTime operands delegate to the existing authored-order millisecond core. -/
theorem dateTimeDifferenceOperand_values_delegate
    (unit : DateTimeDifferenceUnit) (first second : Instant) :
    DateTimeDifferenceOperand.evaluate unit (.value first) (.value second) =
      .value (first.difference unit second) .fixed := by
  rfl

end A12Kernel
