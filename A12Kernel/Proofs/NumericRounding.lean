import A12Kernel.Semantics.NumericComparison
import A12Kernel.Semantics.NumericComputationResult
import A12Kernel.Proofs.NumericFillability

/-! # A12Kernel.Proofs.NumericRounding — rounding bounds and metadata preservation -/

namespace A12Kernel

private theorem decimalFactor_pos (scale : Nat) :
    (0 : Rat) < (decimalFactor scale : Nat) := by
  exact Rat.natCast_pos.mpr (Nat.pow_pos (by decide))

theorem rescaleFloor_le (value : Rat) (scale : Nat) :
    rescaleFloor value scale ≤ value := by
  let factor : Rat := (decimalFactor scale : Nat)
  have factorPos : 0 < factor := decimalFactor_pos scale
  apply Rat.le_of_mul_le_mul_right _ factorPos
  change ((Rat.floor (value * factor) : Rat) / factor) * factor ≤ value * factor
  rw [Rat.div_mul_cancel (Rat.ne_of_gt factorPos)]
  exact Rat.floor_le (value * factor)

theorem le_rescaleCeiling (value : Rat) (scale : Nat) :
    value ≤ rescaleCeiling value scale := by
  let factor : Rat := (decimalFactor scale : Nat)
  have factorPos : 0 < factor := decimalFactor_pos scale
  apply Rat.le_of_mul_le_mul_right _ factorPos
  change value * factor ≤ ((Rat.ceil (value * factor) : Rat) / factor) * factor
  rw [Rat.div_mul_cancel (Rat.ne_of_gt factorPos)]
  exact Rat.le_ceil

/-- `RoundDown` is bounded by the scale-19 pre-rounded value, not necessarily by the raw exact input. -/
theorem roundFloor_le_preRound (value : Rat) (places : RoundingPlaces) :
    roundDecimal .floor value places ≤ rescaleHalfUp value decimalPreRoundScale := by
  exact rescaleFloor_le _ _

/-- `RoundUp` is bounded above the scale-19 pre-rounded value, not necessarily above the raw exact input. -/
theorem preRound_le_roundCeiling (value : Rat) (places : RoundingPlaces) :
    rescaleHalfUp value decimalPreRoundScale ≤ roundDecimal .ceiling value places := by
  exact le_rescaleCeiling _ _

theorem numericOperand_round_unknown (cause : FormalCause) (mode : DecimalRoundingMode)
    (places : RoundingPlaces) :
    (NumericOperand.unknown cause).round mode places = .unknown cause := by
  rfl

theorem numericOperand_round_value_preserves_fillability (amount : Rat)
    (fillability : NumericFillability) (mode : DecimalRoundingMode)
    (places : RoundingPlaces) :
    (NumericOperand.value amount fillability).round mode places =
      .value (roundDecimal mode amount places) fillability := by
  rfl

/-- Rounding preserves exactly whether a checked arithmetic outcome is available. -/
theorem numericArithmeticOutcome_round_notEvaluated_iff
    (outcome : NumericArithmeticOutcome)
    (mode : DecimalRoundingMode) (places : RoundingPlaces) :
    outcome.round mode places = .notEvaluated ↔ outcome = .notEvaluated := by
  exact numericArithmeticOutcome_mapValue_notEvaluated_iff outcome
    (fun amount fillability => (roundDecimal mode amount places, fillability))

/-- Rounding an arithmetic outcome changes only its available amount. -/
theorem numericArithmeticOutcome_round_value
    (amount : Rat) (fillability : NumericFillability)
    (mode : DecimalRoundingMode) (places : RoundingPlaces) :
    (NumericArithmeticOutcome.value amount fillability).round mode places =
      .value (roundDecimal mode amount places) fillability := by
  rfl

end A12Kernel
