import A12Kernel.Elaboration.NumericScale

/-! # Checked numeric-scale summary separating cases -/

namespace A12Kernel.Conformance.NumericScale

open A12Kernel

private def field (scale : Nat) : NumericScaleSummary :=
  NumericScaleSummary.field scale

private def constant (scale : Int) : NumericScaleSummary :=
  NumericScaleSummary.constant scale

/- Exact comparison pads only the smaller-scale side, and only when that side carries the constant capability. -/
example : exactNumericScaleComparisonAllowed (field 2) (constant 0) = true := by
  native_decide

example : exactNumericScaleComparisonAllowed (constant 0) (field 2) = true := by
  native_decide

example : exactNumericScaleComparisonAllowed (field 0) (constant 2) = false := by
  native_decide

example : exactNumericScaleComparisonAllowed (constant 2) (field 0) = false := by
  native_decide

/- Stripped integer constants can carry a negative scale; `100` can expand from scale -2. -/
example : exactNumericScaleComparisonAllowed (field 2) (constant (-2)) = true := by
  native_decide

example : exactNumericScaleComparisonAllowed (field 2) (field 0) = false := by
  native_decide

example : exactNumericScaleComparisonAllowed
    (NumericScaleSummary.binary .divide (field 0) (constant 1)) (field 0) = false := by
  native_decide

example : NumericScaleSummary.binary .divide (field 0) (constant 1) =
    { scale := .unknown, canExpandScale := false } := by
  native_decide

example : (NumericScaleSummary.binary .add
    (NumericScaleSummary.binary .divide (field 0) (constant 1))
    (constant 0)).scale = .unknown := by
  native_decide

/- Expandability can survive independently of a known scale and still cannot rescue exact comparison. -/
private def unknownExpandable : NumericScaleSummary :=
  NumericScaleSummary.binary .multiply
    (NumericScaleSummary.binary .divide (field 0) (field 0)) (constant 0)

example : unknownExpandable = { scale := .unknown, canExpandScale := true } := by
  native_decide

example : exactNumericScaleComparisonAllowed unknownExpandable (field 2) = false := by
  native_decide

/- Addition/subtraction needs capable terms on both sides; multiplication needs only one. -/
example : (NumericScaleSummary.binary .add
    (constant 0) (field 2)).canExpandScale = false := by
  native_decide

example : (NumericScaleSummary.binary .subtract
    (constant 0) (constant 2)).canExpandScale = true := by
  native_decide

example : (NumericScaleSummary.binary .multiply
    (constant 0) (field 2)).canExpandScale = true := by
  native_decide

example : (NumericScaleSummary.binary .multiply
    (constant (-2)) (field 2)).scale = .exact 0 := by
  native_decide

example : (NumericScaleSummary.binary .add
    (constant (-2)) (field 2)).scale = .exact 2 := by
  native_decide

example : NumericScaleSummary.rounded 3 =
    { scale := .exact 3, canExpandScale := false } := by
  native_decide

/- Exponents require a known nonpositive scale; the narrow known power result also needs a scale-0 base and a simple nonnegative constant exponent. -/
example : NumericScaleSummary.validPowerExponent (constant (-2)) = true := by
  native_decide

example : NumericScaleSummary.validPowerExponent (constant 1) = false := by
  native_decide

example : NumericScaleSummary.validPowerExponent
    (NumericScaleSummary.binary .divide (field 0) (constant 1)) = false := by
  native_decide

example : (NumericScaleSummary.power? (field 0) (constant 0) true).map (·.scale) =
    some (.exact 0) := by
  native_decide

example : (NumericScaleSummary.power? (field 2) (constant 0) true).map (·.scale) =
    some .unknown := by
  native_decide

example : (NumericScaleSummary.power? (field 0) (constant 0) false).map (·.scale) =
    some .unknown := by
  native_decide

example : (NumericScaleSummary.power? (field 0) (constant 1) true) = none := by
  native_decide

example : (NumericScaleSummary.power? (field 0) (constant 0) true).map
    (·.canExpandScale) = some false := by
  native_decide

end A12Kernel.Conformance.NumericScale
