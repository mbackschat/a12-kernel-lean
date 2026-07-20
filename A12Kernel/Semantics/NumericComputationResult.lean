import A12Kernel.Cell
import A12Kernel.Semantics.NumericArithmetic

/-! # Numeric computation-expression results

This operation-neutral result sits between numeric expression evaluation and every later computation consumer. It keeps an ordinary value, arithmetic domain failure, and inherited computation-read poison distinct.
-/

namespace A12Kernel

/-- The numeric expression result before any computed-target policy is applied. Number has no clean no-value arm: an empty Number operand contributes the real value zero. -/
inductive NumericComputationResult where
  | value (amount : Rat)
  | domainFailure
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

/-- Transform only an available computation value; arithmetic failure and read poison keep their meanings. -/
def NumericComputationResult.mapValue (result : NumericComputationResult)
    (transform : Rat → Rat) : NumericComputationResult :=
  match result with
  | .value amount => .value (transform amount)
  | .domainFailure => .domainFailure
  | .poison cause => .poison cause

/-- Round only an available computation value. -/
def NumericComputationResult.round (result : NumericComputationResult)
    (mode : DecimalRoundingMode) (places : RoundingPlaces) : NumericComputationResult :=
  result.mapValue (fun amount => roundDecimal mode amount places)

/-- Apply absolute value only to an available computation result. -/
def NumericComputationResult.absolute
    (result : NumericComputationResult) : NumericComputationResult :=
  result.mapValue absoluteNumeric

end A12Kernel
