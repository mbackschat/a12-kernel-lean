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

/-- Project the shared partial arithmetic result into the computation-specific result domain. -/
def NumericComputationResult.ofArithmetic :
    NumericArithmeticResult → NumericComputationResult
  | .value amount => .value amount
  | .notEvaluated => .domainFailure

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

/-- Combine two already-reached numeric operands. Poison retains authored priority, then arithmetic domain failure absorbs, and only two values reach the operation-specific value combiner. -/
def NumericComputationResult.combineReached
    (combineValues : Rat → Rat → NumericComputationResult) :
    NumericComputationResult → NumericComputationResult → NumericComputationResult
  | .poison cause, _ => .poison cause
  | _, .poison cause => .poison cause
  | .domainFailure, _ => .domainFailure
  | _, .domainFailure => .domainFailure
  | .value left, .value right => combineValues left right

/-- Evaluate power over two already-reached computation operands. Runtime-invalid power uses the same arithmetic-domain result as invalid division. -/
def NumericComputationResult.evalPower :
    NumericComputationResult → NumericComputationResult →
      NumericComputationResult
  | left, right =>
      NumericComputationResult.combineReached
        (fun base exponent =>
          NumericComputationResult.ofArithmetic (powerNumeric base exponent))
        left right

/-- Select two reached operand-list computation results through the shared poison/domain/value combiner. The evaluator is responsible for not reaching the right operand after a left poison. -/
def NumericExtremumOp.selectComputationResult (op : NumericExtremumOp) :
    NumericComputationResult → NumericComputationResult → NumericComputationResult
  | left, right =>
      NumericComputationResult.combineReached
        (fun leftValue rightValue => .value (op.selectAmount leftValue rightValue))
        left right

end A12Kernel
