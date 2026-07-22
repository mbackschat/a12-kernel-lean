import A12Kernel.Elaboration.NumericStar
import A12Kernel.Semantics.FirstFilledValue

/-! # Checked finite one-level Number-star `FirstFilledValue` -/

namespace A12Kernel

namespace CheckedNumericStarSource

/-- Evaluate the checked ordered star through the existing prefix-terminating Number consumer. -/
def evaluateFirstFilled (checked : CheckedNumericStarSource model)
    (raw : RawSingleGroupContext) : Except NumericStarContextError FirstFilledNumberResult := do
  checked.validateContext raw
  pure (evalFirstFilledNumber (checked.resolvedValueSide raw))

end CheckedNumericStarSource

end A12Kernel
