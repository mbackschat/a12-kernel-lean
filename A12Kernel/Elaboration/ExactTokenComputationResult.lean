import A12Kernel.Semantics.FirstFilledValue
import A12Kernel.Semantics.StringComputation

/-! # Exact-token computation target projection

This shared bridge converts exact nonempty tokens into the established String-shaped target outcome only after a checked family boundary has established that no further target policy can reject the token. Enumeration establishes that fact through static domain compatibility. Custom `FirstFilledValue` establishes it by requiring one registered Custom declaration on the checked source and target and by consuming only an already accepted prepared source cell.
-/

namespace A12Kernel

namespace TokenComputationResult

/-- Project a computation result whose checked family boundary guarantees exact-token target acceptance. The empty check defensively preserves the common root-store rule. -/
def asExactStringTargetOutcome : TokenComputationResult → StringTargetOutcome
  | .value token =>
      if nonempty : token ≠ "" then
        .accepted { text := token, nonempty }
      else
        .noValue
  | .noValue => .noValue
  | .poison cause => .poison cause

end TokenComputationResult

end A12Kernel
