import A12Kernel.Semantics.FirstFilledValue
import A12Kernel.Semantics.StringComputation
import A12Kernel.Elaboration.StringComputationRunResult

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

/-- One exact-address token result before source-relative String classification. -/
structure AddressedTokenComputationOutcome where
  targetField : CellAddr
  result : TokenComputationResult
  deriving Repr, DecidableEq

/-- Classify exact-address token outcomes against immutable source target state. -/
def projectAddressedTokenResults
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (outcomes : List AddressedTokenComputationOutcome) :
    StringComputationRunView ResidualMessage CellAddr :=
  StringComputationRunView.fromSourcedOutcomes residualMessages
    (outcomes.map fun entry => {
      targetField := entry.targetField
      outcome := entry.result.asExactStringTargetOutcome
      source := input.sourceStringTargetStateAt entry.targetField
    })

end A12Kernel
