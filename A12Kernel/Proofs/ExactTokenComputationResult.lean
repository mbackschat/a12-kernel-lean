import A12Kernel.Elaboration.ExactTokenComputationResult
import A12Kernel.Elaboration.StringComputationRunResult

/-! # Exact-token computation target projection laws -/

namespace A12Kernel

/-- A nonempty exact token becomes the common accepted String-shaped target payload without rewriting its stored identity. -/
theorem nonemptyToken_asExactStringTargetOutcome
    (token : String) (nonempty : token ≠ "") :
    (TokenComputationResult.value token).asExactStringTargetOutcome =
      .accepted { text := token, nonempty } := by
  simp [TokenComputationResult.asExactStringTargetOutcome, nonempty]

/-- Clean absence remains no-value rather than manufacturing an empty stored token. -/
theorem noValue_asExactStringTargetOutcome :
    TokenComputationResult.noValue.asExactStringTargetOutcome = .noValue := by
  rfl

/-- Formal unavailability retains its exact cause through exact-token target projection. -/
theorem poisonedToken_asExactStringTargetOutcome (cause : FormalCause) :
    (TokenComputationResult.poison cause).asExactStringTargetOutcome =
      .poison cause := by
  rfl

/-- Exact-token projection never creates the ordinary String target-rejection channel. -/
theorem exactTokenStringResult_hasNoTargetErrors
    (target : Target) (result : TokenComputationResult)
    (source : StringTargetState) (residualMessages : List ResidualMessage) :
    (StringComputationRunView.fromSourcedOutcomes residualMessages [{
      targetField := target
      outcome := result.asExactStringTargetOutcome
      source
    }]).withErrors = [] := by
  cases result with
  | value token =>
      by_cases empty : token = "" <;>
        simp [TokenComputationResult.asExactStringTargetOutcome, empty,
          StringComputationRunView.fromSourcedOutcomes,
          StringComputationRunView.computedError?]
  | noValue | poison _ =>
      simp [TokenComputationResult.asExactStringTargetOutcome,
        StringComputationRunView.fromSourcedOutcomes,
        StringComputationRunView.computedError?]

private theorem addressedTokenResult_hasNoTargetError
    (entry : AddressedTokenComputationOutcome)
    (input : CheckedDocument model) :
    StringComputationRunView.computedError? {
      targetField := entry.targetField
      outcome := entry.result.asExactStringTargetOutcome
      source := input.sourceStringTargetStateAt entry.targetField
    } = none := by
  cases entry.result with
  | value token =>
      by_cases empty : token = "" <;>
        simp [TokenComputationResult.asExactStringTargetOutcome, empty,
          StringComputationRunView.computedError?]
  | noValue | poison _ =>
      rfl

/-- A list of exact-address token outcomes cannot create the ordinary String target-rejection channel. -/
theorem addressedTokenResults_haveNoTargetErrors
    (outcomes : List AddressedTokenComputationOutcome)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    (projectAddressedTokenResults input residualMessages outcomes).withErrors = [] := by
  simp only [projectAddressedTokenResults,
    StringComputationRunView.fromSourcedOutcomes]
  induction outcomes with
  | nil => rfl
  | cons head tail ih =>
      simp [addressedTokenResult_hasNoTargetError, ih]

end A12Kernel
