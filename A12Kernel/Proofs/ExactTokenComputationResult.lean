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

end A12Kernel
