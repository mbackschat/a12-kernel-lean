import A12Kernel.Elaboration.TemporalComputationResult

/-! # Shared scalar temporal value/clear application -/

namespace A12Kernel

/-- Structural failure shared by temporal target families whose public actions are only clears and changed values. -/
inductive TemporalValueComputationApplicationError where
  | duplicateActionTarget (field : FieldId)
  deriving Repr, DecidableEq

namespace TemporalValueComputationRunView

/-- Targets consumed by value/clear application; unchanged successes and residual messages are absent. -/
def actionTargets
    (view : TemporalComputationRunView
      (TemporalComputedInstance kind) Error ResidualMessage) :
    List FieldId :=
  view.cleared ++ view.withChanges.map (·.targetField)

/-- Apply clears before changed values through the caller's exact one-target transition. -/
def applyTo
    (view : TemporalComputationRunView
      (TemporalComputedInstance kind) Error ResidualMessage)
    (destination : Destination)
    (applyOutcome : Destination → FieldId → Outcome → Destination)
    (noValue : Outcome)
    (accepted : StoredTemporalText kind → Outcome) :
    Except TemporalValueComputationApplicationError Destination :=
  match FieldId.firstDuplicate? (actionTargets view) with
  | some duplicate => .error (.duplicateActionTarget duplicate)
  | none =>
      let afterCleared := view.cleared.foldl
        (fun current target => applyOutcome current target noValue) destination
      .ok (view.withChanges.foldl
        (fun current computed =>
          applyOutcome current computed.targetField
            (accepted computed.value)) afterCleared)

end TemporalValueComputationRunView

end A12Kernel
