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

/-- Apply source-classified retained clears before changed values. The two callbacks are deliberately distinct: a retained clear is an action, not a direct no-value outcome re-evaluated against the destination. -/
def applyTo
    (view : TemporalComputationRunView
      (TemporalComputedInstance kind) Error ResidualMessage)
    (destination : Destination)
    (applyRetainedClear : Destination → FieldId → Destination)
    (applyAccepted :
      Destination → FieldId → StoredTemporalText kind → Destination) :
    Except TemporalValueComputationApplicationError Destination :=
  match FieldId.firstDuplicate? (actionTargets view) with
  | some duplicate => .error (.duplicateActionTarget duplicate)
  | none =>
      let afterCleared := view.cleared.foldl
        applyRetainedClear destination
      .ok (view.withChanges.foldl
        (fun current computed =>
          applyAccepted current computed.targetField computed.value) afterCleared)

end TemporalValueComputationRunView

end A12Kernel
