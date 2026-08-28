import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Semantics.BooleanApplication

/-! # Shared typed Boolean and Confirm computation result -/

namespace A12Kernel

/-- One successful Boolean or Confirm computed instance with a typed payload and caller-owned target identity. -/
structure BooleanComputedInstance (Target : Type := FieldId) where
  targetField : Target
  value : Bool
  deriving Repr, DecidableEq

/-- Canonical Boolean and Confirm rendering has no target-local rejection branch after checked target admission. -/
inductive BooleanComputedError
  deriving Repr, DecidableEq

/-- The shared typed Boolean result and action channels over one caller-owned target identity. -/
structure BooleanComputationRunView (ResidualMessage Target : Type) where
  withoutErrors : List (BooleanComputedInstance Target)
  withChanges : List (BooleanComputedInstance Target)
  withErrors : List BooleanComputedError
  cleared : List Target
  formalErrorsInOperands : List ResidualMessage

namespace CheckedDocument

/-- Recover exact Boolean or Confirm target placement and typed identity from the immutable source. -/
def sourceBooleanTargetStateAt (input : CheckedDocument model)
    (address : CellAddr) : BooleanTargetState :=
  match input.source.cells.find? fun cell =>
      cell.address == address with
  | none => .absent
  | some cell =>
      if cell.stored.isEmpty then
        .presentEmpty
      else
        match cell.raw with
        | .parsed (.bool value) | .parsed (.conf value) => .presentValue value
        | _ => .presentInvalid cell.stored

/-- The fixed-target specialization of exact Boolean or Confirm source-state recovery. -/
def sourceBooleanTargetState (input : CheckedDocument model)
    (field : FieldId) : BooleanTargetState :=
  input.sourceBooleanTargetStateAt { field, path := [] }

end CheckedDocument

namespace BooleanComputationRunView

/-- The public Boolean result is error-free exactly when both error channels are empty. -/
def noErrorOccurred
    (view : BooleanComputationRunView ResidualMessage Target) : Bool :=
  view.withErrors.isEmpty && view.formalErrorsInOperands.isEmpty

/-- Classify ordered Boolean outcomes against their exact immutable source target states. -/
def fromSourcedOutcomes (residualMessages : List ResidualMessage)
    (outcomes : List (Target × BooleanComputationOutcome ×
      BooleanTargetState)) : BooleanComputationRunView ResidualMessage Target :=
  outcomes.foldr (fun (target, outcome, source) view =>
    match outcome with
    | .value value =>
        let computed : BooleanComputedInstance Target := {
          targetField := target, value
        }
        { view with
          withoutErrors := computed :: view.withoutErrors
          withChanges := if source.value? == some value then
              view.withChanges
            else
              computed :: view.withChanges }
    | .noValue | .poison _ =>
        { view with
          cleared := if source.isFilled then target :: view.cleared
            else view.cleared }) {
    withoutErrors := []
    withChanges := []
    withErrors := []
    cleared := []
    formalErrorsInOperands := residualMessages
  }

/-- Targets consumed by the retained Boolean actions. -/
def actionTargets
    (view : BooleanComputationRunView ResidualMessage Target) : List Target :=
  view.cleared ++ view.withChanges.map (·.targetField)

/-- Apply retained Boolean clears and changed values in result-channel order. -/
def applyTo [DecidableEq Target]
    (view : BooleanComputationRunView ResidualMessage Target)
    (initial : BooleanComputationDestination Target) :
    BooleanComputationDestination Target :=
  let afterClears := view.cleared.foldl
    BooleanComputationDestination.applyRetainedClear initial
  view.withChanges.foldl
    (fun current computed => current.applyValue
      computed.targetField computed.value) afterClears

end BooleanComputationRunView

end A12Kernel
