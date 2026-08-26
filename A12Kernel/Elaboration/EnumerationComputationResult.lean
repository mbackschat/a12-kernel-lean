import A12Kernel.Elaboration.EnumerationComputation
import A12Kernel.Elaboration.StringComputationRunApplication

/-! # Ordinary Enumeration computation result and application

This capsule carries one model-certified ordinary Enumeration computation through the established source-relative String result and exact root-target application fold. The model index certifies the target family for both source and destination, so no second destination-model walk or general document transport is introduced.
-/

namespace A12Kernel

/-- One ordinary Enumeration computation result backed by the common String-shaped public channels. Every possible action still names the exact model-certified Enumeration target. -/
structure EnumerationComputationRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  target : CheckedEnumerationComputationTarget model
  string : StringComputationRunView ResidualMessage

namespace CheckedEnumerationComputationOperation

/-- Execute one checked ordinary Enumeration source and classify its exact token relative to the immutable source target. -/
def executeResult (operation : CheckedEnumerationComputationOperation model)
    (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    EnumerationComputationRunView model ResidualMessage :=
  let outcome :=
    (operation.source.evaluate input.flatContext).asExactStringTargetOutcome
  let string := StringComputationRunView.fromSourcedOutcomes residualMessages [{
    targetField := operation.target.field
    outcome
    source := input.sourceStringTargetState operation.target.field
  }]
  {
    target := operation.target
    string
  }

end CheckedEnumerationComputationOperation

namespace EnumerationComputationRunView

/-- Apply the retained source-relative actions to a separately supplied checked document of the same certified model. The result is the exact root text-state projection, not a reconstructed document. -/
def applyToChecked (view : EnumerationComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (StringComputationRunView.StringComputationRunApplicationError FieldId)
      (StringComputationDestination FieldId) :=
  view.string.applyTo destination.sourceStringTargetState

end EnumerationComputationRunView

end A12Kernel
