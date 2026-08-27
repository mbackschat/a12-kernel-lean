import A12Kernel.Elaboration.AddressedNumberField
import A12Kernel.Elaboration.AddressedDateTimeSubdayShiftComputation
import A12Kernel.Elaboration.ComputationFormalInput

/-! # Repeatable Number-to-DateTime shift cascade

This purpose-specific SG4 capsule completes one direct repeatable Number producer before one exact-address DateTime sub-day shift whose numeric amount reads that producer. The transient amount view hides stale producer targets, exposes completed rich outcomes as cause-blind Number cells, and leaves the DateTime source on the immutable checked document.
-/

namespace A12Kernel

inductive AddressedNumberDateTimeShiftCascadePlanError where
  | consumerAmountDoesNotReadProducer
  deriving Repr, DecidableEq

/-- One checked direct Number producer followed by one addressed DateTime shift whose amount reads the producer target. -/
structure CheckedAddressedNumberDateTimeShiftCascade (model : FlatModel) where
  private mk ::
  producer : CheckedAddressedNumberField model
  consumer : CheckedAddressedDateTimeSubdayShiftComputation model
  consumerAmountReadsProducer :
    consumer.shift.amount.referencesField producer.placement.targetField = true

/-- Certify the exact cross-family dependency edge without introducing a general schedule. -/
def certifyAddressedNumberDateTimeShiftCascade
    (producer : CheckedAddressedNumberField model)
    (consumer : CheckedAddressedDateTimeSubdayShiftComputation model) :
    Except AddressedNumberDateTimeShiftCascadePlanError
      (CheckedAddressedNumberDateTimeShiftCascade model) :=
  if hDependency :
      consumer.shift.amount.referencesField producer.placement.targetField = true then
    .ok { producer, consumer, consumerAmountReadsProducer := hDependency }
  else
    .error .consumerAmountDoesNotReadProducer

structure AddressedNumberDateTimeShiftCascadeAnalysis where
  targetFields : List FieldId
  fieldDependencies : List (FieldId × List FieldId)
  deriving Repr, DecidableEq

structure AddressedNumberDateTimeShiftCascadeOutcomes where
  producer : List (SourcedNumericTargetOutcome CellAddr)
  consumer : List AddressedDateTimeSubdayShiftComputationOutcome
  deriving Repr, DecidableEq

/-- Phase-separated family results over the same exact-address domain. Each child retains its established independent application boundary. -/
structure AddressedNumberDateTimeShiftCascadeRunView
    (model : FlatModel) (NumberPayload DateTimeResidual : Type) where
  private mk ::
  plan : CheckedAddressedNumberDateTimeShiftCascade model
  number : NumericComputationRunView
    (ComputationFormalMessage NumberPayload) CellAddr
  dateTime : AddressedDateTimeSubdayShiftComputationRunView
    model DateTimeResidual

/-- One completed cross-family run paired with its call-global direct-field formal-input inventory. -/
structure AddressedNumberDateTimeShiftFormalInputRunView (model : FlatModel) where
  private mk ::
  phases : AddressedNumberDateTimeShiftCascadeRunView
    model Unit ComputationFormalInputFinding
  formalErrorsInOperands : List ComputationFormalInputFinding

inductive AddressedNumberDateTimeShiftCascadeFault where
  | producer (cause : AddressedNumberFieldFault)
  | consumer (cause : AddressedDateTimeSubdayShiftComputationFault)
  deriving Repr, DecidableEq

/-- Failure while composing the checked call-global inventory with cross-family execution. -/
inductive AddressedNumberDateTimeShiftCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | execution (cause : AddressedNumberDateTimeShiftCascadeFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedNumberDateTimeShiftCascade

/-- Retain both target families and their complete static read inventories in execution order. -/
def analyze (plan : CheckedAddressedNumberDateTimeShiftCascade model) :
    AddressedNumberDateTimeShiftCascadeAnalysis := {
  targetFields := [plan.producer.placement.targetField,
    plan.consumer.checkedTarget.targetField]
  fieldDependencies := [
    (plan.producer.placement.targetField,
      [plan.producer.placement.sourceDeclaration.id]),
    (plan.consumer.checkedTarget.targetField,
      plan.consumer.fieldDependencies)]
}

/-- Hide stale producer targets, expose exact completed outcomes as cause-blind Number cells, and delegate every other amount read to the immutable checked document's addressed validation view. -/
def amountRead (plan : CheckedAddressedNumberDateTimeShiftCascade model)
    (input : CheckedDocument model)
    (producer : List (SourcedNumericTargetOutcome CellAddr))
    (environment : Env) (field : FieldId) :
    Except CheckedAddressingError (Option CheckedCell) := do
  let address ← input.cellAddress environment field
  if field == plan.producer.placement.targetField then
    match producer.find? fun completion => completion.targetField == address with
    | some completion =>
        pure (some (NumericDependencyCell.ofOutcome completion.outcome).checked)
    | none =>
        pure (some (NumericDependencyCell.ofObservation .empty).checked)
  else
    (input.validationAddressedCell environment field).map
      (fun addressed => some addressed.cell)

/-- Complete every Number producer row before the DateTime phase starts, then expose only the transient exact-address amount view to the source-first consumer. -/
def execute (plan : CheckedAddressedNumberDateTimeShiftCascade model)
    (input : CheckedDocument model) :
    Except AddressedNumberDateTimeShiftCascadeFault
      AddressedNumberDateTimeShiftCascadeOutcomes := do
  let producer ← plan.producer.execute input |>.mapError .producer
  let consumer ← plan.consumer.executeWithAmountRead input
      (plan.amountRead input producer) |>.mapError .consumer
  pure { producer, consumer }

/-- Execute once and classify the two already-sourced phases independently against the immutable source document. -/
def executeResult (plan : CheckedAddressedNumberDateTimeShiftCascade model)
    (input : CheckedDocument model)
    (numberPayloadAt : CellAddr → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (dateTimeResidualMessages : List DateTimeResidual) :
    Except AddressedNumberDateTimeShiftCascadeFault
      (AddressedNumberDateTimeShiftCascadeRunView
        model NumberPayload DateTimeResidual) := do
  let outcomes ← plan.execute input
  pure {
    plan
    number := NumericComputationRunView.fromSourceOutcomesWithMessages
      MessagePointer.ofCellAddr numberPayloadAt numberMessages outcomes.producer
    dateTime := plan.consumer.resultFromOutcomes input
      dateTimeResidualMessages outcomes.consumer
  }

/-- Bind both analyzed family operations to one call-global direct-field inventory. -/
def formalInputPlan (plan : CheckedAddressedNumberDateTimeShiftCascade model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputOperations model plan.analyze.fieldDependencies

/-- Collect the global inventory eagerly, then execute both typed phases without supplied residuals. Number may still derive its established value-less target messages from its own outcomes. -/
def executeResultWithFormalInputs
    (plan : CheckedAddressedNumberDateTimeShiftCascade model)
    (input : CheckedDocument model) :
    Except AddressedNumberDateTimeShiftCheckedResultFault
      (AddressedNumberDateTimeShiftFormalInputRunView model) := do
  let inputPlan ← plan.formalInputPlan |>.mapError .formalInput
  let phases ← plan.executeResult input (fun _ => ()) [] []
    |>.mapError .execution
  pure {
    phases
    formalErrorsInOperands := inputPlan.findings input
  }

end CheckedAddressedNumberDateTimeShiftCascade

end A12Kernel
