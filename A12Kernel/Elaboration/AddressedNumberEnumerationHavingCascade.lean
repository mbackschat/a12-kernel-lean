import A12Kernel.Elaboration.AddressedNumberField
import A12Kernel.Elaboration.AddressedEnumerationFirstFilledComputation

/-! # Computed Number dependency inside Enumeration `Having`

This bounded SG4 route runs one repeatable direct Number computation before one repeatable Enumeration `FirstFilledValue` whose exact source shape is a direct field followed by a filtered star. The completed Number cells form a transient exact-address read overlay. Runtime still follows first-filled reachability, so the direct prefix can hide a poisoned dependency used only by the later `Having`.
-/

namespace A12Kernel

/-- Filter-only dependencies for the exact direct-then-filtered-star consumer shape. -/
def directThenFilteredEnumerationHavingDependencies?
    (source : CheckedEnumerationFirstFilledSource model scope) :
    Option (List FieldId) :=
  match source.first, source.rest with
  | .field .., [.star star] =>
      star.filter.map (fun having => having.condition.fieldIds)
  | _, _ => none

inductive AddressedNumberEnumerationHavingCascadeElabError where
  | consumerSourceShape
  | missingFilterDependency (field : FieldId)
  deriving Repr, DecidableEq

/-- One checked direct Number producer followed by one exact mixed Enumeration consumer whose filter reads that producer. -/
structure CheckedAddressedNumberEnumerationHavingCascade (model : FlatModel) where
  private mk ::
  producer : CheckedAddressedNumberField model
  consumer : CheckedAddressedEnumerationFirstFilledComputation model
  havingDependencies : List FieldId
  consumerSourceShape :
    directThenFilteredEnumerationHavingDependencies? consumer.source =
      some havingDependencies
  filterDependency :
    havingDependencies.contains producer.placement.targetField = true

/-- Certify the exact mixed source shape and the Number edge that makes it a two-stage route. -/
def checkAddressedNumberEnumerationHavingCascade
    (producer : CheckedAddressedNumberField model)
    (consumer : CheckedAddressedEnumerationFirstFilledComputation model) :
    Except AddressedNumberEnumerationHavingCascadeElabError
      (CheckedAddressedNumberEnumerationHavingCascade model) :=
  match hShape :
      directThenFilteredEnumerationHavingDependencies? consumer.source with
  | none => .error .consumerSourceShape
  | some dependencies =>
      if hDependency :
          dependencies.contains producer.placement.targetField = true then
        .ok {
          producer, consumer
          havingDependencies := dependencies
          consumerSourceShape := hShape
          filterDependency := hDependency
        }
      else
        .error (.missingFilterDependency producer.placement.targetField)

structure AddressedNumberEnumerationHavingCascadeAnalysis where
  producerTarget : FieldId
  consumerTarget : FieldId
  fieldDependencies : List (FieldId × List FieldId)
  deriving Repr, DecidableEq

structure AddressedNumberEnumerationHavingCascadeOutcomes where
  producer : List (SourcedNumericTargetOutcome CellAddr)
  consumer : List AddressedEnumerationComputationOutcome
  deriving Repr, DecidableEq

/-- Family-preserving result over exact addresses. Its children apply independently; this route does not define a mixed document merge. -/
structure AddressedNumberEnumerationHavingCascadeRunView
    (model : FlatModel) (NumberPayload StringResidual : Type) where
  number : NumericComputationRunView
    (ComputationFormalMessage NumberPayload) CellAddr
  enumeration : AddressedEnumerationFirstFilledComputationRunView
    model StringResidual

inductive AddressedNumberEnumerationHavingCascadeFault where
  | producer (cause : AddressedNumberFieldFault)
  | consumer (cause : AddressedEnumerationFirstFilledComputationFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedNumberEnumerationHavingCascade

/-- Expose both checked static edges without treating their ordered field inventories as a runtime trace. -/
def analyze (plan : CheckedAddressedNumberEnumerationHavingCascade model) :
    AddressedNumberEnumerationHavingCascadeAnalysis := {
  producerTarget := plan.producer.placement.targetField
  consumerTarget := plan.consumer.target.field
  fieldDependencies := [
    (plan.producer.placement.targetField,
      [plan.producer.placement.sourceDeclaration.id]),
    (plan.consumer.target.field, plan.consumer.source.fieldDependencies)]
}

/-- Complete the Number phase, expose only its exact-address dependency cells, then run the lazy mixed Enumeration consumer. -/
def execute (plan : CheckedAddressedNumberEnumerationHavingCascade model)
    (input : CheckedDocument model) :
    Except AddressedNumberEnumerationHavingCascadeFault
      AddressedNumberEnumerationHavingCascadeOutcomes := do
  let producer ← plan.producer.execute input |>.mapError .producer
  let consumer ← plan.consumer.executeWithRead input
      (readAfterNumericDependencies input producer) |>.mapError .consumer
  pure { producer, consumer }

/-- Execute once and project the two already-sourced phases through their established family result owners. -/
def executeResult (plan : CheckedAddressedNumberEnumerationHavingCascade model)
    (input : CheckedDocument model)
    (numberPayloadAt : CellAddr → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (stringResidualMessages : List StringResidual) :
    Except AddressedNumberEnumerationHavingCascadeFault
      (AddressedNumberEnumerationHavingCascadeRunView
        model NumberPayload StringResidual) := do
  let producer ← plan.producer.execute input |>.mapError .producer
  let enumeration ← plan.consumer.executeResultWithRead input
      (readAfterNumericDependencies input producer) stringResidualMessages
    |>.mapError .consumer
  pure {
    number := NumericComputationRunView.fromSourceOutcomesWithMessages
      MessagePointer.ofCellAddr numberPayloadAt numberMessages producer
    enumeration
  }

end CheckedAddressedNumberEnumerationHavingCascade

end A12Kernel
