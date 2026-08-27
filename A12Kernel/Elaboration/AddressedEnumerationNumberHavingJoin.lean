import A12Kernel.Elaboration.AddressedEnumerationCascade
import A12Kernel.Elaboration.AddressedNumberEnumerationHavingCascade

/-! # Computed Enumeration value plus Number `Having`

This bounded SG4 route completes one direct Number producer and one independent direct Enumeration producer before a repeatable Enumeration `FirstFilledValue` consumes the Enumeration target as its filtered-star value and the Number target inside that star's `Having`. One combined exact-address read view preserves lazy direct-source and filter-before-value reachability without introducing a generic scheduler.
-/

namespace A12Kernel

inductive AddressedEnumerationNumberHavingJoinElabError where
  | enumerationProducerReadsConsumer
  | enumerationProducerSourceShape
  | consumerSourceShape
  | missingEnumerationValueDependency
  | missingNumberFilterDependency
  deriving Repr, DecidableEq

/-- The source identity of the exact direct-field Enumeration producer admitted by this route. -/
def directAddressedEnumerationSourceField? :
    CheckedAddressedEnumerationSource model scope → Option FieldId
  | .literal _ => none
  | .field _ _ declaration _ _ _ _ _ _ _ _ _ _ => some declaration.id

/-- Two independent typed producers and one exact filtered Enumeration consumer. -/
structure CheckedAddressedEnumerationNumberHavingJoin (model : FlatModel) where
  private mk ::
  numberProducer : CheckedAddressedNumberField model
  enumerationProducer : CheckedAddressedEnumerationComputation model
  consumer : CheckedAddressedEnumerationFirstFilledComputation model
  enumerationSourceField : FieldId
  sourceShape : DirectThenFilteredEnumerationSourceShape
  enumerationDoesNotReadConsumer :
    enumerationProducer.source.referencesField consumer.target.field = false
  enumerationSourceDirect :
    directAddressedEnumerationSourceField? enumerationProducer.source =
      some enumerationSourceField
  consumerSourceShape :
    directThenFilteredEnumerationSourceShape? consumer.source = some sourceShape
  enumerationValueDependency :
    sourceShape.starredField = enumerationProducer.target.field
  numberFilterDependency :
    sourceShape.havingDependencies.contains
      numberProducer.placement.targetField = true

/-- Certify the independent Enumeration producer and the selected-value and filter edges. -/
def checkAddressedEnumerationNumberHavingJoin
    (numberProducer : CheckedAddressedNumberField model)
    (enumerationProducer : CheckedAddressedEnumerationComputation model)
    (consumer : CheckedAddressedEnumerationFirstFilledComputation model) :
    Except AddressedEnumerationNumberHavingJoinElabError
      (CheckedAddressedEnumerationNumberHavingJoin model) :=
  if hReverse : enumerationProducer.source.referencesField consumer.target.field =
      false then
    match hEnumerationSource :
        directAddressedEnumerationSourceField? enumerationProducer.source with
    | none => .error .enumerationProducerSourceShape
    | some enumerationSourceField =>
      match hShape : directThenFilteredEnumerationSourceShape? consumer.source with
      | none => .error .consumerSourceShape
      | some shape =>
          if hValue : shape.starredField = enumerationProducer.target.field then
            if hFilter : shape.havingDependencies.contains
                numberProducer.placement.targetField = true then
              .ok {
                numberProducer, enumerationProducer, consumer
                enumerationSourceField, sourceShape := shape
                enumerationDoesNotReadConsumer := hReverse
                enumerationSourceDirect := hEnumerationSource
                consumerSourceShape := hShape
                enumerationValueDependency := hValue
                numberFilterDependency := hFilter
              }
            else .error .missingNumberFilterDependency
          else .error .missingEnumerationValueDependency
  else .error .enumerationProducerReadsConsumer

structure AddressedEnumerationNumberHavingJoinAnalysis where
  numberProducerTarget : FieldId
  enumerationProducerTarget : FieldId
  consumerTarget : FieldId
  fieldDependencies : List (FieldId × List FieldId)
  deriving Repr, DecidableEq

structure AddressedEnumerationNumberHavingJoinOutcomes where
  numberProducer : List (SourcedNumericTargetOutcome CellAddr)
  enumerationProducer : List AddressedEnumerationComputationOutcome
  consumer : List AddressedEnumerationComputationOutcome
  deriving Repr, DecidableEq

inductive AddressedEnumerationNumberHavingJoinFault where
  | numberProducer (cause : AddressedNumberFieldFault)
  | enumerationProducer (cause : AddressedEnumerationComputationFault)
  | enumerationDependency (target : CellAddr)
      (cause : EnumerationDependencyFault)
  | consumer (cause : AddressedEnumerationFirstFilledComputationFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedEnumerationNumberHavingJoin

/-- Expose both typed producer edges and the consumer's complete checked inventory. -/
def analyze (plan : CheckedAddressedEnumerationNumberHavingJoin model) :
    AddressedEnumerationNumberHavingJoinAnalysis := {
  numberProducerTarget := plan.numberProducer.placement.targetField
  enumerationProducerTarget := plan.enumerationProducer.target.field
  consumerTarget := plan.consumer.target.field
  fieldDependencies := [
    (plan.numberProducer.placement.targetField,
      [plan.numberProducer.placement.sourceDeclaration.id]),
    (plan.enumerationProducer.target.field,
      [plan.enumerationSourceField]),
    (plan.consumer.target.field, plan.consumer.source.fieldDependencies)]
}

/-- Complete both independent producers, combine their exact-address views, then run the lazy filtered consumer. -/
def execute (plan : CheckedAddressedEnumerationNumberHavingJoin model)
    (input : CheckedDocument model) :
    Except AddressedEnumerationNumberHavingJoinFault
      AddressedEnumerationNumberHavingJoinOutcomes := do
  let numberProducer ← plan.numberProducer.execute input |>.mapError .numberProducer
  let enumerationProducer ← plan.enumerationProducer.execute input
    |>.mapError .enumerationProducer
  let enumerationDependencies ←
    projectEnumerationDependencyCells enumerationProducer
      |>.mapError fun error => .enumerationDependency error.target error.cause
  let read := readAfterEnumerationDependenciesWith enumerationDependencies
    (readAfterNumericDependencies input numberProducer)
  let consumer ← plan.consumer.executeWithRead input read |>.mapError .consumer
  pure { numberProducer, enumerationProducer, consumer }

end CheckedAddressedEnumerationNumberHavingJoin

end A12Kernel
