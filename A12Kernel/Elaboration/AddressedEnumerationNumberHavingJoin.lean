import A12Kernel.Elaboration.AddressedEnumerationCascade
import A12Kernel.Elaboration.AddressedNumberEnumerationHavingCascade
import A12Kernel.Elaboration.AddressedFieldValueAsNumber

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
  | source => source.fieldDependencies.head?

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

/-- Three source-relative public result phases tied to the checked join that produced them. -/
structure AddressedEnumerationNumberHavingJoinRunView
    (model : FlatModel) (NumberPayload StringResidual : Type) where
  private mk ::
  plan : CheckedAddressedEnumerationNumberHavingJoin model
  number : NumericComputationRunView
    (ComputationFormalMessage NumberPayload) CellAddr
  enumerationProducer : StringComputationRunView StringResidual CellAddr
  consumer : StringComputationRunView StringResidual CellAddr

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

/-- Execute once, then classify all three retained phases against the immutable source document. -/
def executeResult (plan : CheckedAddressedEnumerationNumberHavingJoin model)
    (input : CheckedDocument model)
    (numberPayloadAt : CellAddr → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (enumerationProducerResidualMessages consumerResidualMessages :
      List StringResidual) :
    Except AddressedEnumerationNumberHavingJoinFault
      (AddressedEnumerationNumberHavingJoinRunView
        model NumberPayload StringResidual) := do
  let outcomes ← plan.execute input
  pure {
    plan
    number := NumericComputationRunView.fromSourceOutcomesWithMessages
      MessagePointer.ofCellAddr numberPayloadAt numberMessages
      outcomes.numberProducer
    enumerationProducer := projectAddressedEnumerationResults input
      enumerationProducerResidualMessages outcomes.enumerationProducer
    consumer := projectAddressedEnumerationResults input consumerResidualMessages
      outcomes.consumer
  }

end CheckedAddressedEnumerationNumberHavingJoin

namespace AddressedEnumerationNumberHavingJoinRunView

/-- Apply the two Enumeration phases in their established phase order to one separately supplied same-model destination. -/
def applyEnumerationsToChecked
    (view : AddressedEnumerationNumberHavingJoinRunView
      model NumberPayload StringResidual)
    (destination : CheckedDocument model) :
    Except (StringComputationRunView.StringComputationRunApplicationError CellAddr)
      (StringComputationDestination CellAddr) := do
  let afterProducer ← view.enumerationProducer.applyTo
    destination.sourceStringTargetStateAt
  view.consumer.applyTo afterProducer

end AddressedEnumerationNumberHavingJoinRunView

inductive AddressedEnumerationToNumberHavingCascadeElabError where
  | enumerationProducerReadsConsumer
  | enumerationProducerSourceShape
  | missingEnumerationNumberDependency
  | consumerSourceShape
  | missingEnumerationValueDependency
  | missingNumberFilterDependency
  deriving Repr, DecidableEq

/-- One direct Enumeration producer, one exact textual-to-Number dependent producer, and one filtered Enumeration consumer. -/
structure CheckedAddressedEnumerationToNumberHavingCascade (model : FlatModel) where
  private mk ::
  enumerationProducer : CheckedAddressedEnumerationComputation model
  numberProducer : CheckedAddressedFieldValueAsNumber model
  consumer : CheckedAddressedEnumerationFirstFilledComputation model
  enumerationSourceField : FieldId
  sourceShape : DirectThenFilteredEnumerationSourceShape
  enumerationDoesNotReadConsumer :
    enumerationProducer.source.referencesField consumer.target.field = false
  enumerationSourceDirect :
    directAddressedEnumerationSourceField? enumerationProducer.source =
      some enumerationSourceField
  enumerationNumberDependency :
    numberProducer.placement.sourceDeclaration.id =
      enumerationProducer.target.field
  consumerSourceShape :
    directThenFilteredEnumerationSourceShape? consumer.source = some sourceShape
  enumerationValueDependency :
    sourceShape.starredField = enumerationProducer.target.field
  numberFilterDependency :
    sourceShape.havingDependencies.contains
      numberProducer.placement.targetField = true

/-- Certify the two serial producer edges and both final lazy-consumer edges. -/
def checkAddressedEnumerationToNumberHavingCascade
    (enumerationProducer : CheckedAddressedEnumerationComputation model)
    (numberProducer : CheckedAddressedFieldValueAsNumber model)
    (consumer : CheckedAddressedEnumerationFirstFilledComputation model) :
    Except AddressedEnumerationToNumberHavingCascadeElabError
      (CheckedAddressedEnumerationToNumberHavingCascade model) :=
  if hReverse : enumerationProducer.source.referencesField consumer.target.field =
      false then
    match hEnumerationSource :
        directAddressedEnumerationSourceField? enumerationProducer.source with
    | none => .error .enumerationProducerSourceShape
    | some enumerationSourceField =>
      if hNumber : numberProducer.placement.sourceDeclaration.id =
          enumerationProducer.target.field then
        match hShape :
            directThenFilteredEnumerationSourceShape? consumer.source with
        | none => .error .consumerSourceShape
        | some shape =>
          if hValue : shape.starredField = enumerationProducer.target.field then
            if hFilter : shape.havingDependencies.contains
                numberProducer.placement.targetField = true then
              .ok {
                enumerationProducer, numberProducer, consumer
                enumerationSourceField, sourceShape := shape
                enumerationDoesNotReadConsumer := hReverse
                enumerationSourceDirect := hEnumerationSource
                enumerationNumberDependency := hNumber
                consumerSourceShape := hShape
                enumerationValueDependency := hValue
                numberFilterDependency := hFilter
              }
            else .error .missingNumberFilterDependency
          else .error .missingEnumerationValueDependency
      else .error .missingEnumerationNumberDependency
  else .error .enumerationProducerReadsConsumer

structure AddressedEnumerationToNumberHavingCascadeAnalysis where
  enumerationProducerTarget : FieldId
  numberProjection : EnumerationProjectionRef
  numberProducerTarget : FieldId
  consumerTarget : FieldId
  fieldDependencies : List (FieldId × List FieldId)
  deriving Repr, DecidableEq

structure AddressedEnumerationToNumberHavingCascadeOutcomes where
  enumerationProducer : List AddressedEnumerationComputationOutcome
  numberProducer : List (SourcedNumericTargetOutcome CellAddr)
  consumer : List AddressedEnumerationComputationOutcome
  deriving Repr, DecidableEq

/-- Three source-relative public result phases tied to the checked serial cascade that produced them. -/
structure AddressedEnumerationToNumberHavingCascadeRunView
    (model : FlatModel) (NumberPayload StringResidual : Type) where
  private mk ::
  plan : CheckedAddressedEnumerationToNumberHavingCascade model
  enumerationProducer : StringComputationRunView StringResidual CellAddr
  number : NumericComputationRunView
    (ComputationFormalMessage NumberPayload) CellAddr
  consumer : StringComputationRunView StringResidual CellAddr

inductive AddressedEnumerationToNumberHavingCascadeFault where
  | enumerationProducer (cause : AddressedEnumerationComputationFault)
  | enumerationDependency (target : CellAddr)
      (cause : EnumerationDependencyFault)
  | numberProducer (cause : AddressedFieldValueAsNumberFault)
  | consumer (cause : AddressedEnumerationFirstFilledComputationFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedEnumerationToNumberHavingCascade

/-- Expose the exact three targets, conversion identity, and ordered source inventories without turning them into a generic schedule. -/
def analyze (plan : CheckedAddressedEnumerationToNumberHavingCascade model) :
    AddressedEnumerationToNumberHavingCascadeAnalysis := {
  enumerationProducerTarget := plan.enumerationProducer.target.field
  numberProjection := plan.numberProducer.projectionRef
  numberProducerTarget := plan.numberProducer.placement.targetField
  consumerTarget := plan.consumer.target.field
  fieldDependencies := [
    (plan.enumerationProducer.target.field, [plan.enumerationSourceField]),
    (plan.numberProducer.placement.targetField,
      [plan.numberProducer.placement.sourceDeclaration.id]),
    (plan.consumer.target.field, plan.consumer.source.fieldDependencies)]
}

/-- Complete Enumeration, convert its exact produced cells to Number, then expose both overlays to the lazy filtered consumer. -/
def execute (plan : CheckedAddressedEnumerationToNumberHavingCascade model)
    (input : CheckedDocument model) :
    Except AddressedEnumerationToNumberHavingCascadeFault
      AddressedEnumerationToNumberHavingCascadeOutcomes := do
  let enumerationProducer ← plan.enumerationProducer.execute input
    |>.mapError .enumerationProducer
  let enumerationDependencies ←
    projectEnumerationDependencyCells enumerationProducer
      |>.mapError fun error => .enumerationDependency error.target error.cause
  let enumerationRead :=
    readAfterEnumerationDependencies input enumerationDependencies
  let numberProducer ← plan.numberProducer.executeWithRead input enumerationRead
    |>.mapError .numberProducer
  let read := readAfterEnumerationDependenciesWith enumerationDependencies
    (readAfterNumericDependencies input numberProducer)
  let consumer ← plan.consumer.executeWithRead input read |>.mapError .consumer
  pure { enumerationProducer, numberProducer, consumer }

/-- Execute once, then classify all three retained phases against the immutable source document. -/
def executeResult (plan : CheckedAddressedEnumerationToNumberHavingCascade model)
    (input : CheckedDocument model)
    (numberPayloadAt : CellAddr → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (enumerationProducerResidualMessages consumerResidualMessages :
      List StringResidual) :
    Except AddressedEnumerationToNumberHavingCascadeFault
      (AddressedEnumerationToNumberHavingCascadeRunView
        model NumberPayload StringResidual) := do
  let outcomes ← plan.execute input
  pure {
    plan
    enumerationProducer := projectAddressedEnumerationResults input
      enumerationProducerResidualMessages outcomes.enumerationProducer
    number := NumericComputationRunView.fromSourceOutcomesWithMessages
      MessagePointer.ofCellAddr numberPayloadAt numberMessages
      outcomes.numberProducer
    consumer := projectAddressedEnumerationResults input consumerResidualMessages
      outcomes.consumer
  }

end CheckedAddressedEnumerationToNumberHavingCascade

namespace AddressedEnumerationToNumberHavingCascadeRunView

/-- Apply the two Enumeration phases in their established phase order to one separately supplied same-model destination. -/
def applyEnumerationsToChecked
    (view : AddressedEnumerationToNumberHavingCascadeRunView
      model NumberPayload StringResidual)
    (destination : CheckedDocument model) :
    Except (StringComputationRunView.StringComputationRunApplicationError CellAddr)
      (StringComputationDestination CellAddr) := do
  let afterProducer ← view.enumerationProducer.applyTo
    destination.sourceStringTargetStateAt
  view.consumer.applyTo afterProducer

end AddressedEnumerationToNumberHavingCascadeRunView

end A12Kernel
