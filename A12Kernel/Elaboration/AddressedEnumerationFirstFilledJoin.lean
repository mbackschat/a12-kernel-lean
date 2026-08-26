import A12Kernel.Elaboration.AddressedEnumerationCascade
import A12Kernel.Elaboration.AddressedEnumerationFirstFilledComputation

/-! # Two-producer Enumeration `FirstFilledValue` join

This purpose-specific SG4 capsule certifies two independent addressed Enumeration producers followed by one ordered first-filled consumer. Completed producer outcomes form one transient exact-address overlay; the immutable input, three public result phases, and separately applied destination remain distinct.
-/

namespace A12Kernel

inductive AddressedEnumerationFirstFilledJoinPlanError where
  | producerTargetsSame
  | firstProducerReadsSecond
  | secondProducerReadsFirst
  | firstProducerReadsConsumer
  | secondProducerReadsConsumer
  | consumerSourcesMismatch
  deriving Repr, DecidableEq

def directEnumerationFirstFilledFieldIds?
    (source : CheckedEnumerationFirstFilledSource model scope) :
    Option (List FieldId) :=
  source.operands.mapM CheckedEnumerationFirstFilledOperand.directFieldId?

/-- Two independent producers and one exact two-slot consumer tied to their target fields in authored order. -/
structure CheckedAddressedEnumerationFirstFilledJoin (model : FlatModel) where
  private mk ::
  firstProducer : CheckedAddressedEnumerationComputation model
  secondProducer : CheckedAddressedEnumerationComputation model
  consumer : CheckedAddressedEnumerationFirstFilledComputation model
  producerTargetsDistinct :
    firstProducer.target.field ≠ secondProducer.target.field
  firstDoesNotReadSecond :
    firstProducer.source.referencesField secondProducer.target.field = false
  secondDoesNotReadFirst :
    secondProducer.source.referencesField firstProducer.target.field = false
  firstDoesNotReadConsumer :
    firstProducer.source.referencesField consumer.target.field = false
  secondDoesNotReadConsumer :
    secondProducer.source.referencesField consumer.target.field = false
  consumerSourceFields :
    directEnumerationFirstFilledFieldIds? consumer.source =
      some [firstProducer.target.field, secondProducer.target.field]

/-- Certify the bounded acyclic join and its exact ordered consumer source. -/
def certifyAddressedEnumerationFirstFilledJoin
    (firstProducer secondProducer : CheckedAddressedEnumerationComputation model)
    (consumer : CheckedAddressedEnumerationFirstFilledComputation model) :
    Except AddressedEnumerationFirstFilledJoinPlanError
      (CheckedAddressedEnumerationFirstFilledJoin model) :=
  if hDistinct : firstProducer.target.field ≠ secondProducer.target.field then
    if hFirstSecond :
        firstProducer.source.referencesField secondProducer.target.field = false then
      if hSecondFirst :
          secondProducer.source.referencesField firstProducer.target.field = false then
        if hFirstConsumer :
            firstProducer.source.referencesField consumer.target.field = false then
          if hSecondConsumer :
              secondProducer.source.referencesField consumer.target.field = false then
            if hSources : directEnumerationFirstFilledFieldIds? consumer.source =
                some [firstProducer.target.field, secondProducer.target.field] then
              .ok {
                firstProducer, secondProducer, consumer
                producerTargetsDistinct := hDistinct
                firstDoesNotReadSecond := hFirstSecond
                secondDoesNotReadFirst := hSecondFirst
                firstDoesNotReadConsumer := hFirstConsumer
                secondDoesNotReadConsumer := hSecondConsumer
                consumerSourceFields := hSources
              }
            else .error .consumerSourcesMismatch
          else .error .secondProducerReadsConsumer
        else .error .firstProducerReadsConsumer
      else .error .secondProducerReadsFirst
    else .error .firstProducerReadsSecond
  else .error .producerTargetsSame

structure AddressedEnumerationFirstFilledJoinOutcomes where
  firstProducer : List AddressedEnumerationComputationOutcome
  secondProducer : List AddressedEnumerationComputationOutcome
  consumer : List AddressedEnumerationComputationOutcome
  deriving Repr, DecidableEq

/-- Phase-separated public result projections for one completed checked join. -/
structure AddressedEnumerationFirstFilledJoinRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  join : CheckedAddressedEnumerationFirstFilledJoin model
  firstProducer : StringComputationRunView ResidualMessage CellAddr
  secondProducer : StringComputationRunView ResidualMessage CellAddr
  consumer : StringComputationRunView ResidualMessage CellAddr

inductive AddressedEnumerationFirstFilledJoinFault where
  | firstProducer (cause : AddressedEnumerationComputationFault)
  | firstDependency (target : CellAddr) (cause : EnumerationDependencyFault)
  | secondProducer (cause : AddressedEnumerationComputationFault)
  | secondDependency (target : CellAddr) (cause : EnumerationDependencyFault)
  | consumer (cause : AddressedEnumerationFirstFilledComputationFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedEnumerationFirstFilledJoin

/-- Complete both independent producer phases, expose their union as transient exact-address cells, then execute the lazy ordered consumer. -/
def execute (join : CheckedAddressedEnumerationFirstFilledJoin model)
    (input : CheckedDocument model) :
    Except AddressedEnumerationFirstFilledJoinFault
      AddressedEnumerationFirstFilledJoinOutcomes := do
  let firstProducer ← join.firstProducer.execute input |>.mapError .firstProducer
  let firstDependencies ← projectEnumerationDependencyCells firstProducer
    |>.mapError fun error => .firstDependency error.target error.cause
  let secondProducer ← join.secondProducer.execute input |>.mapError .secondProducer
  let secondDependencies ← projectEnumerationDependencyCells secondProducer
    |>.mapError fun error => .secondDependency error.target error.cause
  let dependencies := firstDependencies ++ secondDependencies
  let consumer ← join.consumer.executeWithRead input
      (readAfterEnumerationDependencies input dependencies) |>.mapError .consumer
  pure { firstProducer, secondProducer, consumer }

/-- Execute once, then classify the three retained phases independently against immutable source-target state. -/
def executeResult (join : CheckedAddressedEnumerationFirstFilledJoin model)
    (input : CheckedDocument model)
    (firstResidual secondResidual consumerResidual : List ResidualMessage) :
    Except AddressedEnumerationFirstFilledJoinFault
      (AddressedEnumerationFirstFilledJoinRunView model ResidualMessage) := do
  let outcomes ← join.execute input
  pure {
    join
    firstProducer := projectAddressedEnumerationResults input firstResidual
      outcomes.firstProducer
    secondProducer := projectAddressedEnumerationResults input secondResidual
      outcomes.secondProducer
    consumer := projectAddressedEnumerationResults input consumerResidual
      outcomes.consumer
  }

end CheckedAddressedEnumerationFirstFilledJoin

namespace AddressedEnumerationFirstFilledJoinRunView

/-- Apply the two producer phases and then the consumer phase to one separately supplied same-model destination projection. -/
def applyToChecked
    (view : AddressedEnumerationFirstFilledJoinRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (StringComputationRunView.StringComputationRunApplicationError CellAddr)
      (StringComputationDestination CellAddr) := do
  let afterFirst ←
    view.firstProducer.applyTo destination.sourceStringTargetStateAt
  let afterSecond ← view.secondProducer.applyTo afterFirst
  view.consumer.applyTo afterSecond

end AddressedEnumerationFirstFilledJoinRunView

end A12Kernel
