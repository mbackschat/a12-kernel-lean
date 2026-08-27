import A12Kernel.Elaboration.AddressedEnumerationComputation

/-! # Exact-row Enumeration computation cascade

This purpose-specific SG4 capsule certifies one addressed Enumeration producer followed by one scope-bound consumer that reads the producer target. The producer's rich outcomes become transient Enumeration cells at exact addresses; the immutable document, public result, and applied destination remain distinct.
-/

namespace A12Kernel

inductive AddressedEnumerationCascadePlanError where
  | producerReadsConsumer
  | consumerDoesNotReadProducer
  deriving Repr, DecidableEq

structure CheckedAddressedEnumerationCascade (model : FlatModel) where
  private mk ::
  producer : CheckedAddressedEnumerationComputation model
  consumer : CheckedAddressedEnumerationComputation model
  producerDoesNotReadConsumer :
    producer.source.referencesField consumer.target.field = false
  consumerReadsProducer :
    consumer.source.referencesField producer.target.field = true

def certifyAddressedEnumerationCascade
    (producer consumer : CheckedAddressedEnumerationComputation model) :
    Except AddressedEnumerationCascadePlanError
      (CheckedAddressedEnumerationCascade model) :=
  if hReverse :
      producer.source.referencesField consumer.target.field = false then
    if hForward : consumer.source.referencesField producer.target.field = true then
      .ok {
        producer, consumer
        producerDoesNotReadConsumer := hReverse
        consumerReadsProducer := hForward
      }
    else .error .consumerDoesNotReadProducer
  else .error .producerReadsConsumer

structure EnumerationDependencyCell where
  checked : CheckedCell
  wellFormed : checked.WellFormed

inductive EnumerationDependencyFault where
  | validationScopedRequired
  deriving Repr, DecidableEq

namespace EnumerationDependencyCell

/-- Convert a completed exact-token result to the cause-blind cell observed by the consumer. -/
def ofResult :
    TokenComputationResult →
      Except EnumerationDependencyFault EnumerationDependencyCell
  | .value token => pure {
      checked := {
        rawPresent := true
        parsed := some (.enum token)
        findings := []
      }
      wellFormed := by simp [CheckedCell.WellFormed]
    }
  | .noValue => pure {
      checked := { rawPresent := false, parsed := none, findings := [] }
      wellFormed := by simp [CheckedCell.WellFormed]
    }
  | .poison .required => throw .validationScopedRequired
  | .poison _ => pure {
      checked := {
        rawPresent := true
        parsed := none
        findings := [.computedDependency]
      }
      wellFormed := by simp [CheckedCell.WellFormed]
    }

end EnumerationDependencyCell

structure EnumerationDependencyProjectionError where
  target : CellAddr
  cause : EnumerationDependencyFault
  deriving Repr, DecidableEq

/-- Convert completed exact-token outcomes to the cause-blind cells observed by a later computation. -/
def projectEnumerationDependencyCells
    (outcomes : List AddressedEnumerationComputationOutcome) :
    Except EnumerationDependencyProjectionError
      (List (CellAddr × CheckedCell)) :=
  outcomes.mapM fun outcome => do
    let dependency ← EnumerationDependencyCell.ofResult outcome.result
      |>.mapError fun cause => { target := outcome.targetField, cause }
    pure (outcome.targetField, dependency.checked)

/-- Read from a completed exact-address Enumeration overlay before falling back to one caller-supplied checked-cell view. -/
def readAfterEnumerationDependenciesWith
    (dependencies : List (CellAddr × CheckedCell))
    (fallback : CellAddr → Except CheckedDocumentError CheckedCell)
    (address : CellAddr) : Except CheckedDocumentError CheckedCell :=
  match dependencies.find? fun dependency => dependency.1 == address with
  | some dependency => .ok dependency.2
  | none => fallback address

/-- Read from a completed exact-address dependency overlay before falling back to the immutable checked input. -/
def readAfterEnumerationDependencies (input : CheckedDocument model)
    (dependencies : List (CellAddr × CheckedCell)) :
    CellAddr → Except CheckedDocumentError CheckedCell :=
  readAfterEnumerationDependenciesWith dependencies input.read

structure AddressedEnumerationCascadeOutcomes where
  producer : List AddressedEnumerationComputationOutcome
  consumer : List AddressedEnumerationComputationOutcome
  deriving Repr, DecidableEq

/-- Phase-separated public result projections for one completed checked cascade. -/
structure AddressedEnumerationCascadeRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  cascade : CheckedAddressedEnumerationCascade model
  producer : StringComputationRunView ResidualMessage CellAddr
  consumer : StringComputationRunView ResidualMessage CellAddr

inductive AddressedEnumerationCascadeFault where
  | producer (cause : AddressedEnumerationComputationFault)
  | dependency (target : CellAddr) (cause : EnumerationDependencyFault)
  | consumer (cause : AddressedEnumerationComputationFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedEnumerationCascade

/-- Complete every producer row, expose only its transient exact-address cells, then execute every consumer row. -/
def execute (cascade : CheckedAddressedEnumerationCascade model)
    (input : CheckedDocument model) :
    Except AddressedEnumerationCascadeFault
      AddressedEnumerationCascadeOutcomes := do
  let producer ← cascade.producer.execute input |>.mapError .producer
  let dependencies ← projectEnumerationDependencyCells producer
    |>.mapError fun error => .dependency error.target error.cause
  let consumer ← cascade.consumer.executeWithRead input
      (readAfterEnumerationDependencies input dependencies) |>.mapError .consumer
  pure { producer, consumer }

/-- Execute once, then classify the retained producer and consumer phases independently against immutable source-target state. -/
def executeResult (cascade : CheckedAddressedEnumerationCascade model)
    (input : CheckedDocument model)
    (producerResidual consumerResidual : List ResidualMessage) :
    Except AddressedEnumerationCascadeFault
      (AddressedEnumerationCascadeRunView model ResidualMessage) := do
  let outcomes ← cascade.execute input
  pure {
    cascade
    producer := projectAddressedEnumerationResults input producerResidual
      outcomes.producer
    consumer := projectAddressedEnumerationResults input consumerResidual
      outcomes.consumer
  }

end CheckedAddressedEnumerationCascade

namespace AddressedEnumerationCascadeRunView

/-- Apply producer actions and then consumer actions to one separately supplied same-model destination projection. -/
def applyToChecked
    (view : AddressedEnumerationCascadeRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (StringComputationRunView.StringComputationRunApplicationError CellAddr)
      (StringComputationDestination CellAddr) := do
  let afterProducer ← view.producer.applyTo destination.sourceStringTargetStateAt
  view.consumer.applyTo afterProducer

end AddressedEnumerationCascadeRunView

inductive AddressedEnumerationThreeStageCascadePlanError where
  | firstToSecond (cause : AddressedEnumerationCascadePlanError)
  | firstAndThirdTargetsSame
  | firstReadsThird
  | thirdDoesNotReadSecond
  deriving Repr, DecidableEq

/-- Exactly three serial addressed Enumeration computations with distinct targets and no reverse edge from the first stage to the third. -/
structure CheckedAddressedEnumerationThreeStageCascade (model : FlatModel) where
  private mk ::
  first : CheckedAddressedEnumerationComputation model
  second : CheckedAddressedEnumerationComputation model
  third : CheckedAddressedEnumerationComputation model
  firstDoesNotReadSecond :
    first.source.referencesField second.target.field = false
  secondReadsFirst :
    second.source.referencesField first.target.field = true
  firstAndThirdTargetsDistinct : first.target.field ≠ third.target.field
  firstDoesNotReadThird :
    first.source.referencesField third.target.field = false
  thirdReadsSecond :
    third.source.referencesField second.target.field = true

/-- Certify the two adjacent dependency edges and the remaining nonadjacent cycle boundary. -/
def certifyAddressedEnumerationThreeStageCascade
    (first second third : CheckedAddressedEnumerationComputation model) :
    Except AddressedEnumerationThreeStageCascadePlanError
      (CheckedAddressedEnumerationThreeStageCascade model) :=
  if hFirstSecond :
      first.source.referencesField second.target.field = false then
    if hSecondFirst :
        second.source.referencesField first.target.field = true then
      if hDistinct : first.target.field ≠ third.target.field then
        if hFirstThird :
            first.source.referencesField third.target.field = false then
          if hThirdSecond :
              third.source.referencesField second.target.field = true then
            .ok {
              first, second, third
              firstDoesNotReadSecond := hFirstSecond
              secondReadsFirst := hSecondFirst
              firstAndThirdTargetsDistinct := hDistinct
              firstDoesNotReadThird := hFirstThird
              thirdReadsSecond := hThirdSecond
            }
          else .error .thirdDoesNotReadSecond
        else .error .firstReadsThird
      else .error .firstAndThirdTargetsSame
    else .error (.firstToSecond .consumerDoesNotReadProducer)
  else .error (.firstToSecond .producerReadsConsumer)

structure AddressedEnumerationThreeStageCascadeAnalysis where
  targetFields : List FieldId
  fieldDependencies : List (FieldId × List FieldId)
  deriving Repr, DecidableEq

structure AddressedEnumerationThreeStageCascadeOutcomes where
  first : List AddressedEnumerationComputationOutcome
  second : List AddressedEnumerationComputationOutcome
  third : List AddressedEnumerationComputationOutcome
  deriving Repr, DecidableEq

inductive AddressedEnumerationThreeStageCascadeFault where
  | first (cause : AddressedEnumerationComputationFault)
  | firstDependency (target : CellAddr) (cause : EnumerationDependencyFault)
  | second (cause : AddressedEnumerationComputationFault)
  | secondDependency (target : CellAddr) (cause : EnumerationDependencyFault)
  | third (cause : AddressedEnumerationComputationFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedEnumerationThreeStageCascade

/-- Expose the exact ordered target and direct dependency inventories of the fixed chain. -/
def analyze (plan : CheckedAddressedEnumerationThreeStageCascade model) :
    AddressedEnumerationThreeStageCascadeAnalysis := {
  targetFields := [plan.first.target.field, plan.second.target.field,
    plan.third.target.field]
  fieldDependencies := [
    (plan.first.target.field, plan.first.source.fieldDependencies),
    (plan.second.target.field, plan.second.source.fieldDependencies),
    (plan.third.target.field, plan.third.source.fieldDependencies)]
}

/-- Accumulate the first two exact-address dependency overlays before executing the third stage. -/
def execute (plan : CheckedAddressedEnumerationThreeStageCascade model)
    (input : CheckedDocument model) :
    Except AddressedEnumerationThreeStageCascadeFault
      AddressedEnumerationThreeStageCascadeOutcomes := do
  let first ← plan.first.execute input |>.mapError .first
  let firstDependencies ← projectEnumerationDependencyCells first
    |>.mapError fun error => .firstDependency error.target error.cause
  let readAfterFirst := readAfterEnumerationDependencies input firstDependencies
  let second ← plan.second.executeWithRead input readAfterFirst
    |>.mapError .second
  let secondDependencies ← projectEnumerationDependencyCells second
    |>.mapError fun error => .secondDependency error.target error.cause
  let readAfterSecond := readAfterEnumerationDependenciesWith secondDependencies
    readAfterFirst
  let third ← plan.third.executeWithRead input readAfterSecond |>.mapError .third
  pure { first, second, third }

end CheckedAddressedEnumerationThreeStageCascade

end A12Kernel
