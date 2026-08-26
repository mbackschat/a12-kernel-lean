import A12Kernel.Elaboration.AddressedEnumerationComputation

/-! # Exact-row Enumeration computation cascade

This purpose-specific SG4 capsule certifies one addressed Enumeration producer followed by one same-scope consumer that reads the producer target. The producer's rich outcomes become transient Enumeration cells at exact addresses; the immutable document, public result, and applied destination remain distinct.
-/

namespace A12Kernel

inductive AddressedEnumerationCascadePlanError where
  | producerReadsConsumer
  | consumerDoesNotDirectlyReadProducer
  | scopeMismatch
  deriving Repr, DecidableEq

structure CheckedAddressedEnumerationCascade (model : FlatModel) where
  private mk ::
  producer : CheckedAddressedEnumerationComputation model
  consumer : CheckedAddressedEnumerationComputation model
  producerDoesNotReadConsumer :
    producer.source.referencesField consumer.target.field = false
  consumerReadsProducerDirectly :
    consumer.source.directlyReferencesStoredField producer.target.field = true
  sameScope :
    (producer.target.declaration.repeatableScope ==
      consumer.target.declaration.repeatableScope) = true

def certifyAddressedEnumerationCascade
    (producer consumer : CheckedAddressedEnumerationComputation model) :
    Except AddressedEnumerationCascadePlanError
      (CheckedAddressedEnumerationCascade model) :=
  if hReverse :
      producer.source.referencesField consumer.target.field = false then
    if hForward : consumer.source.directlyReferencesStoredField
        producer.target.field = true then
      if hScope :
          (producer.target.declaration.repeatableScope ==
            consumer.target.declaration.repeatableScope) = true then
        .ok {
          producer, consumer
          producerDoesNotReadConsumer := hReverse
          consumerReadsProducerDirectly := hForward
          sameScope := hScope
        }
      else .error .scopeMismatch
    else .error .consumerDoesNotDirectlyReadProducer
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

structure AddressedEnumerationCascadeOutcomes where
  producer : List AddressedEnumerationComputationOutcome
  consumer : List AddressedEnumerationComputationOutcome
  deriving Repr, DecidableEq

inductive AddressedEnumerationCascadeFault where
  | producer (cause : AddressedEnumerationComputationFault)
  | dependency (target : CellAddr) (cause : EnumerationDependencyFault)
  | consumer (cause : AddressedEnumerationComputationFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedEnumerationCascade

private def dependencyCells
    (outcomes : List AddressedEnumerationComputationOutcome) :
    Except AddressedEnumerationCascadeFault
      (List (CellAddr × CheckedCell)) :=
  outcomes.mapM fun outcome => do
    let dependency ← EnumerationDependencyCell.ofResult outcome.result
      |>.mapError (.dependency outcome.targetField)
    pure (outcome.targetField, dependency.checked)

private def readAfterProducer (input : CheckedDocument model)
    (dependencies : List (CellAddr × CheckedCell))
    (address : CellAddr) : Except CheckedDocumentError CheckedCell :=
  match dependencies.find? fun dependency => dependency.1 == address with
  | some dependency => .ok dependency.2
  | none => input.read address

/-- Complete every producer row, expose only its transient exact-address cells, then execute every consumer row. -/
def execute (cascade : CheckedAddressedEnumerationCascade model)
    (input : CheckedDocument model) :
    Except AddressedEnumerationCascadeFault
      AddressedEnumerationCascadeOutcomes := do
  let producer ← cascade.producer.execute input |>.mapError .producer
  let dependencies ← dependencyCells producer
  let consumer ← cascade.consumer.executeWithRead input
      (readAfterProducer input dependencies) |>.mapError .consumer
  pure { producer, consumer }

end CheckedAddressedEnumerationCascade

end A12Kernel
