import A12Kernel.Elaboration.ParallelNumericAlternativeTable
import A12Kernel.Semantics.NumericDependency

/-! # Checked two-target parallel Number runs

This capsule certifies one exact producer-to-consumer dependency between two already-checked repeatable Number tables. It adds no graph or scheduler: the supplied pair is the complete order. The transient overlay hides stored inputs for both computed fields and exposes completed rich outcomes only at their exact repetition addresses.
-/

namespace A12Kernel

inductive ParallelNumericRunPlanError where
  | duplicateTarget (field : FieldId)
  | producerReadsConsumer (producer consumer : FieldId)
  | consumerDoesNotReadProducer (consumer producer : FieldId)
  deriving Repr, DecidableEq

/-- Two unique tables in their certified producer-first order. The consumer must read the producer, while the producer must not read the pending consumer. -/
structure CheckedParallelNumericRun (model : FlatModel) where
  producer : CheckedParallelNumericAlternativeTable model
  consumer : CheckedParallelNumericAlternativeTable model
  targetsDistinct : producer.targetField ≠ consumer.targetField
  producerIndependent :
    producer.referencesField consumer.targetField = false
  consumerDepends :
    consumer.referencesField producer.targetField = true

/-- Certify the exact two-node dependency without constructing or sorting a graph. -/
def certifyParallelNumericRun
    (producer consumer : CheckedParallelNumericAlternativeTable model) :
    Except ParallelNumericRunPlanError (CheckedParallelNumericRun model) :=
  if targetsDistinct : producer.targetField ≠ consumer.targetField then
    match producerIndependent :
        producer.referencesField consumer.targetField with
    | true =>
        .error (.producerReadsConsumer
          producer.targetField consumer.targetField)
    | false =>
        match consumerDepends :
            consumer.referencesField producer.targetField with
        | true =>
            .ok {
              producer
              consumer
              targetsDistinct
              producerIndependent
              consumerDepends
            }
        | false =>
            .error (.consumerDoesNotReadProducer
              consumer.targetField producer.targetField)
  else
    .error (.duplicateTarget producer.targetField)

/-- Exact addressed outcomes accumulated in producer-first execution order. -/
structure ParallelNumericRunState where
  completed : List ParallelNumericDirectOutcome := []
  deriving Repr, DecidableEq

namespace ParallelNumericRunState

def find? (state : ParallelNumericRunState) (address : CellAddr) :
    Option ParallelNumericDirectOutcome :=
  state.completed.find? fun completion => completion.address == address

end ParallelNumericRunState

namespace CheckedParallelNumericRun

def targetFields (run : CheckedParallelNumericRun model) :
    List FieldId :=
  [run.producer.targetField, run.consumer.targetField]

/-- Hide every pending computed address, expose an exact completed outcome as a typed dependency cell, and delegate ordinary addresses to the immutable checked document. -/
def readPolicy (run : CheckedParallelNumericRun model)
    (state : ParallelNumericRunState) (input : CheckedDocument model)
    (address : CellAddr) : Except CheckedDocumentError CheckedCell :=
  if run.targetFields.contains address.field then
    match state.find? address with
    | some completion =>
        .ok (NumericDependencyCell.ofOutcome completion.outcome).checked
    | none =>
        .ok (NumericDependencyCell.ofObservation .empty).checked
  else
    input.read address

end CheckedParallelNumericRun

end A12Kernel
