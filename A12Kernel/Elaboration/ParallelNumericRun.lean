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

/-- Complete checked route inventories for both target methods. Routes are not deduplicated across tables because equal operand groups still own different target clearings. -/
def operandRoutes (run : CheckedParallelNumericRun model) :
    List (CheckedParallelNumericTargetRoute model) :=
  run.producer.operandRoutes ++ run.consumer.operandRoutes

inductive ExecutionError where
  | producer
      (error : CheckedIsolatedParallelNumericDirectRun.ExecutionError)
  | consumer
      (error : CheckedIsolatedParallelNumericDirectRun.ExecutionError)
  deriving Repr, DecidableEq

/-- Execute the producer against the stripped input, then execute the consumer through the exact completed producer overlay. -/
def execute (run : CheckedParallelNumericRun model)
    (preliminary : CheckedIndexPreliminary model) :
    Except ExecutionError (List ParallelNumericDirectOutcome) :=
  match run.producer.executeWithRead preliminary
      (run.readPolicy {} preliminary.base) with
  | .error error => .error (.producer error)
  | .ok producerOutcomes =>
      match run.consumer.executeWithRead preliminary
          (run.readPolicy { completed := producerOutcomes }
            preliminary.base) with
      | .error error => .error (.consumer error)
      | .ok consumerOutcomes =>
          .ok (producerOutcomes ++ consumerOutcomes)

inductive ResultError where
  | execution (error : ExecutionError)
  | classification (error : ParallelNumericDirectRunResultError)
  deriving Repr, DecidableEq

/-- Execute and classify both addressed target families against the same immutable preliminary. Residual-message construction remains outside this boundary. -/
def executeResult (run : CheckedParallelNumericRun model)
    (preliminary : CheckedIndexPreliminary model)
    (residualMessages : List ResidualMessage) :
    Except ResultError
      (NumericComputationRunView ResidualMessage CellAddr) :=
  match run.execute preliminary with
  | .error error => .error (.execution error)
  | .ok outcomes =>
      match classifyParallelNumericOutcomes preliminary run.operandRoutes
          residualMessages outcomes with
      | .error error => .error (.classification error)
      | .ok view => .ok view

end CheckedParallelNumericRun

end A12Kernel
