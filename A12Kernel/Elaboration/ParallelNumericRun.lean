import A12Kernel.Elaboration.ComputationRunPlan
import A12Kernel.Elaboration.ParallelNumericAlternativeTable
import A12Kernel.Semantics.NumericDependency

/-! # Checked supplied-order parallel Number runs

This capsule retains the completed two-target producer/consumer execution and adds a conservative finite plan over the same already-checked repeatable Number tables. The finite certificate checks only nonemptiness, target uniqueness, and reads of later supplied targets; it adds no graph, sort, scheduler, or trace. Current checked route and operand construction reject the exercised target-group self-reference shapes, but the finite plan does not restate that behavior as a named certificate.
-/

namespace A12Kernel

/-- Return the first table that reads a target owned by a later supplied table. -/
def firstForwardParallelNumericDependency?
    (tables : List (CheckedParallelNumericAlternativeTable model)) :
    Option (FieldId × FieldId) :=
  firstForwardComputationDependency?
    (·.targetField) (·.referencesField ·) tables

/-- Structural failures while checking a supplied finite table list. -/
inductive ParallelNumericPlanError where
  | empty
  | duplicateTarget (field : FieldId)
  | forwardDependency (consumer dependency : FieldId)
  deriving Repr, DecidableEq

/-- A nonempty finite supplied-order repeatable Number plan with unique targets and no read of a later plan target. -/
structure CheckedParallelNumericPlan (model : FlatModel) where
  tables : List (CheckedParallelNumericAlternativeTable model)
  nonempty : tables ≠ []
  uniqueTargets :
    FieldId.firstDuplicate? (tables.map (·.targetField)) = none
  dependenciesOrdered :
    firstForwardParallelNumericDependency? tables = none

/-- Check target uniqueness and dependency order without constructing or sorting a graph. -/
def certifyParallelNumericPlan
    (tables : List (CheckedParallelNumericAlternativeTable model)) :
    Except ParallelNumericPlanError (CheckedParallelNumericPlan model) :=
  match tables with
  | [] => .error .empty
  | first :: remaining =>
      match hDuplicate :
          FieldId.firstDuplicate?
            ((first :: remaining).map (·.targetField)) with
      | some duplicate => .error (.duplicateTarget duplicate)
      | none =>
          match hForward :
              firstForwardParallelNumericDependency?
                (first :: remaining) with
          | some (consumer, dependency) =>
              .error (.forwardDependency consumer dependency)
          | none =>
              .ok {
                tables := first :: remaining
                nonempty := by simp
                uniqueTargets := hDuplicate
                dependenciesOrdered := hForward
              }

namespace CheckedParallelNumericPlan

/-- The plan's unique target fields in supplied execution order. -/
def targetFields (plan : CheckedParallelNumericPlan model) :
    List FieldId :=
  plan.tables.map (·.targetField)

end CheckedParallelNumericPlan

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
