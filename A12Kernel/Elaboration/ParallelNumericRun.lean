import A12Kernel.Elaboration.ComputationRunPlan
import A12Kernel.Elaboration.ParallelNumericAlternativeTable
import A12Kernel.Semantics.NumericDependency

/-! # Checked finite supplied-order parallel Number runs

This capsule certifies and executes a nonempty finite list of already-checked repeatable Number tables in their supplied order. It adds no graph, sort, scheduler, or trace. The transient overlay hides stored inputs at every plan target and exposes completed rich outcomes only at their exact repetition addresses. Each checked table carries the operation-owned target-exclusion certificate proved at its complete guard/expression boundary.
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

/-- Complete checked route inventories for every target method, concatenated in supplied table order. Routes are deliberately not deduplicated across tables: different target fields can share one operand group and still own different source-relative clears. -/
def operandRoutes (plan : CheckedParallelNumericPlan model) :
    List (CheckedParallelNumericTargetRoute model) :=
  plan.tables.flatMap (·.operandRoutes)

end CheckedParallelNumericPlan

/-- Exact addressed outcomes accumulated in supplied table and target-row order. -/
structure ParallelNumericRunState where
  completed : List ParallelNumericDirectOutcome := []
  deriving Repr, DecidableEq

namespace ParallelNumericRunState

/-- Find an exact completed address. The linear lookup is intentional for the reference semantics; indexing would add mutable or duplicate state without changing the admitted behavior. -/
def find? (state : ParallelNumericRunState) (address : CellAddr) :
    Option ParallelNumericDirectOutcome :=
  state.completed.find? fun completion => completion.address == address

end ParallelNumericRunState

namespace CheckedParallelNumericPlan

/-- Hide every pending plan-target address, expose an exact completed outcome as a typed dependency cell, and delegate ordinary addresses to the immutable checked document. Stripping by target field is exact for this fragment because each table owns all existing instances of its target; index-invalid instances are independently classified as clears. -/
def readPolicy (plan : CheckedParallelNumericPlan model)
    (state : ParallelNumericRunState) (input : CheckedDocument model)
    (address : CellAddr) : Except CheckedDocumentError CheckedCell :=
  if plan.targetFields.contains address.field then
    match state.find? address with
    | some completion =>
        .ok (NumericDependencyCell.ofOutcome completion.outcome).checked
    | none =>
        .ok (NumericDependencyCell.ofObservation .empty).checked
  else
    input.read address

/-- A structural table failure retains its plan target as diagnostic context. Semantic no-value and poison remain rich outcomes instead. -/
inductive ExecutionFault where
  | table (target : FieldId)
      (error : CheckedIsolatedParallelNumericDirectRun.ExecutionError)
  deriving Repr, DecidableEq

/-- Fold checked tables in supplied order, appending each table's exact addressed outcomes to the overlay before the next table executes. A structural failure retains diagnostic target context; semantic no-value and poison remain rich outcomes. -/
def executeTables (plan : CheckedParallelNumericPlan model)
    (preliminary : CheckedIndexPreliminary model) :
    List (CheckedParallelNumericAlternativeTable model) →
      ParallelNumericRunState → Except ExecutionFault ParallelNumericRunState
  | [], state => .ok state
  | table :: remaining, state =>
      match table.executeWithRead preliminary
          (plan.readPolicy state preliminary.base) with
      | .error error => .error (.table table.targetField error)
      | .ok outcomes =>
          plan.executeTables preliminary remaining
            { completed := state.completed ++ outcomes }

/-- Execute every checked table from an empty overlay and return the complete supplied-order outcome list. -/
def execute (plan : CheckedParallelNumericPlan model)
    (preliminary : CheckedIndexPreliminary model) :
    Except ExecutionFault (List ParallelNumericDirectOutcome) :=
  match plan.executeTables preliminary plan.tables {} with
  | .error error => .error error
  | .ok state => .ok state.completed

/-- Distinguish table execution faults from failures in the existing addressed-result classifier. -/
inductive ResultError where
  | execution (error : ExecutionFault)
  | classification (error : ParallelNumericDirectRunResultError)
  deriving Repr, DecidableEq

/-- Execute and classify every addressed target family against the same immutable preliminary. The complete per-table route inventory is retained because equal operand groups for different targets own different index clears. Message payload rendering remains outside this boundary. -/
def executeResult (plan : CheckedParallelNumericPlan model)
    (preliminary : CheckedIndexPreliminary model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except ResultError
      (NumericComputationRunView (ComputationFormalMessage Payload) CellAddr) :=
  match plan.execute preliminary with
  | .error error => .error (.execution error)
  | .ok outcomes =>
      match classifyParallelNumericOutcomes preliminary plan.operandRoutes
          payloadAt supplied outcomes with
      | .error error => .error (.classification error)
      | .ok view => .ok view

end CheckedParallelNumericPlan

end A12Kernel
