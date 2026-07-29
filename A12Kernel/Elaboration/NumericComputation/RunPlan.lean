import A12Kernel.Elaboration.ComputationRunPlan
import A12Kernel.Elaboration.NumericComputation.Table

/-! # Checked scalar Number computation run plans

This capsule certifies supplied-order Number tables for the scalar executor only. It rejects every checked atom whose established scalar entry point would require repeatable context, then enforces unique targets and backward-only computed dependencies without constructing a graph.
-/

namespace A12Kernel

namespace CheckedNumericComputationAtom

/-- Mirror the exact context-required branches of the existing scalar Numeric evaluator. -/
def supportsScalarEvaluation :
    CheckedNumericComputationAtom model → Bool
  | .firstFilled source | .valueCount _ source =>
      source.directFields?.isSome
  | .tokenValueCount source => source.source.directFields?.isSome
  | .booleanValueCount source => source.directFields?.isSome
  | .sumOfProducts _ => false
  | .numeric (.aggregate _ source) => source.directAggregateFields?.isSome
  | .numeric (.filledGroupCount _) => false
  | .numeric _ => true

end CheckedNumericComputationAtom

namespace CheckedNumericTargetComputationOperation

def supportsScalarEvaluation
    (operation : CheckedNumericTargetComputationOperation model) : Bool :=
  operation.operation.core.expression.allAtoms
    CheckedNumericComputationAtom.supportsScalarEvaluation

def referencesField (operation :
    CheckedNumericTargetComputationOperation model) (field : FieldId) : Bool :=
  operation.operation.core.expression.anyAtom
    (CheckedNumericComputationAtom.references model field)

end CheckedNumericTargetComputationOperation

namespace CheckedNumericComputationTable

/-- Whether every operation can use the scalar evaluator if its guard selects it. -/
def supportsScalarEvaluation
    (table : CheckedNumericComputationTable model) : Bool :=
  table.selectableAlternatives.all
    (·.operation.supportsScalarEvaluation)

/-- Whether any guard or complete Numeric expression reads one exact field. -/
def referencesField (table : CheckedNumericComputationTable model)
    (field : FieldId) : Bool :=
  table.selectableAlternatives.any fun alternative =>
    alternative.precondition.referencesField field ||
      alternative.operation.referencesField field

end CheckedNumericComputationTable

def firstNonScalarNumericTable? :
    List (CheckedNumericComputationTable model) → Option FieldId
  | [] => none
  | table :: remaining =>
      if table.supportsScalarEvaluation then
        firstNonScalarNumericTable? remaining
      else
        some table.targetField

/-- Specialize the shared supplied-order dependency check to checked Number tables. -/
def firstForwardNumericDependency?
    (tables : List (CheckedNumericComputationTable model)) :
    Option (FieldId × FieldId) :=
  firstForwardComputationDependency?
    (·.targetField) (·.referencesField ·) tables

inductive NumericComputationRunPlanError where
  | empty
  | repeatableContextRequired (target : FieldId)
  | duplicateTarget (field : FieldId)
  | forwardDependency (consumer dependency : FieldId)
  deriving Repr, DecidableEq

/-- A nonempty finite scalar Number run with unique targets and backward-only computed dependencies. -/
structure CheckedNumericComputationRun (model : FlatModel) where
  tables : List (CheckedNumericComputationTable model)
  nonempty : tables ≠ []
  scalarTables : firstNonScalarNumericTable? tables = none
  uniqueTargets :
    FieldId.firstDuplicate? (tables.map (·.targetField)) = none
  dependenciesOrdered : firstForwardNumericDependency? tables = none

/-- Check scalar context, target uniqueness, and dependency order without changing supplied table order. -/
def certifyNumericComputationRun
    (tables : List (CheckedNumericComputationTable model)) :
    Except NumericComputationRunPlanError
      (CheckedNumericComputationRun model) :=
  match tables with
  | [] => .error .empty
  | first :: remaining =>
      match hScalar : firstNonScalarNumericTable? (first :: remaining) with
      | some target => .error (.repeatableContextRequired target)
      | none =>
          match hDuplicate :
              FieldId.firstDuplicate?
                ((first :: remaining).map (·.targetField)) with
          | some duplicate => .error (.duplicateTarget duplicate)
          | none =>
              match hForward :
                  firstForwardNumericDependency? (first :: remaining) with
              | some (consumer, dependency) =>
                  .error (.forwardDependency consumer dependency)
              | none => .ok {
                  tables := first :: remaining
                  nonempty := by simp
                  scalarTables := hScalar
                  uniqueTargets := hDuplicate
                  dependenciesOrdered := hForward
                }

end A12Kernel
