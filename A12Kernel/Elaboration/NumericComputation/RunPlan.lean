import A12Kernel.Elaboration.ComputationRunPlan
import A12Kernel.Elaboration.NumericComputation.Table

/-! # Checked scalar Number computation run plans

This capsule certifies supplied-order Number tables for the scalar executor only. The authored-table entry point consolidates repeated targets at their first position while preserving guarded-row order and exact full target-policy identity. It then rejects every checked atom whose established scalar entry point would require repeatable context and enforces unique targets plus backward-only computed dependencies without constructing a graph. The low-level unique-target certifier remains explicit.
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
  -- Never scalar-evaluable: the contribution is a row count and this plan's context has no
  -- row topology, so the operation routes to the addressed evaluator like every other
  -- repeatable-reading atom.
  | .filledGroupCountMixed _ => false
  | .numeric (.aggregate _ source) => source.directAggregateFields?.isSome
  | .numeric (.filledGroupCount groups) =>
      groups.all fun reference =>
        (reference.computationDescendants? model).isSome
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
  | conflictingTargetPolicy (target : FieldId)
  | duplicateTarget (field : FieldId)
  | forwardDependency (consumer dependency : FieldId)
  deriving Repr, DecidableEq

/-- Append every row from a later table for the same target and policy. The first table retains its checked operations and owns the consolidated target position. -/
def CheckedNumericComputationTable.appendSameTarget
    (left right : CheckedNumericComputationTable model)
    (sameTarget : right.targetField = left.targetField)
    (samePolicy : right.targetPolicy = left.targetPolicy) :
    CheckedNumericComputationTable model :=
  let atLeftTarget :
      List (CheckedNumericComputationAlternative
        model left.targetField right.targetPolicy) :=
    sameTarget ▸ right.checkedAlternatives
  let rightAlternatives :
      List (CheckedNumericComputationAlternative
        model left.targetField left.targetPolicy) :=
    samePolicy ▸ atLeftTarget
  {
    left with
    remaining := left.remaining ++ rightAlternatives
  }

/-- Insert one checked table into an encounter-ordered target grouping. Full target-policy equality is explicit because the checked operation compatibility seam proves only scale/signedness identity; ordinary authored lowering always supplies the model-derived policy. -/
def insertNumericComputationTable
    (incoming : CheckedNumericComputationTable model) :
    List (CheckedNumericComputationTable model) →
      Except NumericComputationRunPlanError
        (List (CheckedNumericComputationTable model))
  | [] => pure [incoming]
  | current :: remaining =>
      if hTarget : incoming.targetField = current.targetField then
        if hPolicy : incoming.targetPolicy = current.targetPolicy then
          pure (current.appendSameTarget incoming hTarget hPolicy :: remaining)
        else
          throw (.conflictingTargetPolicy current.targetField)
      else
        do
          let updated ← insertNumericComputationTable incoming remaining
          pure (current :: updated)

/-- Left-to-right worker for same-target Number table consolidation. -/
def flattenNumericComputationTablesFrom :
    List (CheckedNumericComputationTable model) →
      List (CheckedNumericComputationTable model) →
        Except NumericComputationRunPlanError
          (List (CheckedNumericComputationTable model))
  | grouped, [] => pure grouped
  | grouped, table :: remaining => do
      let updated ← insertNumericComputationTable table grouped
      flattenNumericComputationTablesFrom updated remaining

/-- Consolidate repeated Number targets into their first occurrence while preserving table and row encounter order. -/
def flattenNumericComputationTables
    (tables : List (CheckedNumericComputationTable model)) :
    Except NumericComputationRunPlanError
      (List (CheckedNumericComputationTable model)) :=
  flattenNumericComputationTablesFrom [] tables

/-- A nonempty finite scalar Number run with unique targets and backward-only computed dependencies. -/
structure CheckedNumericComputationRun (model : FlatModel) where
  tables : List (CheckedNumericComputationTable model)
  nonempty : tables ≠ []
  scalarTables : firstNonScalarNumericTable? tables = none
  uniqueTargets :
    FieldId.firstDuplicate? (tables.map (·.targetField)) = none
  dependenciesOrdered : firstForwardNumericDependency? tables = none

/-- Check scalar context, target uniqueness, and dependency order for tables already consolidated to one table per target. -/
def certifyUniqueNumericComputationRun
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

/-- Flatten authored same-target Number computations before applying the unique-target scalar dependency plan check. -/
def certifyNumericComputationRun
    (tables : List (CheckedNumericComputationTable model)) :
    Except NumericComputationRunPlanError
      (CheckedNumericComputationRun model) := do
  let flattened ← flattenNumericComputationTables tables
  certifyUniqueNumericComputationRun flattened

end A12Kernel
