import A12Kernel.Elaboration.ComputationRunPlan
import A12Kernel.Elaboration.StringComputationTable

/-! # Checked nonrepeatable String computation run plans

This capsule certifies a finite supplied-order list of checked String tables. The low-level certifier requires unique targets. The authored-table entry point first flattens repeated targets into the first target occurrence while preserving every row's encounter order, then applies the same dependency check. A table may read another computed target only after that target's consolidated table. Ordinary input reads are not part of the scheduling graph.
-/

namespace A12Kernel

namespace CheckedStringComputationAlternative

/-- Whether either side of one checked row reads the named field. An unguarded row contributes no condition dependency. -/
def referencesField (alternative : CheckedStringComputationAlternative model target)
    (field : FieldId) : Bool :=
  alternative.precondition.any (·.referencesField field) ||
    alternative.expression.core.referencesField field

end CheckedStringComputationAlternative

namespace CheckedStringComputationTable

/-- Whether any row reads the named field. -/
def referencesField (table : CheckedStringComputationTable model)
    (field : FieldId) : Bool :=
  table.selectableAlternatives.any (·.referencesField field)

end CheckedStringComputationTable

inductive StringComputationRunPlanError where
  | empty
  | duplicateTarget (field : FieldId)
  | forwardDependency (consumer dependency : FieldId)
  deriving Repr, DecidableEq

namespace CheckedStringComputationTable

/-- Append every row from a later table for the same target and policy. The first table retains declaration certificates and owns the consolidated target position. -/
def appendSameTarget (left right : CheckedStringComputationTable model)
    (sameTarget : right.targetField = left.targetField)
    (_samePolicy : right.targetPolicy = left.targetPolicy) :
    CheckedStringComputationTable model :=
  let rightAlternatives :
      List (CheckedStringComputationAlternative model left.targetField) :=
    sameTarget ▸ right.selectableAlternatives
  {
    left with
    remaining := left.remaining ++ rightAlternatives
  }

end CheckedStringComputationTable

private theorem sameStringTarget_policy
    (left right : CheckedStringComputationTable model)
    (sameTarget : right.targetField = left.targetField) :
    right.targetPolicy = left.targetPolicy := by
  have leftAdmitted := left.targetAdmitted
  have rightAdmitted := right.targetAdmitted
  unfold FlatModel.admitsStringComputationTarget at leftAdmitted rightAdmitted
  rw [sameTarget] at rightAdmitted
  cases lookup : model.lookupUniqueId left.targetField with
  | error error =>
      simp [lookup] at leftAdmitted
  | ok declaration =>
      simp [lookup] at leftAdmitted rightAdmitted
      exact rightAdmitted.2.symm.trans leftAdmitted.2

/-- Insert one checked table into an encounter-ordered target grouping, appending rows when the target is already present. -/
def insertStringComputationTable
    (incoming : CheckedStringComputationTable model) :
    List (CheckedStringComputationTable model) →
      List (CheckedStringComputationTable model)
  | [] => [incoming]
  | current :: remaining =>
      if hTarget : incoming.targetField = current.targetField then
        current.appendSameTarget incoming hTarget
          (sameStringTarget_policy current incoming hTarget) :: remaining
      else
        current :: insertStringComputationTable incoming remaining

/-- Left-to-right worker for same-target String table consolidation. -/
def flattenStringComputationTablesFrom :
    List (CheckedStringComputationTable model) →
      List (CheckedStringComputationTable model) →
        List (CheckedStringComputationTable model)
  | grouped, [] => grouped
  | grouped, table :: remaining =>
      flattenStringComputationTablesFrom
        (insertStringComputationTable table grouped) remaining

/-- Consolidate repeated String targets into their first occurrence. Tables and alternatives retain supplied encounter order; the checked model fixes one policy for every target. -/
def flattenStringComputationTables
    (tables : List (CheckedStringComputationTable model)) :
    List (CheckedStringComputationTable model) :=
  flattenStringComputationTablesFrom [] tables

/-- Specialize the shared supplied-order dependency check to checked String tables. -/
def firstForwardStringDependency?
    (tables : List (CheckedStringComputationTable model)) :
    Option (FieldId × FieldId) :=
  firstForwardComputationDependency?
    (·.targetField) (·.referencesField ·) tables

/-- A nonempty finite String run whose target is unique per step and whose computed dependencies precede every consumer. -/
structure CheckedStringComputationRun (model : FlatModel) where
  tables : List (CheckedStringComputationTable model)
  nonempty : tables ≠ []
  uniqueTargets : FieldId.firstDuplicate? (tables.map (·.targetField)) = none
  dependenciesOrdered : firstForwardStringDependency? tables = none

/-- Check the two static scheduling obligations for tables that have already been consolidated to one table per target. -/
def certifyUniqueStringComputationRun
    (tables : List (CheckedStringComputationTable model)) :
    Except StringComputationRunPlanError (CheckedStringComputationRun model) :=
  match tables with
  | [] => .error .empty
  | first :: remaining =>
      match hDuplicate :
          FieldId.firstDuplicate? ((first :: remaining).map (·.targetField)) with
      | some duplicate => .error (.duplicateTarget duplicate)
      | none =>
          match hForward : firstForwardStringDependency? (first :: remaining) with
          | some (consumer, dependency) =>
              .error (.forwardDependency consumer dependency)
          | none =>
              .ok {
                tables := first :: remaining
                nonempty := by simp
                uniqueTargets := hDuplicate
                dependenciesOrdered := hForward
              }

/-- Flatten authored same-target String computations before applying the unique-target dependency plan check. -/
def certifyStringComputationRun
    (tables : List (CheckedStringComputationTable model)) :
    Except StringComputationRunPlanError (CheckedStringComputationRun model) :=
  certifyUniqueStringComputationRun (flattenStringComputationTables tables)

end A12Kernel
