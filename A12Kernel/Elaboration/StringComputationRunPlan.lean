import A12Kernel.Elaboration.StringComputationTable

/-! # Checked nonrepeatable String computation run plans

This capsule certifies a finite supplied-order list of checked String tables. Targets are unique, and a table may read another computed target only after that target's table. Ordinary input reads are not part of the scheduling graph.
-/

namespace A12Kernel

namespace CheckedStringComputationAlternative

/-- Whether either side of one checked guarded row reads the named field. -/
def referencesField (alternative : CheckedStringComputationAlternative model target)
    (field : FieldId) : Bool :=
  alternative.precondition.referencesField field ||
    alternative.expression.core.referencesField field

end CheckedStringComputationAlternative

namespace CheckedStringComputationTable

/-- Whether any guarded row reads the named field. -/
def referencesField (table : CheckedStringComputationTable model)
    (field : FieldId) : Bool :=
  table.first.referencesField field ||
    table.remaining.any (·.referencesField field)

end CheckedStringComputationTable

inductive StringComputationRunPlanError where
  | empty
  | duplicateTarget (field : FieldId)
  | forwardDependency (consumer dependency : FieldId)
  deriving Repr, DecidableEq

/-- Return the first supplied-order consumer whose table reads a target that has not run yet. -/
def firstForwardStringDependency? :
    List (CheckedStringComputationTable model) → Option (FieldId × FieldId)
  | [] => none
  | table :: remaining =>
      match remaining.find? fun later =>
          table.referencesField later.targetField with
      | some dependency => some (table.targetField, dependency.targetField)
      | none => firstForwardStringDependency? remaining

/-- A nonempty finite String run whose target is unique per step and whose computed dependencies precede every consumer. -/
structure CheckedStringComputationRun (model : FlatModel) where
  tables : List (CheckedStringComputationTable model)
  nonempty : tables ≠ []
  uniqueTargets : FieldId.firstDuplicate? (tables.map (·.targetField)) = none
  dependenciesOrdered : firstForwardStringDependency? tables = none

/-- Check the two static scheduling obligations without changing supplied table order. -/
def certifyStringComputationRun
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

end A12Kernel
