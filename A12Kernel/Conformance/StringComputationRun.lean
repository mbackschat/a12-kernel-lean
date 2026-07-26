import A12Kernel.Elaboration.StringComputationRunPlan

/-! # Checked nonrepeatable String-run locks

This first matrix locks the unique-target and supplied-order dependency gates before document execution exists.
-/

namespace A12Kernel.Conformance.StringComputationRun

open A12Kernel

private def source : FlatFieldDecl :=
  { id := 0, groupPath := ["Form"], name := "Source", policy := { kind := .string } }

private def gate : FlatFieldDecl :=
  { id := 1, groupPath := ["Form"], name := "Gate", policy := { kind := .string } }

private def producer : FlatFieldDecl :=
  { id := 2, groupPath := ["Form"], name := "Producer", policy := { kind := .string } }

private def consumer : FlatFieldDecl :=
  { id := 3, groupPath := ["Form"], name := "Consumer", policy := { kind := .string } }

private def model : FlatModel :=
  { fields := [source, gate, producer, consumer] }

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def operation? (target : FieldId) (expression : StringExpr SurfaceFieldPath) :
    Option (CheckedStringComputationOperation model) :=
  (elaborateStringComputationOperation model ["Form"] target expression).toOption

private def alternative (condition : ComputationCondition)
    (op : CheckedStringComputationOperation model) :
    ComputationAlternative (CheckedStringComputationOperation model) :=
  { precondition := condition, operation := op }

private def table? (alternatives : List
    (ComputationAlternative (CheckedStringComputationOperation model))) :
    Option (CheckedStringComputationTable model) :=
  (certifyStringComputationTable alternatives).toOption

private def holding : ComputationCondition := .fieldNotFilled gate.id

private inductive FixtureOperation
  | producerCopySource | producerValue | consumerCopy

private def FixtureOperation.checked :
    FixtureOperation → CheckedStringComputationOperation model
  | .producerCopySource =>
      (operation? producer.id (.field (bare "Source"))).get (by native_decide)
  | .producerValue => (operation? producer.id (.literal "NEW")).get (by native_decide)
  | .consumerCopy => (operation? consumer.id (.field (bare "Producer"))).get (by native_decide)

private inductive FixtureTable
  | producerCopySource | producerValue | consumerCopy

private def FixtureTable.checked :
    FixtureTable → CheckedStringComputationTable model
  | .producerCopySource =>
      (table? [alternative holding (FixtureOperation.checked .producerCopySource)]).get (by native_decide)
  | .producerValue =>
      (table? [alternative holding (FixtureOperation.checked .producerValue)]).get (by native_decide)
  | .consumerCopy =>
      (table? [alternative holding (FixtureOperation.checked .consumerCopy)]).get (by native_decide)

private def runError (tables : List (CheckedStringComputationTable model)) :
    Option StringComputationRunPlanError :=
  match certifyStringComputationRun tables with
  | .ok _ => none
  | .error error => some error

/- Duplicate targets and forward computed reads fail before execution. -/
example :
    runError [FixtureTable.checked .producerValue,
      FixtureTable.checked .producerCopySource] =
      some (.duplicateTarget producer.id) ∧
    runError [FixtureTable.checked .consumerCopy,
      FixtureTable.checked .producerValue] =
      some (.forwardDependency consumer.id producer.id) := by
  native_decide

end A12Kernel.Conformance.StringComputationRun
