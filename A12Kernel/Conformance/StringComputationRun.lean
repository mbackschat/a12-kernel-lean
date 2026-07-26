import A12Kernel.Elaboration.StringComputationRun

/-! # Checked nonrepeatable String-run locks

The matrix separates stripped stale targets, completed-value visibility, reached and short-circuited poison, unrelated invalid input, and the unique dependency-ordered plan gate.
-/

namespace A12Kernel.Conformance.StringComputationRun

open A12Kernel

private def source : FlatFieldDecl :=
  { id := 0, groupPath := ["Form"], name := "Source", policy := { kind := .string } }

private def gate : FlatFieldDecl :=
  { id := 1, groupPath := ["Form"], name := "Gate", policy := { kind := .string } }

private def bad : FlatFieldDecl :=
  { id := 2, groupPath := ["Form"], name := "Bad", policy := { kind := .string } }

private def producer : FlatFieldDecl :=
  { id := 3, groupPath := ["Form"], name := "Producer", policy := { kind := .string },
    stringPolicy := { maxLength := some 3 } }

private def consumer : FlatFieldDecl :=
  { id := 4, groupPath := ["Form"], name := "Consumer", policy := { kind := .string } }

private def model : FlatModel :=
  { fields := [source, gate, bad, producer, consumer] }

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

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
  | producerCopySource | producerValue | producerError | producerPoison
  | consumerCopy | consumerWrong | consumerFallback | consumerSafe

private def FixtureOperation.checked :
    FixtureOperation → CheckedStringComputationOperation model
  | .producerCopySource =>
      (operation? producer.id (.field (bare "Source"))).get (by native_decide)
  | .producerValue => (operation? producer.id (.literal "NEW")).get (by native_decide)
  | .producerError => (operation? producer.id (.literal "LONG")).get (by native_decide)
  | .producerPoison => (operation? producer.id (.field (bare "Bad"))).get (by native_decide)
  | .consumerCopy => (operation? consumer.id (.field (bare "Producer"))).get (by native_decide)
  | .consumerWrong => (operation? consumer.id (.literal "WRONG")).get (by native_decide)
  | .consumerFallback => (operation? consumer.id (.literal "FALLBACK")).get (by native_decide)
  | .consumerSafe => (operation? consumer.id (.literal "SAFE")).get (by native_decide)

private inductive FixtureTable
  | producerCopySource | producerValue | producerError | producerPoison
  | consumerCopy | consumerReached | consumerHiddenAnd | consumerHiddenOr

private def FixtureTable.checked :
    FixtureTable → CheckedStringComputationTable model
  | .producerCopySource =>
      (table? [alternative holding (FixtureOperation.checked .producerCopySource)]).get (by native_decide)
  | .producerValue =>
      (table? [alternative holding (FixtureOperation.checked .producerValue)]).get (by native_decide)
  | .producerError =>
      (table? [alternative holding (FixtureOperation.checked .producerError)]).get (by native_decide)
  | .producerPoison =>
      (table? [alternative holding (FixtureOperation.checked .producerPoison)]).get (by native_decide)
  | .consumerCopy =>
      (table? [alternative holding (FixtureOperation.checked .consumerCopy)]).get (by native_decide)
  | .consumerReached =>
      (table? [alternative (.fieldFilled producer.id) (FixtureOperation.checked .consumerWrong),
        alternative holding (FixtureOperation.checked .consumerFallback)]).get (by native_decide)
  | .consumerHiddenAnd =>
      (table? [alternative (.and (.fieldFilled gate.id) (.fieldFilled producer.id))
          (FixtureOperation.checked .consumerWrong),
        alternative holding (FixtureOperation.checked .consumerSafe)]).get (by native_decide)
  | .consumerHiddenOr =>
      (table? [alternative (.or (.fieldNotFilled gate.id) (.fieldFilled producer.id))
        (FixtureOperation.checked .consumerSafe)]).get (by native_decide)

private def cell (field : FieldId) (stored : String) (raw : RawCell) :
    ClassifiedCellInput :=
  { address := { field, path := [] }, stored, raw }

private def checkedDocument (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" { instantiatedRows := [], cells }).toOption

private def runError (tables : List (CheckedStringComputationTable model)) :
    Option StringComputationRunPlanError :=
  match certifyStringComputationRun tables with
  | .ok _ => none
  | .error error => some error

private def outcomeAt (target : FieldId)
    (tables : List (CheckedStringComputationTable model))
    (cells : List ClassifiedCellInput := []) : Option StringTargetOutcome := do
  let run ← (certifyStringComputationRun tables).toOption
  let input ← checkedDocument cells
  let outcomes ← (run.execute prepared.patterns input).toOption
  (outcomes.find? fun entry => entry.1 == target).map (·.2)

/- Duplicate targets and forward computed reads fail before execution. -/
example :
    runError [FixtureTable.checked .producerValue,
      FixtureTable.checked .producerCopySource] =
      some (.duplicateTarget producer.id) ∧
    runError [FixtureTable.checked .consumerCopy,
      FixtureTable.checked .producerValue] =
      some (.forwardDependency consumer.id producer.id) := by
  native_decide

/- A pending or clean-no-value computed target hides its stale source value. -/
example :
    outcomeAt consumer.id [FixtureTable.checked .producerCopySource,
      FixtureTable.checked .consumerCopy]
      [cell producer.id "OLD" (.parsed (.str "OLD"))] = some .noValue := by
  native_decide

/- A completed accepted producer is immediately visible to its dependent. -/
example :
    outcomeAt consumer.id [FixtureTable.checked .producerValue,
      FixtureTable.checked .consumerCopy] =
      some (.accepted ⟨"NEW", by decide⟩) := by
  native_decide

/- A reached poisoned producer poisons the consumer and suppresses fallback. -/
example :
    outcomeAt consumer.id [FixtureTable.checked .producerPoison,
      FixtureTable.checked .consumerReached]
      [cell bad.id "bad" (.rejected .malformed)] = some (.poison .malformed) := by
  native_decide

/- Left-deciding And and Or hide the same poisoned dependency read. -/
example :
    outcomeAt consumer.id [FixtureTable.checked .producerPoison,
      FixtureTable.checked .consumerHiddenAnd]
      [cell bad.id "bad" (.rejected .malformed)] =
        some (.accepted ⟨"SAFE", by decide⟩) ∧
    outcomeAt consumer.id [FixtureTable.checked .producerPoison,
      FixtureTable.checked .consumerHiddenOr]
      [cell bad.id "bad" (.rejected .malformed)] =
        some (.accepted ⟨"SAFE", by decide⟩) := by
  native_decide

/- A target-rejected producer becomes formal poison only when the consumer reads it. -/
example :
    outcomeAt consumer.id [FixtureTable.checked .producerError,
      FixtureTable.checked .consumerCopy] =
      some (.poison .declaredConstraint) := by
  native_decide

/- An unrelated invalid input cannot affect a literal-only producer. -/
example :
    outcomeAt producer.id [FixtureTable.checked .producerValue]
      [cell bad.id "bad" (.rejected .malformed)] =
        some (.accepted ⟨"NEW", by decide⟩) := by
  native_decide

end A12Kernel.Conformance.StringComputationRun
