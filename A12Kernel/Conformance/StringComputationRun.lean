import A12Kernel.Elaboration.StringComputationRunRelation
import A12Kernel.Elaboration.StringComputationRunResult

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
  | consumerIndependent

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
  | .consumerIndependent =>
      (table? [alternative holding (FixtureOperation.checked .consumerSafe)]).get
        (by native_decide)

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

private def resultView?
    (tables : List (CheckedStringComputationTable model))
    (cells : List ClassifiedCellInput := [])
    (formalErrors : List FormalCause := []) :
    Option (StringComputationRunView FormalCause) := do
  let run ← (certifyStringComputationRun tables).toOption
  let input ← checkedDocument cells
  (run.executeResult prepared.patterns input formalErrors).toOption

private def producerTable := FixtureTable.checked .producerValue

private def independentConsumerTable := FixtureTable.checked .consumerIndependent

private def independentRun : CheckedStringComputationRun model := {
  tables := [producerTable, independentConsumerTable]
  nonempty := by simp
  uniqueTargets := by native_decide
  dependenciesOrdered := by native_decide
}

private def independentInput : CheckedDocument model :=
  (checkedDocument []).get (by native_decide)

private def completionAt? (state : StringComputationRunState)
    (table : CheckedStringComputationTable model) : Option StringComputationRunCompletion :=
  (independentRun.evaluateTable prepared.patterns independentInput state table).toOption

private theorem completionAt_ok (state : StringComputationRunState)
    (table : CheckedStringComputationTable model)
    (success : (completionAt? state table).isSome = true) :
    independentRun.evaluateTable prepared.patterns independentInput state table =
      .ok ((completionAt? state table).get success) := by
  cases evaluated :
      independentRun.evaluateTable prepared.patterns independentInput state table with
  | error fault =>
      have impossible : False := by
        simp [completionAt?, evaluated, Except.toOption] at success
      exact False.elim impossible
  | ok completion =>
      simp [completionAt?, evaluated, Except.toOption]

private def producerFirst := (completionAt? {} producerTable).get (by native_decide)

private def consumerFirst := (completionAt? {} independentConsumerTable).get (by native_decide)

private def afterProducer : StringComputationRunState :=
  { completed := [producerFirst] }

private def afterConsumer : StringComputationRunState :=
  { completed := [consumerFirst] }

private def consumerSecond :=
  (completionAt? afterProducer independentConsumerTable).get (by native_decide)

private def producerSecond :=
  (completionAt? afterConsumer producerTable).get (by native_decide)

private def producerThenConsumer : StringComputationRunState :=
  { completed := [producerFirst, consumerSecond] }

private def consumerThenProducer : StringComputationRunState :=
  { completed := [consumerFirst, producerSecond] }

private theorem producerEnabled (state : StringComputationRunState) :
    StringComputationDependenciesEnabled independentRun producerTable state := by
  intro dependency member referenced
  simp [independentRun] at member
  rcases member with rfl | rfl
  · have notReferenced :
        producerTable.referencesField producerTable.targetField = false := by
      native_decide
    rw [notReferenced] at referenced
    contradiction
  · have notReferenced :
        producerTable.referencesField independentConsumerTable.targetField = false := by
      native_decide
    rw [notReferenced] at referenced
    contradiction

private theorem consumerEnabled (state : StringComputationRunState) :
    StringComputationDependenciesEnabled independentRun independentConsumerTable state := by
  intro dependency member referenced
  simp [independentRun] at member
  rcases member with rfl | rfl
  · have notReferenced :
        independentConsumerTable.referencesField producerTable.targetField = false := by
      native_decide
    rw [notReferenced] at referenced
    contradiction
  · have notReferenced :
        independentConsumerTable.referencesField
          independentConsumerTable.targetField = false := by
      native_decide
    rw [notReferenced] at referenced
    contradiction

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

/- Successful unchanged values remain public successes but are not changes. -/
example : (do
    let view ← resultView? [FixtureTable.checked .producerValue]
      [cell producer.id "NEW" (.parsed (.str "NEW"))]
    pure (view.withoutErrors, view.withChanges)) =
      some ([{ targetField := producer.id, value := ⟨"NEW", by decide⟩ }], []) := by
  native_decide

/- A target error has one computed instance, so it is an error rather than a cleared target. -/
example : (do
    let view ← resultView? [FixtureTable.checked .producerError]
      [cell producer.id "OLD" (.parsed (.str "OLD"))]
    pure (view.withErrors, view.cleared, view.noErrorOccurred)) =
      some ([(⟨producer.id, ⟨"LONG", by decide⟩, .tooLong⟩ :
        StringComputedError)], [], false) := by
  native_decide

/- Clean no-value and inherited poison clear a source-filled target without creating a computed error. -/
example :
    (do
      let view ← resultView? [FixtureTable.checked .producerCopySource]
        [cell producer.id "OLD" (.parsed (.str "OLD"))]
      pure (view.cleared, view.withErrors, view.noErrorOccurred)) =
        some ([producer.id], [], true) ∧
    (do
      let view ← resultView? [FixtureTable.checked .producerPoison]
        [cell producer.id "OLD" (.parsed (.str "OLD")),
          cell bad.id "bad" (.rejected .malformed)]
      pure (view.cleared, view.withErrors, view.noErrorOccurred)) =
        some ([producer.id], [], true) := by
  native_decide

/- An empty source target is not reported as cleared, while the opaque formal-error channel independently controls the error predicate. -/
example :
    (do
      let view ← resultView? [FixtureTable.checked .producerCopySource]
        [cell producer.id "" .presentEmpty]
      pure view.cleared) = some [] ∧
    (do
      let view ← resultView? [FixtureTable.checked .producerCopySource]
      pure view.cleared) = some [] ∧
    (do
      let view ← resultView? [FixtureTable.checked .producerValue] []
        [.malformed]
      pure (view.withoutErrors, view.withChanges, view.formalErrorsInOperands,
        view.noErrorOccurred)) =
        some ([{ targetField := producer.id, value := ⟨"NEW", by decide⟩ }],
          [{ targetField := producer.id, value := ⟨"NEW", by decide⟩ }],
          [.malformed], false) := by
  native_decide

/- The independent relation admits both orders, while field lookup erases their private completion order. -/
example :
    StringComputationRunStep independentRun prepared.patterns independentInput {}
        (producerFirst.targetField, producerFirst.outcome) afterProducer ∧
    StringComputationRunStep independentRun prepared.patterns independentInput
        afterProducer (consumerSecond.targetField, consumerSecond.outcome)
        producerThenConsumer ∧
    StringComputationRunStep independentRun prepared.patterns independentInput {}
        (consumerFirst.targetField, consumerFirst.outcome) afterConsumer ∧
    StringComputationRunStep independentRun prepared.patterns independentInput
        afterConsumer (producerSecond.targetField, producerSecond.outcome)
        consumerThenProducer ∧
    (producerThenConsumer.find? producer.id).map (·.outcome) =
        (consumerThenProducer.find? producer.id).map (·.outcome) ∧
    (producerThenConsumer.find? consumer.id).map (·.outcome) =
        (consumerThenProducer.find? consumer.id).map (·.outcome) := by
  constructor
  · exact .compute producerTable (by simp [independentRun])
      (by native_decide) (producerEnabled {}) producerFirst
      (by simpa [producerFirst] using completionAt_ok {} producerTable (by native_decide))
  constructor
  · exact .compute independentConsumerTable (by simp [independentRun])
      (by native_decide) (consumerEnabled afterProducer) consumerSecond
      (by simpa [consumerSecond] using
        completionAt_ok afterProducer independentConsumerTable (by native_decide))
  constructor
  · exact .compute independentConsumerTable (by simp [independentRun])
      (by native_decide) (consumerEnabled {}) consumerFirst
      (by simpa [consumerFirst] using
        completionAt_ok {} independentConsumerTable (by native_decide))
  constructor
  · exact .compute producerTable (by simp [independentRun])
      (by native_decide) (producerEnabled afterConsumer) producerSecond
      (by simpa [producerSecond] using
        completionAt_ok afterConsumer producerTable (by native_decide))
  native_decide

end A12Kernel.Conformance.StringComputationRun
