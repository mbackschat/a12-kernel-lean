import A12Kernel.Conformance.NumericComputation.Table
import A12Kernel.Elaboration.NumericComputation.RunRelation

/-! # Checked scalar Number run locks -/

namespace A12Kernel.Conformance.NumericComputation.RunPlan

open A12Kernel
open A12Kernel.Conformance.NumericComputation.Support

private def table? (target : FieldId)
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (guard : ComputationCondition := .fieldNotFilled laterId)
    (suppressExactScaleWarning : Bool := false) :
    Option (CheckedNumericComputationTable model) := do
  let operation ← (elaborateNumericTargetComputationOperation
    model ["Root"] target expression suppressExactScaleWarning).toOption
  (certifyNumericComputationTable [
    { precondition := guard, operation }]).toOption

private def tableWithPolicy? (target : FieldId)
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (policy : NumericTargetPolicy) :
    Option (CheckedNumericComputationTable model) := do
  let core ← (elaborateNumericComputationOperation
    model ["Root"] target expression).toOption
  let operation ← (core.attachTargetPolicy policy).toOption
  (certifyNumericComputationTable [
    { precondition := some (.fieldNotFilled laterId), operation }]).toOption

private def completeTable?
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom) :
    Option (CheckedNumericComputationTable model) := do
  let operation ← (elaborateCompleteNumericTargetComputationOperation
    model ["Root"] targetId expression).toOption
  (certifyNumericComputationTable [
    { precondition := some (.fieldNotFilled laterId), operation }]).toOption

private def repeatableTable? :=
  completeTable? surfaceRepeatableFirstFilled

private def collectTables? :
    List (Option (CheckedNumericComputationTable model)) →
      Option (List (CheckedNumericComputationTable model))
  | [] => some []
  | some table :: remaining => (table :: ·) <$> collectTables? remaining
  | none :: _ => none

private def runError?
    (tables : List (Option (CheckedNumericComputationTable model))) :
    Option NumericComputationRunPlanError := do
  let checked ← collectTables? tables
  match certifyNumericComputationRun checked with
  | .error error => some error
  | .ok _ => none

private def uniqueRunError?
    (tables : List (Option (CheckedNumericComputationTable model))) :
    Option NumericComputationRunPlanError := do
  let checked ← collectTables? tables
  match certifyUniqueNumericComputationRun checked with
  | .error error => some error
  | .ok _ => none

private def runTargets?
    (tables : List (Option (CheckedNumericComputationTable model))) :
    Option (List FieldId) := do
  let checked ← collectTables? tables
  let run ← (certifyNumericComputationRun checked).toOption
  pure (run.tables.map (·.targetField))

private def literal (value : Rat) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .literal { value, authoredScale := 0 }

private def divisionByZero :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .divide (literal 1) (literal 0)

private def zeroForbiddenPolicy : NumericTargetPolicy :=
  { info := numberInfo
    zeroAllowed := false
    minLeMax := by decide }

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def checkedDocument (cells : List ClassifiedCellInput := []) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US"
    { instantiatedRows := [], cells }).toOption

private def inputCell (field : FieldId) (stored : String) (amount : Rat) :
    ClassifiedCellInput :=
  { address := { field, path := [] }, stored, raw := .parsed (.num amount) }

/-- A stored Date cell whose calendar provenance selects whether a month/year difference can decode it at all. -/
private def dateInput (basis : DateCalendarBasis) : ClassifiedCellInput :=
  { address := { field := dateId, path := [] }
    stored := "2020-02-29"
    raw := .parsed (dateValue 2020 2 29 basis) }

private def dateTimeInput (epochMillis : Int) : ClassifiedCellInput :=
  { address := { field := dateTimeId, path := [] }
    stored := "2024-06-25T05:21:07"
    raw := .parsed (dateTimeValueAt epochMillis) }

private def worldAt (epochMillis : Int) : World :=
  { now := { epochMillis } }

private def executionWorld : World := worldAt 0

private def runOutcomes?
    (tables : List (Option (CheckedNumericComputationTable model)))
    (cells : List ClassifiedCellInput := []) :
    Option (List (FieldId × NumericTargetOutcome)) := do
  let checked ← collectTables? tables
  let run ← (certifyNumericComputationRun checked).toOption
  let input ← checkedDocument cells
  (run.execute executionWorld input).toOption

private def runFault?
    (tables : List (Option (CheckedNumericComputationTable model)))
    (cells : List ClassifiedCellInput := []) :
    Option NumericComputationRunFault := do
  let checked ← collectTables? tables
  let run ← (certifyNumericComputationRun checked).toOption
  let input ← checkedDocument cells
  match run.execute executionWorld input with
  | .error fault => some fault
  | .ok _ => none

private def runOutcomesAt?
    (nowMillis : Int)
    (tables : List (Option (CheckedNumericComputationTable model)))
    (cells : List ClassifiedCellInput := []) :
    Option (List (FieldId × NumericTargetOutcome)) := do
  let checked ← collectTables? tables
  let run ← (certifyNumericComputationRun checked).toOption
  let input ← checkedDocument cells
  (run.execute (worldAt nowMillis) input).toOption

private def independentSourceTable : CheckedNumericComputationTable model :=
  (table? sourceId (literal 2)).get (by native_decide)

private def independentTargetTable : CheckedNumericComputationTable model :=
  (table? targetId (literal 3)).get (by native_decide)

private def independentRun : CheckedNumericComputationRun model := {
  tables := [independentSourceTable, independentTargetTable]
  nonempty := by simp
  scalarTables := by native_decide
  uniqueTargets := by native_decide
  dependenciesOrdered := by native_decide
}

private def independentInput : CheckedDocument model :=
  (checkedDocument []).get (by native_decide)

private def completionAt? (state : NumericComputationRunState)
    (table : CheckedNumericComputationTable model) :
    Option NumericComputationRunCompletion :=
  (independentRun.evaluateTable executionWorld independentInput state table).toOption

private theorem completionAt_ok (state : NumericComputationRunState)
    (table : CheckedNumericComputationTable model)
    (success : (completionAt? state table).isSome = true) :
    independentRun.evaluateTable executionWorld independentInput state table =
      .ok ((completionAt? state table).get success) := by
  cases evaluated :
      independentRun.evaluateTable executionWorld independentInput state table with
  | error fault =>
      have impossible : False := by
        simp [completionAt?, evaluated, Except.toOption] at success
      exact False.elim impossible
  | ok completion =>
      simp [completionAt?, evaluated, Except.toOption]

private def sourceFirst :=
  (completionAt? {} independentSourceTable).get (by native_decide)

private def afterSource : NumericComputationRunState :=
  { completed := [sourceFirst] }

private def targetSecond :=
  (completionAt? afterSource independentTargetTable).get (by native_decide)

private def targetFirst :=
  (completionAt? {} independentTargetTable).get (by native_decide)

private def afterTarget : NumericComputationRunState :=
  { completed := [targetFirst] }

private def sourceSecond :=
  (completionAt? afterTarget independentSourceTable).get (by native_decide)

private def sourceThenTarget : NumericComputationRunState :=
  { completed := [sourceFirst, targetSecond] }

private def targetThenSource : NumericComputationRunState :=
  { completed := [targetFirst, sourceSecond] }

private theorem sourceEnabled (state : NumericComputationRunState) :
    NumericComputationDependenciesEnabled
      independentRun independentSourceTable state := by
  intro dependency member referenced
  simp [independentRun] at member
  rcases member with rfl | rfl
  · have notReferenced :
        independentSourceTable.referencesField
          independentSourceTable.targetField = false := by
      native_decide
    rw [notReferenced] at referenced
    contradiction
  · have notReferenced :
        independentSourceTable.referencesField
          independentTargetTable.targetField = false := by
      native_decide
    rw [notReferenced] at referenced
    contradiction

private theorem targetEnabled (state : NumericComputationRunState) :
    NumericComputationDependenciesEnabled
      independentRun independentTargetTable state := by
  intro dependency member referenced
  simp [independentRun] at member
  rcases member with rfl | rfl
  · have notReferenced :
        independentTargetTable.referencesField
          independentSourceTable.targetField = false := by
      native_decide
    rw [notReferenced] at referenced
    contradiction
  · have notReferenced :
        independentTargetTable.referencesField
          independentTargetTable.targetField = false := by
      native_decide
    rw [notReferenced] at referenced
    contradiction

/- The scalar plan rejects empty input and the first table whose selected operation could require repeatable context. -/
example :
    runError? [] = some .empty ∧
    runError? [repeatableTable?] =
        some (.repeatableContextRequired targetId) ∧
    runError? [completeTable? (surfaceRepeatableValueCount 1)] =
        some (.repeatableContextRequired targetId) ∧
    runError? [completeTable? (surfaceRepeatableTokenValueCount "X")] =
        some (.repeatableContextRequired targetId) ∧
    runError? [completeTable? surfaceProductAggregate] =
        some (.repeatableContextRequired targetId) ∧
    runError? [completeTable?
      ((surfaceRepeatableAggregate .sum).map
        SurfaceNumericComputationAtom.numeric)] =
      some (.repeatableContextRequired targetId) := by
  native_decide

/- The low-level plan keeps structural target uniqueness, while the authored-table entry point consolidates repeated targets into the first target position. -/
example :
    uniqueRunError? [
      table? sourceId (literal 1),
      table? sourceId (literal 2)] =
      some (.duplicateTarget sourceId) := by
  native_decide

/- Same-target consolidation fails closed when the low-level target-policy compatibility seam supplies conflicting full policies. Ordinary authored lowering derives one policy from the model and cannot reach this branch. -/
example :
    runError? [
      table? sourceId (literal 1),
      tableWithPolicy? sourceId (literal 2) zeroForbiddenPolicy] =
        some (.conflictingTargetPolicy sourceId) := by
  native_decide

/- Same-target Number rows retain encounter order: a selected value ends the target scan, while a false guard alone falls through to the later authored table. -/
example :
    runOutcomes? [
      table? sourceId (literal 1),
      table? sourceId (literal 2)] =
        some [
          (sourceId, .accepted { unscaled := 1, scale := 0 })] ∧
    runOutcomes? [
      table? sourceId (literal 1) (.fieldFilled wrongId),
      table? sourceId (literal 2)] =
        some [
          (sourceId, .accepted { unscaled := 2, scale := 0 })] := by
  native_decide

/- A selected domain-invalid Number row terminates the consolidated target scan; a later valid row cannot replace it. -/
example :
    runOutcomes? [
      table? sourceId divisionByZero
        (suppressExactScaleWarning := true),
      table? sourceId (literal 2)] =
        some [
          (sourceId, .invalidNoValue .calculationValue)] := by
  native_decide

/- Consolidation keeps the first target position, so a consumer encountered between two producer tables runs only after their one flattened first-selected table. -/
example :
    runTargets? [
      table? sourceId (literal 1) (.fieldFilled wrongId),
      table? targetId (surfaceField ["Root"] "Source"),
      table? sourceId (literal 2)] =
        some [sourceId, targetId] ∧
    runOutcomes? [
      table? sourceId (literal 1) (.fieldFilled wrongId),
      table? targetId (surfaceField ["Root"] "Source"),
      table? sourceId (literal 2)] =
        some [
          (sourceId, .accepted { unscaled := 2, scale := 0 }),
          (targetId, .accepted { unscaled := 2, scale := 0 })] := by
  native_decide

/- A computed dependency must precede its consumer, whether the read occurs in the Numeric tree or a direct-presence guard. -/
example :
    runError? [
      table? targetId (surfaceField ["Root"] "Source"),
      table? sourceId (literal 2)] =
        some (.forwardDependency targetId sourceId) ∧
    runError? [
      table? targetId (literal 3) (.fieldFilled sourceId),
      table? sourceId (literal 2)] =
        some (.forwardDependency targetId sourceId) := by
  native_decide

/- The same dependency is accepted in producer-first order without changing supplied order. -/
example :
    runTargets? [
      table? sourceId (literal 2),
      table? targetId (surfaceField ["Root"] "Source")] =
        some [sourceId, targetId] ∧
    runTargets? [completeTable? (surfaceFirstFilled
      (.field (surfacePath ["Root"] "Source"))
      [.field (surfacePath ["Root"] "Later")])] =
        some [targetId] := by
  native_decide

/- A completed producer shadows stale source data with its exact accepted value. -/
example :
    runOutcomes? [
      table? sourceId (literal 2),
      table? targetId (surfaceField ["Root"] "Source")]
      [inputCell sourceId "9" 9, inputCell targetId "8" 8] =
        some [
          (sourceId, .accepted { unscaled := 2, scale := 0 }),
          (targetId, .accepted { unscaled := 2, scale := 0 })] := by
  native_decide

/- A clean no-result hides the stale computed input and supplies numeric empty-as-zero downstream. -/
example :
    runOutcomes? [
      table? sourceId (literal 2) (.fieldFilled wrongId),
      table? laterId (surfaceField ["Root"] "Source")
        (.fieldNotFilled wrongId)]
      [inputCell sourceId "9" 9] =
        some [
          (sourceId, .noValue),
          (laterId, .accepted { unscaled := 0, scale := 0 })] := by
  native_decide

/- A reached domain-invalid producer becomes cause-blind poison at the consumer. -/
example :
    runOutcomes? [
      table? sourceId divisionByZero
        (suppressExactScaleWarning := true),
      table? targetId (surfaceField ["Root"] "Source")] =
        some [
          (sourceId, .invalidNoValue .calculationValue),
          (targetId, .inheritedPoison .computedDependency)] := by
  native_decide

/- One caller-supplied world reaches every selected table through the existing overlay. Reusing the checked plan under another world changes only the dynamic `Now` result. -/
example :
    let elapsed := surfaceDateTimeDifference .seconds
      (surfaceDateOperand "DateTime") .now
    let tables := [
      table? sourceId (literal 2) (.fieldNotFilled wrongId),
      table? laterId elapsed (.fieldFilled sourceId)]
    runOutcomesAt? 999 tables [dateTimeInput 0] =
        some [
          (sourceId, .accepted { unscaled := 2, scale := 0 }),
          (laterId, .accepted { unscaled := 0, scale := 0 })] ∧
      runOutcomesAt? 1000 tables [dateTimeInput 0] =
        some [
          (sourceId, .accepted { unscaled := 2, scale := 0 }),
          (laterId, .accepted { unscaled := 1, scale := 0 })] := by
  native_decide

/- The relation admits both orders for independent tables, and target lookup erases private completion order. -/
example :
    NumericComputationRunStep independentRun executionWorld independentInput {}
        (sourceFirst.targetField, sourceFirst.outcome) afterSource ∧
    NumericComputationRunStep independentRun executionWorld independentInput afterSource
        (targetSecond.targetField, targetSecond.outcome) sourceThenTarget ∧
    NumericComputationRunStep independentRun executionWorld independentInput {}
        (targetFirst.targetField, targetFirst.outcome) afterTarget ∧
    NumericComputationRunStep independentRun executionWorld independentInput afterTarget
        (sourceSecond.targetField, sourceSecond.outcome) targetThenSource ∧
    (sourceThenTarget.find? sourceId).map (·.outcome) =
        (targetThenSource.find? sourceId).map (·.outcome) ∧
    (sourceThenTarget.find? targetId).map (·.outcome) =
        (targetThenSource.find? targetId).map (·.outcome) := by
  constructor
  · exact .compute independentSourceTable (by simp [independentRun])
      (by native_decide) (sourceEnabled {}) sourceFirst
      (by simpa [sourceFirst] using
        completionAt_ok {} independentSourceTable (by native_decide))
  constructor
  · exact .compute independentTargetTable (by simp [independentRun])
      (by native_decide) (targetEnabled afterSource) targetSecond
      (by simpa [targetSecond] using
        completionAt_ok afterSource independentTargetTable (by native_decide))
  constructor
  · exact .compute independentTargetTable (by simp [independentRun])
      (by native_decide) (targetEnabled {}) targetFirst
      (by simpa [targetFirst] using
        completionAt_ok {} independentTargetTable (by native_decide))
  constructor
  · exact .compute independentSourceTable (by simp [independentRun])
      (by native_decide) (sourceEnabled afterTarget) sourceSecond
      (by simpa [sourceSecond] using
        completionAt_ok afterTarget independentSourceTable (by native_decide))
  native_decide

/- A structural run fault names the computation that failed rather than the run.
The faulting table is second in supplied order, so its retained label separates
the failing table's own target from the run's first target; reversing the order
keeps that same label, which separates table identity from position in the other
direction. The Gregorian rows are the positive control: the identical plan over a
decodable calendar payload runs to completion, so neither fault row is a fixture
that merely fails to compute. -/
example :
    let months := surfaceDateDifference .months
      (.baseYear .direct) (surfaceDateOperand "Date")
    let producer := table? sourceId (literal 2) (.fieldNotFilled wrongId)
    let faulting := table? laterId months (.fieldNotFilled wrongId)
    runFault? [producer, faulting] [dateInput .legacyHybrid] =
        some (.evaluation laterId .unsupportedDateCalendar) ∧
      (runFault? [producer, faulting] [dateInput .legacyHybrid]).map
          NumericComputationRunFault.target = some laterId ∧
      runFault? [faulting, producer] [dateInput .legacyHybrid] =
        some (.evaluation laterId .unsupportedDateCalendar) ∧
      runFault? [producer, faulting] [dateInput .storedGregorian] = none ∧
      runOutcomes? [producer, faulting] [dateInput .storedGregorian] =
        some [
          (sourceId, .accepted { unscaled := 2, scale := 0 }),
          (laterId, .accepted { unscaled := 1, scale := 0 })] := by
  native_decide

end A12Kernel.Conformance.NumericComputation.RunPlan
