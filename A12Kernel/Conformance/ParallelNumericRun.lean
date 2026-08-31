import A12Kernel.Elaboration.ParallelNumericRun
import A12Kernel.Elaboration.ParallelNumericRunRelation
import A12Kernel.Conformance.ParallelNumericAlternativeTable

/-! # Parallel Number run-plan and overlay locks -/

namespace A12Kernel.Conformance.ParallelNumericRun

open A12Kernel
open A12Kernel.Conformance.ParallelNumericThreeGroupOperands

private def literal (value : Rat) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .literal { value, authoredScale := 0 }

private def rowExpression? (target : FieldId)
    (operand : SurfaceFieldPath)
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (guard : ComputationCondition)
    (suppressExactScaleWarning : Bool := false) :=
  (checkIsolatedParallelNumericExpressionRunWithGuard
    model ["Plan"] target operand expression (some guard)
      suppressExactScaleWarning).toOption

private def row? (target : FieldId) (operand : SurfaceFieldPath)
    (guard : ComputationCondition) :=
  rowExpression? target operand (.atom (.field operand)) guard

private def table? (target : FieldId) (operand : SurfaceFieldPath)
    (guardField : FieldId) :
    Option (CheckedParallelNumericAlternativeTable model) := do
  let first ← row? target operand (.fieldFilled guardField)
  let second ← row? target operand (.fieldNotFilled guardField)
  (certifyParallelNumericAlternativeTable [first, second]).toOption

private def checkedPlan?
    (tables :
      List (Option (CheckedParallelNumericAlternativeTable model))) :
    Option (CheckedParallelNumericPlan model) := do
  let tables ← tables.mapM id
  (certifyParallelNumericPlan tables).toOption

private def run? : Option (CheckedParallelNumericPlan model) :=
  checkedPlan? [table? 4 offsetPath 6, table? 2 inputPath 4]

private def invalidProducerTable? :
    Option (CheckedParallelNumericAlternativeTable model) := do
  let divide :=
    AuthoredNumericExpr.binary .divide
      (.atom (.field offsetPath)) (literal 0)
  let first ← rowExpression? 4 offsetPath divide (.fieldFilled 6) true
  let second ← rowExpression? 4 offsetPath divide (.fieldNotFilled 6) true
  (certifyParallelNumericAlternativeTable [first, second]).toOption

private def noValueProducerTable? :
    Option (CheckedParallelNumericAlternativeTable model) := do
  let first ← row? 4 offsetPath (.fieldFilled 7)
  let second ← row? 4 offsetPath (.fieldFilled 7)
  (certifyParallelNumericAlternativeTable [first, second]).toOption

private def unreadProducerConsumerTable? :
    Option (CheckedParallelNumericAlternativeTable model) := do
  let guard := ComputationCondition.or
    (.fieldFilled 6) (.fieldNotFilled 6)
  let first ← row? 2 offsetPath guard
  let second ← row? 2 inputPath (.fieldFilled 4)
  (certifyParallelNumericAlternativeTable [first, second]).toOption

private def finitePlan? : Option (CheckedParallelNumericPlan model) := do
  let seedProducer ← table? 6 seedPath 8
  let middle ← table? 4 offsetPath 6
  let consumer ← table? 2 inputPath 4
  (certifyParallelNumericPlan [seedProducer, middle, consumer]).toOption

private def checkedDocument? (cells : List ClassifiedCellInput) :=
  (preliminaryFor cells).map (·.base)

private def read? (state : ParallelNumericRunState)
    (cells : List ClassifiedCellInput) (address : CellAddr) :
    Option CheckedCell := do
  let run ← run?
  let document ← checkedDocument? cells
  (run.readPolicy state document address).toOption

private def accepted (field : FieldId) (path : List Nat)
    (value : Int) : ParallelNumericDirectOutcome := {
  address := { field, path }
  outcome := .accepted { unscaled := value, scale := 0 }
}

private def outcomes?
    (checked : Option (CheckedParallelNumericPlan model))
    (cells : List ClassifiedCellInput) :
    Option (List ParallelNumericDirectOutcome) := do
  let run ← checked
  let preliminary ← preliminaryFor cells
  (run.execute preliminary).toOption

private def result?
    (checked : Option (CheckedParallelNumericPlan model))
    (cells : List ClassifiedCellInput) :
    Option
      (NumericComputationRunView (ComputationFormalMessage Bool) CellAddr) := do
  let run ← checked
  let preliminary ← preliminaryFor cells
  (run.executeResult preliminary (fun _ => true) []).toOption

private def computedNumberCell (field : FieldId) (path : List Nat)
    (stored : StoredNumber) : ClassifiedCellInput := {
  address := { field, path }
  stored := stored.render
  raw := .parsed (.num stored.amount)
  numericDecimal := some {
    unscaled := stored.unscaled
    scale := stored.scale
  }
}

private def sourceFilledPlanTargets : List ClassifiedCellInput :=
  (cleanCells.filter fun cell =>
    ![2, 4, 6].contains cell.address.field) ++ [
      computedNumberCell 2 [1] { unscaled := 7, scale := 0 },
      computedNumberCell 2 [2] { unscaled := 8, scale := 0 },
      computedNumberCell 4 [1] { unscaled := 10, scale := 0 },
      computedNumberCell 4 [2] { unscaled := 20, scale := 0 },
      computedNumberCell 6 [1] { unscaled := 1, scale := 0 },
      computedNumberCell 6 [2] { unscaled := 99, scale := 0 }
    ]

private def invalidIndexCell (field : FieldId) (path : List Nat) :
    List ClassifiedCellInput :=
  sourceFilledPlanTargets.filter fun cell =>
    cell.address != { field, path }

/-- The clean document with one target row beyond the group's declared capacity of two. -/
private def overLimitPreliminary : Option (CheckedIndexPreliminary model) := do
  let prepared ←
    (prepareFlatStringContext { now := { epochMillis := 0 } }
      builtinStringPatternCompiler model).toOption
  let document ←
    (checkDocument prepared "en_US" {
      instantiatedRows := rows ++ [{ group := 1, path := [3] }]
      cells := cleanCells }).toOption
  document.applyFullIndexPreliminary.toOption

/- **An over-limit target row is neither computed nor fatal.** The index column already skipped it,
   and before the target inventory did too the two enumerations disagreed: the row survived the
   invalid-index filter, reached `targetKeyFor` with no column entry, and aborted the whole run with
   a structural `missingTargetIndex` fault on a document the checker had accepted. That was this
   family's only witnessed structural failure, and it was a defect rather than a reachable Kernel
   behaviour — the Kernel writes into in-capacity rows only
   ([checkpoint](../../docs/SOURCES.md#src-over-limit-computation-target)). The in-capacity control
   beside it is the same document without the excess row, and each list repeats because the plan
   holds two tables that each cover both rows. -/
private def executedPaths? (preliminary : Option (CheckedIndexPreliminary model)) :
    Option (List (List Nat)) := do
  let checked ← run?
  let p ← preliminary
  let outcomes ← (checked.execute p).toOption
  some (outcomes.map (·.address.path))

example :
    (executedPaths? overLimitPreliminary, executedPaths? (preliminaryFor cleanCells)) =
    (some [[1], [2], [1], [2]], some [[1], [2], [1], [2]]) := by
  native_decide

private def sharedOperandPlan? :
    Option (CheckedParallelNumericPlan model) :=
  checkedPlan? [table? 4 offsetPath 6, table? 2 offsetPath 6]

private def appendRouteUnlessOperandGroupSeen
    (routes : List (CheckedParallelNumericTargetRoute model))
    (candidate : CheckedParallelNumericTargetRoute model) :
    List (CheckedParallelNumericTargetRoute model) :=
  if routes.any fun route =>
      route.groups.rightGroup.path == candidate.groups.rightGroup.path then
    routes
  else
    routes ++ [candidate]

private def deduplicatePlanRoutesByOperandGroup
    (plan : CheckedParallelNumericPlan model) :
    List (CheckedParallelNumericTargetRoute model) :=
  plan.operandRoutes.foldl appendRouteUnlessOperandGroupSeen []

private def resultWithRoutes?
    (checked : Option (CheckedParallelNumericPlan model))
    (cells : List ClassifiedCellInput)
    (routes :
      CheckedParallelNumericPlan model →
        List (CheckedParallelNumericTargetRoute model)) :
    Option
      (NumericComputationRunView (ComputationFormalMessage Bool) CellAddr) := do
  let plan ← checked
  let preliminary ← preliminaryFor cells
  let outcomes ← (plan.execute preliminary).toOption
  (classifyParallelNumericOutcomes preliminary (routes plan)
    (fun _ => true) [] outcomes).toOption

/- Duplicate targets and reads of later supplied targets fail structurally; independent tables need no artificial dependency edge. -/
example :
    (do
      let producer ← table? 4 offsetPath 6
      match certifyParallelNumericPlan [producer, producer] with
      | .error error => some error
      | .ok _ => none) = some (.duplicateTarget 4) ∧
    (do
      let producer ← table? 4 offsetPath 6
      let consumer ← table? 2 inputPath 4
      match certifyParallelNumericPlan [consumer, producer] with
      | .error error => some error
      | .ok _ => none) =
        some (.forwardDependency 2 4) ∧
    (checkedPlan?
      [table? 4 offsetPath 6, table? 2 offsetPath 6]).map
        (·.targetFields) = some [4, 2] := by
  native_decide

/- A genuine three-target chain is accepted; empty, duplicate, and forward-dependent supplied orders fail before execution. -/
example :
    finitePlan?.map (·.targetFields) = some [6, 4, 2] ∧
      (match certifyParallelNumericPlan
        ([] : List (CheckedParallelNumericAlternativeTable model)) with
      | .error error => some error
      | .ok _ => none) = some .empty ∧
      (do
        let table ← table? 6 seedPath 8
        match certifyParallelNumericPlan [table, table] with
        | .error error => some error
        | .ok _ => none) = some (.duplicateTarget 6) ∧
      (do
        let first ← table? 6 seedPath 8
        let middle ← table? 4 offsetPath 6
        let consumer ← table? 2 inputPath 4
        match certifyParallelNumericPlan [middle, first, consumer] with
        | .error error => some error
        | .ok _ => none) = some (.forwardDependency 4 6) := by
  native_decide

/- Pending computed addresses hide stale input, and completion is exact to one repetition address. -/
example :
    let stale := (cleanCells.filter fun cell => cell.address.field != 4) ++ [
      numberCell 4 [1] { unscaled := 99, scale := 0 },
      numberCell 4 [2] { unscaled := 98, scale := 0 }
    ]
    (read? {} stale { field := 4, path := [1] }).map
        (observeCell .computation) = some CellObservation.empty ∧
      (read? { completed := [accepted 4 [1] 30] }
        stale { field := 4, path := [1] }).map
          (observeCell .computation) =
        some (CellObservation.value (.num 30)) ∧
      (read? { completed := [accepted 4 [1] 30] }
        stale { field := 4, path := [2] }).map
          (observeCell .computation) =
        some CellObservation.empty := by
  native_decide

/- Invalid producer classes collapse to cause-blind dependency poison, while an ordinary input delegates unchanged. -/
example :
    let invalid : ParallelNumericDirectOutcome := {
      address := { field := 4, path := [1] }
      outcome := .invalidNoValue .calculationValue
    }
    (read? { completed := [invalid] }
      cleanCells { field := 4, path := [1] }).map
        (observeCell .computation) =
        some (CellObservation.poison .computedDependency) ∧
      (read? {} cleanCells { field := 6, path := [1] }).map
        (observeCell .computation) =
        some (CellObservation.value (.num 1)) := by
  native_decide

/- Producer outcomes replace stale addressed inputs before the dependent table runs. -/
example :
    (outcomes? run? cleanCells).map (·.map (fun result =>
      (result.address, result.outcome))) =
      some [
        ({ field := 4, path := [1] },
          .accepted { unscaled := 1, scale := 0 }),
        ({ field := 4, path := [2] },
          .accepted { unscaled := 0, scale := 0 }),
        ({ field := 2, path := [1] },
          .accepted { unscaled := 1, scale := 0 }),
        ({ field := 2, path := [2] },
          .accepted { unscaled := 0, scale := 0 })
      ] := by
  native_decide

/- Clean producer no-value reads as numeric empty/zero; reached producer invalidity poisons the dependent target. -/
example :
    (outcomes?
      (checkedPlan? [noValueProducerTable?, table? 2 inputPath 4])
      cleanCells).map (·.map (·.outcome)) =
        some [
          .noValue, .noValue,
          .accepted { unscaled := 0, scale := 0 },
          .accepted { unscaled := 0, scale := 0 }
        ] ∧
      (outcomes?
        (checkedPlan? [invalidProducerTable?, table? 2 inputPath 4])
        cleanCells).map (·.map (·.outcome)) =
        some [
          .invalidNoValue .calculationValue,
          .invalidNoValue .calculationValue,
          .inheritedPoison .computedDependency,
          .inheritedPoison .computedDependency
        ] := by
  native_decide

/- Static dependency orders the tables but does not poison a selected row that never reads the invalid producer. -/
example :
    (outcomes?
      (checkedPlan? [invalidProducerTable?, unreadProducerConsumerTable?])
      cleanCells).map (·.map (·.outcome)) =
      some [
        .invalidNoValue .calculationValue,
        .invalidNoValue .calculationValue,
        .accepted { unscaled := 1, scale := 0 },
        .accepted { unscaled := 0, scale := 0 }
      ] := by
  native_decide

/- The finite entry point executes a genuine three-target dependency chain through exact completed addresses. -/
example :
    outcomes? finitePlan? cleanCells =
      some [
        accepted 6 [1] 2, accepted 6 [2] 0,
        accepted 4 [1] 2, accepted 4 [2] 0,
        accepted 2 [1] 2, accepted 2 [2] 0
      ] := by
  native_decide

/- An invalid producer index column suppresses and clears that producer while a later consumer reads the absent completion as clean numeric zero. Invalidity in the target group independently suppresses the first and last tables without aborting the middle table. -/
example :
    let invalidOffset := invalidIndexCell 5 [2]
    let invalidTarget := invalidIndexCell 1 [2]
    (outcomes? finitePlan? invalidOffset,
      (result? finitePlan? invalidOffset).map (·.cleared)) =
      (some [
        accepted 2 [1] 0, accepted 2 [2] 0
      ], some [
        { field := 6, path := [1] },
        { field := 6, path := [2] },
        { field := 4, path := [1] },
        { field := 4, path := [2] }
      ]) ∧
    (outcomes? finitePlan? invalidTarget,
      (result? finitePlan? invalidTarget).map (·.cleared)) =
      (some [
        accepted 4 [1] 0, accepted 4 [2] 0
      ], some [
        { field := 6, path := [1] },
        { field := 6, path := [2] },
        { field := 2, path := [1] },
        { field := 2, path := [2] }
      ]) := by
  native_decide

/- Plan-level route deduplication by operand group is unsound: equal operand groups still own different target clears. -/
example :
    let invalidOffset := invalidIndexCell 5 [2]
    (result? sharedOperandPlan? invalidOffset).map (·.cleared) =
      some [
        { field := 4, path := [1] },
        { field := 4, path := [2] },
        { field := 2, path := [1] },
        { field := 2, path := [2] }
      ] ∧
    (resultWithRoutes? sharedOperandPlan? invalidOffset
      deduplicatePlanRoutesByOperandGroup).map (·.cleared) =
      some [
        { field := 4, path := [1] },
        { field := 4, path := [2] }
      ] := by
  native_decide

/- Independent tables are legal in either supplied order. Their target-indexed values agree while the private outcome list retains supplied table order. -/
example :
    let forward :=
      checkedPlan? [table? 4 offsetPath 6, table? 2 offsetPath 6]
    let reverse :=
      checkedPlan? [table? 2 offsetPath 6, table? 4 offsetPath 6]
    outcomes? forward cleanCells =
      some [
        accepted 4 [1] 1, accepted 4 [2] 0,
        accepted 2 [1] 1, accepted 2 [2] 0
      ] ∧
    outcomes? reverse cleanCells =
      some [
        accepted 2 [1] 1, accepted 2 [2] 0,
        accepted 4 [1] 1, accepted 4 [2] 0
      ] := by
  native_decide

/- Combined classification retains producer and consumer instances in the shared addressed Number result domain. -/
example :
    let source :=
      (cleanCells.filter fun cell => cell.address.field != 4) ++ [
        computedNumberCell 4 [1] { unscaled := 10, scale := 0 },
        computedNumberCell 4 [2] { unscaled := 20, scale := 0 }
    ]
    ((result? run? source).map fun view =>
      (view.withoutErrors.map fun computed =>
        (computed.targetField, computed.value), view.cleared)) =
      some ([
        ({ field := 4, path := [1] },
          { unscaled := 1, scale := 0 }),
        ({ field := 4, path := [2] },
          { unscaled := 0, scale := 0 }),
        ({ field := 2, path := [1] },
          { unscaled := 1, scale := 0 }),
        ({ field := 2, path := [2] },
          { unscaled := 0, scale := 0 })
      ], []) := by
  native_decide

private def relationSeedTable :=
  (table? 6 seedPath 8).get (by native_decide)

private def relationMiddleTable :=
  (table? 4 offsetPath 6).get (by native_decide)

private def relationConsumerTable :=
  (table? 2 inputPath 4).get (by native_decide)

private def relationPlan : CheckedParallelNumericPlan model :=
  (certifyParallelNumericPlan [
    relationSeedTable, relationMiddleTable, relationConsumerTable])
      |>.toOption |>.get (by native_decide)

private def relationPreliminary : CheckedIndexPreliminary model :=
  (preliminaryFor (invalidIndexCell 5 [2])).get (by native_decide)

private def relationSeedOutcomes : List ParallelNumericDirectOutcome :=
  (relationSeedTable.executeWithRead relationPreliminary
    (relationPlan.readPolicy
      ({} : ParallelNumericTransitionState).runState relationPreliminary.base))
      |>.toOption |>.get (by native_decide)

private def afterActionFreeSeed : ParallelNumericTransitionState :=
  { completedTargets := [6], outcomes := relationSeedOutcomes }

private theorem evaluated_to_get (evaluation : Except ε α)
    (available : evaluation.toOption.isSome = true) :
    evaluation = .ok (evaluation.toOption.get available) := by
  cases evaluation with
  | error cause => simp [Except.toOption] at available
  | ok value => rfl

private theorem relationSeedExecuted :
    relationSeedTable.executeWithRead relationPreliminary
      (relationPlan.readPolicy
        ({} : ParallelNumericTransitionState).runState relationPreliminary.base) =
        .ok relationSeedOutcomes := by
  simpa [relationSeedOutcomes] using evaluated_to_get
    (evaluation := relationSeedTable.executeWithRead relationPreliminary
      (relationPlan.readPolicy
        ({} : ParallelNumericTransitionState).runState relationPreliminary.base))
    (by native_decide)

private theorem relationEnabled
    (table : CheckedParallelNumericAlternativeTable model)
    (state : ParallelNumericTransitionState)
    (onSeed : table.referencesField 6 = true → 6 ∈ state.completedTargets)
    (onMiddle : table.referencesField 4 = true → 4 ∈ state.completedTargets)
    (onConsumer : table.referencesField 2 = true → 2 ∈ state.completedTargets) :
    ParallelNumericDependenciesEnabled relationPlan table state := by
  intro dependency member referenced
  have targets : relationPlan.targetFields = [6, 4, 2] := by native_decide
  rw [targets] at member
  simp at member
  rcases member with rfl | rfl | rfl
  · exact onSeed referenced
  · exact onMiddle referenced
  · exact onConsumer referenced

/- A structurally action-free producer still completes its table target and thereby enables the dependent batch; completion cannot be inferred from emitted rows. -/
example :
    ¬ ParallelNumericDependenciesEnabled relationPlan relationMiddleTable {} ∧
    ParallelNumericRunTransition relationPlan relationPreliminary {}
        (6, relationSeedOutcomes) afterActionFreeSeed ∧
      relationSeedOutcomes = [] ∧
        ParallelNumericDependenciesEnabled relationPlan relationMiddleTable
          afterActionFreeSeed := by
  constructor
  · intro enabled
    have completed := enabled 6 (by native_decide) (by native_decide)
    simp at completed
  constructor
  · exact .compute relationSeedTable (by
      change relationSeedTable ∈
        [relationSeedTable, relationMiddleTable, relationConsumerTable]
      simp)
      (by native_decide)
      (relationEnabled _ _ (by native_decide) (by native_decide)
        (by native_decide)) relationSeedOutcomes relationSeedExecuted
  constructor
  · native_decide
  · exact relationEnabled _ _ (by native_decide) (by native_decide)
      (by native_decide)

/- A structural table fault is only a conditional branch for this fixture: no
current valid input witnesses one. If it occurs, the enabled table fails after
the action-free seed's completed-target state and cannot reset that state merely
because the seed emitted no addressed outcomes. -/
example (error : CheckedIsolatedParallelNumericDirectRun.ExecutionError)
    (executed :
      relationMiddleTable.executeWithRead relationPreliminary
        (relationPlan.readPolicy afterActionFreeSeed.runState
          relationPreliminary.base) = .error error) :
    afterActionFreeSeed.completedTargets = [6] ∧
      afterActionFreeSeed.outcomes = [] ∧
      ParallelNumericRunFailureTransition relationPlan relationPreliminary
        afterActionFreeSeed (.table relationMiddleTable.targetField error) ∧
      ParallelNumericRunFailureTrace relationPlan relationPreliminary
        afterActionFreeSeed [] afterActionFreeSeed
          (.table relationMiddleTable.targetField error) := by
  constructor
  · native_decide
  constructor
  · native_decide
  have failed : ParallelNumericRunFailureTransition relationPlan
      relationPreliminary afterActionFreeSeed
        (.table relationMiddleTable.targetField error) :=
    .fail relationMiddleTable (by
      change relationMiddleTable ∈
        [relationSeedTable, relationMiddleTable, relationConsumerTable]
      simp)
      (by native_decide)
      (relationEnabled _ _ (by native_decide) (by native_decide)
        (by native_decide)) error executed
  exact ⟨failed, .failed failed⟩

private def independentFirstTable :=
  (table? 4 offsetPath 6).get (by native_decide)

private def independentSecondTable :=
  (table? 2 offsetPath 6).get (by native_decide)

private def independentRelationPlan : CheckedParallelNumericPlan model :=
  (certifyParallelNumericPlan [independentFirstTable, independentSecondTable])
    |>.toOption |>.get (by native_decide)

private theorem independentRelationEnabled
    (table : CheckedParallelNumericAlternativeTable model)
    (notFirst : table.referencesField 4 = false)
    (notSecond : table.referencesField 2 = false) :
    ParallelNumericDependenciesEnabled independentRelationPlan table {} := by
  intro dependency member referenced
  have targets : independentRelationPlan.targetFields = [4, 2] := by native_decide
  rw [targets] at member
  simp at member
  rcases member with rfl | rfl
  · rw [notFirst] at referenced
    contradiction
  · rw [notSecond] at referenced
    contradiction

/- Both independent plan members are enabled in the empty relation state, so supplied list position does not become a dependency edge. -/
example :
    ParallelNumericDependenciesEnabled independentRelationPlan
        independentFirstTable {} ∧
      ParallelNumericDependenciesEnabled independentRelationPlan
        independentSecondTable {} := by
  exact ⟨independentRelationEnabled _ (by native_decide) (by native_decide),
    independentRelationEnabled _ (by native_decide) (by native_decide)⟩

end A12Kernel.Conformance.ParallelNumericRun
