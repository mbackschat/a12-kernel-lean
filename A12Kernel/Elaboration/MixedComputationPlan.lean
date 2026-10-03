import A12Kernel.Elaboration.ScalarComputationRun
import A12Kernel.Elaboration.RepeatableNumberPlan
import A12Kernel.Elaboration.RowComputationStep
import A12Kernel.Elaboration.ParallelNumericStep

/-! # One computation plan over every target kind, fixed and repeatable

The scalar plan runs fixed String, Number and whole-document targets, and the repeatable Number plan
runs Number targets at fixed and row addresses. A model mixing a row target with a target of another
kind needs both at once, so this plan composes them rather than choosing one: every step keeps its own
checked family and evaluator, and the plan owns only the order and what a step reads.

**The order** is the shared authored-order rule (`computationAuthoredOrder`), so a step runs after
its required producer dependencies, with independent steps in authored order.

**What a step reads** is one overlay, the rule both component plans already apply: a completed
target at its exact address through the cell its outcome reads back as, every other address of a
plan target as clean empty, and the immutable document otherwise, so a stale stored value in a plan
target is never read ([`kf459`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf459)). A Number table
runs through the repeatable Number plan's own fixed and row executors with that overlay as its read;
a String table reads completed fixed targets through their String-family cell, as in the scalar
plan; a whole-document step, row step and parallel Number step read the overlaid document.
Parallel Number steps retain their checked key joins and include index-invalid rows as clean clears.

A **row step** ([`RowComputationStep`](RowComputationStep.lean)) is a checked computation into a
repeatable target of a kind other than Number, run once per instantiated target row by its own carrier.
-/

namespace A12Kernel

/-- One plan step with its family retained. A Number table runs at its fixed target or at every row
of its target's scope, by its own reading scope. -/
inductive MixedComputationStep (model : FlatModel) (compilePattern : StringPatternCompiler) where
  | number (table : CheckedNumericComputationTable model)
  | parallel (step : CheckedParallelNumericStep model)
  | string (table : CheckedStringComputationTable model)
  | document (step : CheckedDocumentComputationStep model)
  | rows (step : CheckedRowComputationStep model compilePattern)

namespace MixedComputationStep

def targetField : MixedComputationStep model compilePattern → FieldId
  | .number table => table.targetField
  | .parallel step => step.targetField
  | .string table => table.targetField
  | .document step => step.target
  | .rows step => step.target

def referencesField : MixedComputationStep model compilePattern → FieldId → Bool
  | .number table => table.referencesField
  | .parallel step => step.referencesField
  | .string table => table.referencesField
  | .document step => step.referencesField
  | .rows step => step.referencesField

def protectionConditions : MixedComputationStep model compilePattern → List (Option ComputationCondition)
  | .number table => table.protectionConditions
  | .parallel step => step.protectionConditions
  | .string table => table.protectionConditions
  | .document step => step.protectionConditions
  | .rows step => step.protectionConditions

def requiresProducer (producerProtected : FieldId → ResolvedGroupReference → Bool) :
    MixedComputationStep model compilePattern → FieldId → Bool
  | .number table => table.requiresProducer producerProtected
  | .parallel step => step.requiresProducer producerProtected
  | .string table => table.requiresProducer producerProtected
  | .document step => step.requiresProducer producerProtected
  | .rows step => step.requiresProducer producerProtected

end MixedComputationStep

def mixedComputationProducerProtection (steps : List (MixedComputationStep model compilePattern)) :=
  computationProducerProtection model MixedComputationStep.targetField MixedComputationStep.protectionConditions steps

def mixedComputationDependencies (steps : List (MixedComputationStep model compilePattern)) :
    MixedComputationStep model compilePattern → FieldId → Bool :=
  MixedComputationStep.requiresProducer (mixedComputationProducerProtection steps)


/-- One reported outcome. A Number keeps its sourced change projection; a String and a whole-document
target keep their family outcome at their address. -/
inductive MixedComputationOutcome where
  | number (outcome : SourcedNumericTargetOutcome CellAddr)
  | string (target : FieldId) (outcome : StringTargetOutcome)
  | document (target : CellAddr) (outcome : DocumentTargetOutcome)
  deriving Repr, DecidableEq

inductive MixedComputationPlanError where
  | empty
  | duplicateTarget (target : FieldId)
  | conflictingTargetPolicy (target : FieldId)
  | cycle (step reads : FieldId)
  deriving Repr, DecidableEq

inductive MixedComputationPlanFault where
  | number (cause : RepeatableNumberPlanFault)
  | parallel (target : FieldId) (cause : ParallelNumericStepFault)
  | string (cause : StringComputationRunFault)
  | document (target : FieldId) (cause : DocumentComputationStepFault)
  | rows (target : FieldId) (cause : RowComputationStepFault)
  deriving Repr, DecidableEq

/-- An authored mixed plan with its certified dependency order. -/
structure CheckedMixedComputationPlan (model : FlatModel) (compilePattern : StringPatternCompiler) where
  private mk ::
  authored : List (MixedComputationStep model compilePattern)
  execution : List (MixedComputationStep model compilePattern)
  executionOrdered : execution = computationAuthoredOrder MixedComputationStep.targetField
    (mixedComputationDependencies authored) authored.length authored
  uniqueTargets : FieldId.firstDuplicate? (authored.map (·.targetField)) = none
  dependenciesOrdered : firstForwardComputationDependency? MixedComputationStep.targetField
    (mixedComputationDependencies authored) execution = none

def certifyMixedComputationPlan (steps : List (MixedComputationStep model compilePattern)) :
    Except MixedComputationPlanError (CheckedMixedComputationPlan model compilePattern) :=
  if steps.isEmpty then .error .empty else
  match hDuplicate : FieldId.firstDuplicate? (steps.map (·.targetField)) with
  | some target => .error (.duplicateTarget target)
  | none =>
      match hForward : firstForwardComputationDependency? MixedComputationStep.targetField
          (mixedComputationDependencies steps)
          (computationAuthoredOrder MixedComputationStep.targetField
            (mixedComputationDependencies steps) steps.length steps) with
      | some (step, reads) => .error (.cycle step reads)
      | none => .ok { authored := steps, execution := _, executionOrdered := rfl
                      uniqueTargets := hDuplicate, dependenciesOrdered := hForward }

/-- Consolidate Number and String tables at their first target position using their existing
checked append operations. Other step families have no alternative-table carrier here. -/
private def insertMixedComputationStep (incoming : MixedComputationStep model compilePattern) :
    List (MixedComputationStep model compilePattern) →
      Except MixedComputationPlanError (List (MixedComputationStep model compilePattern))
  | [] => pure [incoming]
  | current :: rest => do
      if same : incoming.targetField = current.targetField then
        match incoming, current, same with
        | .number incoming, .number current, same =>
            if policy : incoming.targetPolicy = current.targetPolicy then
              pure (.number (current.appendSameTarget incoming same policy) :: rest)
            else throw (.conflictingTargetPolicy current.targetField)
        | .string incoming, .string current, same =>
            if policy : incoming.targetPolicy = current.targetPolicy then
              pure (.string (current.appendSameTarget incoming same policy) :: rest)
            else throw (.conflictingTargetPolicy current.targetField)
        | _, _, _ => throw (.duplicateTarget current.targetField)
      else pure (current :: (← insertMixedComputationStep incoming rest))

/-- Preserve authored alternative order before certifying one execution step per target. -/
def certifyAuthoredMixedComputationPlan (steps : List (MixedComputationStep model compilePattern)) :
    Except MixedComputationPlanError (CheckedMixedComputationPlan model compilePattern) := do
  let grouped ← steps.foldlM (fun grouped incoming => insertMixedComputationStep incoming grouped) []
  certifyMixedComputationPlan grouped

/-- What the plan has completed: fixed targets through the scalar plan's completion, which owns each
family's String and Number read cells and its placement, and row targets as placements. -/
structure MixedComputationState where
  fixed : List ScalarComputationCompletion := []
  rows : List CheckedCellPlacement := []
  outcomes : List MixedComputationOutcome := []

namespace CheckedMixedComputationPlan

def targetFields (plan : CheckedMixedComputationPlan model compilePattern) : List FieldId :=
  plan.authored.map (·.targetField)

/-- The overlaid document every step reads. -/
def documentFor (plan : CheckedMixedComputationPlan model compilePattern)
    (state : MixedComputationState) (input : CheckedDocument model) : CheckedDocument model :=
  input.overlayCells plan.targetFields (state.fixed.map (·.placement) ++ state.rows)

/-- The String-family read of a fixed String table: a completed fixed target through its String
cell, a pending one empty, as in the scalar plan. -/
def stringContext (plan : CheckedMixedComputationPlan model compilePattern)
    (state : MixedComputationState) (input : CheckedDocument model) : StringComputationContext :=
  { (plan.documentFor state input).stringComputationContext with
    read := fun field =>
      match state.fixed.find? (·.targetField == field) with
      | some completion => completion.stringCell
      | none =>
          if plan.targetFields.contains field then StringDependencyCell.empty.checked
          else input.stringComputationContext.read field
  }

private def numberCompletion (outcome : SourcedNumericTargetOutcome CellAddr) :
    ScalarComputationCompletion :=
  .number { targetField := outcome.targetField.field, outcome := outcome.outcome }

private def numberPlacement (outcome : SourcedNumericTargetOutcome CellAddr) : CheckedCellPlacement :=
  { (numberCompletion outcome).placement with address := outcome.targetField }

def executeStep (plan : CheckedMixedComputationPlan model compilePattern) (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern) (input : CheckedDocument model)
    (state : MixedComputationState) :
    MixedComputationStep model compilePattern → Except MixedComputationPlanFault MixedComputationState
  | .number table => do
      let read := (plan.documentFor state input).read
      if table.readingScope.isEmpty then
        let outcome ← (CheckedRepeatableNumberPlan.executeFixed table world input read).mapError .number
        pure { state with fixed := state.fixed ++ [numberCompletion outcome]
                          outcomes := state.outcomes ++ [.number outcome] }
      else
        let outcomes ← (CheckedRepeatableNumberPlan.executeRows table world input read).mapError .number
        pure { state with rows := state.rows ++ outcomes.map numberPlacement
                          outcomes := state.outcomes ++ outcomes.map .number }
  | .parallel step => do
      let results ← (step.execute (plan.documentFor state input)).mapError (.parallel step.targetField)
      let outcomes := results.map fun result =>
        ({ targetField := result.address, outcome := result.outcome
           source := input.numericTargetPlacementStateAt result.address } : SourcedNumericTargetOutcome CellAddr)
      pure { state with rows := state.rows ++ outcomes.map numberPlacement
                        outcomes := state.outcomes ++ outcomes.map .number }
  | .string table => do
      let completion ← (table.evaluateCompletion patterns (plan.stringContext state input)).mapError .string
      pure { state with fixed := state.fixed ++ [.string completion]
                        outcomes := state.outcomes ++ [.string completion.targetField completion.outcome] }
  | .document step => do
      let (outcome, cell) ← (step.run world patterns.targetMatcher? (plan.documentFor state input)).mapError
        (.document step.target)
      pure { state with fixed := state.fixed ++ [.document step.target outcome cell]
                        outcomes := state.outcomes ++ [.document { field := step.target, path := [] } outcome] }
  | .rows step => do
      let results ← (step.run world patterns (plan.documentFor state input)).mapError (.rows step.target)
      let placements := results.map fun (address, outcome, cell) =>
        ({ address, cell, storedText := outcome.storedText? } : CheckedCellPlacement)
      pure { state with rows := state.rows ++ placements
                        outcomes := state.outcomes ++ results.map fun (address, outcome, _) =>
                          .document address outcome }

def executeSteps (plan : CheckedMixedComputationPlan model compilePattern) (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern) (input : CheckedDocument model) :
    List (MixedComputationStep model compilePattern) → MixedComputationState →
      Except MixedComputationPlanFault MixedComputationState
  | [], state => pure state
  | step :: remaining, state => do
      plan.executeSteps world patterns input remaining (← plan.executeStep world patterns input state step)

/-- Run the certified order and return every outcome in that order, by row within a step. -/
def execute (plan : CheckedMixedComputationPlan model compilePattern) (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern) (input : CheckedDocument model) :
    Except MixedComputationPlanFault (List MixedComputationOutcome) :=
  (·.outcomes) <$> plan.executeSteps world patterns input plan.execution {}

end CheckedMixedComputationPlan

end A12Kernel
