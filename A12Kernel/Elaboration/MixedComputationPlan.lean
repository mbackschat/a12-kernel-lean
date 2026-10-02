import A12Kernel.Elaboration.ScalarComputationRun
import A12Kernel.Elaboration.RepeatableNumberPlan
import A12Kernel.Elaboration.RepeatableStringConstantComputation

/-! # One computation plan over every target kind, fixed and repeatable

The scalar plan runs fixed String, Number and whole-document targets, and the repeatable Number plan
runs Number targets at fixed and row addresses. A model mixing a row target with a target of another
kind needs both at once, so this plan composes them rather than choosing one: every step keeps its own
checked family and evaluator, and the plan owns only the order and what a step reads.

**The order** is the shared authored-order rule (`computationAuthoredOrder`), so a step runs after
every step whose target it reads, independent steps in authored order.

**What a step reads** is one overlay, the rule both component plans already apply: a completed
target at its exact address through the cell its outcome reads back as, every other address of a
plan target as clean empty, and the immutable document otherwise, so a stale stored value in a plan
target is never read ([`kf459`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf459)). A Number table
runs through the repeatable Number plan's own fixed and row executors with that overlay as its read;
a String table reads completed fixed targets through their String-family cell, as in the scalar
plan; a whole-document step and a row step read the overlaid document.

A **row step** is a checked computation into a repeatable target of a kind other than Number, run once
per instantiated target row by its own carrier and read back per row as the whole-document steps
are. Its instances are the row carriers; each is one constructor.
-/

namespace A12Kernel

/-- Why a row step failed structurally. -/
inductive RowComputationStepFault where
  | readBack (cause : DocumentComputationStepFault)
  | stringConstant (cause : RepeatableStringConstantComputationFault)
  deriving Repr, DecidableEq

/-- One checked computation into a repeatable non-Number target, run at every instantiated row. -/
structure CheckedRowComputationStep (model : FlatModel) (compilePattern : StringPatternCompiler) where
  private mk ::
  target : FieldId
  family : DocumentTargetFamily
  referencesField : FieldId → Bool
  excludesTarget : referencesField target = false
  run : World → PreparedFlatStringPatterns model compilePattern → CheckedDocument model →
    Except RowComputationStepFault (List (CellAddr × DocumentTargetOutcome × CheckedCell))

namespace CheckedRowComputationStep

/-- A String constant written into every row of a repeatable String target. -/
def ofRepeatableStringConstant (operation : CheckedRepeatableStringConstantComputation model) :
    CheckedRowComputationStep model compilePattern where
  target := operation.checkedTarget.targetField
  family := .string
  referencesField _ := false
  excludesTarget := rfl
  run _ patterns document := do
    let outcomes ← (operation.execute patterns document).mapError .stringConstant
    outcomes.mapM fun entry => do
      let cell ← (DocumentComputationReadBack.string entry.outcome).mapError .readBack
      pure (entry.targetField, .string entry.outcome, cell)

end CheckedRowComputationStep

/-- One plan step with its family retained. A Number table runs at its fixed target or at every row
of its target's scope, by its own reading scope. -/
inductive MixedComputationStep (model : FlatModel) (compilePattern : StringPatternCompiler) where
  | number (table : CheckedNumericComputationTable model)
  | string (table : CheckedStringComputationTable model)
  | document (step : CheckedDocumentComputationStep model)
  | rows (step : CheckedRowComputationStep model compilePattern)

namespace MixedComputationStep

def targetField : MixedComputationStep model compilePattern → FieldId
  | .number table => table.targetField
  | .string table => table.targetField
  | .document step => step.target
  | .rows step => step.target

def referencesField : MixedComputationStep model compilePattern → FieldId → Bool
  | .number table => table.referencesField
  | .string table => table.referencesField
  | .document step => step.referencesField
  | .rows step => step.referencesField

end MixedComputationStep

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
  | cycle (step reads : FieldId)
  deriving Repr, DecidableEq

inductive MixedComputationPlanFault where
  | number (cause : RepeatableNumberPlanFault)
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
    MixedComputationStep.referencesField authored.length authored
  uniqueTargets : FieldId.firstDuplicate? (authored.map (·.targetField)) = none
  dependenciesOrdered : firstForwardComputationDependency? MixedComputationStep.targetField
    MixedComputationStep.referencesField execution = none

def certifyMixedComputationPlan (steps : List (MixedComputationStep model compilePattern)) :
    Except MixedComputationPlanError (CheckedMixedComputationPlan model compilePattern) :=
  if steps.isEmpty then .error .empty else
  match hDuplicate : FieldId.firstDuplicate? (steps.map (·.targetField)) with
  | some target => .error (.duplicateTarget target)
  | none =>
      match hForward : firstForwardComputationDependency? MixedComputationStep.targetField
          MixedComputationStep.referencesField
          (computationAuthoredOrder MixedComputationStep.targetField
            MixedComputationStep.referencesField steps.length steps) with
      | some (step, reads) => .error (.cycle step reads)
      | none => .ok { authored := steps, execution := _, executionOrdered := rfl
                      uniqueTargets := hDuplicate, dependenciesOrdered := hForward }

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
    (state : MixedComputationState) (input : CheckedDocument model) : StringComputationContext where
  read field :=
    match state.fixed.find? (·.targetField == field) with
    | some completion => completion.stringCell
    | none =>
        if plan.targetFields.contains field then StringDependencyCell.empty.checked
        else input.stringComputationContext.read field

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
