import A12Kernel.Elaboration.ScalarComputationRun
import A12Kernel.Elaboration.RepeatableNumberPlan
import A12Kernel.Elaboration.RowComputationStep
import A12Kernel.Elaboration.ParallelNumericStep
import A12Kernel.Elaboration.ParallelJoinedRowStep
import A12Kernel.Elaboration.ComputationFormalInput

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
A **joined row step** ([`ParallelJoinedRowStep`](ParallelJoinedRowStep.lean)) is its key-joined String or
temporal counterpart, which reads the overlaid document like a parallel Number step.
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
  | joinedRows (step : CheckedParallelJoinedRowStep model)

namespace MixedComputationStep

def targetField : MixedComputationStep model compilePattern → FieldId
  | .number table => table.targetField
  | .parallel step => step.targetField
  | .string table => table.targetField
  | .document step => step.target
  | .rows step => step.target
  | .joinedRows step => step.targetField

def referencesField : MixedComputationStep model compilePattern → FieldId → Bool
  | .number table => table.referencesField
  | .parallel step => step.referencesField
  | .string table => table.referencesField
  | .document step => step.referencesField
  | .rows step => step.referencesField
  | .joinedRows step => step.referencesField

/-- Each guard's group-presence projection; a joined guard is typed by its instance view, so the
plan's steps share only this projection. -/
def protectionConditions : MixedComputationStep model compilePattern → List (Option ComputationProtectionView)
  | .number table => table.protectionConditions.map (·.map (·.protectionView))
  | .parallel step => step.protectionConditions
  | .string table => table.protectionConditions.map (·.map (·.protectionView))
  | .document step => step.protectionConditions.map (·.map (·.protectionView))
  | .rows step => step.protectionConditions.map (·.map (·.protectionView))
  | .joinedRows step => step.protectionConditions

/-- Expanded operands are independent of the scheduler's conditional producer exemptions. -/
def operandField (step : MixedComputationStep model compilePattern) (field : FieldId) : Bool :=
  computationOperandField model step.targetField step.referencesField step.protectionConditions
    field id

def requiresProducer (producerProtected : FieldId → ResolvedGroupReference → Bool) :
    MixedComputationStep model compilePattern → FieldId → Bool
  | .number table => table.requiresProducer producerProtected
  | .parallel step => step.requiresProducer producerProtected
  | .string table => table.requiresProducer producerProtected
  | .document step => step.requiresProducer producerProtected
  | .rows step => step.requiresProducer producerProtected
  | .joinedRows step => step.requiresProducer producerProtected

/-- What a joined table keeps of a separate declaration that reads no partner field. -/
def readFootprint (step : MixedComputationStep model compilePattern) : ComputationReadFootprint :=
  { references := step.referencesField
    requiresProducer := fun producerProtected => MixedComputationStep.requiresProducer producerProtected step
    protectionConditions := step.protectionConditions }

end MixedComputationStep

def mixedComputationProducerProtection (steps : List (MixedComputationStep model compilePattern)) : FieldId → ResolvedGroupReference → Bool :=
  fun producer reference => computationProducerProtection model MixedComputationStep.targetField MixedComputationStep.protectionConditions steps producer reference id

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
  | joinedRows (target : FieldId) (cause : ParallelJoinedRowStepFault)
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

private def MixedComputationStep.rowTable? : MixedComputationStep model compilePattern →
    Option (CheckedRowComputationTable model)
  | .rows step => step.sourceTable?
  | .document step => CheckedRowComputationTable.ofDocument? step
  | .string table => CheckedRowComputationTable.ofString? table
  | .number _ | .parallel _ | .joinedRows _ => none

/-- Keep the first target position and concatenate checked alternatives; each operation retains
its own addressing and target evaluator (spec/09 §§1.1, 5). -/
private def insertMixedComputationStep (incoming : MixedComputationStep model compilePattern) :
    List (MixedComputationStep model compilePattern) →
      Except MixedComputationPlanError (List (MixedComputationStep model compilePattern))
  | [] => pure [incoming]
  | current :: rest => do
      if same : incoming.targetField = current.targetField then
        match hIncoming : incoming, hCurrent : current with
        | .number incoming, .number current =>
            have sameTarget : incoming.targetField = current.targetField := by
              simpa [hIncoming, hCurrent, MixedComputationStep.targetField] using same
            if policy : incoming.targetPolicy = current.targetPolicy then
              pure (.number (current.appendSameTarget incoming sameTarget policy) :: rest)
            else throw (.conflictingTargetPolicy current.targetField)
        | .string incoming, .string current =>
            have sameTarget : incoming.targetField = current.targetField := by
              simpa [hIncoming, hCurrent, MixedComputationStep.targetField] using same
            if policy : incoming.targetPolicy = current.targetPolicy then
              pure (.string (current.appendSameTarget incoming sameTarget policy) :: rest)
            else throw (.conflictingTargetPolicy current.targetField)
        | .parallel incoming, .parallel current =>
            have sameTarget : incoming.targetField = current.targetField := by
              simpa [hIncoming, hCurrent, MixedComputationStep.targetField] using same
            pure (.parallel (current.appendSameTarget incoming sameTarget) :: rest)
        | .number incoming, .parallel current =>
            have sameTarget : incoming.targetField = current.targetField := by
              simpa [hIncoming, hCurrent, MixedComputationStep.targetField] using same
            if incoming.targetPolicy == current.primary.targetPolicy then
              pure (.parallel (current.withBoundTable incoming sameTarget false) :: rest)
            else throw (.conflictingTargetPolicy current.targetField)
        | .parallel incoming, .number current =>
            have sameTarget : current.targetField = incoming.targetField := by
              simpa [hIncoming, hCurrent, MixedComputationStep.targetField] using same.symm
            if current.targetPolicy == incoming.primary.targetPolicy then
              pure (.parallel (incoming.withBoundTable current sameTarget true) :: rest)
            else throw (.conflictingTargetPolicy current.targetField)
        | .rows incoming, .rows current =>
            match current.appendSameTarget? incoming with
            | some combined => pure (.rows combined :: rest)
            | none => throw (.duplicateTarget current.target)
        | .joinedRows incoming, .joinedRows current =>
            match current.appendSameTarget? incoming with
            | some combined => pure (.joinedRows combined :: rest)
            | none => throw (.duplicateTarget current.targetField)
        | _, .joinedRows joined =>
            match joined.withBound incoming.readFootprint false with
            | some combined => pure (.joinedRows combined :: rest)
            | none => throw (.duplicateTarget joined.targetField)
        | .joinedRows joined, _ =>
            match joined.withBound current.readFootprint true with
            | some combined => pure (.joinedRows combined :: rest)
            | none => throw (.duplicateTarget joined.targetField)
        | _, _ =>
            match (do
              let left ← current.rowTable?
              let right ← incoming.rowTable?
              let table ← left.appendSameTarget? right
              let step ← CheckedRowComputationStep.ofTable? table
              pure (step compilePattern)) with
            | some combined => pure (.rows combined :: rest)
            | none => throw (.duplicateTarget current.targetField)
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

/-- Record a row-addressed step's completed targets as placements and their outcomes. -/
def MixedComputationState.withRowResults (state : MixedComputationState)
    (results : List (CellAddr × DocumentTargetOutcome × CheckedCell)) : MixedComputationState :=
  { state with
    rows := state.rows ++ results.map fun (address, outcome, cell) =>
      ({ address, cell, storedText := outcome.storedText? } : CheckedCellPlacement)
    outcomes := state.outcomes ++ results.map fun (address, outcome, _) => .document address outcome }

/-- A successfully assembled call keeps its outcomes beside every selected noncomputed input finding. -/
structure MixedComputationCheckedResult where
  outcomes : List MixedComputationOutcome
  formalErrorsInOperands : List ComputationFormalInputFinding
  deriving Repr, DecidableEq

namespace CheckedMixedComputationPlan

def targetFields (plan : CheckedMixedComputationPlan model compilePattern) : List FieldId :=
  plan.authored.map (·.targetField)

/-- The overlaid document every step reads. -/
def documentFor (plan : CheckedMixedComputationPlan model compilePattern)
    (state : MixedComputationState) (input : CheckedDocument model) : CheckedDocument model :=
  (input.withComputationFilterRows fun field =>
    plan.authored.any fun step => step.targetField == field || step.operandField field)
    |>.overlayCells plan.targetFields (state.fixed.map (·.placement) ++ state.rows)

/-- The document overlay owns both fixed and row-table completions, including fixed targets
executed by row tables. Its String projection also preserves Number formal-read text (spec/09 §3.1). -/
def stringContext (plan : CheckedMixedComputationPlan model compilePattern)
    (state : MixedComputationState) (input : CheckedDocument model) : StringComputationContext :=
  (plan.documentFor state input).stringComputationContext

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
      -- Evaluation reads completed cells and spellings together; change projection still compares
      -- with the original target (calendar review-control grid, 2026-10-04).
      let current := plan.documentFor state input
      if table.readingScope.isEmpty then
        let outcome ← (CheckedRepeatableNumberPlan.executeFixed table world current current.read current.computationFillContext.numberText).mapError .number
        let outcome := { outcome with source := input.numericTargetPlacementStateAt outcome.targetField }
        pure { state with fixed := state.fixed ++ [numberCompletion outcome]
                          outcomes := state.outcomes ++ [.number outcome] }
      else
        let outcomes ← (CheckedRepeatableNumberPlan.executeRows table world current current.read current.computationFillContext.numberText).mapError .number
        let outcomes := outcomes.map fun outcome =>
          { outcome with source := input.numericTargetPlacementStateAt outcome.targetField }
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
      let current := plan.documentFor state input
      let completion ← (table.evaluateCompletion patterns (plan.stringContext state input)
        (current.scalarComputationContext world)
        (some (current.resolveSemanticIndexColumnWith current.read))).mapError .string
      pure { state with fixed := state.fixed ++ [.string completion]
                        outcomes := state.outcomes ++ [.string completion.targetField completion.outcome] }
  | .document step => do
      let (outcome, cell) ← (step.run world patterns.targetMatcher? (plan.documentFor state input)).mapError
        (.document step.target)
      pure { state with fixed := state.fixed ++ [.document step.target outcome cell]
                        outcomes := state.outcomes ++ [.document { field := step.target, path := [] } outcome] }
  | .rows step => do
      let results ← (step.run world patterns (plan.documentFor state input)).mapError (.rows step.target)
      pure (state.withRowResults results)
  | .joinedRows step => do
      let results ← (step.execute world patterns.targetMatcher? (plan.documentFor state input)).mapError
        (.joinedRows step.targetField)
      pure (state.withRowResults results)

def executeSteps (plan : CheckedMixedComputationPlan model compilePattern) (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern) (input : CheckedDocument model) :
    List (MixedComputationStep model compilePattern) → MixedComputationState →
      Except MixedComputationPlanFault MixedComputationState
  | [], state => pure state
  | step :: remaining, state => do
      plan.executeSteps world patterns input remaining (← plan.executeStep world patterns input state step)

/-- Run the certified order and return execution-stage outcomes before diagnostic assembly, by row within a step. -/
def execute (plan : CheckedMixedComputationPlan model compilePattern) (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern) (input : CheckedDocument model) :
    Except MixedComputationPlanFault (List MixedComputationOutcome) :=
  (·.outcomes) <$> plan.executeSteps world patterns input plan.execution {}

/-- Select the expanded authored operand union, excluding every computed target from eager input reports. -/
def formalInputPlan (plan : CheckedMixedComputationPlan model compilePattern) :
    Except ComputationFormalInputPlanError (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model
    ((model.fields.filter fun field => plan.authored.any (·.operandField field.id)).map (·.id))
    plan.targetFields

/-- Prepare selected input findings once, execute through those exact cells and spellings, then reject colliding report pointers before exposing the call result. -/
def executeResultWithFormalInputs (plan : CheckedMixedComputationPlan model compilePattern)
    (world : World) (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    Except (ComputationFormalInputRunFault MixedComputationPlanFault) MixedComputationCheckedResult := do
  let inputPlan ← plan.formalInputPlan |>.mapError .formalInput
  let prepared ← inputPlan.prepare input |>.mapError .preliminary
  let outcomes ← (plan.execute world patterns prepared.preliminary.computationInput)
    |>.mapError (.execution prepared.formalErrorsInOperands)
  ComputationFormalInputFinding.assembleResult prepared.formalErrorsInOperands {
    outcomes
    formalErrorsInOperands := prepared.formalErrorsInOperands }
    |>.mapError (.assembly prepared.formalErrorsInOperands)

end CheckedMixedComputationPlan

end A12Kernel
