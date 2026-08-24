import A12Kernel.Elaboration.RepeatableNumberAggregateCascade
import A12Kernel.Elaboration.ScalarComputationRun

/-! # Aggregate-seeded mixed scalar computation runs -/

namespace A12Kernel

inductive RepeatableNumberAggregateMixedRunElabError where
  | duplicateTarget (field : FieldId)
  | missingAggregateDependency (field : FieldId)
  | cycle (field : FieldId)
  | incoherentRun
  deriving Repr, DecidableEq

/-- One checked row-to-aggregate prefix followed by an existing finite supplied-order mixed scalar run. The aggregate enters the suffix as a typed Number completion. -/
structure CheckedRepeatableNumberAggregateMixedRun (model : FlatModel) where
  private mk ::
  cascade : CheckedRepeatableNumberAggregateCascade model
  run : CheckedScalarComputationRun model
  distinctTargets : run.targetFields.all (fun field =>
    field != cascade.row.targetField &&
      field != cascade.total.operation.core.target.id) = true
  noBackEdge : run.targetFields.all (fun field =>
    !(cascade.row.sourceFields ++
      cascade.consumer.fieldDependencies).contains field) = true
  aggregateDependency : run.steps.any (fun step =>
    step.referencesField cascade.total.operation.core.target.id) = true

/-- Compose two already-checked phases. The suffix must consume the aggregate, own disjoint targets, and remain absent from both prefix dependency sets. -/
def checkRepeatableNumberAggregateMixedRun
    (cascade : CheckedRepeatableNumberAggregateCascade model)
    (run : CheckedScalarComputationRun model) :
    Except RepeatableNumberAggregateMixedRunElabError
      (CheckedRepeatableNumberAggregateMixedRun model) := do
  if hDistinct : run.targetFields.all (fun field =>
      field != cascade.row.targetField &&
        field != cascade.total.operation.core.target.id) = true then
    if hBackEdge : run.targetFields.all (fun field =>
        !(cascade.row.sourceFields ++
          cascade.consumer.fieldDependencies).contains field) = true then
      if hDependency : run.steps.any (fun step =>
          step.referencesField
            cascade.total.operation.core.target.id) = true then
        pure {
          cascade
          run
          distinctTargets := hDistinct
          noBackEdge := hBackEdge
          aggregateDependency := hDependency
        }
      else throw (.missingAggregateDependency
        cascade.total.operation.core.target.id)
    else
      match run.targetFields.find? fun field =>
          (cascade.row.sourceFields ++
            cascade.consumer.fieldDependencies).contains field with
      | some field => throw (.cycle field)
      | none => throw .incoherentRun
  else
    match run.targetFields.find? fun field =>
        field == cascade.row.targetField ||
          field == cascade.total.operation.core.target.id with
    | some field => throw (.duplicateTarget field)
    | none => throw .incoherentRun

structure RepeatableNumberAggregateMixedRunAnalysis where
  cascade : RepeatableNumberAggregateCascadeAnalysis
  scalarTargets : List (SurfaceScalarKind × FieldId)
  computedDependencies : List (FieldId × List FieldId)
  deriving Repr, DecidableEq

structure RepeatableNumberAggregateMixedRunOutcomes where
  cascade : RepeatableNumberAggregateCascadeOutcomes
  scalars : List ScalarComputationOutcome
  deriving Repr, DecidableEq

inductive RepeatableNumberAggregateMixedRunFault where
  | cascade (cause : RepeatableNumberAggregateCascadeFault)
  | run (cause : ScalarComputationRunFault)
  deriving Repr, DecidableEq

namespace CheckedRepeatableNumberAggregateMixedRun

def analyze (plan : CheckedRepeatableNumberAggregateMixedRun model) :
    RepeatableNumberAggregateMixedRunAnalysis :=
  let candidates :=
    plan.cascade.total.operation.core.target.id :: plan.run.targetFields
  {
    cascade := plan.cascade.analyze
    scalarTargets := plan.run.steps.map fun step =>
      (step.targetKind, step.targetField)
    computedDependencies := plan.run.steps.map fun step =>
      (step.targetField,
        candidates.filter fun field => step.referencesField field)
  }

/-- Execute the prefix, seed its aggregate as one typed Number completion, and reuse the existing supplied-order mixed executor. -/
def execute (plan : CheckedRepeatableNumberAggregateMixedRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    Except RepeatableNumberAggregateMixedRunFault
      RepeatableNumberAggregateMixedRunOutcomes := do
  let cascade ← plan.cascade.execute world input |>.mapError .cascade
  let initial : ScalarComputationRunState := {
    completed := [.number {
      targetField := plan.cascade.total.operation.core.target.id
      outcome := cascade.aggregate.outcome
    }]
  }
  let final ← plan.run.executeSteps world patterns input plan.run.steps initial
    |>.mapError .run
  pure { cascade, scalars := final.outcomes.drop 1 }

end CheckedRepeatableNumberAggregateMixedRun

end A12Kernel
