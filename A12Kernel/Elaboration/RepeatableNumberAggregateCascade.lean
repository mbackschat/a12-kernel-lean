import A12Kernel.Elaboration.RepeatableNumberAggregatePlan
import A12Kernel.Elaboration.NumericComputation.Run
import A12Kernel.Semantics.NumericDependency

/-! # Repeatable Number to aggregate cascade execution and bounded suffixes -/

namespace A12Kernel

/-- Rich row outcomes followed by the rich root aggregate outcome. -/
structure RepeatableNumberAggregateCascadeOutcomes where
  rows : List (SourcedNumericTargetOutcome CellAddr)
  aggregate : SourcedNumericTargetOutcome CellAddr
  deriving Repr, DecidableEq

inductive RepeatableNumberAggregateCascadeFault where
  | row (cause : AddressedNumberFieldFault)
  | aggregate (cause : NumericComputationFault)
  | targetCheck (cause : NumericTargetCheckFault)
  deriving Repr, DecidableEq

namespace CheckedRepeatableNumberAggregateCascade

/-- The exact root address owned by the aggregate target. -/
def aggregateAddress
    (cascade : CheckedRepeatableNumberAggregateCascade model) : CellAddr := {
  field := cascade.total.operation.core.target.id
  path := []
}

/-- Expose one completed aggregate through the Number dependency boundary only at its exact root address. -/
def readCompletion (cascade : CheckedRepeatableNumberAggregateCascade model)
    (outcome : NumericTargetOutcome) (input : CheckedDocument model)
    (address : CellAddr) : Except CheckedDocumentError CheckedCell :=
  if address == cascade.aggregateAddress then
    .ok (NumericDependencyCell.ofOutcome outcome).checked
  else
    input.read address

def analyze (plan : CheckedRepeatableNumberAggregateCascade model) :
    RepeatableNumberAggregateCascadeAnalysis := {
  producer := plan.row.kind
  consumer := plan.consumer.kind
  operation := plan.operation
  repeatableScope := plan.row.targetDeclaration.repeatableScope
  fieldDependencies := [
    (plan.row.targetField, plan.row.sourceFields),
    (plan.total.operation.core.target.id,
      plan.consumer.fieldDependencies)]
}

private def readAfterRows (input : CheckedDocument model)
    (rows : List (SourcedNumericTargetOutcome CellAddr))
    (environment : Env) (field : FieldId) : CheckedCell :=
  match input.cellAddress environment field with
  | .error _ => malformedCheckedCell
  | .ok address =>
      match readAfterNumericDependencies input rows address with
      | .ok cell => cell
      | .error _ => malformedCheckedCell

/-- Evaluate the aggregate phase against the exact completed row overlay. -/
def executeAggregateAfterRows
    (plan : CheckedRepeatableNumberAggregateCascade model)
    (world : World) (input : CheckedDocument model)
    (rows : List (SourcedNumericTargetOutcome CellAddr)) :
    Except RepeatableNumberAggregateCascadeFault
      (SourcedNumericTargetOutcome CellAddr) := do
  let read := readAfterRows input rows
  let checked ← plan.total.evaluateIn {
      scalar := input.scalarComputationContext world
      document := input.source.toDocument
      outer := []
      filterRead := read
      starRead := read
    } |>.mapError .aggregate
  let outcome ← match checked with
    | .supported outcome => pure outcome
    | .unsupported cause => throw (.targetCheck cause)
  let target : CellAddr := {
    field := plan.total.operation.core.target.id
    path := []
  }
  pure {
    targetField := target
    outcome
    source := input.numericTargetPlacementStateAt target
  }

/-- Execute the row computation first, then expose every rich row outcome through its exact address to the later aggregate traversal. -/
def execute (plan : CheckedRepeatableNumberAggregateCascade model)
    (world : World) (input : CheckedDocument model) :
    Except RepeatableNumberAggregateCascadeFault
      RepeatableNumberAggregateCascadeOutcomes := do
  let rows ← plan.row.execute input |>.mapError .row
  let aggregate ← plan.executeAggregateAfterRows world input rows
  pure { rows, aggregate }

end CheckedRepeatableNumberAggregateCascade

/-- Fail-closed errors for extending one checked row-to-aggregate cascade with a later scalar direct-field binary computation. -/
inductive RepeatableNumberAggregateScalarCascadeElabError where
  | scalar (cause : NumericComputationElabError)
  | incoherentScalar
  | duplicateTarget (field : FieldId)
  | missingAggregateDependency (field : FieldId)
  | cycle (field : FieldId)
  deriving Repr, DecidableEq

/-- One checked row-to-aggregate cascade followed by one nonrepeatable direct-field binary Number computation that reads the aggregate target. This remains a fixed three-stage route rather than a scheduler. -/
structure CheckedRepeatableNumberAggregateScalarCascade (model : FlatModel) where
  private mk ::
  cascade : CheckedRepeatableNumberAggregateCascade model
  scalar : CheckedNumericTargetComputationOperation model
  scalarOperation : NumericScaleBinaryOp
  leftDeclaration : FlatFieldDecl
  rightDeclaration : FlatFieldDecl
  expressionOwned :
    scalar.operation.core.expression =
      .binary scalarOperation
        (.atom (.numeric (.field leftDeclaration)))
        (.atom (.numeric (.field rightDeclaration)))
  aggregateDependency :
    (leftDeclaration.id == cascade.total.operation.core.target.id ||
      rightDeclaration.id == cascade.total.operation.core.target.id) = true
  distinctFromRows : scalar.operation.core.target.id ≠ cascade.row.targetField
  distinctFromAggregate :
    scalar.operation.core.target.id ≠ cascade.total.operation.core.target.id
  noBackEdge :
    (cascade.row.sourceFields ++ cascade.consumer.fieldDependencies).contains
      scalar.operation.core.target.id = false

private def certifyRepeatableNumberAggregateScalarCascade
    (cascade : CheckedRepeatableNumberAggregateCascade model)
    (scalar : CheckedNumericTargetComputationOperation model)
    (operation : NumericScaleBinaryOp) (left right : FlatFieldDecl)
    (hExpression : scalar.operation.core.expression =
      .binary operation
        (.atom (.numeric (.field left)))
        (.atom (.numeric (.field right)))) :
    Except RepeatableNumberAggregateScalarCascadeElabError
      (CheckedRepeatableNumberAggregateScalarCascade model) := do
  if hRows : scalar.operation.core.target.id ≠ cascade.row.targetField then
    if hAggregate : scalar.operation.core.target.id ≠
        cascade.total.operation.core.target.id then
      if hBackEdge :
          (cascade.row.sourceFields ++ cascade.consumer.fieldDependencies).contains
            scalar.operation.core.target.id = false then
        if hDependency :
            (left.id == cascade.total.operation.core.target.id ||
              right.id == cascade.total.operation.core.target.id) = true then
          pure {
            cascade, scalar, scalarOperation := operation
            leftDeclaration := left
            rightDeclaration := right
            expressionOwned := hExpression
            aggregateDependency := hDependency
            distinctFromRows := hRows
            distinctFromAggregate := hAggregate
            noBackEdge := hBackEdge
          }
        else
          throw (.missingAggregateDependency
            cascade.total.operation.core.target.id)
      else throw (.cycle scalar.operation.core.target.id)
    else throw (.duplicateTarget scalar.operation.core.target.id)
  else throw (.duplicateTarget scalar.operation.core.target.id)

/-- Extend a checked row-to-aggregate cascade with one exact scalar direct-field binary target. The later expression must read the aggregate, and neither earlier stage may read the later target. -/
def checkRepeatableNumberAggregateScalarCascade
    (cascade : CheckedRepeatableNumberAggregateCascade model)
    (scalarDeclaringGroup : GroupPath) (scalarTarget : FieldId)
    (leftSource rightSource : SurfaceFieldPath)
    (operation : NumericScaleBinaryOp) :
    Except RepeatableNumberAggregateScalarCascadeElabError
      (CheckedRepeatableNumberAggregateScalarCascade model) := do
  if scalarTarget == cascade.row.targetField ||
      scalarTarget == cascade.total.operation.core.target.id then
    throw (.duplicateTarget scalarTarget)
  if (cascade.row.sourceFields ++ cascade.consumer.fieldDependencies).contains
      scalarTarget then
    throw (.cycle scalarTarget)
  let expression : AuthoredNumericExpr SurfaceNumericComputationAtom :=
    .binary operation
      (.atom (.numeric (.field leftSource)))
      (.atom (.numeric (.field rightSource)))
  let scalar ← elaborateCompleteNumericTargetComputationOperation model
      scalarDeclaringGroup scalarTarget expression |>.mapError .scalar
  match hExpression : scalar.operation.core.expression with
  | .binary actualOperation
      (.atom (.numeric (.field left)))
      (.atom (.numeric (.field right))) =>
      certifyRepeatableNumberAggregateScalarCascade cascade scalar
        actualOperation left right hExpression
  | _ => throw .incoherentScalar

/-- The prior Analyze view plus the later scalar edge. -/
structure RepeatableNumberAggregateScalarCascadeAnalysis where
  cascade : RepeatableNumberAggregateCascadeAnalysis
  scalarOperation : NumericScaleBinaryOp
  fieldDependencies : List (FieldId × List FieldId)
  deriving Repr, DecidableEq

/-- Rich outcomes from all three fixed stages. -/
structure RepeatableNumberAggregateScalarCascadeOutcomes where
  cascade : RepeatableNumberAggregateCascadeOutcomes
  scalar : SourcedNumericTargetOutcome CellAddr
  deriving Repr, DecidableEq

inductive RepeatableNumberAggregateScalarCascadeFault where
  | cascade (cause : RepeatableNumberAggregateCascadeFault)
  | scalar (cause : NumericComputationFault)
  | targetCheck (cause : NumericTargetCheckFault)
  deriving Repr, DecidableEq

namespace CheckedRepeatableNumberAggregateScalarCascade

def analyze (plan : CheckedRepeatableNumberAggregateScalarCascade model) :
    RepeatableNumberAggregateScalarCascadeAnalysis := {
  cascade := plan.cascade.analyze
  scalarOperation := plan.scalarOperation
  fieldDependencies := plan.cascade.analyze.fieldDependencies ++ [
    (plan.scalar.operation.core.target.id,
      [plan.leftDeclaration.id, plan.rightDeclaration.id].eraseDups)]
}

/-- Execute the checked row and aggregate prefix, then expose only its rich aggregate outcome through the existing cause-blind scalar dependency cell. -/
def execute (plan : CheckedRepeatableNumberAggregateScalarCascade model)
    (world : World) (input : CheckedDocument model) :
    Except RepeatableNumberAggregateScalarCascadeFault
      RepeatableNumberAggregateScalarCascadeOutcomes := do
  let cascade ← plan.cascade.execute world input |>.mapError .cascade
  let base := input.scalarComputationContext world
  let aggregateField := plan.cascade.total.operation.core.target.id
  let context : ScalarComputationContext := {
    read := fun field =>
      if field == aggregateField then
        (NumericDependencyCell.ofOutcome cascade.aggregate.outcome).checked
      else base.read field
    world := base.world
  }
  let checked ← plan.scalar.evaluate context |>.mapError .scalar
  let outcome ← match checked with
    | .supported outcome => pure outcome
    | .unsupported cause => throw (.targetCheck cause)
  let target : CellAddr := {
    field := plan.scalar.operation.core.target.id
    path := []
  }
  pure {
    cascade
    scalar := {
      targetField := target
      outcome
      source := input.numericTargetPlacementStateAt target
    }
  }

end CheckedRepeatableNumberAggregateScalarCascade

/-- Fail-closed errors for composing a checked aggregate prefix with one existing finite scalar Number run. -/
inductive RepeatableNumberAggregateRunCascadeElabError where
  | duplicateTarget (field : FieldId)
  | missingAggregateDependency (field : FieldId)
  | cycle (field : FieldId)
  | incoherentRun
  deriving Repr, DecidableEq

/-- One checked row-to-aggregate prefix followed by an existing finite supplied-order scalar Number run seeded with the aggregate completion. -/
structure CheckedRepeatableNumberAggregateRunCascade (model : FlatModel) where
  private mk ::
  cascade : CheckedRepeatableNumberAggregateCascade model
  run : CheckedNumericComputationRun model
  distinctTargets : run.targetFields.all (fun field =>
    field != cascade.row.targetField &&
      field != cascade.total.operation.core.target.id) = true
  noBackEdge : run.targetFields.all (fun field =>
    !(cascade.row.sourceFields ++
      cascade.consumer.fieldDependencies).contains field) = true
  aggregateDependency : run.tables.any (fun table =>
    table.referencesField cascade.total.operation.core.target.id) = true

/-- Compose an already-checked aggregate prefix and scalar run without introducing another schedule. The run must consume the aggregate, own disjoint targets, and remain absent from both earlier dependency sets. -/
def checkRepeatableNumberAggregateRunCascade
    (cascade : CheckedRepeatableNumberAggregateCascade model)
    (run : CheckedNumericComputationRun model) :
    Except RepeatableNumberAggregateRunCascadeElabError
      (CheckedRepeatableNumberAggregateRunCascade model) := do
  if hDistinct : run.targetFields.all (fun field =>
      field != cascade.row.targetField &&
        field != cascade.total.operation.core.target.id) = true then
    if hBackEdge : run.targetFields.all (fun field =>
        !(cascade.row.sourceFields ++
          cascade.consumer.fieldDependencies).contains field) = true then
      if hDependency : run.tables.any (fun table =>
          table.referencesField
            cascade.total.operation.core.target.id) = true then
        pure {
          cascade := cascade
          run := run
          distinctTargets := hDistinct
          noBackEdge := hBackEdge
          aggregateDependency := hDependency }
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

/-- The checked prefix plus the scalar run's supplied target order and computed-target edges. -/
structure RepeatableNumberAggregateRunCascadeAnalysis where
  cascade : RepeatableNumberAggregateCascadeAnalysis
  scalarTargets : List FieldId
  computedDependencies : List (FieldId × List FieldId)
  deriving Repr, DecidableEq

/-- Rich prefix outcomes plus the rich scalar run outcomes in supplied order. -/
structure RepeatableNumberAggregateRunCascadeOutcomes where
  cascade : RepeatableNumberAggregateCascadeOutcomes
  scalars : List (FieldId × NumericTargetOutcome)
  deriving Repr, DecidableEq

inductive RepeatableNumberAggregateRunCascadeFault where
  | cascade (cause : RepeatableNumberAggregateCascadeFault)
  | run (cause : NumericComputationRunFault)
  deriving Repr, DecidableEq

namespace CheckedRepeatableNumberAggregateRunCascade

def analyze (plan : CheckedRepeatableNumberAggregateRunCascade model) :
    RepeatableNumberAggregateRunCascadeAnalysis :=
  let candidates :=
    plan.cascade.total.operation.core.target.id :: plan.run.targetFields
  {
    cascade := plan.cascade.analyze
    scalarTargets := plan.run.targetFields
    computedDependencies := plan.run.tables.map fun table =>
      (table.targetField,
        candidates.filter fun field => table.referencesField field)
  }

/-- Execute the prefix, seed its aggregate as one completed Number state entry, and reuse the existing supplied-order scalar executor unchanged. -/
def execute (plan : CheckedRepeatableNumberAggregateRunCascade model)
    (world : World) (input : CheckedDocument model) :
    Except RepeatableNumberAggregateRunCascadeFault
      RepeatableNumberAggregateRunCascadeOutcomes := do
  let cascade ← plan.cascade.execute world input |>.mapError .cascade
  let initial : NumericComputationRunState := {
    completed := [{
      targetField := plan.cascade.total.operation.core.target.id
      outcome := cascade.aggregate.outcome
    }]
  }
  let final ← plan.run.executeTables world input plan.run.tables initial
    |>.mapError .run
  pure { cascade, scalars := final.outcomes.drop 1 }

end CheckedRepeatableNumberAggregateRunCascade

end A12Kernel
