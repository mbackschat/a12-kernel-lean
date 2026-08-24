import A12Kernel.Elaboration.AddressedNumberField
import A12Kernel.Elaboration.AddressedNumberBinary
import A12Kernel.Elaboration.NumericComputation.Target
import A12Kernel.Semantics.NumericDependency

/-! # Repeatable Number to aggregate cascade -/

namespace A12Kernel

/-- The exact row-local producer identity needed by Analyze. -/
inductive RepeatableNumberAggregateProducerKind where
  | direct
  | binary (operation : NumericArithmeticOp)
  deriving Repr, DecidableEq

/-- One completed row-local producer admitted by this fixed aggregate route. -/
inductive CheckedRepeatableNumberAggregateProducer (model : FlatModel) where
  | direct (operation : CheckedAddressedNumberField model)
  | binary (operation : CheckedAddressedNumberBinary model)

namespace CheckedRepeatableNumberAggregateProducer

def kind : CheckedRepeatableNumberAggregateProducer model →
    RepeatableNumberAggregateProducerKind
  | .direct _ => .direct
  | .binary operation => .binary operation.op

def targetField : CheckedRepeatableNumberAggregateProducer model → FieldId
  | .direct operation => operation.placement.targetField
  | .binary operation => operation.pair.left.placement.targetField

def targetDeclaration : CheckedRepeatableNumberAggregateProducer model →
    FlatFieldDecl
  | .direct operation => operation.placement.targetDeclaration
  | .binary operation => operation.pair.left.placement.targetDeclaration

def declaringGroup : CheckedRepeatableNumberAggregateProducer model → GroupPath
  | .direct operation => operation.placement.declaringGroup
  | .binary operation => operation.pair.left.placement.declaringGroup

def sourceFields : CheckedRepeatableNumberAggregateProducer model → List FieldId
  | .direct operation => [operation.placement.sourceDeclaration.id]
  | .binary operation => [
      operation.pair.left.placement.sourceDeclaration.id,
      operation.pair.right.placement.sourceDeclaration.id]

def execute (producer : CheckedRepeatableNumberAggregateProducer model)
    (input : CheckedDocument model) :
    Except AddressedNumericLeafFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  match producer with
  | .direct operation => operation.execute input
  | .binary operation => operation.execute input

end CheckedRepeatableNumberAggregateProducer

/-- Fail-closed errors for one row-local Number computation followed by one root aggregate over that exact target. -/
inductive RepeatableNumberAggregateCascadeElabError where
  | row (cause : AddressedNumberFieldElabError)
  | binary (cause : AddressedNumberBinaryElabError)
  | aggregate (cause : NumericComputationElabError)
  | incoherentAggregate
  | dependency (expected actual : FieldId)
  | groupMismatch (row aggregate : GroupPath)
  | scopeMismatch (row aggregate : List RepeatableLevel)
  | unsupportedScope (actual : List RepeatableLevel)
  | cycle (field : FieldId)
  deriving Repr, DecidableEq

/-- One checked one-level Number producer followed by one nonrepeatable `Sum`, `MinValue`, `MaxValue`, or distinct-count computation over its sole plain-star target. This is a fixed two-stage route, not a scheduler. -/
structure CheckedRepeatableNumberAggregateCascade (model : FlatModel) where
  private mk ::
  row : CheckedRepeatableNumberAggregateProducer model
  aggregate : CheckedNumberEntitySource model
  star : CheckedStarNumberSource model
  total : CheckedNumericTargetComputationOperation model
  operation : NumericAggregateOp
  expressionOwned :
    total.operation.core.expression =
      .atom (.numeric (.aggregate operation aggregate))
  plainStar : aggregate.first = .star star
  soleOperand : aggregate.rest = []
  dependency : star.field.id = row.targetField
  sameGroup :
    star.source.declaration.groupPath = row.declaringGroup
  sameScope :
    star.source.declaration.repeatableScope =
      row.targetDeclaration.repeatableScope
  oneLevel : row.targetDeclaration.repeatableScope.length = 1
  noCycle : row.sourceFields.contains total.operation.core.target.id = false

private def finishRepeatableNumberAggregateCascade
    (model : FlatModel) (row : CheckedRepeatableNumberAggregateProducer model)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (aggregateSource : SurfaceStarFieldPath) (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) := do
  let expression : AuthoredNumericExpr SurfaceNumericComputationAtom :=
    .atom (.numeric (.aggregate operation {
      first := .star aggregateSource
      rest := []
    }))
  let total ← elaborateCompleteNumericTargetComputationOperation model
      aggregateDeclaringGroup aggregateTarget expression
    |>.mapError .aggregate
  match hExpression : total.operation.core.expression with
  | .atom (.numeric (.aggregate actualOperation aggregate)) =>
      if hOperation : actualOperation = operation then
        match hFirst : aggregate.first with
        | .star star =>
            if hRest : aggregate.rest = [] then
              if hDependency : star.field.id = row.targetField then
                if hGroup : star.source.declaration.groupPath =
                    row.declaringGroup then
                  if hScope : star.source.declaration.repeatableScope =
                      row.targetDeclaration.repeatableScope then
                    if hOneLevel :
                        row.targetDeclaration.repeatableScope.length = 1 then
                      if hNoCycle : row.sourceFields.contains
                          total.operation.core.target.id = false then
                        pure {
                          row, aggregate, star, total, operation
                          expressionOwned := hOperation ▸ hExpression
                          plainStar := hFirst
                          soleOperand := hRest
                          dependency := hDependency
                          sameGroup := hGroup
                          sameScope := hScope
                          oneLevel := hOneLevel
                          noCycle := hNoCycle
                        }
                      else throw (.cycle total.operation.core.target.id)
                    else
                      throw (.unsupportedScope
                        row.targetDeclaration.repeatableScope)
                  else
                    throw (.scopeMismatch
                      row.targetDeclaration.repeatableScope
                      star.source.declaration.repeatableScope)
                else
                  throw (.groupMismatch row.declaringGroup
                    star.source.declaration.groupPath)
              else
                throw (.dependency row.targetField star.field.id)
            else throw .incoherentAggregate
        | _ => throw .incoherentAggregate
      else throw .incoherentAggregate
  | _ => throw .incoherentAggregate

/-- Check the exact direct-assignment producer followed by a sole plain-star aggregate. -/
def checkRepeatableNumberAggregateCascade
    (model : FlatModel)
    (rowDeclaringGroup : GroupPath) (rowTarget : FieldId)
    (rowSource : SurfaceFieldPath)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (aggregateSource : SurfaceStarFieldPath) (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) := do
  let row ← checkAddressedNumberField model rowDeclaringGroup
      rowTarget rowSource |>.mapError .row
  finishRepeatableNumberAggregateCascade model (.direct row)
    aggregateDeclaringGroup aggregateTarget aggregateSource operation

/-- Check the exact direct-field binary producer followed by a sole plain-star aggregate. -/
def checkRepeatableNumberBinaryAggregateCascade
    (model : FlatModel)
    (rowDeclaringGroup : GroupPath) (rowTarget : FieldId)
    (leftSource rightSource : SurfaceFieldPath) (rowOperation : NumericArithmeticOp)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (aggregateSource : SurfaceStarFieldPath) (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) := do
  let row ← checkAddressedNumberBinary model rowDeclaringGroup rowTarget
      leftSource rightSource rowOperation |>.mapError .binary
  finishRepeatableNumberAggregateCascade model (.binary row)
    aggregateDeclaringGroup aggregateTarget aggregateSource operation

/-- The exact two dependency stages and the one-level row scope exposed to Analyze. -/
structure RepeatableNumberAggregateCascadeAnalysis where
  producer : RepeatableNumberAggregateProducerKind
  operation : NumericAggregateOp
  repeatableScope : List RepeatableLevel
  fieldDependencies : List (FieldId × List FieldId)
  deriving Repr, DecidableEq

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

def analyze (plan : CheckedRepeatableNumberAggregateCascade model) :
    RepeatableNumberAggregateCascadeAnalysis := {
  producer := plan.row.kind
  operation := plan.operation
  repeatableScope := plan.row.targetDeclaration.repeatableScope
  fieldDependencies := [
    (plan.row.targetField, plan.row.sourceFields),
    (plan.total.operation.core.target.id,
      [plan.row.targetField])]
}

private def readAfterRows (input : CheckedDocument model)
    (rows : List (SourcedNumericTargetOutcome CellAddr))
    (environment : Env) (field : FieldId) : CheckedCell :=
  match input.addressedCell environment field with
  | .error _ => malformedCheckedCell
  | .ok addressed =>
      match rows.find? fun row => row.targetField == addressed.address with
      | some row => (NumericDependencyCell.ofOutcome row.outcome).checked
      | none => addressed.cell

/-- Execute the row computation first, then expose every rich row outcome through its exact address to the later aggregate traversal. -/
def execute (plan : CheckedRepeatableNumberAggregateCascade model)
    (world : World) (input : CheckedDocument model) :
    Except RepeatableNumberAggregateCascadeFault
      RepeatableNumberAggregateCascadeOutcomes := do
  let rows ← plan.row.execute input |>.mapError .row
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
    rows
    aggregate := {
      targetField := target
      outcome
      source := input.numericTargetPlacementStateAt target
    }
  }

end CheckedRepeatableNumberAggregateCascade

end A12Kernel
