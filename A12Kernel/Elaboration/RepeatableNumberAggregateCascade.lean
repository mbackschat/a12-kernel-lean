import A12Kernel.Elaboration.AddressedNumberField
import A12Kernel.Elaboration.NumericComputation.Target
import A12Kernel.Semantics.NumericDependency

/-! # Repeatable Number to aggregate cascade -/

namespace A12Kernel

/-- Fail-closed errors for one row-local Number computation followed by one root aggregate over that exact target. -/
inductive RepeatableNumberAggregateCascadeElabError where
  | row (cause : AddressedNumberFieldElabError)
  | aggregate (cause : NumericComputationElabError)
  | incoherentAggregate
  | dependency (expected actual : FieldId)
  | groupMismatch (row aggregate : GroupPath)
  | scopeMismatch (row aggregate : List RepeatableLevel)
  | unsupportedScope (actual : List RepeatableLevel)
  | cycle (field : FieldId)
  deriving Repr, DecidableEq

/-- One checked one-level direct Number computation followed by one nonrepeatable `Sum`, `MinValue`, `MaxValue`, or distinct-count computation over its sole plain-star target. This is a fixed two-stage route, not a scheduler. -/
structure CheckedRepeatableNumberAggregateCascade (model : FlatModel) where
  private mk ::
  row : CheckedAddressedNumberField model
  aggregate : CheckedNumberEntitySource model
  star : CheckedStarNumberSource model
  total : CheckedNumericTargetComputationOperation model
  operation : NumericAggregateOp
  expressionOwned :
    total.operation.core.expression =
      .atom (.numeric (.aggregate operation aggregate))
  plainStar : aggregate.first = .star star
  soleOperand : aggregate.rest = []
  dependency : star.field.id = row.placement.targetField
  sameGroup :
    star.source.declaration.groupPath = row.placement.declaringGroup
  sameScope :
    star.source.declaration.repeatableScope =
      row.placement.targetDeclaration.repeatableScope
  oneLevel : row.placement.targetDeclaration.repeatableScope.length = 1
  noCycle :
    row.placement.sourceDeclaration.id ≠ total.operation.core.target.id

/-- Check only the exact plain-star aggregate route and its two supplied-order field edges. -/
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
              if hDependency : star.field.id = row.placement.targetField then
                if hGroup : star.source.declaration.groupPath =
                    row.placement.declaringGroup then
                  if hScope : star.source.declaration.repeatableScope =
                      row.placement.targetDeclaration.repeatableScope then
                    if hOneLevel :
                        row.placement.targetDeclaration.repeatableScope.length = 1 then
                      if hCycle : row.placement.sourceDeclaration.id =
                          total.operation.core.target.id then
                        throw (.cycle total.operation.core.target.id)
                      else
                        pure {
                          row, aggregate, star, total, operation
                          expressionOwned := hOperation ▸ hExpression
                          plainStar := hFirst
                          soleOperand := hRest
                          dependency := hDependency
                          sameGroup := hGroup
                          sameScope := hScope
                          oneLevel := hOneLevel
                          noCycle := hCycle
                        }
                    else
                      throw (.unsupportedScope
                        row.placement.targetDeclaration.repeatableScope)
                  else
                    throw (.scopeMismatch
                      row.placement.targetDeclaration.repeatableScope
                      star.source.declaration.repeatableScope)
                else
                  throw (.groupMismatch row.placement.declaringGroup
                    star.source.declaration.groupPath)
              else
                throw (.dependency row.placement.targetField star.field.id)
            else throw .incoherentAggregate
        | _ => throw .incoherentAggregate
      else throw .incoherentAggregate
  | _ => throw .incoherentAggregate

/-- The exact two field edges and the one-level row scope exposed to Analyze. -/
structure RepeatableNumberAggregateCascadeAnalysis where
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
  operation := plan.operation
  repeatableScope := plan.row.placement.targetDeclaration.repeatableScope
  fieldDependencies := [
    (plan.row.placement.targetField,
      [plan.row.placement.sourceDeclaration.id]),
    (plan.total.operation.core.target.id,
      [plan.row.placement.targetField])]
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
