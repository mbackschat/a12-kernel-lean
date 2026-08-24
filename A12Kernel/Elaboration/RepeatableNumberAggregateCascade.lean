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

/-- Whether the later aggregate reads the producer as its value or only through its filter. -/
inductive RepeatableNumberAggregateConsumerKind where
  | plain
  | filtered
  deriving Repr, DecidableEq

/-- One sole starred aggregate operand retained with its exact checked filter boundary. -/
inductive CheckedRepeatableNumberAggregateConsumer (model : FlatModel) where
  | plain (source : CheckedStarNumberSource model)
  | filtered (source : CheckedStarNumberHavingSource model)

namespace CheckedRepeatableNumberAggregateConsumer

def kind : CheckedRepeatableNumberAggregateConsumer model →
    RepeatableNumberAggregateConsumerKind
  | .plain _ => .plain
  | .filtered _ => .filtered

def valueSource : CheckedRepeatableNumberAggregateConsumer model →
    CheckedStarNumberSource model
  | .plain source => source
  | .filtered source => source.source

def valueField (consumer : CheckedRepeatableNumberAggregateConsumer model) :
    FlatNumberField :=
  consumer.valueSource.field

def valueDeclaration
    (consumer : CheckedRepeatableNumberAggregateConsumer model) : FlatFieldDecl :=
  consumer.valueSource.source.declaration

/-- Complete static dependencies in first authored occurrence order: the aggregate value field precedes any fields used only by `Having`. -/
def fieldDependencies : CheckedRepeatableNumberAggregateConsumer model → List FieldId
  | .plain source => [source.field.id]
  | .filtered source =>
      (source.source.field.id :: source.having.fieldIds).eraseDups

/-- The stage-forming dependency is the plain value read or, for the filtered route, a read inside `Having`. The aggregate value field cannot stand in for the latter. -/
def referencesProducer : CheckedRepeatableNumberAggregateConsumer model → FieldId → Bool
  | .plain source, field => source.field.id == field
  | .filtered source, field => source.having.referencesField field

def operand : CheckedRepeatableNumberAggregateConsumer model →
    CheckedNumberEntityOperand model
  | .plain source => .star source
  | .filtered source => .starHaving source

end CheckedRepeatableNumberAggregateConsumer

/-- Fail-closed errors for one row-local Number computation followed by one root aggregate that reads it directly or through its filter. -/
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
  | missingFilterDependency (field : FieldId)
  deriving Repr, DecidableEq

/-- One checked one-level Number producer followed by one nonrepeatable `Sum`, `MinValue`, `MaxValue`, or distinct-count computation whose sole star reads that producer directly or through `Having`. This is a fixed two-stage route, not a scheduler. -/
structure CheckedRepeatableNumberAggregateCascade (model : FlatModel) where
  private mk ::
  row : CheckedRepeatableNumberAggregateProducer model
  aggregate : CheckedNumberEntitySource model
  consumer : CheckedRepeatableNumberAggregateConsumer model
  total : CheckedNumericTargetComputationOperation model
  operation : NumericAggregateOp
  expressionOwned :
    total.operation.core.expression =
      .atom (.numeric (.aggregate operation aggregate))
  firstOwned : aggregate.first = consumer.operand
  soleOperand : aggregate.rest = []
  dependency : consumer.referencesProducer row.targetField = true
  sameGroup :
    consumer.valueDeclaration.groupPath = row.declaringGroup
  sameScope :
    consumer.valueDeclaration.repeatableScope =
      row.targetDeclaration.repeatableScope
  oneLevel : row.targetDeclaration.repeatableScope.length = 1
  noCycle : row.sourceFields.contains total.operation.core.target.id = false

private def certifyRepeatableNumberAggregateCascade
    (row : CheckedRepeatableNumberAggregateProducer model)
    (aggregate : CheckedNumberEntitySource model)
    (consumer : CheckedRepeatableNumberAggregateConsumer model)
    (total : CheckedNumericTargetComputationOperation model)
    (operation : NumericAggregateOp)
    (hExpression : total.operation.core.expression =
      .atom (.numeric (.aggregate operation aggregate)))
    (hFirst : aggregate.first = consumer.operand) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) := do
  if hRest : aggregate.rest = [] then
    if hDependency : consumer.referencesProducer row.targetField = true then
      if hGroup : consumer.valueDeclaration.groupPath = row.declaringGroup then
        if hScope : consumer.valueDeclaration.repeatableScope =
            row.targetDeclaration.repeatableScope then
          if hOneLevel : row.targetDeclaration.repeatableScope.length = 1 then
            if hNoCycle : row.sourceFields.contains
                total.operation.core.target.id = false then
              pure {
                row, aggregate, consumer, total, operation
                expressionOwned := hExpression
                firstOwned := hFirst
                soleOperand := hRest
                dependency := hDependency
                sameGroup := hGroup
                sameScope := hScope
                oneLevel := hOneLevel
                noCycle := hNoCycle
              }
            else throw (.cycle total.operation.core.target.id)
          else
            throw (.unsupportedScope row.targetDeclaration.repeatableScope)
        else
          throw (.scopeMismatch row.targetDeclaration.repeatableScope
            consumer.valueDeclaration.repeatableScope)
      else
        throw (.groupMismatch row.declaringGroup
          consumer.valueDeclaration.groupPath)
    else
      match consumer with
      | .plain _ => throw (.dependency row.targetField consumer.valueField.id)
      | .filtered _ => throw (.missingFilterDependency row.targetField)
  else throw .incoherentAggregate

private def finishRepeatableNumberAggregateCascade
    (model : FlatModel) (row : CheckedRepeatableNumberAggregateProducer model)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (aggregateFirst : SurfaceNumberEntityOperand) (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) := do
  let expression : AuthoredNumericExpr SurfaceNumericComputationAtom :=
    .atom (.numeric (.aggregate operation {
      first := aggregateFirst
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
            certifyRepeatableNumberAggregateCascade row aggregate (.plain star)
              total operation (hOperation ▸ hExpression)
              (by simpa [CheckedRepeatableNumberAggregateConsumer.operand] using hFirst)
        | .starHaving source =>
            certifyRepeatableNumberAggregateCascade row aggregate (.filtered source)
              total operation (hOperation ▸ hExpression)
              (by simpa [CheckedRepeatableNumberAggregateConsumer.operand] using hFirst)
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
    aggregateDeclaringGroup aggregateTarget (.star aggregateSource) operation

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
    aggregateDeclaringGroup aggregateTarget (.star aggregateSource) operation

/-- Check one direct-field binary producer followed by a sole filtered star whose filter depends on that producer. The aggregate value field may be a different Number in the same one-level row scope. -/
def checkRepeatableNumberBinaryFilteredAggregateCascade
    (model : FlatModel)
    (rowDeclaringGroup : GroupPath) (rowTarget : FieldId)
    (leftSource rightSource : SurfaceFieldPath) (rowOperation : NumericArithmeticOp)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (aggregateSource : SurfaceStarFieldPath) (having : SurfaceCorrelatedHaving)
    (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) := do
  let row ← checkAddressedNumberBinary model rowDeclaringGroup rowTarget
      leftSource rightSource rowOperation |>.mapError .binary
  finishRepeatableNumberAggregateCascade model (.binary row)
    aggregateDeclaringGroup aggregateTarget
    (.starHaving aggregateSource having) operation

/-- The exact two dependency stages and the one-level row scope exposed to Analyze. -/
structure RepeatableNumberAggregateCascadeAnalysis where
  producer : RepeatableNumberAggregateProducerKind
  consumer : RepeatableNumberAggregateConsumerKind
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
