import A12Kernel.Elaboration.AddressedNumberField
import A12Kernel.Elaboration.AddressedNumberBinary
import A12Kernel.Elaboration.NumericComputation.Target

/-! # Checked repeatable Number to aggregate plans -/

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

/-- Either one-or-more plain starred operands or one filtered starred operand.
Plain operands retain authored order; the filtered form stays deliberately
single until a mixed-list observation justifies a wider boundary. -/
inductive CheckedRepeatableNumberAggregateConsumer (model : FlatModel) where
  | plain (first : CheckedStarNumberSource model)
      (rest : List (CheckedStarNumberSource model))
  | filtered (source : CheckedStarNumberHavingSource model)

namespace CheckedRepeatableNumberAggregateConsumer

def kind : CheckedRepeatableNumberAggregateConsumer model →
    RepeatableNumberAggregateConsumerKind
  | .plain _ _ => .plain
  | .filtered _ => .filtered

def valueSources : CheckedRepeatableNumberAggregateConsumer model →
    List (CheckedStarNumberSource model)
  | .plain first rest => first :: rest
  | .filtered source => [source.source]

def valueField : CheckedRepeatableNumberAggregateConsumer model → FlatNumberField
  | .plain first _ => first.field
  | .filtered source => source.source.field

/-- Complete static dependencies in first authored occurrence order: the aggregate value field precedes any fields used only by `Having`. -/
def fieldDependencies : CheckedRepeatableNumberAggregateConsumer model → List FieldId
  | .plain first rest =>
      (first.field.id :: rest.map (·.field.id)).eraseDups
  | .filtered source =>
      (source.source.field.id :: source.having.fieldIds).eraseDups

/-- The stage-forming dependency is the plain value read or, for the filtered route, a read inside `Having`. The aggregate value field cannot stand in for the latter. -/
def referencesProducer : CheckedRepeatableNumberAggregateConsumer model → FieldId → Bool
  | .plain first rest, field =>
      first.field.id == field || rest.any fun source => source.field.id == field
  | .filtered source, field => source.having.referencesField field

def operands : CheckedRepeatableNumberAggregateConsumer model →
    List (CheckedNumberEntityOperand model)
  | .plain first rest => .star first :: rest.map .star
  | .filtered source => [.starHaving source]

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
  | aggregateBindingRequired (levels : List RepeatableLevel)
  | cycle (field : FieldId)
  | missingFilterDependency (field : FieldId)
  deriving Repr, DecidableEq

/-- One checked repeatable Number producer followed by one nonrepeatable `Sum`, `MinValue`, `MaxValue`, or distinct-count computation. A plain aggregate retains one-or-more starred operands and must read the producer in at least one authored position; the filtered form remains a sole star whose `Having` reads the producer. This is a fixed two-stage route, not a scheduler. -/
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
  operandsOwned : aggregate.first :: aggregate.rest = consumer.operands
  dependency : consumer.referencesProducer row.targetField = true
  sameGroup :
    consumer.valueSources.all (fun source =>
      source.source.declaration.groupPath == row.declaringGroup) = true
  sameScope :
    consumer.valueSources.all (fun source =>
      source.source.declaration.repeatableScope ==
        row.targetDeclaration.repeatableScope) = true
  rootClosed :
    consumer.valueSources.all (fun source =>
      source.source.bindingScope.isEmpty) = true
  noCycle : row.sourceFields.contains total.operation.core.target.id = false

structure RepeatableNumberAggregateSuffixScopeCertificate
    (cascade : CheckedRepeatableNumberAggregateCascade model)
    (suffixScope : List RepeatableLevel) : Type where
  sameScope : suffixScope = cascade.row.targetDeclaration.repeatableScope

/-- Certify that a bounded suffix stays in the aggregate producer's exact row scope. -/
def certifyRepeatableNumberAggregateSuffixScope
    (cascade : CheckedRepeatableNumberAggregateCascade model)
    (suffixScope : List RepeatableLevel) :
    Except (List RepeatableLevel × List RepeatableLevel)
      (RepeatableNumberAggregateSuffixScopeCertificate cascade suffixScope) :=
  if hScope : suffixScope = cascade.row.targetDeclaration.repeatableScope then
    .ok { sameScope := hScope }
  else
    .error (cascade.row.targetDeclaration.repeatableScope, suffixScope)

private def certifyRepeatableNumberAggregateCascade
    (row : CheckedRepeatableNumberAggregateProducer model)
    (aggregate : CheckedNumberEntitySource model)
    (consumer : CheckedRepeatableNumberAggregateConsumer model)
    (total : CheckedNumericTargetComputationOperation model)
    (operation : NumericAggregateOp)
    (hExpression : total.operation.core.expression =
      .atom (.numeric (.aggregate operation aggregate)))
    (hOperands : aggregate.first :: aggregate.rest = consumer.operands) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) := do
  if hDependency : consumer.referencesProducer row.targetField = true then
    if hGroup : consumer.valueSources.all (fun source =>
        source.source.declaration.groupPath == row.declaringGroup) = true then
      if hScope : consumer.valueSources.all (fun source =>
          source.source.declaration.repeatableScope ==
            row.targetDeclaration.repeatableScope) = true then
        if hRoot : consumer.valueSources.all (fun source =>
            source.source.bindingScope.isEmpty) = true then
          if hNoCycle : row.sourceFields.contains
              total.operation.core.target.id = false then
            pure {
              row, aggregate, consumer, total, operation
              expressionOwned := hExpression
              operandsOwned := hOperands
              dependency := hDependency
              sameGroup := hGroup
              sameScope := hScope
              rootClosed := hRoot
              noCycle := hNoCycle
            }
          else throw (.cycle total.operation.core.target.id)
        else
          match consumer.valueSources.find? fun source =>
              !source.source.bindingScope.isEmpty with
          | some source =>
              throw (.aggregateBindingRequired source.source.bindingScope)
          | none => throw .incoherentAggregate
      else
        match consumer.valueSources.find? fun source =>
            source.source.declaration.repeatableScope !=
              row.targetDeclaration.repeatableScope with
        | some source =>
            throw (.scopeMismatch row.targetDeclaration.repeatableScope
              source.source.declaration.repeatableScope)
        | none => throw .incoherentAggregate
    else
      match consumer.valueSources.find? fun source =>
          source.source.declaration.groupPath != row.declaringGroup with
      | some source =>
          throw (.groupMismatch row.declaringGroup
            source.source.declaration.groupPath)
      | none => throw .incoherentAggregate
  else
    match consumer with
    | .plain _ _ => throw (.dependency row.targetField consumer.valueField.id)
    | .filtered _ => throw (.missingFilterDependency row.targetField)

private structure CheckedPlainStarTail
    (operands : List (CheckedNumberEntityOperand model)) where
  sources : List (CheckedStarNumberSource model)
  owned : operands = sources.map .star

private def checkedPlainStarTail? :
    (operands : List (CheckedNumberEntityOperand model)) →
      Option (CheckedPlainStarTail operands)
  | [] => some { sources := [], owned := rfl }
  | .star source :: rest => do
      let tail ← checkedPlainStarTail? rest
      pure {
        sources := source :: tail.sources
        owned := by simp [tail.owned]
      }
  | _ :: _ => none

private def finishRepeatableNumberAggregateCascade
    (model : FlatModel) (row : CheckedRepeatableNumberAggregateProducer model)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (aggregateSource : SurfaceNumberEntitySource)
    (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) := do
  let expression : AuthoredNumericExpr SurfaceNumericComputationAtom :=
    .atom (.numeric (.aggregate operation aggregateSource))
  let total ← elaborateCompleteNumericTargetComputationOperation model
      aggregateDeclaringGroup aggregateTarget expression
    |>.mapError .aggregate
  match hExpression : total.operation.core.expression with
  | .atom (.numeric (.aggregate actualOperation aggregate)) =>
      if hOperation : actualOperation = operation then
        match hFirst : aggregate.first with
        | .star first =>
            match checkedPlainStarTail? aggregate.rest with
            | some tail =>
                certifyRepeatableNumberAggregateCascade row aggregate
                  (.plain first tail.sources) total operation
                  (hOperation ▸ hExpression) (by
                    simp [CheckedRepeatableNumberAggregateConsumer.operands,
                      hFirst, tail.owned])
            | none => throw .incoherentAggregate
        | .starHaving source =>
            if hRest : aggregate.rest = [] then
              certifyRepeatableNumberAggregateCascade row aggregate
                (.filtered source) total operation
                (hOperation ▸ hExpression) (by
                  simp [CheckedRepeatableNumberAggregateConsumer.operands,
                    hFirst, hRest])
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
    aggregateDeclaringGroup aggregateTarget {
      first := .star aggregateSource
      rest := []
    } operation

/-- Check a direct-assignment producer followed by a sole filtered star whose filter depends on that producer. The aggregate value field may be a different Number in the same repeatable row scope. -/
def checkRepeatableNumberFilteredAggregateCascade
    (model : FlatModel)
    (rowDeclaringGroup : GroupPath) (rowTarget : FieldId)
    (rowSource : SurfaceFieldPath)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (aggregateSource : SurfaceStarFieldPath) (having : SurfaceCorrelatedHaving)
    (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) := do
  let row ← checkAddressedNumberField model rowDeclaringGroup
      rowTarget rowSource |>.mapError .row
  finishRepeatableNumberAggregateCascade model (.direct row)
    aggregateDeclaringGroup aggregateTarget {
      first := .starHaving aggregateSource having
      rest := []
    } operation

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
    aggregateDeclaringGroup aggregateTarget {
      first := .star aggregateSource
      rest := []
    } operation

/-- Check one direct-field binary producer followed by a sole filtered star whose filter depends on that producer. The aggregate value field may be a different Number in the same repeatable row scope. -/
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
    aggregateDeclaringGroup aggregateTarget {
      first := .starHaving aggregateSource having
      rest := []
    } operation

/-- Check a direct producer followed by two-or-more plain starred operands in
the producer's exact repeatable scope. The producer may occur at any authored
operand position. -/
def checkRepeatableNumberMultiStarAggregateCascade
    (model : FlatModel)
    (rowDeclaringGroup : GroupPath) (rowTarget : FieldId)
    (rowSource : SurfaceFieldPath)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (aggregateFirst aggregateSecond : SurfaceStarFieldPath)
    (aggregateRest : List SurfaceStarFieldPath)
    (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) := do
  let row ← checkAddressedNumberField model rowDeclaringGroup
      rowTarget rowSource |>.mapError .row
  finishRepeatableNumberAggregateCascade model (.direct row)
    aggregateDeclaringGroup aggregateTarget {
      first := .star aggregateFirst
      rest := .star aggregateSecond :: aggregateRest.map .star
    } operation

/-- Binary-producer counterpart of the multi-star aggregate route. -/
def checkRepeatableNumberBinaryMultiStarAggregateCascade
    (model : FlatModel)
    (rowDeclaringGroup : GroupPath) (rowTarget : FieldId)
    (leftSource rightSource : SurfaceFieldPath)
    (rowOperation : NumericArithmeticOp)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (aggregateFirst aggregateSecond : SurfaceStarFieldPath)
    (aggregateRest : List SurfaceStarFieldPath)
    (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) := do
  let row ← checkAddressedNumberBinary model rowDeclaringGroup rowTarget
      leftSource rightSource rowOperation |>.mapError .binary
  finishRepeatableNumberAggregateCascade model (.binary row)
    aggregateDeclaringGroup aggregateTarget {
      first := .star aggregateFirst
      rest := .star aggregateSecond :: aggregateRest.map .star
    } operation

/-- The exact two dependency stages and complete repeatable row scope exposed to Analyze. -/
structure RepeatableNumberAggregateCascadeAnalysis where
  producer : RepeatableNumberAggregateProducerKind
  consumer : RepeatableNumberAggregateConsumerKind
  operation : NumericAggregateOp
  repeatableScope : List RepeatableLevel
  fieldDependencies : List (FieldId × List FieldId)
  deriving Repr, DecidableEq

end A12Kernel
