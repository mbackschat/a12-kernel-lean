import A12Kernel.Elaboration.RepeatableNumberAggregateProducer
import A12Kernel.Elaboration.NumericComputation.Target

/-! # Checked repeatable Number to aggregate plans -/

namespace A12Kernel

/-- The authored order accepted by the compatibility wrapper for one exact plain-star and filtered-star pair. -/
inductive RepeatableNumberAggregateMixedOperandOrder where
  | plainThenFiltered
  | filteredThenPlain
  deriving Repr, DecidableEq

/-- Whether every aggregate slot is plain, every slot is filtered, or the list contains both kinds. -/
inductive RepeatableNumberAggregateConsumerKind where
  | plain
  | filtered
  | mixed
  deriving Repr, DecidableEq

/-- One checked aggregate slot at the repeatable star-list boundary. -/
inductive CheckedRepeatableNumberAggregateOperand (model : FlatModel) where
  | plain (source : CheckedStarNumberSource model)
  | filtered (source : CheckedStarNumberHavingSource model)

namespace CheckedRepeatableNumberAggregateOperand

def valueSource : CheckedRepeatableNumberAggregateOperand model →
    CheckedStarNumberSource model
  | .plain source => source
  | .filtered source => source.source

def isPlain : CheckedRepeatableNumberAggregateOperand model → Bool
  | .plain _ => true
  | .filtered _ => false

def isFiltered : CheckedRepeatableNumberAggregateOperand model → Bool
  | .plain _ => false
  | .filtered _ => true

def fieldDependencies : CheckedRepeatableNumberAggregateOperand model →
    List FieldId
  | .plain source => [source.field.id]
  | .filtered source => source.source.field.id :: source.having.fieldIds

/-- A plain value read forms a stage dependency. A filtered slot forms one only through its `Having`; its selected value does not stand in for that read. -/
def referencesProducer (field : FieldId) :
    CheckedRepeatableNumberAggregateOperand model → Bool
  | .plain source => source.field.id == field
  | .filtered source => source.having.referencesField field

def toEntityOperand : CheckedRepeatableNumberAggregateOperand model →
    CheckedNumberEntityOperand model
  | .plain source => .star source
  | .filtered source => .starHaving source

end CheckedRepeatableNumberAggregateOperand

/-- A checked nonempty aggregate operand list containing only plain or filtered Number stars in authored order. -/
structure CheckedRepeatableNumberAggregateConsumer (model : FlatModel) where
  first : CheckedRepeatableNumberAggregateOperand model
  rest : List (CheckedRepeatableNumberAggregateOperand model)

namespace CheckedRepeatableNumberAggregateConsumer

def slots (consumer : CheckedRepeatableNumberAggregateConsumer model) :
    List (CheckedRepeatableNumberAggregateOperand model) :=
  consumer.first :: consumer.rest

def kind : CheckedRepeatableNumberAggregateConsumer model →
    RepeatableNumberAggregateConsumerKind
  | { first := .plain _, rest } =>
      if rest.all CheckedRepeatableNumberAggregateOperand.isPlain then
        .plain
      else
        .mixed
  | { first := .filtered _, rest } =>
      if rest.all CheckedRepeatableNumberAggregateOperand.isFiltered then
        .filtered
      else
        .mixed

def valueSources : CheckedRepeatableNumberAggregateConsumer model →
    List (CheckedStarNumberSource model)
  | consumer => consumer.slots.map (·.valueSource)

/-- Complete static dependencies in first authored occurrence order: the aggregate value field precedes any fields used only by `Having`. -/
def fieldDependencies : CheckedRepeatableNumberAggregateConsumer model → List FieldId
  | consumer => (consumer.slots.flatMap (·.fieldDependencies)).eraseDups

/-- The stage-forming dependency is any plain value read or a read inside any filtered slot's `Having`. -/
def referencesProducer : CheckedRepeatableNumberAggregateConsumer model → FieldId → Bool
  | consumer, field => consumer.slots.any (·.referencesProducer field)

def operands : CheckedRepeatableNumberAggregateConsumer model →
    List (CheckedNumberEntityOperand model)
  | consumer => consumer.slots.map (·.toEntityOperand)

end CheckedRepeatableNumberAggregateConsumer

/-- Fail-closed errors for one repeatable Number-result computation followed by one root aggregate that reads it directly or through its filter. -/
inductive RepeatableNumberAggregateCascadeElabError where
  | row (cause : AddressedNumberFieldElabError)
  | binary (cause : AddressedNumberBinaryElabError)
  | abs (cause : AddressedNumberAbsElabError)
  | round (cause : AddressedNumberRoundElabError)
  | extremum (cause : AddressedNumberExtremumElabError)
  | power (cause : AddressedNumberPowerElabError)
  | division (cause : AddressedNumberDivisionElabError)
  | stringLength (cause : AddressedStringLengthElabError)
  | fieldValueAsNumber (cause : AddressedFieldValueAsNumberElabError)
  | rangeAsNumber (cause : AddressedRangeAsNumberElabError)
  | dateRangeBoundPart (cause : AddressedDateRangeBoundPartElabError)
  | firstFilled (cause : AddressedNumberFirstFilledComputationElabError)
  | aggregate (cause : NumericComputationElabError)
  | incoherentAggregate
  | dependency (expected actual : FieldId)
  | groupMismatch (row aggregate : GroupPath)
  | scopeMismatch (row aggregate : List RepeatableLevel)
  | aggregateBindingRequired (levels : List RepeatableLevel)
  | cycle (field : FieldId)
  | missingFilterDependency (field : FieldId)
  | missingMixedDependency (field : FieldId)
  deriving Repr, DecidableEq

/-- One checked repeatable Number producer followed by one nonrepeatable `Sum`, `MinValue`, `MaxValue`, or distinct-count computation over a nonempty authored list of plain and filtered stars. A plain slot reads the producer through its value; a filtered slot does so only through `Having`. This is a fixed two-stage route, not a scheduler. -/
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
    match consumer.kind with
    | .plain =>
        throw (.dependency row.targetField consumer.first.valueSource.field.id)
    | .filtered => throw (.missingFilterDependency row.targetField)
    | .mixed => throw (.missingMixedDependency row.targetField)

private structure CheckedRepeatableNumberAggregateTail
    (operands : List (CheckedNumberEntityOperand model)) where
  slots : List (CheckedRepeatableNumberAggregateOperand model)
  owned : operands = slots.map (·.toEntityOperand)

private def checkedRepeatableNumberAggregateTail? :
    (operands : List (CheckedNumberEntityOperand model)) →
      Option (CheckedRepeatableNumberAggregateTail operands)
  | [] => some { slots := [], owned := rfl }
  | .star source :: rest => do
      let tail ← checkedRepeatableNumberAggregateTail? rest
      pure {
        slots := .plain source :: tail.slots
        owned := by
          simp [CheckedRepeatableNumberAggregateOperand.toEntityOperand,
            tail.owned]
      }
  | .starHaving source :: rest => do
      let tail ← checkedRepeatableNumberAggregateTail? rest
      pure {
        slots := .filtered source :: tail.slots
        owned := by
          simp [CheckedRepeatableNumberAggregateOperand.toEntityOperand,
            tail.owned]
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
            match checkedRepeatableNumberAggregateTail? aggregate.rest with
            | some tail =>
                certifyRepeatableNumberAggregateCascade row aggregate
                  { first := .plain first, rest := tail.slots } total operation
                  (hOperation ▸ hExpression) (by
                    simp [CheckedRepeatableNumberAggregateConsumer.operands,
                      CheckedRepeatableNumberAggregateConsumer.slots,
                      CheckedRepeatableNumberAggregateOperand.toEntityOperand,
                      hFirst, tail.owned])
            | none => throw .incoherentAggregate
        | .starHaving first =>
            match checkedRepeatableNumberAggregateTail? aggregate.rest with
            | some tail =>
                certifyRepeatableNumberAggregateCascade row aggregate
                  { first := .filtered first, rest := tail.slots } total operation
                  (hOperation ▸ hExpression) (by
                    simp [CheckedRepeatableNumberAggregateConsumer.operands,
                      CheckedRepeatableNumberAggregateConsumer.slots,
                      CheckedRepeatableNumberAggregateOperand.toEntityOperand,
                      hFirst, tail.owned])
            | none => throw .incoherentAggregate
        | _ => throw .incoherentAggregate
      else throw .incoherentAggregate
  | _ => throw .incoherentAggregate

/-- Check a direct row producer followed by one root aggregate whose nonempty operand list contains only plain and filtered Number stars. -/
def checkRepeatableNumberStarListAggregateCascade
    (model : FlatModel)
    (rowDeclaringGroup : GroupPath) (rowTarget : FieldId)
    (rowSource : SurfaceFieldPath)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (aggregateSource : SurfaceNumberEntitySource)
    (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) := do
  let row ← checkAddressedNumberField model rowDeclaringGroup
      rowTarget rowSource |>.mapError .row
  finishRepeatableNumberAggregateCascade model (.direct row)
    aggregateDeclaringGroup aggregateTarget aggregateSource operation

/-- Binary-producer counterpart of the checked star-list aggregate route. -/
def checkRepeatableNumberBinaryStarListAggregateCascade
    (model : FlatModel)
    (rowDeclaringGroup : GroupPath) (rowTarget : FieldId)
    (leftSource rightSource : SurfaceFieldPath)
    (rowOperation : NumericArithmeticOp)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (aggregateSource : SurfaceNumberEntitySource)
    (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) := do
  let row ← checkAddressedNumberBinary model rowDeclaringGroup rowTarget
      leftSource rightSource rowOperation |>.mapError .binary
  finishRepeatableNumberAggregateCascade model (.binary row)
    aggregateDeclaringGroup aggregateTarget aggregateSource operation

/-- Absolute-value-producer counterpart of the checked star-list aggregate route. -/
def checkRepeatableNumberAbsStarListAggregateCascade
    (model : FlatModel)
    (rowDeclaringGroup : GroupPath) (rowTarget : FieldId)
    (rowSource : SurfaceFieldPath)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (aggregateSource : SurfaceNumberEntitySource)
    (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) := do
  let row ← checkAddressedNumberAbs model rowDeclaringGroup
      rowTarget rowSource |>.mapError .abs
  finishRepeatableNumberAggregateCascade model (.abs row)
    aggregateDeclaringGroup aggregateTarget aggregateSource operation

/-- Rounding-producer counterpart of the checked star-list aggregate route. -/
def checkRepeatableNumberRoundStarListAggregateCascade
    (model : FlatModel)
    (rowDeclaringGroup : GroupPath) (rowTarget : FieldId)
    (rowSource : SurfaceFieldPath) (mode : DecimalRoundingMode)
    (places : RoundingPlaces)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (aggregateSource : SurfaceNumberEntitySource)
    (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) := do
  let row ← checkAddressedNumberRound model rowDeclaringGroup
      rowTarget rowSource mode places |>.mapError .round
  finishRepeatableNumberAggregateCascade model (.round row)
    aggregateDeclaringGroup aggregateTarget aggregateSource operation

/-- Operand-list-extremum-producer counterpart of the checked star-list aggregate route. -/
def checkRepeatableNumberExtremumStarListAggregateCascade
    (model : FlatModel)
    (rowDeclaringGroup : GroupPath) (rowTarget : FieldId)
    (firstOperand : SurfaceAddressedNumberExtremumOperand)
    (restOperands : List SurfaceAddressedNumberExtremumOperand)
    (rowOperation : NumericExtremumOp)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (aggregateSource : SurfaceNumberEntitySource)
    (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) := do
  let row ← checkAddressedNumberExtremumOperands model rowDeclaringGroup
      rowTarget firstOperand restOperands rowOperation |>.mapError .extremum
  finishRepeatableNumberAggregateCascade model (.extremum row)
    aggregateDeclaringGroup aggregateTarget aggregateSource operation

/-- Field-exponent-power-producer counterpart of the checked star-list aggregate route. -/
def checkRepeatableNumberPowerStarListAggregateCascade
    (model : FlatModel)
    (rowDeclaringGroup : GroupPath) (rowTarget : FieldId)
    (baseSource exponentSource : SurfaceFieldPath)
    (suppressExactScaleWarning : Bool)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (aggregateSource : SurfaceNumberEntitySource)
    (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) := do
  let row ← checkAddressedNumberPower model rowDeclaringGroup rowTarget
      baseSource exponentSource suppressExactScaleWarning |>.mapError .power
  finishRepeatableNumberAggregateCascade model (.power row)
    aggregateDeclaringGroup aggregateTarget aggregateSource operation

/-- Warning-suppressed-division-producer counterpart of the checked star-list aggregate route. -/
def checkRepeatableNumberDivisionStarListAggregateCascade
    (model : FlatModel)
    (rowDeclaringGroup : GroupPath) (rowTarget : FieldId)
    (leftSource rightSource : SurfaceFieldPath)
    (suppressExactScaleWarning : Bool)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (aggregateSource : SurfaceNumberEntitySource)
    (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) := do
  let row ← checkAddressedNumberDivision model rowDeclaringGroup rowTarget
      leftSource rightSource suppressExactScaleWarning |>.mapError .division
  finishRepeatableNumberAggregateCascade model (.division row)
    aggregateDeclaringGroup aggregateTarget aggregateSource operation

/-- String-length-producer counterpart of the checked star-list aggregate route. -/
def checkRepeatableStringLengthStarListAggregateCascade
    (model : FlatModel)
    (rowDeclaringGroup : GroupPath) (rowTarget : FieldId)
    (rowSource : SurfaceFieldPath)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (aggregateSource : SurfaceNumberEntitySource)
    (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) := do
  let row ← checkAddressedStringLength model rowDeclaringGroup
      rowTarget rowSource |>.mapError .stringLength
  finishRepeatableNumberAggregateCascade model (.stringLength row)
    aggregateDeclaringGroup aggregateTarget aggregateSource operation

/-- Field-value-as-Number-producer counterpart of the checked star-list aggregate route. -/
def checkRepeatableFieldValueAsNumberStarListAggregateCascade
    (model : FlatModel)
    (rowDeclaringGroup : GroupPath) (rowTarget : FieldId)
    (rowSource : SurfaceTextFieldOperand)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (aggregateSource : SurfaceNumberEntitySource)
    (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) := do
  let row ← checkAddressedFieldValueAsNumber model rowDeclaringGroup
      rowTarget rowSource |>.mapError .fieldValueAsNumber
  finishRepeatableNumberAggregateCascade model (.fieldValueAsNumber row)
    aggregateDeclaringGroup aggregateTarget aggregateSource operation

/-- Range-as-Number-producer counterpart of the checked star-list aggregate route. -/
def checkRepeatableRangeAsNumberStarListAggregateCascade
    (model : FlatModel)
    (rowDeclaringGroup : GroupPath) (rowTarget : FieldId)
    (rowSource : SurfaceFieldPath) (start finish : Nat)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (aggregateSource : SurfaceNumberEntitySource)
    (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) := do
  let row ← checkAddressedRangeAsNumber model rowDeclaringGroup
      rowTarget rowSource start finish |>.mapError .rangeAsNumber
  finishRepeatableNumberAggregateCascade model (.rangeAsNumber row)
    aggregateDeclaringGroup aggregateTarget aggregateSource operation

/-- DateRange-endpoint-component-producer counterpart of the checked star-list aggregate route. -/
def checkRepeatableDateRangeBoundPartStarListAggregateCascade
    (model : FlatModel)
    (rowDeclaringGroup : GroupPath) (rowTarget : FieldId)
    (rowSource : SurfaceFieldPath) (bound : DateRangeBound)
    (part : DateNumericPart)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (aggregateSource : SurfaceNumberEntitySource)
    (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) := do
  let row ← checkAddressedDateRangeBoundPart model rowDeclaringGroup
      rowTarget rowSource bound part |>.mapError .dateRangeBoundPart
  finishRepeatableNumberAggregateCascade model (.dateRangeBoundPart row)
    aggregateDeclaringGroup aggregateTarget aggregateSource operation

/-- Authored-list sibling-star Number `FirstFilledValue` producer followed by one sole plain-star root aggregate. -/
def checkRepeatableNumberFirstFilledListAggregateCascade
    (model : FlatModel)
    (rowDeclaringGroup : GroupPath) (rowTarget : FieldId)
    (rowFirstSource : SurfaceStarFieldPath)
    (rowRestSources : List SurfaceStarFieldPath)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (aggregateSource : SurfaceStarFieldPath)
    (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) := do
  let row ← checkAddressedNumberFirstFilledComputation model
      rowDeclaringGroup rowTarget rowFirstSource rowRestSources
    |>.mapError .firstFilled
  finishRepeatableNumberAggregateCascade model (.firstFilled row)
    aggregateDeclaringGroup aggregateTarget {
      first := .star aggregateSource
      rest := []
    } operation

/-- One-source compatibility wrapper for the established first-filled aggregate cascade. -/
def checkRepeatableNumberFirstFilledAggregateCascade
    (model : FlatModel)
    (rowDeclaringGroup : GroupPath) (rowTarget : FieldId)
    (rowSource : SurfaceStarFieldPath)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (aggregateSource : SurfaceStarFieldPath)
    (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) :=
  checkRepeatableNumberFirstFilledListAggregateCascade model
    rowDeclaringGroup rowTarget rowSource [] aggregateDeclaringGroup
    aggregateTarget aggregateSource operation

/-- Check the exact direct-assignment producer followed by a sole plain-star aggregate. -/
def checkRepeatableNumberAggregateCascade
    (model : FlatModel)
    (rowDeclaringGroup : GroupPath) (rowTarget : FieldId)
    (rowSource : SurfaceFieldPath)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (aggregateSource : SurfaceStarFieldPath) (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) :=
  checkRepeatableNumberStarListAggregateCascade model
    rowDeclaringGroup rowTarget rowSource
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
      (CheckedRepeatableNumberAggregateCascade model) :=
  checkRepeatableNumberStarListAggregateCascade model
    rowDeclaringGroup rowTarget rowSource
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
      (CheckedRepeatableNumberAggregateCascade model) :=
  checkRepeatableNumberBinaryStarListAggregateCascade model
    rowDeclaringGroup rowTarget leftSource rightSource rowOperation
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
      (CheckedRepeatableNumberAggregateCascade model) :=
  checkRepeatableNumberBinaryStarListAggregateCascade model
    rowDeclaringGroup rowTarget leftSource rightSource rowOperation
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
      (CheckedRepeatableNumberAggregateCascade model) :=
  checkRepeatableNumberStarListAggregateCascade model
    rowDeclaringGroup rowTarget rowSource
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
      (CheckedRepeatableNumberAggregateCascade model) :=
  checkRepeatableNumberBinaryStarListAggregateCascade model
    rowDeclaringGroup rowTarget leftSource rightSource rowOperation
    aggregateDeclaringGroup aggregateTarget {
      first := .star aggregateFirst
      rest := .star aggregateSecond :: aggregateRest.map .star
    } operation

private def mixedAggregateSource (plain filtered : SurfaceStarFieldPath)
    (having : SurfaceCorrelatedHaving)
    (order : RepeatableNumberAggregateMixedOperandOrder) :
    SurfaceNumberEntitySource :=
  match order with
  | .plainThenFiltered => {
      first := .star plain
      rest := [.starHaving filtered having]
    }
  | .filteredThenPlain => {
      first := .starHaving filtered having
      rest := [.star plain]
    }

/-- Check a direct producer followed by one plain star and one filtered star in either authored order. -/
def checkRepeatableNumberMixedAggregateCascade
    (model : FlatModel)
    (rowDeclaringGroup : GroupPath) (rowTarget : FieldId)
    (rowSource : SurfaceFieldPath)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (plainSource filteredSource : SurfaceStarFieldPath)
    (having : SurfaceCorrelatedHaving)
    (order : RepeatableNumberAggregateMixedOperandOrder)
    (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) :=
  checkRepeatableNumberStarListAggregateCascade model
    rowDeclaringGroup rowTarget rowSource
    aggregateDeclaringGroup aggregateTarget
    (mixedAggregateSource plainSource filteredSource having order) operation

/-- Binary-producer counterpart of the exact mixed aggregate route. -/
def checkRepeatableNumberBinaryMixedAggregateCascade
    (model : FlatModel)
    (rowDeclaringGroup : GroupPath) (rowTarget : FieldId)
    (leftSource rightSource : SurfaceFieldPath)
    (rowOperation : NumericArithmeticOp)
    (aggregateDeclaringGroup : GroupPath) (aggregateTarget : FieldId)
    (plainSource filteredSource : SurfaceStarFieldPath)
    (having : SurfaceCorrelatedHaving)
    (order : RepeatableNumberAggregateMixedOperandOrder)
    (operation : NumericAggregateOp) :
    Except RepeatableNumberAggregateCascadeElabError
      (CheckedRepeatableNumberAggregateCascade model) :=
  checkRepeatableNumberBinaryStarListAggregateCascade model
    rowDeclaringGroup rowTarget leftSource rightSource rowOperation
    aggregateDeclaringGroup aggregateTarget
    (mixedAggregateSource plainSource filteredSource having order) operation

/-- The exact two dependency stages and complete repeatable row scope exposed to Analyze. -/
structure RepeatableNumberAggregateCascadeAnalysis where
  producer : RepeatableNumberAggregateProducerKind
  consumer : RepeatableNumberAggregateConsumerKind
  operation : NumericAggregateOp
  repeatableScope : List RepeatableLevel
  fieldDependencies : List (FieldId × List FieldId)
  deriving Repr, DecidableEq

end A12Kernel
