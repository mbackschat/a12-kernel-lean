import A12Kernel.Elaboration.AddressedNumberField
import A12Kernel.Elaboration.AddressedNumberBinary
import A12Kernel.Elaboration.AddressedNumberAbs
import A12Kernel.Elaboration.AddressedNumberRound
import A12Kernel.Elaboration.AddressedNumberExtremum
import A12Kernel.Elaboration.AddressedNumberPower
import A12Kernel.Elaboration.AddressedNumberDivision
import A12Kernel.Elaboration.AddressedStringLength
import A12Kernel.Elaboration.AddressedFieldValueAsNumber
import A12Kernel.Elaboration.AddressedRangeAsNumber

/-! # Checked repeatable Number aggregate row producers -/

namespace A12Kernel

/-- The exact row-local producer identity needed by Analyze. -/
inductive RepeatableNumberAggregateProducerKind where
  | direct
  | binary (operation : NumericArithmeticOp)
  | abs
  | round (mode : DecimalRoundingMode) (places : RoundingPlaces)
  | extremum (operation : NumericExtremumOp)
  | power
  | division
  | stringLength
  | fieldValueAsNumber (projection : EnumerationProjectionRef)
  | rangeAsNumber (start finish : Nat)
  deriving Repr, DecidableEq

/-- One completed row-local producer admitted by the fixed aggregate route. -/
inductive CheckedRepeatableNumberAggregateProducer (model : FlatModel) where
  | direct (operation : CheckedAddressedNumberField model)
  | binary (operation : CheckedAddressedNumberBinary model)
  | abs (operation : CheckedAddressedNumberAbs model)
  | round (operation : CheckedAddressedNumberRound model)
  | extremum (operation : CheckedAddressedNumberExtremum model)
  | power (operation : CheckedAddressedNumberPower model)
  | division (operation : CheckedAddressedNumberDivision model)
  | stringLength (operation : CheckedAddressedStringLength model)
  | fieldValueAsNumber (operation : CheckedAddressedFieldValueAsNumber model)
  | rangeAsNumber (operation : CheckedAddressedRangeAsNumber model)

namespace CheckedRepeatableNumberAggregateProducer

def kind : CheckedRepeatableNumberAggregateProducer model →
    RepeatableNumberAggregateProducerKind
  | .direct _ => .direct
  | .binary operation => .binary operation.op
  | .abs _ => .abs
  | .round operation => .round operation.mode operation.places
  | .extremum operation => .extremum operation.op
  | .power _ => .power
  | .division _ => .division
  | .stringLength _ => .stringLength
  | .fieldValueAsNumber operation =>
      .fieldValueAsNumber operation.projectionRef
  | .rangeAsNumber operation =>
      .rangeAsNumber operation.start operation.finish

def targetField : CheckedRepeatableNumberAggregateProducer model → FieldId
  | .direct operation => operation.placement.targetField
  | .binary operation => operation.pair.left.placement.targetField
  | .abs operation => operation.numberSource.placement.targetField
  | .round operation => operation.numberSource.placement.targetField
  | .extremum operation => operation.target.targetField
  | .power operation => operation.pair.left.placement.targetField
  | .division operation => operation.pair.left.placement.targetField
  | .stringLength operation => operation.placement.targetField
  | .fieldValueAsNumber operation => operation.placement.targetField
  | .rangeAsNumber operation => operation.placement.targetField

def targetDeclaration : CheckedRepeatableNumberAggregateProducer model →
    FlatFieldDecl
  | .direct operation => operation.placement.targetDeclaration
  | .binary operation => operation.pair.left.placement.targetDeclaration
  | .abs operation => operation.numberSource.placement.targetDeclaration
  | .round operation => operation.numberSource.placement.targetDeclaration
  | .extremum operation => operation.target.targetDeclaration
  | .power operation => operation.pair.left.placement.targetDeclaration
  | .division operation => operation.pair.left.placement.targetDeclaration
  | .stringLength operation => operation.placement.targetDeclaration
  | .fieldValueAsNumber operation => operation.placement.targetDeclaration
  | .rangeAsNumber operation => operation.placement.targetDeclaration

def declaringGroup : CheckedRepeatableNumberAggregateProducer model → GroupPath
  | .direct operation => operation.placement.declaringGroup
  | .binary operation => operation.pair.left.placement.declaringGroup
  | .abs operation => operation.numberSource.placement.declaringGroup
  | .round operation => operation.numberSource.placement.declaringGroup
  | .extremum operation => operation.target.declaringGroup
  | .power operation => operation.pair.left.placement.declaringGroup
  | .division operation => operation.pair.left.placement.declaringGroup
  | .stringLength operation => operation.placement.declaringGroup
  | .fieldValueAsNumber operation => operation.placement.declaringGroup
  | .rangeAsNumber operation => operation.placement.declaringGroup

def sourceFields : CheckedRepeatableNumberAggregateProducer model → List FieldId
  | .direct operation => [operation.placement.sourceDeclaration.id]
  | .binary operation => [
      operation.pair.left.placement.sourceDeclaration.id,
      operation.pair.right.placement.sourceDeclaration.id]
  | .abs operation => [operation.numberSource.placement.sourceDeclaration.id]
  | .round operation => [operation.numberSource.placement.sourceDeclaration.id]
  | .extremum operation => operation.sourceFields
  | .power operation => [
      operation.pair.left.placement.sourceDeclaration.id,
      operation.pair.right.placement.sourceDeclaration.id]
  | .division operation => [
      operation.pair.left.placement.sourceDeclaration.id,
      operation.pair.right.placement.sourceDeclaration.id]
  | .stringLength operation => [operation.placement.sourceDeclaration.id]
  | .fieldValueAsNumber operation =>
      [operation.placement.sourceDeclaration.id]
  | .rangeAsNumber operation => [operation.placement.sourceDeclaration.id]

def execute (producer : CheckedRepeatableNumberAggregateProducer model)
    (input : CheckedDocument model) :
    Except AddressedNumericLeafFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  match producer with
  | .direct operation => operation.execute input
  | .binary operation => operation.execute input
  | .abs operation => operation.execute input
  | .round operation => operation.execute input
  | .extremum operation => operation.execute input
  | .power operation => operation.execute input
  | .division operation => operation.execute input
  | .stringLength operation => operation.execute input
  | .fieldValueAsNumber operation => operation.execute input
  | .rangeAsNumber operation => operation.execute input

end CheckedRepeatableNumberAggregateProducer

end A12Kernel
