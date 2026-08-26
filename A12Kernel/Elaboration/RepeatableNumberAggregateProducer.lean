import A12Kernel.Elaboration.AddressedNumberField
import A12Kernel.Elaboration.AddressedNumberBinary
import A12Kernel.Elaboration.AddressedNumberAbs
import A12Kernel.Elaboration.AddressedNumberRound
import A12Kernel.Elaboration.AddressedNumberExtremum
import A12Kernel.Elaboration.AddressedNumberPower

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
  deriving Repr, DecidableEq

/-- One completed row-local producer admitted by the fixed aggregate route. -/
inductive CheckedRepeatableNumberAggregateProducer (model : FlatModel) where
  | direct (operation : CheckedAddressedNumberField model)
  | binary (operation : CheckedAddressedNumberBinary model)
  | abs (operation : CheckedAddressedNumberAbs model)
  | round (operation : CheckedAddressedNumberRound model)
  | extremum (operation : CheckedAddressedNumberExtremum model)
  | power (operation : CheckedAddressedNumberPower model)

namespace CheckedRepeatableNumberAggregateProducer

def kind : CheckedRepeatableNumberAggregateProducer model →
    RepeatableNumberAggregateProducerKind
  | .direct _ => .direct
  | .binary operation => .binary operation.op
  | .abs _ => .abs
  | .round operation => .round operation.mode operation.places
  | .extremum operation => .extremum operation.op
  | .power _ => .power

def targetField : CheckedRepeatableNumberAggregateProducer model → FieldId
  | .direct operation => operation.placement.targetField
  | .binary operation => operation.pair.left.placement.targetField
  | .abs operation => operation.numberSource.placement.targetField
  | .round operation => operation.numberSource.placement.targetField
  | .extremum operation => operation.target.targetField
  | .power operation => operation.pair.left.placement.targetField

def targetDeclaration : CheckedRepeatableNumberAggregateProducer model →
    FlatFieldDecl
  | .direct operation => operation.placement.targetDeclaration
  | .binary operation => operation.pair.left.placement.targetDeclaration
  | .abs operation => operation.numberSource.placement.targetDeclaration
  | .round operation => operation.numberSource.placement.targetDeclaration
  | .extremum operation => operation.target.targetDeclaration
  | .power operation => operation.pair.left.placement.targetDeclaration

def declaringGroup : CheckedRepeatableNumberAggregateProducer model → GroupPath
  | .direct operation => operation.placement.declaringGroup
  | .binary operation => operation.pair.left.placement.declaringGroup
  | .abs operation => operation.numberSource.placement.declaringGroup
  | .round operation => operation.numberSource.placement.declaringGroup
  | .extremum operation => operation.target.declaringGroup
  | .power operation => operation.pair.left.placement.declaringGroup

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

end CheckedRepeatableNumberAggregateProducer

end A12Kernel
