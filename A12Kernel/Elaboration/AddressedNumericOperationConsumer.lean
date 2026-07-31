import A12Kernel.Elaboration.AddressedFieldValueAsNumber
import A12Kernel.Elaboration.AddressedRangeAsNumber
import A12Kernel.Elaboration.AddressedNumberAbs
import A12Kernel.Elaboration.AddressedNumberRound
import A12Kernel.Elaboration.AddressedNumberExtremum

/-! # Bounded addressed numeric-operation Analyze/Transform view

This internal consumer view covers the completed same-scope repeatable textual conversions and direct-Number field, `Abs`, Round, and bounded operand-list extrema over direct fields, operand-local `Abs`, and at most one immediate literal. It projects their exact bounded read/write footprint and transformation-sensitive fingerprint from checked operations, compares fingerprints without claiming equivalence, and exposes only exact identity as a Transform. It adds no evaluator, recursive rewrite system, solver, protocol, command, or shipment.
-/

namespace A12Kernel

/-- The checked addressed numeric operations covered by the bounded consumer probe. -/
inductive CheckedAddressedNumericOperation (model : FlatModel) where
  | fieldValueAsNumber
      (operation : CheckedAddressedFieldValueAsNumber model)
  | rangeAsNumber
      (operation : CheckedAddressedRangeAsNumber model)
  | numberField
      (operation : CheckedAddressedNumberField model)
  | abs
      (operation : CheckedAddressedNumberAbs model)
  | round
      (operation : CheckedAddressedNumberRound model)
  | extremum
      (operation : CheckedAddressedNumberExtremum model)

/-- One bounded operand identity retained for consumer-visible extrema order. -/
inductive AddressedNumberExtremumOperandIdentity where
  | field (field : FieldId)
  | abs (field : FieldId)
  | literal (decoded : DecodedNumericLiteral)
  deriving Repr, DecidableEq

/-- The exact operation identity and parameters whose change can alter this family's observations. -/
inductive AddressedNumericOperationParameters where
  | fieldValueAsNumber
      (projection : EnumerationProjectionRef) (scale : Nat)
  | rangeAsNumber (start finish : Nat)
  | numberField (resultScale : Nat)
  | abs (resultScale : Nat)
  | round (mode : DecimalRoundingMode) (resultScale : Nat)
  | extremum (op : NumericExtremumOp) (resultScale : Nat)
      (operands : List AddressedNumberExtremumOperandIdentity)
  deriving Repr, DecidableEq

/-- The complete bounded Analyze fingerprint for one checked operation in a fixed validated model. -/
structure AddressedNumericOperationAnalysis where
  targetField : FieldId
  sourceFields : List FieldId
  scope : List RepeatableLevel
  targetPolicy : NumericTargetPolicy
  parameters : AddressedNumericOperationParameters
  deriving Repr, DecidableEq

namespace CheckedAddressedNumericOperation

private def extremumOperandIdentity :
    CheckedAddressedNumberExtremumOperand model →
      AddressedNumberExtremumOperandIdentity
  | .field source => .field source.placement.sourceDeclaration.id
  | .abs source => .abs source.placement.sourceDeclaration.id
  | .literal decoded => .literal decoded

/-- Analyze exact read/write identity, repeatable scope, target policy, and conversion parameters without reconstructing an expression. -/
def analyze :
    CheckedAddressedNumericOperation model → AddressedNumericOperationAnalysis
  | .fieldValueAsNumber operation => {
      targetField := operation.placement.targetField
      sourceFields := [operation.placement.sourceDeclaration.id]
      scope := operation.placement.targetDeclaration.repeatableScope
      targetPolicy := operation.placement.targetPolicy
      parameters := .fieldValueAsNumber operation.projectionRef
        operation.source.scale
    }
  | .rangeAsNumber operation => {
      targetField := operation.placement.targetField
      sourceFields := [operation.placement.sourceDeclaration.id]
      scope := operation.placement.targetDeclaration.repeatableScope
      targetPolicy := operation.placement.targetPolicy
      parameters := .rangeAsNumber operation.start operation.finish
    }
  | .numberField operation => {
      targetField := operation.placement.targetField
      sourceFields := [operation.placement.sourceDeclaration.id]
      scope := operation.placement.targetDeclaration.repeatableScope
      targetPolicy := operation.placement.targetPolicy
      parameters := .numberField operation.source.info.scale
    }
  | .abs operation => {
      targetField := operation.numberSource.placement.targetField
      sourceFields := [operation.numberSource.placement.sourceDeclaration.id]
      scope := operation.numberSource.placement.targetDeclaration.repeatableScope
      targetPolicy := operation.numberSource.placement.targetPolicy
      parameters := .abs operation.numberSource.source.info.scale
    }
  | .round operation => {
      targetField := operation.numberSource.placement.targetField
      sourceFields := [operation.numberSource.placement.sourceDeclaration.id]
      scope := operation.numberSource.placement.targetDeclaration.repeatableScope
      targetPolicy := operation.numberSource.placement.targetPolicy
      parameters := .round operation.mode operation.places.val
    }
  | .extremum operation => {
      targetField := operation.first.numberSource.placement.targetField
      sourceFields :=
        operation.first.numberSource.placement.sourceDeclaration.id ::
        operation.rest.map (fun source =>
          source.numberSource.placement.sourceDeclaration.id)
      scope :=
        operation.first.numberSource.placement.targetDeclaration.repeatableScope
      targetPolicy := operation.first.numberSource.placement.targetPolicy
      parameters := .extremum operation.op
        (addressedNumberExtremumOperandResultScale operation.first
          operation.rest operation.literal)
        (operation.orderedOperands.map extremumOperandIdentity)
    }

/-- Whether evaluation reads the named expression operand. Result classification has its distinct target-state read below. -/
def readsOperand (leaf : CheckedAddressedNumericOperation model)
    (field : FieldId) : Bool :=
  leaf.analyze.sourceFields.contains field

/-- Whether source-relative result classification reads the named target's prior state. -/
def readsTargetState (leaf : CheckedAddressedNumericOperation model)
    (field : FieldId) : Bool :=
  leaf.analyze.targetField == field

/-- Complete field-read footprint of this bounded execution: every expression operand plus prior target state for result classification. -/
def readsDuringExecution (leaf : CheckedAddressedNumericOperation model)
    (field : FieldId) : Bool :=
  leaf.readsOperand field || leaf.readsTargetState field

/-- Whether the checked operation writes the named field. -/
def writesTo (leaf : CheckedAddressedNumericOperation model)
    (field : FieldId) : Bool :=
  leaf.analyze.targetField == field

/-- Compare two checked operations' bounded fingerprints. Equality is an Analyze fact, not a semantic-equivalence certificate. -/
def matchingFingerprint? (before after : CheckedAddressedNumericOperation model) :
    Option AddressedNumericOperationAnalysis :=
  let candidate := after.analyze
  if before.analyze = candidate then some candidate else none

/-- Execute one checked family member through its existing semantic owner. -/
def execute (leaf : CheckedAddressedNumericOperation model)
    (input : CheckedDocument model) :
    Except AddressedNumericLeafFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  match leaf with
  | .fieldValueAsNumber operation => operation.execute input
  | .rangeAsNumber operation => operation.execute input
  | .numberField operation => operation.execute input
  | .abs operation => operation.execute input
  | .round operation => operation.execute input
  | .extremum operation => operation.execute input

/-- Project one checked family member through its existing rich result owner. -/
def executeResult (leaf : CheckedAddressedNumericOperation model)
    (input : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except AddressedNumericLeafFault
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) :=
  match leaf with
  | .fieldValueAsNumber operation =>
      operation.executeResult input payloadAt supplied
  | .rangeAsNumber operation =>
      operation.executeResult input payloadAt supplied
  | .numberField operation =>
      operation.executeResult input payloadAt supplied
  | .abs operation =>
      operation.executeResult input payloadAt supplied
  | .round operation =>
      operation.executeResult input payloadAt supplied
  | .extremum operation =>
      operation.executeResult input payloadAt supplied

/-- The sole admitted Transform in this bounded probe: retain the exact checked operation. -/
def identityTransform (leaf : CheckedAddressedNumericOperation model) :
    CheckedAddressedNumericOperation model :=
  leaf

end CheckedAddressedNumericOperation

end A12Kernel
