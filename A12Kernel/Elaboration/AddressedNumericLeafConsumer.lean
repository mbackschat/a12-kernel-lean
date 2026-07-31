import A12Kernel.Elaboration.AddressedFieldValueAsNumber
import A12Kernel.Elaboration.AddressedRangeAsNumber
import A12Kernel.Elaboration.AddressedNumberAbs
import A12Kernel.Elaboration.AddressedNumberRound

/-! # Bounded addressed numeric-leaf Analyze/Transform view

This internal consumer view covers the completed same-scope repeatable textual conversions and direct-Number field, `Abs`, and Round operations. It projects their exact bounded read/write footprint and transformation-sensitive fingerprint from checked operations, compares fingerprints without claiming equivalence, and exposes only exact identity as a Transform. It adds no evaluator, recursive rewrite system, solver, protocol, command, or shipment.
-/

namespace A12Kernel

/-- The checked addressed numeric operations covered by the bounded consumer probe. -/
inductive CheckedAddressedNumericLeaf (model : FlatModel) where
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

/-- The exact operation identity and parameters whose change can alter this family's observations. -/
inductive AddressedNumericLeafParameters where
  | fieldValueAsNumber
      (projection : EnumerationProjectionRef) (scale : Nat)
  | rangeAsNumber (start finish : Nat)
  | numberField (resultScale : Nat)
  | abs (resultScale : Nat)
  | round (mode : DecimalRoundingMode) (resultScale : Nat)
  deriving Repr, DecidableEq

/-- The complete bounded Analyze fingerprint for one checked leaf in a fixed validated model. -/
structure AddressedNumericLeafAnalysis where
  targetField : FieldId
  sourceField : FieldId
  scope : List RepeatableLevel
  targetPolicy : NumericTargetPolicy
  parameters : AddressedNumericLeafParameters
  deriving Repr, DecidableEq

namespace CheckedAddressedNumericLeaf

/-- Analyze exact read/write identity, repeatable scope, target policy, and conversion parameters without reconstructing an expression. -/
def analyze :
    CheckedAddressedNumericLeaf model → AddressedNumericLeafAnalysis
  | .fieldValueAsNumber operation => {
      targetField := operation.placement.targetField
      sourceField := operation.placement.sourceDeclaration.id
      scope := operation.placement.targetDeclaration.repeatableScope
      targetPolicy := operation.placement.targetPolicy
      parameters := .fieldValueAsNumber operation.projectionRef
        operation.source.scale
    }
  | .rangeAsNumber operation => {
      targetField := operation.placement.targetField
      sourceField := operation.placement.sourceDeclaration.id
      scope := operation.placement.targetDeclaration.repeatableScope
      targetPolicy := operation.placement.targetPolicy
      parameters := .rangeAsNumber operation.start operation.finish
    }
  | .numberField operation => {
      targetField := operation.placement.targetField
      sourceField := operation.placement.sourceDeclaration.id
      scope := operation.placement.targetDeclaration.repeatableScope
      targetPolicy := operation.placement.targetPolicy
      parameters := .numberField operation.source.info.scale
    }
  | .abs operation => {
      targetField := operation.numberSource.placement.targetField
      sourceField := operation.numberSource.placement.sourceDeclaration.id
      scope := operation.numberSource.placement.targetDeclaration.repeatableScope
      targetPolicy := operation.numberSource.placement.targetPolicy
      parameters := .abs operation.numberSource.source.info.scale
    }
  | .round operation => {
      targetField := operation.numberSource.placement.targetField
      sourceField := operation.numberSource.placement.sourceDeclaration.id
      scope := operation.numberSource.placement.targetDeclaration.repeatableScope
      targetPolicy := operation.numberSource.placement.targetPolicy
      parameters := .round operation.mode operation.places.val
    }

/-- Whether evaluation reads the named expression operand. Result classification has its distinct target-state read below. -/
def readsOperand (leaf : CheckedAddressedNumericLeaf model)
    (field : FieldId) : Bool :=
  leaf.analyze.sourceField == field

/-- Whether source-relative result classification reads the named target's prior state. -/
def readsTargetState (leaf : CheckedAddressedNumericLeaf model)
    (field : FieldId) : Bool :=
  leaf.analyze.targetField == field

/-- Complete field-read footprint of this bounded execution: one expression operand plus prior target state for result classification. -/
def readsDuringExecution (leaf : CheckedAddressedNumericLeaf model)
    (field : FieldId) : Bool :=
  leaf.readsOperand field || leaf.readsTargetState field

/-- Whether the checked leaf writes the named field. -/
def writesTo (leaf : CheckedAddressedNumericLeaf model)
    (field : FieldId) : Bool :=
  leaf.analyze.targetField == field

/-- Compare two checked leaves' bounded fingerprints. Equality is an Analyze fact, not a semantic-equivalence certificate. -/
def matchingFingerprint? (before after : CheckedAddressedNumericLeaf model) :
    Option AddressedNumericLeafAnalysis :=
  let candidate := after.analyze
  if before.analyze = candidate then some candidate else none

/-- Execute one checked family member through its existing semantic owner. -/
def execute (leaf : CheckedAddressedNumericLeaf model)
    (input : CheckedDocument model) :
    Except AddressedNumericLeafFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  match leaf with
  | .fieldValueAsNumber operation => operation.execute input
  | .rangeAsNumber operation => operation.execute input
  | .numberField operation => operation.execute input
  | .abs operation => operation.execute input
  | .round operation => operation.execute input

/-- Project one checked family member through its existing rich result owner. -/
def executeResult (leaf : CheckedAddressedNumericLeaf model)
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

/-- The sole admitted Transform in this bounded probe: retain the exact checked leaf. -/
def identityTransform (leaf : CheckedAddressedNumericLeaf model) :
    CheckedAddressedNumericLeaf model :=
  leaf

end CheckedAddressedNumericLeaf

end A12Kernel
