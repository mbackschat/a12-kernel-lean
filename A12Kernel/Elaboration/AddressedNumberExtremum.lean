import A12Kernel.Elaboration.AddressedNumberField
import A12Kernel.Elaboration.NumericExpression

/-! # Same-scope repeatable direct-Number extrema

This capsule retains a nonempty ordered list containing one or more checked Number sources and at most one immediate decoded literal, delegates the authored-order fold to the existing scalar extrema semantics, and reuses the shared exact-address target owner.
-/

namespace A12Kernel

/-- The bounded addressed surface admits direct Number fields plus one immediate decoded literal. Wider numeric operations remain with the scalar expression owner. -/
inductive SurfaceAddressedNumberExtremumOperand where
  | field (reference : SurfaceFieldPath)
  | literal (decoded : DecodedNumericLiteral)
  deriving Repr, DecidableEq

/-- One literal's exact insertion point among the retained direct-field sources. With at most one literal, this is also its authored operand-list position. -/
structure AddressedNumberExtremumLiteral where
  position : Nat
  decoded : DecodedNumericLiteral
  deriving Repr, DecidableEq

private def literalPositionWithin
    (literal : Option AddressedNumberExtremumLiteral)
    (sourceCount : Nat) : Prop :=
  match literal with
  | none => True
  | some positioned =>
      AddressedNumberExtremumLiteral.position positioned ≤ sourceCount

inductive AddressedNumberExtremumElabError where
  | source (position : Nat) (cause : AddressedNumberSourceElabError)
  | tooManyLiterals
  | noFieldSource
  | incoherentTarget
  | scaleMismatch (target result : Nat)
  deriving Repr, DecidableEq

private structure CheckedAddressedNumberExtremumScan (model : FlatModel) where
  sources : List (CheckedAddressedNumberSource model)
  literal : Option AddressedNumberExtremumLiteral
  literalWithinSources : literalPositionWithin literal sources.length

private def checkNumberOperands
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId) :
    Nat → List SurfaceAddressedNumberExtremumOperand →
      Except AddressedNumberExtremumElabError
        (CheckedAddressedNumberExtremumScan model)
  | _, [] => pure {
      sources := []
      literal := none
      literalWithinSources := True.intro
    }
  | operandPosition, .field reference :: rest => do
      let source ←
        checkAddressedNumberSource model declaringGroup targetField reference
          |>.mapError (.source operandPosition)
      let tail ← checkNumberOperands model declaringGroup targetField
        (operandPosition + 1) rest
      let shiftedLiteral := tail.literal.map fun positioned => {
        position := positioned.position + 1
        decoded := positioned.decoded
      }
      have shiftedWithin : literalPositionWithin shiftedLiteral
          (source :: tail.sources).length := by
        cases hLiteral : tail.literal with
        | none => simp [shiftedLiteral, hLiteral, literalPositionWithin]
        | some positioned =>
          have tailWithin :
              positioned.position ≤ tail.sources.length := by
            simpa [literalPositionWithin, hLiteral] using
              tail.literalWithinSources
          simpa [shiftedLiteral, literalPositionWithin, hLiteral] using
            Nat.succ_le_succ tailWithin
      pure {
        sources := source :: tail.sources
        literal := shiftedLiteral
        literalWithinSources := shiftedWithin
      }
  | operandPosition, .literal decoded :: rest => do
      let tail ← checkNumberOperands model declaringGroup targetField
        (operandPosition + 1) rest
      match tail.literal with
      | some _ => throw .tooManyLiterals
      | none => pure {
          sources := tail.sources
          literal := some { position := 0, decoded }
          literalWithinSources := Nat.zero_le _
        }

def addressedNumberExtremumResultScale
    (first : CheckedAddressedNumberSource model)
    (rest : List (CheckedAddressedNumberSource model)) : Nat :=
  rest.foldl (fun scale source => max scale source.source.info.scale)
    first.source.info.scale

/-- Include the one retained literal's syntax-derived signed scale. A direct field is always present with nonnegative scale, so negative literal scales cannot raise the resulting natural target scale. -/
def addressedNumberExtremumOperandResultScale
    (first : CheckedAddressedNumberSource model)
    (rest : List (CheckedAddressedNumberSource model))
    (literal : Option AddressedNumberExtremumLiteral) : Nat :=
  let fieldScale := addressedNumberExtremumResultScale first rest
  match literal with
  | none => fieldScale
  | some positioned => max fieldScale positioned.decoded.authoredScale.toNat

structure CheckedAddressedNumberExtremum (model : FlatModel) where
  private mk ::
  first : CheckedAddressedNumberSource model
  rest : List (CheckedAddressedNumberSource model)
  literal : Option AddressedNumberExtremumLiteral
  literalWithinSources : literalPositionWithin literal (rest.length + 1)
  restSameTarget :
    ∀ source ∈ rest,
      first.placement.targetField = source.placement.targetField
  op : NumericExtremumOp
  sameScale :
    first.placement.targetPolicy.info.scale =
      addressedNumberExtremumOperandResultScale first rest literal

/-- Validate the bounded ordered operand list, retaining at most one literal and requiring one direct field to own the exact addressed placement. -/
def checkAddressedNumberExtremumOperands
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (firstOperand : SurfaceAddressedNumberExtremumOperand)
    (restOperands : List SurfaceAddressedNumberExtremumOperand)
    (op : NumericExtremumOp) :
    Except AddressedNumberExtremumElabError
      (CheckedAddressedNumberExtremum model) := do
  let scan ← checkNumberOperands model declaringGroup targetField 1
    (firstOperand :: restOperands)
  match hSources : scan.sources with
  | [] => throw .noFieldSource
  | first :: rest =>
    if hTargets : ∀ source ∈ rest,
        first.placement.targetField = source.placement.targetField then
      let resultScale := addressedNumberExtremumOperandResultScale
        first rest scan.literal
      if hScale : first.placement.targetPolicy.info.scale = resultScale then
        have literalWithin :
            literalPositionWithin scan.literal (rest.length + 1) := by
          simpa [hSources] using scan.literalWithinSources
        pure {
          first
          rest
          literal := scan.literal
          literalWithinSources := literalWithin
          restSameTarget := hTargets
          op
          sameScale := hScale
        }
      else
        throw (.scaleMismatch first.placement.targetPolicy.info.scale
          resultScale)
    else
      throw .incoherentTarget

def checkAddressedNumberExtremumList
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (firstReference : SurfaceFieldPath)
    (restReferences : List SurfaceFieldPath)
    (op : NumericExtremumOp) :
    Except AddressedNumberExtremumElabError
      (CheckedAddressedNumberExtremum model) :=
  checkAddressedNumberExtremumOperands model declaringGroup targetField
    (.field firstReference) (restReferences.map .field) op

def checkAddressedNumberExtremum
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (leftReference rightReference : SurfaceFieldPath)
    (op : NumericExtremumOp) :
    Except AddressedNumberExtremumElabError
      (CheckedAddressedNumberExtremum model) :=
  checkAddressedNumberExtremumList model declaringGroup targetField
    leftReference [rightReference] op

abbrev AddressedNumberExtremumFault := AddressedNumericLeafFault

/-- The exact bounded checked operand retained for authored-order execution and consumer identity. -/
inductive CheckedAddressedNumberExtremumOperand (model : FlatModel) where
  | field (source : CheckedAddressedNumberSource model)
  | literal (decoded : DecodedNumericLiteral)

namespace CheckedAddressedNumberExtremum

private def insertLiteral :
    Nat → DecodedNumericLiteral →
      List (CheckedAddressedNumberSource model) →
        List (CheckedAddressedNumberExtremumOperand model)
  | _, decoded, [] => [.literal decoded]
  | 0, decoded, sources => .literal decoded :: sources.map .field
  | position + 1, decoded, source :: rest =>
      .field source :: insertLiteral position decoded rest

private def firstAndRestOperands
    (operation : CheckedAddressedNumberExtremum model) :
    CheckedAddressedNumberExtremumOperand model ×
      List (CheckedAddressedNumberExtremumOperand model) :=
  match operation.literal with
  | some { position := 0, decoded } =>
      (.literal decoded,
        .field operation.first :: operation.rest.map .field)
  | some { position := position + 1, decoded } =>
      (.field operation.first,
        insertLiteral position decoded operation.rest)
  | none =>
      (.field operation.first, operation.rest.map .field)

/-- Reconstruct the exact bounded authored operand order from the direct-field list and optional literal insertion point. -/
def orderedOperands
    (operation : CheckedAddressedNumberExtremum model) :
    List (CheckedAddressedNumberExtremumOperand model) :=
  let operands := operation.firstAndRestOperands
  operands.1 :: operands.2

private def evaluateOperandAtPath
    (operand : CheckedAddressedNumberExtremumOperand model)
    (input : CheckedDocument model) (path : List Nat) :
    Except AddressedNumberExtremumFault NumericComputationResult :=
  match operand with
  | .field source => source.evaluateAtPath input path
  | .literal decoded => pure (.value decoded.value)

private def evaluateRestAtPath (op : NumericExtremumOp)
    (input : CheckedDocument model) (path : List Nat) :
    List (CheckedAddressedNumberExtremumOperand model) →
      NumericComputationResult →
      Except AddressedNumberExtremumFault NumericComputationResult
  | [], result => pure result
  | _, .poison cause => pure (.poison cause)
  | operand :: rest, result => do
      let next ← evaluateOperandAtPath operand input path
      evaluateRestAtPath op input path rest
        (op.selectComputationResult result next)

private def evaluateAtPath
    (operation : CheckedAddressedNumberExtremum model)
    (input : CheckedDocument model) (path : List Nat) :
    Except AddressedNumberExtremumFault NumericComputationResult := do
  let operands := operation.firstAndRestOperands
  let initial ← evaluateOperandAtPath operands.1 input path
  evaluateRestAtPath operation.op input path operands.2 initial

def execute (operation : CheckedAddressedNumberExtremum model)
    (input : CheckedDocument model) :
    Except AddressedNumberExtremumFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  operation.first.placement.executeWithPath input
    (operation.evaluateAtPath input)

def executeResult
    (operation : CheckedAddressedNumberExtremum model)
    (input : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except AddressedNumberExtremumFault
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) := do
  let outcomes ← operation.execute input
  pure (NumericComputationRunView.fromSourceOutcomesWithMessages
    ComputationErrorPointer.ofCellAddr payloadAt supplied outcomes)

end CheckedAddressedNumberExtremum

end A12Kernel
