import A12Kernel.Elaboration.AddressedNumberField
import A12Kernel.Elaboration.NumericExpression

/-! # Same-scope repeatable bounded Number extrema

This capsule retains a nonempty ordered list containing one or more checked Number sources, permits operand-local absolute-value or rounding tags on those sources, and admits at most one immediate decoded literal. It delegates each local transformation and the authored-order fold to the existing scalar semantics, then reuses the shared exact-address target owner.
-/

namespace A12Kernel

/-- The bounded addressed surface admits direct Number fields, operand-local `Abs` or Round over those fields, and one immediate decoded literal. Wider numeric operations remain with the scalar expression owner. -/
inductive SurfaceAddressedNumberExtremumOperand where
  | field (reference : SurfaceFieldPath)
  | abs (reference : SurfaceFieldPath)
  | round (reference : SurfaceFieldPath) (mode : DecimalRoundingMode)
      (places : RoundingPlaces)
  | literal (decoded : DecodedNumericLiteral)
  deriving Repr, DecidableEq

/-- The bounded direct and unary-wrapper operations that can currently own a checked addressed Number source inside an extremum operand list. -/
inductive AddressedNumberExtremumFieldOperation where
  | direct
  | abs
  | round (mode : DecimalRoundingMode) (places : RoundingPlaces)
  deriving Repr, DecidableEq

/-- One certified Number source together with its operand-local transformation. This is deliberately not a target-owning addressed computation. -/
structure CheckedAddressedNumberExtremumFieldOperand (model : FlatModel) where
  operation : AddressedNumberExtremumFieldOperation
  numberSource : CheckedAddressedNumberSource model

/-- One literal's exact insertion point among the retained field-backed sources. With at most one literal, this is also its authored operand-list position. -/
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
  sources : List (CheckedAddressedNumberExtremumFieldOperand model)
  literal : Option AddressedNumberExtremumLiteral
  literalWithinSources : literalPositionWithin literal sources.length

private inductive CheckedAddressedNumberExtremumSurfaceOperand
    (model : FlatModel) where
  | source (operand : CheckedAddressedNumberExtremumFieldOperand model)
  | literal (decoded : DecodedNumericLiteral)

private def checkNumberSourceOperand
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (position : Nat) (operation : AddressedNumberExtremumFieldOperation)
    (reference : SurfaceFieldPath) :
    Except AddressedNumberExtremumElabError
      (CheckedAddressedNumberExtremumSurfaceOperand model) := do
  let numberSource ←
    checkAddressedNumberSource model declaringGroup targetField reference
      |>.mapError (.source position)
  pure (.source { operation, numberSource })

private def checkNumberOperand
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (position : Nat) : SurfaceAddressedNumberExtremumOperand →
      Except AddressedNumberExtremumElabError
        (CheckedAddressedNumberExtremumSurfaceOperand model)
  | .field reference =>
      checkNumberSourceOperand model declaringGroup targetField position
        .direct reference
  | .abs reference =>
      checkNumberSourceOperand model declaringGroup targetField position
        .abs reference
  | .round reference mode places =>
      checkNumberSourceOperand model declaringGroup targetField position
        (.round mode places) reference
  | .literal decoded => pure (.literal decoded)

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
  | operandPosition, operand :: rest => do
      let checked ← checkNumberOperand model declaringGroup targetField
        operandPosition operand
      let tail ← checkNumberOperands model declaringGroup targetField
        (operandPosition + 1) rest
      match checked with
      | .source source =>
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
      | .literal decoded =>
          match tail.literal with
          | some _ => throw .tooManyLiterals
          | none => pure {
              sources := tail.sources
              literal := some { position := 0, decoded }
              literalWithinSources := Nat.zero_le _
            }

/-- The static result scale contributed by one field-backed operand after its local wrapper. -/
def CheckedAddressedNumberExtremumFieldOperand.resultScale
    (source : CheckedAddressedNumberExtremumFieldOperand model) : Nat :=
  match source.operation with
  | .direct | .abs => source.numberSource.source.info.scale
  | .round _ places => places.val

def addressedNumberExtremumResultScale
    (first : CheckedAddressedNumberExtremumFieldOperand model)
    (rest : List (CheckedAddressedNumberExtremumFieldOperand model)) : Nat :=
  rest.foldl (fun scale source => max scale source.resultScale)
    first.resultScale

/-- Include the one retained literal's syntax-derived signed scale. A field-backed source is always present with nonnegative scale, so negative literal scales cannot raise the resulting natural target scale. -/
def addressedNumberExtremumOperandResultScale
    (first : CheckedAddressedNumberExtremumFieldOperand model)
    (rest : List (CheckedAddressedNumberExtremumFieldOperand model))
    (literal : Option AddressedNumberExtremumLiteral) : Nat :=
  let fieldScale := addressedNumberExtremumResultScale first rest
  match literal with
  | none => fieldScale
  | some positioned => max fieldScale positioned.decoded.authoredScale.toNat

structure CheckedAddressedNumberExtremum (model : FlatModel) where
  private mk ::
  first : CheckedAddressedNumberExtremumFieldOperand model
  rest : List (CheckedAddressedNumberExtremumFieldOperand model)
  literal : Option AddressedNumberExtremumLiteral
  literalWithinSources : literalPositionWithin literal (rest.length + 1)
  restSameTarget :
    ∀ source ∈ rest,
      first.numberSource.placement.targetField =
        source.numberSource.placement.targetField
  op : NumericExtremumOp
  sameScale :
    first.numberSource.placement.targetPolicy.info.scale =
      addressedNumberExtremumOperandResultScale first rest literal

/-- Validate the bounded ordered operand list, retaining at most one literal and requiring one field-backed source to own the exact addressed placement. -/
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
        first.numberSource.placement.targetField =
          source.numberSource.placement.targetField then
      let resultScale := addressedNumberExtremumOperandResultScale
        first rest scan.literal
      if hScale : first.numberSource.placement.targetPolicy.info.scale =
          resultScale then
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
        throw (.scaleMismatch first.numberSource.placement.targetPolicy.info.scale
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
  | abs (source : CheckedAddressedNumberSource model)
  | round (source : CheckedAddressedNumberSource model)
      (mode : DecimalRoundingMode) (places : RoundingPlaces)
  | literal (decoded : DecodedNumericLiteral)

namespace CheckedAddressedNumberExtremum

/-- Recover the exact checked runtime operand represented by one field-backed source tag. -/
private def asOperand
    (source : CheckedAddressedNumberExtremumFieldOperand model) :
    CheckedAddressedNumberExtremumOperand model :=
  match source.operation with
  | .direct => .field source.numberSource
  | .abs => .abs source.numberSource
  | .round mode places => .round source.numberSource mode places

private def insertLiteral :
    Nat → DecodedNumericLiteral →
      List (CheckedAddressedNumberExtremumFieldOperand model) →
        List (CheckedAddressedNumberExtremumOperand model)
  | _, decoded, [] => [.literal decoded]
  | 0, decoded, sources =>
      .literal decoded :: sources.map asOperand
  | position + 1, decoded, source :: rest =>
      asOperand source :: insertLiteral position decoded rest

private def firstAndRestOperands
    (operation : CheckedAddressedNumberExtremum model) :
    CheckedAddressedNumberExtremumOperand model ×
      List (CheckedAddressedNumberExtremumOperand model) :=
  match operation.literal with
  | some { position := 0, decoded } =>
      (.literal decoded,
        asOperand operation.first :: operation.rest.map asOperand)
  | some { position := position + 1, decoded } =>
      (asOperand operation.first,
        insertLiteral position decoded operation.rest)
  | none =>
      (asOperand operation.first, operation.rest.map asOperand)

/-- Reconstruct the exact bounded authored operand order from the field-backed list and optional literal insertion point. -/
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
  | .abs source =>
      return (← source.evaluateAtPath input path).absolute
  | .round source mode places =>
      return (← source.evaluateAtPath input path).round mode places
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
  operation.first.numberSource.placement.executeWithPath input
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
