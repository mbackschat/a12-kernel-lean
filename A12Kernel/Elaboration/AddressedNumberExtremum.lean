import A12Kernel.Elaboration.AddressedNumberField
import A12Kernel.Elaboration.NumericExpression

/-! # Same-scope repeatable bounded Number extrema

This capsule retains a nonempty ordered list containing one or more checked Number sources, permits operand-local absolute-value, rounding, or one arithmetic node over two field-or-literal operands, and admits at most one immediate decoded literal in the outer list. It delegates each local transformation and the authored-order fold to the existing scalar semantics, then reuses the shared exact-address target owner.
-/

namespace A12Kernel

/-- One inner operand of an operand-local arithmetic child: a direct Number field or an immediate decoded literal. -/
inductive SurfaceAddressedNumberArithmeticOperand where
  | field (reference : SurfaceFieldPath)
  | literal (decoded : DecodedNumericLiteral)
  deriving Repr, DecidableEq

/-- The bounded addressed surface admits direct Number fields, operand-local `Abs`, Round, or one arithmetic node over two field-or-literal operands, and one immediate decoded literal in the outer list. Wider numeric operations remain with the scalar expression owner. -/
inductive SurfaceAddressedNumberExtremumOperand where
  | field (reference : SurfaceFieldPath)
  | abs (reference : SurfaceFieldPath)
  | round (reference : SurfaceFieldPath) (mode : DecimalRoundingMode)
      (places : RoundingPlaces)
  | arithmetic (operation : NumericArithmeticOp)
      (left right : SurfaceAddressedNumberArithmeticOperand)
  | literal (decoded : DecodedNumericLiteral)
  deriving Repr, DecidableEq

/-- One retained arithmetic child of an extremum operand. Every admitted form keeps at least one certified Number source, whose placement owns the outer operand's target iteration; a constant-only child is authorable in the kernel but outside this fragment. -/
inductive CheckedAddressedNumberArithmeticChild (model : FlatModel) where
  | fields (pair : CheckedAddressedNumberPair model)
  | fieldLiteral (source : CheckedAddressedNumberSource model)
      (decoded : DecodedNumericLiteral)
  | literalField (decoded : DecodedNumericLiteral)
      (source : CheckedAddressedNumberSource model)

namespace CheckedAddressedNumberArithmeticChild

/-- The source whose already-certified placement owns the outer operand's target iteration. -/
def primarySource : CheckedAddressedNumberArithmeticChild model →
    CheckedAddressedNumberSource model
  | .fields pair => pair.left
  | .fieldLiteral source _ => source
  | .literalField _ source => source

/-- Every ordered field dependency this child actually reads. A retained literal contributes none, so a literal in place of a field also removes that field's failure from the row. -/
def sources : CheckedAddressedNumberArithmeticChild model →
    List (CheckedAddressedNumberSource model)
  | .fields pair => [pair.left, pair.right]
  | .fieldLiteral source _ => [source]
  | .literalField _ source => [source]

/-- The two operand scales in authored order, fed to the operation's own derived-scale rule. A literal contributes its authored scale, so the same value written `1.5` or `1.50` changes the derived scale. -/
def operandScales : CheckedAddressedNumberArithmeticChild model → Nat × Nat
  | .fields pair =>
      (pair.left.source.info.scale, pair.right.source.info.scale)
  | .fieldLiteral source decoded =>
      (source.source.info.scale, decoded.authoredScale.toNat)
  | .literalField decoded source =>
      (decoded.authoredScale.toNat, source.source.info.scale)

end CheckedAddressedNumberArithmeticChild

/-- The bounded direct and unary-wrapper operations that can currently own a checked addressed Number source inside an extremum operand list. -/
inductive AddressedNumberExtremumFieldOperation where
  | direct
  | abs
  | round (mode : DecimalRoundingMode) (places : RoundingPlaces)
  deriving Repr, DecidableEq

/-- One field-backed extremum operand. Unary forms retain one checked source; arithmetic forms retain their child and its operation without embedding a target-owning binary computation. -/
inductive CheckedAddressedNumberExtremumFieldOperand (model : FlatModel) where
  | unary (operation : AddressedNumberExtremumFieldOperation)
      (numberSource : CheckedAddressedNumberSource model)
  | arithmetic (operation : NumericArithmeticOp)
      (child : CheckedAddressedNumberArithmeticChild model)

namespace CheckedAddressedNumberExtremumFieldOperand

/-- The source whose already-certified placement owns the outer operation's target iteration. -/
def primarySource : CheckedAddressedNumberExtremumFieldOperand model →
    CheckedAddressedNumberSource model
  | .unary _ source => source
  | .arithmetic _ child => child.primarySource

/-- Every ordered field dependency contributed by this one outer operand. -/
def sources : CheckedAddressedNumberExtremumFieldOperand model →
    List (CheckedAddressedNumberSource model)
  | .unary _ source => [source]
  | .arithmetic _ child => child.sources

def targetField (operand : CheckedAddressedNumberExtremumFieldOperand model) :
    FieldId :=
  operand.primarySource.placement.targetField

def sourceFields (operand : CheckedAddressedNumberExtremumFieldOperand model) :
    List FieldId :=
  operand.sources.map fun source => source.placement.sourceDeclaration.id

end CheckedAddressedNumberExtremumFieldOperand

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
  | pair (position : Nat) (cause : AddressedNumberPairElabError)
  | constantOnlyArithmetic (position : Nat)
  | negativeLiteralScale (position : Nat) (authored : Int)
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
  pure (.source (.unary operation numberSource))

/-- A child literal must carry a nonnegative authored scale: a negative one would lower a product's derived scale, and no current observation covers that shape. -/
private def checkArithmeticLiteral (position : Nat)
    (decoded : DecodedNumericLiteral) :
    Except AddressedNumberExtremumElabError DecodedNumericLiteral :=
  if 0 ≤ decoded.authoredScale then pure decoded
  else throw (.negativeLiteralScale position decoded.authoredScale)

private def checkNumberArithmeticOperand
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (position : Nat) (operation : NumericArithmeticOp) :
    SurfaceAddressedNumberArithmeticOperand →
      SurfaceAddressedNumberArithmeticOperand →
      Except AddressedNumberExtremumElabError
        (CheckedAddressedNumberExtremumSurfaceOperand model)
  | .field left, .field right => do
      let pair ←
        checkAddressedNumberPair model declaringGroup targetField left right
          |>.mapError (.pair position)
      pure (.source (.arithmetic operation (.fields pair)))
  | .field left, .literal decoded => do
      let checkedLiteral ← checkArithmeticLiteral position decoded
      let source ←
        checkAddressedNumberSource model declaringGroup targetField left
          |>.mapError (.source position)
      pure (.source (.arithmetic operation (.fieldLiteral source checkedLiteral)))
  | .literal decoded, .field right => do
      let checkedLiteral ← checkArithmeticLiteral position decoded
      let source ←
        checkAddressedNumberSource model declaringGroup targetField right
          |>.mapError (.source position)
      pure (.source (.arithmetic operation (.literalField checkedLiteral source)))
  | .literal _, .literal _ => throw (.constantOnlyArithmetic position)

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
  | .arithmetic operation left right =>
      checkNumberArithmeticOperand model declaringGroup targetField position
        operation left right
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
  match source with
  | .unary .direct numberSource
  | .unary .abs numberSource => numberSource.source.info.scale
  | .unary (.round _ places) _ => places.val
  | .arithmetic operation child =>
      operation.directFieldResultScale child.operandScales.1
        child.operandScales.2

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
      first.targetField = source.targetField
  op : NumericExtremumOp
  sameScale :
    first.primarySource.placement.targetPolicy.info.scale =
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
        first.targetField = source.targetField then
      let resultScale := addressedNumberExtremumOperandResultScale
        first rest scan.literal
      if hScale : first.primarySource.placement.targetPolicy.info.scale =
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
        throw (.scaleMismatch first.primarySource.placement.targetPolicy.info.scale
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

namespace CheckedAddressedNumberArithmeticChild

/-- Evaluate one arithmetic child at an already-certified row. A field pair delegates both ordered reads to the shared pair evaluator; a literal side contributes its exact decoded value at its authored position without a row read, so poison and empty-as-zero come only from the retained source. -/
def evaluateAtPath (child : CheckedAddressedNumberArithmeticChild model)
    (operation : NumericArithmeticOp) (input : CheckedDocument model)
    (path : List Nat) :
    Except AddressedNumberExtremumFault NumericComputationResult :=
  let combine := NumericComputationResult.combineReached fun left right =>
    .value (operation.eval left right)
  match child with
  | .fields pair => pair.evaluateAtPath input combine path
  | .fieldLiteral source decoded =>
      return combine (← source.evaluateAtPath input path) (.value decoded.value)
  | .literalField decoded source =>
      return combine (.value decoded.value) (← source.evaluateAtPath input path)

end CheckedAddressedNumberArithmeticChild

/-- The exact bounded checked operand retained for authored-order execution and consumer identity. -/
inductive CheckedAddressedNumberExtremumOperand (model : FlatModel) where
  | field (source : CheckedAddressedNumberSource model)
  | abs (source : CheckedAddressedNumberSource model)
  | round (source : CheckedAddressedNumberSource model)
      (mode : DecimalRoundingMode) (places : RoundingPlaces)
  | arithmetic (operation : NumericArithmeticOp)
      (child : CheckedAddressedNumberArithmeticChild model)
  | literal (decoded : DecodedNumericLiteral)

namespace CheckedAddressedNumberExtremum

/-- Recover the exact checked runtime operand represented by one field-backed source tag. -/
private def asOperand
    (source : CheckedAddressedNumberExtremumFieldOperand model) :
    CheckedAddressedNumberExtremumOperand model :=
  match source with
  | .unary .direct numberSource => .field numberSource
  | .unary .abs numberSource => .abs numberSource
  | .unary (.round mode places) numberSource =>
      .round numberSource mode places
  | .arithmetic operation child => .arithmetic operation child

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

end CheckedAddressedNumberExtremum

namespace CheckedAddressedNumberExtremumOperand

/-- Evaluate one retained outer operand at an already-certified row. Pair nodes delegate ordered reads to the shared pair evaluator and supply only their existing scalar arithmetic node. -/
def evaluateAtPath
    (operand : CheckedAddressedNumberExtremumOperand model)
    (input : CheckedDocument model) (path : List Nat) :
    Except AddressedNumberExtremumFault NumericComputationResult :=
  match operand with
  | .field source => source.evaluateAtPath input path
  | .abs source =>
      return (← source.evaluateAtPath input path).absolute
  | .round source mode places =>
      return (← source.evaluateAtPath input path).round mode places
  | .arithmetic operation child => child.evaluateAtPath operation input path
  | .literal decoded => pure (.value decoded.value)

end CheckedAddressedNumberExtremumOperand

namespace CheckedAddressedNumberExtremum

private def evaluateRestAtPath (op : NumericExtremumOp)
    (input : CheckedDocument model) (path : List Nat) :
    List (CheckedAddressedNumberExtremumOperand model) →
      NumericComputationResult →
      Except AddressedNumberExtremumFault NumericComputationResult
  | [], result => pure result
  | _, .poison cause => pure (.poison cause)
  | operand :: rest, result => do
      let next ← operand.evaluateAtPath input path
      evaluateRestAtPath op input path rest
        (op.selectComputationResult result next)

private def evaluateAtPath
    (operation : CheckedAddressedNumberExtremum model)
    (input : CheckedDocument model) (path : List Nat) :
    Except AddressedNumberExtremumFault NumericComputationResult := do
  let operands := operation.firstAndRestOperands
  let initial ← operands.1.evaluateAtPath input path
  evaluateRestAtPath operation.op input path operands.2 initial

def execute (operation : CheckedAddressedNumberExtremum model)
    (input : CheckedDocument model) :
    Except AddressedNumberExtremumFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  operation.first.primarySource.placement.executeWithPath input
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
    MessagePointer.ofCellAddr payloadAt supplied outcomes)

end CheckedAddressedNumberExtremum

end A12Kernel
