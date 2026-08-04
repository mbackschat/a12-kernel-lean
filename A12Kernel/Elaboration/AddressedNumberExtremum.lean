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

namespace NumericArithmeticOp

/-- View one arithmetic node through the shared static scale algebra. -/
def scaleBinaryOp : NumericArithmeticOp → NumericScaleBinaryOp
  | .add => .add
  | .subtract => .subtract
  | .multiply => .multiply

end NumericArithmeticOp

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

/-- The two operand summaries in authored order. A field contributes its declared nonnegative scale without multiplicative-constant capability; a literal contributes its authored signed scale — negative once an integer literal strips trailing zeros — together with that capability. -/
def operandSummaries : CheckedAddressedNumberArithmeticChild model →
    NumericScaleSummary × NumericScaleSummary
  | .fields pair =>
      (.field pair.left.source.info.scale, .field pair.right.source.info.scale)
  | .fieldLiteral source decoded =>
      (.field source.source.info.scale,
        NumericScaleSummary.constant decoded.authoredScale)
  | .literalField decoded source =>
      (NumericScaleSummary.constant decoded.authoredScale,
        .field source.source.info.scale)

/-- The child's derived summary through the shared scale algebra: the additive nodes take the maximum scale and require both operands to be capable, while multiplication adds scales and keeps capability from either operand. -/
def scaleSummary (child : CheckedAddressedNumberArithmeticChild model)
    (operation : NumericArithmeticOp) : NumericScaleSummary :=
  let operands := child.operandSummaries
  NumericScaleSummary.binary operation.scaleBinaryOp operands.1 operands.2

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
  | tooManyLiterals
  | noFieldSource
  | incoherentTarget
  | scaleMismatch (target : Nat) (result : NumericScaleSummary)
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
      let source ←
        checkAddressedNumberSource model declaringGroup targetField left
          |>.mapError (.source position)
      pure (.source (.arithmetic operation (.fieldLiteral source decoded)))
  | .literal decoded, .field right => do
      let source ←
        checkAddressedNumberSource model declaringGroup targetField right
          |>.mapError (.source position)
      pure (.source (.arithmetic operation (.literalField decoded source)))
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

/-- The static scale summary contributed by one field-backed operand after its local wrapper. A direct or `Abs` source keeps its declared scale, explicit rounding replaces it with the authored places, and both remain incapable of trailing-zero expansion. -/
def CheckedAddressedNumberExtremumFieldOperand.scaleSummary
    (source : CheckedAddressedNumberExtremumFieldOperand model) :
    NumericScaleSummary :=
  match source with
  | .unary .direct numberSource
  | .unary .abs numberSource => .field numberSource.source.info.scale
  | .unary (.round _ places) _ => .rounded places.val
  | .arithmetic operation child => child.scaleSummary operation

def addressedNumberExtremumScaleSummary
    (first : CheckedAddressedNumberExtremumFieldOperand model)
    (rest : List (CheckedAddressedNumberExtremumFieldOperand model)) :
    NumericScaleSummary :=
  rest.foldl (fun summary source => summary.union source.scaleSummary)
    first.scaleSummary

/-- Fold the one retained outer literal into the list summary. The union takes the larger scale and keeps capability only when every operand carries it, so a single bare field or wrapper operand makes the whole list incapable. -/
def addressedNumberExtremumOperandScaleSummary
    (first : CheckedAddressedNumberExtremumFieldOperand model)
    (rest : List (CheckedAddressedNumberExtremumFieldOperand model))
    (literal : Option AddressedNumberExtremumLiteral) : NumericScaleSummary :=
  let fields := addressedNumberExtremumScaleSummary first rest
  match literal with
  | none => fields
  | some positioned =>
      fields.union (NumericScaleSummary.constant
        positioned.decoded.authoredScale)

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
  /-- Target admission is the shared `==`/`!=` scale predicate, not equality: an equal derived scale passes, and a smaller derived scale passes only while the whole list retains multiplicative-constant capability. -/
  targetAdmitted :
    exactNumericScaleComparisonAllowedWithSuppression false
        (NumericScaleSummary.field
          first.primarySource.placement.targetPolicy.info.scale)
        (addressedNumberExtremumOperandScaleSummary first rest literal) = true

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
      let summary := addressedNumberExtremumOperandScaleSummary
        first rest scan.literal
      if hScale : exactNumericScaleComparisonAllowedWithSuppression false
          (NumericScaleSummary.field
            first.primarySource.placement.targetPolicy.info.scale)
          summary = true then
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
          targetAdmitted := hScale
        }
      else
        throw (.scaleMismatch
          first.primarySource.placement.targetPolicy.info.scale summary)
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
