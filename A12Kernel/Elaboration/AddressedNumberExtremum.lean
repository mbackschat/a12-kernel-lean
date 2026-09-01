import A12Kernel.Elaboration.AddressedNumberField
import A12Kernel.Elaboration.NumericExpression

/-! # Repeatable bounded Number extrema

This capsule retains a nonempty ordered list containing one or more checked Number sources, permits operand-local absolute-value, rounding, one arithmetic, division, or power node over two field-or-literal operands, or one nested extremum over direct field-or-literal leaves, and admits at most one immediate decoded literal per extremum call. It delegates each local transformation and the authored-order folds to the existing scalar semantics, then reuses the shared exact-address target owner.
-/

namespace A12Kernel

/-- One inner operand of an operand-local arithmetic child: a direct Number field or an immediate decoded literal. -/
inductive SurfaceAddressedNumberArithmeticOperand where
  | field (reference : SurfaceFieldPath)
  | literal (decoded : DecodedNumericLiteral)
  deriving Repr, DecidableEq

/-- The bounded addressed surface admits direct Number fields, operand-local `Abs`, Round, one ordinary arithmetic, division, or power node over two field-or-literal operands, one nested extremum over direct field-or-literal leaves, and one immediate decoded literal in the outer list. Wider numeric operations remain with the scalar expression owner. -/
inductive SurfaceAddressedNumberExtremumOperand where
  | field (reference : SurfaceFieldPath)
  | abs (reference : SurfaceFieldPath)
  | round (reference : SurfaceFieldPath) (mode : DecimalRoundingMode)
      (places : RoundingPlaces)
  | arithmetic (operation : NumericArithmeticOp)
      (left right : SurfaceAddressedNumberArithmeticOperand)
  | division (left right : SurfaceAddressedNumberArithmeticOperand)
  | power (base exponent : SurfaceAddressedNumberArithmeticOperand)
  | extremum (operation : NumericExtremumOp) (first : SurfaceAddressedNumberArithmeticOperand)
      (rest : List SurfaceAddressedNumberArithmeticOperand)
  | literal (decoded : DecodedNumericLiteral)
  deriving Repr, DecidableEq

namespace NumericArithmeticOp

/-- View one arithmetic node through the shared static scale algebra. -/
def scaleBinaryOp : NumericArithmeticOp → NumericScaleBinaryOp
  | .add => .add
  | .subtract => .subtract
  | .multiply => .multiply

end NumericArithmeticOp

/-- One retained arithmetic child of an extremum operand. A child may read two fields, one field and one immediate literal in either order, or only literals; the target's own certificate owns iteration, so a constant-only child needs no source. -/
inductive CheckedAddressedNumberArithmeticChild (model : FlatModel) where
  | fields (pair : CheckedAddressedNumberPair model)
  | fieldLiteral (source : CheckedAddressedNumberSource model)
      (decoded : DecodedNumericLiteral)
  | literalField (decoded : DecodedNumericLiteral)
      (source : CheckedAddressedNumberSource model)
  | literals (left right : DecodedNumericLiteral)

namespace CheckedAddressedNumberArithmeticChild

/-- Every ordered field dependency this child actually reads. A retained literal contributes none, so a literal in place of a field also removes that field's failure from the row. -/
def sources : CheckedAddressedNumberArithmeticChild model →
    List (CheckedAddressedNumberSource model)
  | .fields pair => [pair.left, pair.right]
  | .fieldLiteral source _ => [source]
  | .literalField _ source => [source]
  | .literals _ _ => []

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
  | .literals left right =>
      (NumericScaleSummary.constant left.authoredScale,
        NumericScaleSummary.constant right.authoredScale)

/-- The child's derived summary through the shared scale algebra: the additive nodes take the maximum scale and require both operands to be capable, while multiplication adds scales and keeps capability from either operand. -/
def scaleSummary (child : CheckedAddressedNumberArithmeticChild model)
    (operation : NumericArithmeticOp) : NumericScaleSummary :=
  let operands := child.operandSummaries
  NumericScaleSummary.binary operation.scaleBinaryOp operands.1 operands.2

/-- The power scale exception recognizes only a nonnegative literal in the authored exponent position. -/
def hasSimpleNonnegativeLiteralExponent :
    CheckedAddressedNumberArithmeticChild model → Bool
  | .fieldLiteral _ decoded | .literals _ decoded => decide (0 ≤ decoded.value)
  | .fields _ | .literalField _ _ => false

end CheckedAddressedNumberArithmeticChild

/-- The bounded direct and unary-wrapper operations that can currently own a checked addressed Number source inside an extremum operand list. -/
inductive AddressedNumberExtremumFieldOperation where
  | direct
  | abs
  | round (mode : DecimalRoundingMode) (places : RoundingPlaces)
  deriving Repr, DecidableEq

inductive AddressedNumberExtremumElabError where
  | target (cause : AddressedNumericPlacementElabError)
  | source (position : Nat) (cause : AddressedNumberSourceElabError)
  | pair (position : Nat) (cause : AddressedNumberPairElabError)
  | invalidPowerExponentScale (position : Nat) (actual : ScaleInfo)
  | tooManyLiterals
  | incoherentTarget
  | scaleMismatch (target : Nat) (result : NumericScaleSummary)
  deriving Repr, DecidableEq

abbrev AddressedNumberExtremumFault := AddressedNumericLeafFault

namespace CheckedAddressedNumberArithmeticChild

/-- Evaluate one binary child at an already-certified row. A field pair delegates both ordered reads to the shared pair evaluator; a literal side contributes its exact decoded value at its authored position without a row read, so poison and empty-as-zero come only from a retained source. A constant-only child reads nothing at all and is therefore constant across rows. -/
def evaluateAtEnvironmentUsing (child : CheckedAddressedNumberArithmeticChild model)
    (combine : NumericComputationResult → NumericComputationResult →
      NumericComputationResult)
    (input : CheckedDocument model)
    (environment : Env) :
    Except AddressedNumberExtremumFault NumericComputationResult :=
  match child with
  | .fields pair => pair.evaluateAtEnvironment input combine environment
  | .fieldLiteral source decoded =>
      return combine (← source.evaluateAtEnvironment input environment) (.value decoded.value)
  | .literalField decoded source =>
      return combine (.value decoded.value) (← source.evaluateAtEnvironment input environment)
  | .literals left right =>
      pure (combine (.value left.value) (.value right.value))

/-- Evaluate an ordinary arithmetic child through its existing scalar operation. -/
def evaluateAtEnvironment (child : CheckedAddressedNumberArithmeticChild model)
    (operation : NumericArithmeticOp) (input : CheckedDocument model)
    (environment : Env) :
    Except AddressedNumberExtremumFault NumericComputationResult :=
  child.evaluateAtEnvironmentUsing
    (NumericComputationResult.combineReached fun left right =>
      .value (operation.eval left right)) input environment

end CheckedAddressedNumberArithmeticChild

/-- One statically admitted power operand with its derived scale retained for the enclosing list. -/
structure CheckedAddressedNumberPowerOperand (model : FlatModel) where
  private mk ::
  child : CheckedAddressedNumberArithmeticChild model
  summary : NumericScaleSummary
  summaryCertified : NumericScaleSummary.power?
    child.operandSummaries.1 child.operandSummaries.2
    child.hasSimpleNonnegativeLiteralExponent = some summary

/-- One direct field-or-literal leaf of a nested addressed Number extremum. Keeping this type separate bounds nesting to one level and prevents wrappers or arithmetic children from being admitted by accident. -/
inductive CheckedAddressedNumberExtremumLeaf (model : FlatModel) where
  | field (source : CheckedAddressedNumberSource model)
  | literal (decoded : DecodedNumericLiteral)

namespace CheckedAddressedNumberExtremumLeaf

/-- The optional field dependency read by this leaf. -/
def sources : CheckedAddressedNumberExtremumLeaf model →
    List (CheckedAddressedNumberSource model)
  | .field source => [source]
  | .literal _ => []

/-- The leaf's contribution to its immediate extremum call. -/
def scaleSummary : CheckedAddressedNumberExtremumLeaf model →
    NumericScaleSummary
  | .field source => .field source.source.info.scale
  | .literal decoded => NumericScaleSummary.constant decoded.authoredScale

/-- Only a literal authored directly in this nested call consumes its literal budget. -/
def isImmediateLiteral : CheckedAddressedNumberExtremumLeaf model → Bool
  | .literal _ => true
  | _ => false

/-- Evaluate one direct nested leaf at the target-owned row. -/
def evaluateAtEnvironment
    (leaf : CheckedAddressedNumberExtremumLeaf model)
    (input : CheckedDocument model) (environment : Env) :
    Except AddressedNumberExtremumFault NumericComputationResult :=
  match leaf with
  | .field source => source.evaluateAtEnvironment input environment
  | .literal decoded => pure (.value decoded.value)

end CheckedAddressedNumberExtremumLeaf

/-- One nested `Min` or `Max` call whose ordered direct leaves own an independent immediate-literal budget. -/
structure CheckedAddressedNumberNestedExtremum (model : FlatModel) where
  private mk ::
  op : NumericExtremumOp
  first : CheckedAddressedNumberExtremumLeaf model
  rest : List (CheckedAddressedNumberExtremumLeaf model)
  atMostOneLiteral :
    ((first :: rest).filter
      CheckedAddressedNumberExtremumLeaf.isImmediateLiteral).length ≤ 1

namespace CheckedAddressedNumberNestedExtremum

/-- The exact authored nested leaf order. -/
def orderedOperands (operation : CheckedAddressedNumberNestedExtremum model) :
    List (CheckedAddressedNumberExtremumLeaf model) :=
  operation.first :: operation.rest

/-- Every ordered field dependency read by this nested call. -/
def sources (operation : CheckedAddressedNumberNestedExtremum model) :
    List (CheckedAddressedNumberSource model) :=
  operation.orderedOperands.flatMap CheckedAddressedNumberExtremumLeaf.sources

/-- Fold the nested call's leaf summaries without flattening it into its parent. -/
def scaleSummary (operation : CheckedAddressedNumberNestedExtremum model) :
    NumericScaleSummary :=
  operation.rest.foldl
    (fun summary leaf => summary.union leaf.scaleSummary)
    operation.first.scaleSummary

private def evaluateRestAtPath (op : NumericExtremumOp)
    (input : CheckedDocument model) (environment : Env) :
    List (CheckedAddressedNumberExtremumLeaf model) →
      NumericComputationResult →
      Except AddressedNumberExtremumFault NumericComputationResult
  | [], result => pure result
  | _, .poison cause => pure (.poison cause)
  | leaf :: rest, result => do
      let next ← leaf.evaluateAtEnvironment input environment
      evaluateRestAtPath op input environment rest
        (op.selectComputationResult result next)

/-- Evaluate the nested call in authored order at one target-owned row. -/
def evaluateAtEnvironment (operation : CheckedAddressedNumberNestedExtremum model)
    (input : CheckedDocument model) (environment : Env) :
    Except AddressedNumberExtremumFault NumericComputationResult := do
  let initial ← operation.first.evaluateAtEnvironment input environment
  evaluateRestAtPath operation.op input environment operation.rest initial

end CheckedAddressedNumberNestedExtremum

/-- One retained operand in exact authored order. Literal and constant-only forms read no row, and the outer target's own certificate owns iteration, so no operand has to supply a placement. -/
inductive CheckedAddressedNumberExtremumOperand (model : FlatModel) where
  | field (source : CheckedAddressedNumberSource model)
  | abs (source : CheckedAddressedNumberSource model)
  | round (source : CheckedAddressedNumberSource model)
      (mode : DecimalRoundingMode) (places : RoundingPlaces)
  | arithmetic (operation : NumericArithmeticOp)
      (child : CheckedAddressedNumberArithmeticChild model)
  | division (child : CheckedAddressedNumberArithmeticChild model)
  | power (operation : CheckedAddressedNumberPowerOperand model)
  | extremum (operation : CheckedAddressedNumberNestedExtremum model)
  | literal (decoded : DecodedNumericLiteral)

namespace CheckedAddressedNumberExtremumOperand

/-- Every ordered field dependency this operand reads. -/
def sources : CheckedAddressedNumberExtremumOperand model →
    List (CheckedAddressedNumberSource model)
  | .field source | .abs source => [source]
  | .round source _ _ => [source]
  | .arithmetic _ child => child.sources
  | .division child => child.sources
  | .power operation => operation.child.sources
  | .extremum operation => operation.sources
  | .literal _ => []

def sourceFields (operand : CheckedAddressedNumberExtremumOperand model) :
    List FieldId :=
  operand.sources.map fun source => source.placement.sourceDeclaration.id

/-- The static scale summary this operand contributes. A direct or `Abs` source keeps its declared scale, explicit rounding replaces it with the authored places, and both remain incapable of trailing-zero expansion; a literal contributes its authored signed scale with that capability. -/
def scaleSummary : CheckedAddressedNumberExtremumOperand model →
    NumericScaleSummary
  | .field source | .abs source => .field source.source.info.scale
  | .round _ _ places => .rounded places.val
  | .arithmetic operation child => child.scaleSummary operation
  | .division child =>
      let summaries := child.operandSummaries
      NumericScaleSummary.binary .divide summaries.1 summaries.2
  | .power operation => operation.summary
  | .extremum operation => operation.scaleSummary
  | .literal decoded => NumericScaleSummary.constant decoded.authoredScale

/-- Whether this operand is an immediate literal of the enclosing call, which is the only form the kernel's one-constant budget counts. A literal inside an arithmetic child is not one. -/
def isImmediateLiteral : CheckedAddressedNumberExtremumOperand model → Bool
  | .literal _ => true
  | _ => false

/-- Evaluate one retained operand at an already-certified row. Arithmetic nodes delegate ordered reads to their child and supply only the existing scalar node. -/
def evaluateAtEnvironment
    (operand : CheckedAddressedNumberExtremumOperand model)
    (input : CheckedDocument model) (environment : Env) :
    Except AddressedNumberExtremumFault NumericComputationResult :=
  match operand with
  | .field source => source.evaluateAtEnvironment input environment
  | .abs source =>
      return (← source.evaluateAtEnvironment input environment).absolute
  | .round source mode places =>
      return (← source.evaluateAtEnvironment input environment).round mode places
  | .arithmetic operation child => child.evaluateAtEnvironment operation input environment
  | .division child =>
      child.evaluateAtEnvironmentUsing
        (NumericComputationResult.combineReached fun left right =>
          NumericComputationResult.ofArithmetic (divideNumeric left right))
        input environment
  | .power operation =>
      operation.child.evaluateAtEnvironmentUsing NumericComputationResult.evalPower
        input environment
  | .extremum operation => operation.evaluateAtEnvironment input environment
  | .literal decoded => pure (.value decoded.value)

end CheckedAddressedNumberExtremumOperand

/-- Fold the ordered operand list's summaries. The union takes the larger scale and keeps multiplicative-constant capability only when every operand carries it, so one bare field or wrapper operand makes the whole list incapable. -/
def addressedNumberExtremumOperandsScaleSummary
    (first : CheckedAddressedNumberExtremumOperand model)
    (rest : List (CheckedAddressedNumberExtremumOperand model)) :
    NumericScaleSummary :=
  rest.foldl (fun summary operand => summary.union operand.scaleSummary)
    first.scaleSummary

/-- One checked repeatable operand-list extremum. The target certificate owns iteration and the target policy; the operand list is stored in exact authored order with no positional literal encoding. -/
structure CheckedAddressedNumberExtremum (model : FlatModel) where
  private mk ::
  target : CheckedAddressedNumericTarget model
  first : CheckedAddressedNumberExtremumOperand model
  rest : List (CheckedAddressedNumberExtremumOperand model)
  /-- The enclosing call admits at most one immediate constant; constants inside an arithmetic child are not counted. -/
  atMostOneLiteral :
    ((first :: rest).filter
      CheckedAddressedNumberExtremumOperand.isImmediateLiteral).length ≤ 1
  /-- Every field dependency anywhere in the list is certified against this one target. -/
  sourcesShareTarget :
    ∀ source ∈ (first :: rest).flatMap
        CheckedAddressedNumberExtremumOperand.sources,
      source.placement.targetField = target.targetField
  op : NumericExtremumOp
  suppressExactScaleWarning : Bool
  /-- Target admission uses the shared scale predicate: suppression admits any summary; otherwise exact equality or capable smaller-scale padding is required. -/
  targetAdmitted :
    exactNumericScaleComparisonAllowedWithSuppression suppressExactScaleWarning
        (NumericScaleSummary.field target.targetPolicy.info.scale)
        (addressedNumberExtremumOperandsScaleSummary first rest) = true

private def checkNumberSourceOperand
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (position : Nat) (operation : AddressedNumberExtremumFieldOperation)
    (reference : SurfaceFieldPath) :
    Except AddressedNumberExtremumElabError
      (CheckedAddressedNumberExtremumOperand model) := do
  let numberSource ←
    checkAddressedNumberSource model declaringGroup targetField reference
      |>.mapError (.source position)
  pure <| match operation with
    | .direct => .field numberSource
    | .abs => .abs numberSource
    | .round mode places => .round numberSource mode places

private def checkNumberArithmeticChild
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (position : Nat) :
    SurfaceAddressedNumberArithmeticOperand →
      SurfaceAddressedNumberArithmeticOperand →
      Except AddressedNumberExtremumElabError
        (CheckedAddressedNumberArithmeticChild model)
  | .field left, .field right => do
      let pair ←
        checkAddressedNumberPair model declaringGroup targetField left right
          |>.mapError (.pair position)
      pure (.fields pair)
  | .field left, .literal decoded => do
      let source ←
        checkAddressedNumberSource model declaringGroup targetField left
          |>.mapError (.source position)
      pure (.fieldLiteral source decoded)
  | .literal decoded, .field right => do
      let source ←
        checkAddressedNumberSource model declaringGroup targetField right
          |>.mapError (.source position)
      pure (.literalField decoded source)
  | .literal left, .literal right =>
      pure (.literals left right)

private def checkNumberBinaryOperand
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (position : Nat)
    (wrap : CheckedAddressedNumberArithmeticChild model →
      CheckedAddressedNumberExtremumOperand model)
    (left right : SurfaceAddressedNumberArithmeticOperand) :
    Except AddressedNumberExtremumElabError
      (CheckedAddressedNumberExtremumOperand model) := do
  pure (wrap (← checkNumberArithmeticChild model declaringGroup targetField
    position left right))

private def checkNumberPowerOperand
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (position : Nat) (base exponent : SurfaceAddressedNumberArithmeticOperand) :
    Except AddressedNumberExtremumElabError
      (CheckedAddressedNumberExtremumOperand model) := do
  let child ←
    checkNumberArithmeticChild model declaringGroup targetField position base exponent
  let summaries := child.operandSummaries
  match hSummary : NumericScaleSummary.power? summaries.1 summaries.2
      child.hasSimpleNonnegativeLiteralExponent with
  | some summary =>
      pure (.power { child, summary, summaryCertified := hSummary })
  | none => throw (.invalidPowerExponentScale position summaries.2.scale)

private def checkNumberNestedLeaf
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (position : Nat) : SurfaceAddressedNumberArithmeticOperand →
      Except AddressedNumberExtremumElabError
        (CheckedAddressedNumberExtremumLeaf model)
  | .field reference => do
      let source ←
        checkAddressedNumberSource model declaringGroup targetField reference
          |>.mapError (.source position)
      pure (.field source)
  | .literal decoded => pure (.literal decoded)

private def checkNumberNestedLeaves
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (position : Nat) : List SurfaceAddressedNumberArithmeticOperand →
      Except AddressedNumberExtremumElabError
        (List (CheckedAddressedNumberExtremumLeaf model))
  | [] => pure []
  | leaf :: rest => do
      let checked ←
        checkNumberNestedLeaf model declaringGroup targetField position leaf
      let tail ←
        checkNumberNestedLeaves model declaringGroup targetField position rest
      pure (checked :: tail)

private def checkNumberNestedExtremum
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (position : Nat) (op : NumericExtremumOp)
    (firstOperand : SurfaceAddressedNumberArithmeticOperand)
    (restOperands : List SurfaceAddressedNumberArithmeticOperand) :
    Except AddressedNumberExtremumElabError
      (CheckedAddressedNumberExtremumOperand model) := do
  let first ←
    checkNumberNestedLeaf model declaringGroup targetField position firstOperand
  let rest ←
    checkNumberNestedLeaves model declaringGroup targetField position restOperands
  if hLiterals : ((first :: rest).filter
      CheckedAddressedNumberExtremumLeaf.isImmediateLiteral).length ≤ 1 then
    pure (.extremum { op, first, rest, atMostOneLiteral := hLiterals })
  else
    throw .tooManyLiterals

private def checkNumberOperand
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (position : Nat) : SurfaceAddressedNumberExtremumOperand →
      Except AddressedNumberExtremumElabError
        (CheckedAddressedNumberExtremumOperand model)
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
      checkNumberBinaryOperand model declaringGroup targetField position
        (.arithmetic operation) left right
  | .division left right =>
      checkNumberBinaryOperand model declaringGroup targetField position
        .division left right
  | .power base exponent =>
      checkNumberPowerOperand model declaringGroup targetField position base exponent
  | .extremum operation first rest =>
      checkNumberNestedExtremum model declaringGroup targetField position
        operation first rest
  | .literal decoded => pure (.literal decoded)

private def checkNumberOperands
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId) :
    Nat → List SurfaceAddressedNumberExtremumOperand →
      Except AddressedNumberExtremumElabError
        (List (CheckedAddressedNumberExtremumOperand model))
  | _, [] => pure []
  | position, operand :: rest => do
      let checked ←
        checkNumberOperand model declaringGroup targetField position operand
      let tail ←
        checkNumberOperands model declaringGroup targetField (position + 1) rest
      pure (checked :: tail)

private def checkAddressedNumberExtremumOperandsUsing
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (firstOperand : SurfaceAddressedNumberExtremumOperand)
    (restOperands : List SurfaceAddressedNumberExtremumOperand)
    (op : NumericExtremumOp) (suppressExactScaleWarning : Bool) :
    Except AddressedNumberExtremumElabError
      (CheckedAddressedNumberExtremum model) := do
  let target ←
    checkAddressedNumericTarget model declaringGroup targetField
      |>.mapError .target
  let first ←
    checkNumberOperand model declaringGroup targetField 1 firstOperand
  let rest ←
    checkNumberOperands model declaringGroup targetField 2 restOperands
  if hLiterals : ((first :: rest).filter
      CheckedAddressedNumberExtremumOperand.isImmediateLiteral).length ≤ 1 then
    if hTargets : ∀ source ∈ (first :: rest).flatMap
        CheckedAddressedNumberExtremumOperand.sources,
        source.placement.targetField = target.targetField then
      let summary := addressedNumberExtremumOperandsScaleSummary first rest
      if hScale : exactNumericScaleComparisonAllowedWithSuppression
          suppressExactScaleWarning
          (NumericScaleSummary.field target.targetPolicy.info.scale)
          summary = true then
        pure {
          target
          first
          rest
          atMostOneLiteral := hLiterals
          sourcesShareTarget := hTargets
          op
          suppressExactScaleWarning
          targetAdmitted := hScale
        }
      else
        throw (.scaleMismatch target.targetPolicy.info.scale summary)
    else
      throw .incoherentTarget
  else
    throw .tooManyLiterals

/-- Validate the bounded ordered operand list through the shared exact-scale gate. No operand has to be field-backed: a constant-only list still iterates at the target's own repeatable scope. -/
def checkAddressedNumberExtremumOperands
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (firstOperand : SurfaceAddressedNumberExtremumOperand)
    (restOperands : List SurfaceAddressedNumberExtremumOperand)
    (op : NumericExtremumOp) (suppressExactScaleWarning : Bool := false) :
    Except AddressedNumberExtremumElabError
      (CheckedAddressedNumberExtremum model) :=
  checkAddressedNumberExtremumOperandsUsing model declaringGroup targetField
    firstOperand restOperands op suppressExactScaleWarning

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

namespace CheckedAddressedNumberExtremum

/-- The exact authored operand order. -/
def orderedOperands (operation : CheckedAddressedNumberExtremum model) :
    List (CheckedAddressedNumberExtremumOperand model) :=
  operation.first :: operation.rest

/-- Every ordered field dependency of the whole call. -/
def sourceFields (operation : CheckedAddressedNumberExtremum model) :
    List FieldId :=
  operation.orderedOperands.flatMap
    CheckedAddressedNumberExtremumOperand.sourceFields

/-- This call's derived static scale summary. -/
def scaleSummary (operation : CheckedAddressedNumberExtremum model) :
    NumericScaleSummary :=
  addressedNumberExtremumOperandsScaleSummary operation.first operation.rest

private def evaluateRestAtPath (op : NumericExtremumOp)
    (input : CheckedDocument model) (environment : Env) :
    List (CheckedAddressedNumberExtremumOperand model) →
      NumericComputationResult →
      Except AddressedNumberExtremumFault NumericComputationResult
  | [], result => pure result
  | _, .poison cause => pure (.poison cause)
  | operand :: rest, result => do
      let next ← operand.evaluateAtEnvironment input environment
      evaluateRestAtPath op input environment rest
        (op.selectComputationResult result next)

private def evaluateAtEnvironment
    (operation : CheckedAddressedNumberExtremum model)
    (input : CheckedDocument model) (environment : Env) :
    Except AddressedNumberExtremumFault NumericComputationResult := do
  let initial ← operation.first.evaluateAtEnvironment input environment
  evaluateRestAtPath operation.op input environment operation.rest initial

def execute (operation : CheckedAddressedNumberExtremum model)
    (input : CheckedDocument model) :
    Except AddressedNumberExtremumFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  if operation.suppressExactScaleWarning then
    operation.target.executeAtEnvironmentScaleWarningSuppressed input
      (operation.evaluateAtEnvironment input)
  else
    operation.target.executeAtEnvironment input
      (operation.evaluateAtEnvironment input)

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
