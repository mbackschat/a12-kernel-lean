import A12Kernel.Reference.Dm.LowerCore
import A12Kernel.Elaboration.NumericSource
import A12Kernel.Elaboration.NumericComputation.OperationTyping
import A12Kernel.Elaboration.ScalarComparisonAdmission

namespace A12Kernel.Dm

def rawScalarComparisonOperand (type : NumericOperandType) : Expr → ScalarComparisonOperand
  | .braces body | .parens body => { rawScalarComparisonOperand type body with directField := false }
  | .string text => { type, literal := some (.inl text) }
  | .constant "True" => { type, literal := some (.inr true) }
  | .constant "False" => { type, literal := some (.inr false) }
  | .value _ => { type, directField := true }
  | _ => { type }

/-- Scalar temporal extrema compare component sets after model Base Year supplementation
(CheckFeldListenOperOpImpl; retained date-components and date-validity captures). -/
def rawNumericType (hasBaseYear : Bool) (expression : AuthoredNumericExpr NumericOperandType) : Lowering NumericOperandType :=
  (checkNumericOperationNodes (fun type => (.ok type : Except Refusal NumericOperandType))
    expression hasBaseYear).mapError fun
    | .operand refusal => refusal
    | .node diagnostic => { construct := "Having", detail := diagnostic.map (·.kernelCode) |>.getD "unsupported numeric node" }

def rawComparisonEntry (kind : SurfaceScalarKind) : Expr → ComparisonEntryOperand
  | .braces body | .parens body => .grouped (rawComparisonEntry kind body)
  | .constant "Today" => .clock .date
  | .constant "Now" => .clock .dateTime
  | .number _ | .string _ | .constant "True" | .constant "False" => .literal kind
  | .entity _ | .value _ => .field kind
  | _ => .expression kind

private def Expr.isBaseYearOperation : Expr → Bool
  | .constant "BaseYear" => true
  | .braces body => body.isBaseYearOperation
  | .call "Abs" [.mk body none] none none => body.isBaseYearOperation
  | _ => false

def rawTemporalComparisonComponents? (type : NumericOperandType) (source : Expr) :
    Option TemporalComponents :=
  match type with
  | .temporal _ components => some components
  | .number _ => if source.isBaseYearOperation then some .baseYear else none
  | _ => none


/-- Compare admitted operation results without requiring an executable filter certificate.
The same gates judge authored comparisons and generated computation mismatches (spec/09 §6). -/
def checkRawComparisonOperands (model : FlatModel) (op : CompareOp) (leftSource rightSource : Expr)
    (left right : AuthoredNumericExpr NumericOperandType) (suppressExactScaleWarning : Bool) : Lowering Unit := do
  let some numericOp := op.toNumeric? | refuse "Having" "nested comparison operator"
  let leftType ← rawNumericType model.hasBaseYear left
  let rightType ← rawNumericType model.hasBaseYear right
  let family := match op with
    | .eq | .ne => ComparisonEntryFamily.equality
    | .tolerance _ => .tolerance
    | _ => .ordering
  match checkComparisonEntry family
      (rawComparisonEntry leftType.surfaceKind leftSource) (rawComparisonEntry rightType.surfaceKind rightSource) with
  | .error diagnostic => refuse "Having" diagnostic.kernelCode
  | .ok .complete => return
  | .ok _ => pure ()
  if let some comparison := op.toSurface? then
    match checkScalarComparison comparison (rawScalarComparisonOperand leftType leftSource)
        (rawScalarComparisonOperand rightType rightSource) with
    | .error diagnostic => refuse "Having" diagnostic.kernelCode
    | .ok true => return
    | .ok false => pure ()
  if leftType.surfaceKind == .dateRange || rightType.surfaceKind == .dateRange then
    if let some arm := copyComparisonKindArm? leftType.surfaceKind rightType.surfaceKind then
      refuse "Having" arm.diagnostic.kernelCode
    let .dateRange first := leftType | refuse "Having" "unsupported range comparison profile"
    let .dateRange second := rightType | refuse "Having" "unsupported range comparison profile"
    if first != second then refuse "Having" KernelStaticDiagnostic.invalidCompareToDateRange.kernelCode
    return
  if (match leftType, rightType with | .temporal .., _ | _, .temporal .. => true | _, _ => false) then
    let some first := rawTemporalComparisonComponents? leftType leftSource |
      refuse "Having" KernelStaticDiagnostic.invalidCompareToDate.kernelCode
    let some second := rawTemporalComparisonComponents? rightType rightSource |
      refuse "Having" KernelStaticDiagnostic.invalidCompareToDate.kernelCode
    let some comparison := op.toSurface? | refuse "Having" "temporal comparison operator"
    if !comparison.toTemporal.admitsFormats model.hasBaseYear first second then
      refuse "Having" KernelStaticDiagnostic.invalidCompareToDate.kernelCode
    return
  let comparison : NumericComparisonOf NumericOperandType := { op := numericOp, left, right, suppressExactScaleWarning }
  if !{ comparison with suppressExactScaleWarning := true }.admittedWith (fun | .number _ => true | _ => false)
      (fun | .number scale => scale | _ => .constant 0) then
    refuse "Having" "unsupported nested numeric comparison"
  if !comparison.admittedWith (fun | .number _ => true | _ => false)
      (fun | .number scale => scale | _ => .constant 0) then
    refuse "Having" KernelStaticDiagnostic.invalidCompareDecimalPlaces.kernelCode
  if leftSource.isBaseYearOperation && rightSource.isBaseYearOperation then
    refuse "Having" KernelStaticDiagnostic.inconsistentTypesCompared.kernelCode


private def Expr.isWrapperLiteral : Expr → Bool
  | .number _ | .string _ | .constant "True" | .constant "False" => true
  | .constant "Today" | .constant "Now" => true
  | .braces body => body.isWrapperLiteral
  | _ => false

/-- Absolute-value and rounding operations reject constants before checking the operand kind;
rounding precision follows both gates (CheckFeldOperOpImpl; CheckRundenOperOpImpl). -/
def checkRawNumericWrapper (hasBaseYear : Bool) (source : Expr) (body : AuthoredNumericExpr NumericOperandType) : Lowering Unit := do
  if source.isWrapperLiteral then refuse "Having" KernelStaticDiagnostic.noConst.kernelCode
  if (← rawNumericType hasBaseYear body).surfaceKind != .number then
    refuse "Having" KernelStaticDiagnostic.noNumber.kernelCode

/-- Authored constantness precedes result-kind checks at a completed operation. Extrema count
all constant kinds only after every operand finishes (CheckFeldListenOperOpImpl). -/
def checkRawNumericOperation (hasBaseYear : Bool) (source : Expr) (tree : AuthoredNumericExpr NumericOperandType) : Lowering Unit := do
  match source, tree with
  | .call "Abs" [.mk operand none] none none, .abs body => checkRawNumericWrapper hasBaseYear operand body
  | .call name arguments none none, _ =>
      if name == "Min" || name == "Max" then
        let constants := arguments.filter fun
          | .mk operand none => operand.isWrapperLiteral
          | _ => false
        if constants.length > 1 then
          refuse "Having" KernelStaticDiagnostic.tooManyConstantsInOperandList.kernelCode
  | _, _ => pure ()
  discard <| rawNumericType hasBaseYear tree


inductive RawScalarOperator where
  | length | asNumber | asString | rangeNumber | rangeString
  deriving BEq

def rawScalarOperator? : String → Option RawScalarOperator
  | "Length" => some .length
  | "FieldValueAsNumber" => some .asNumber
  | "FieldValueAsString" => some .asString
  | "RangeAsNumber" => some .rangeNumber
  | "RangeAsString" => some .rangeString
  | _ => none

/-- These five entity-parameter operators share field/star gates, then their own category,
interval, type and value-validation checks. Raw Length is a later rule gate, not an operand
failure (CheckFeldOpImpl; CheckFeldOpMitParamsImpl; ParserService; spec/06 Part A). -/
def rawScalarType (operator : RawScalarOperator) (reference : Reference)
    (entity : Sum FlatFieldDecl GroupPath) (bounds : Option (Nat × Nat)) : Lowering NumericOperandType := do
  let .inl declaration := entity | refuse "Having" KernelStaticDiagnostic.noGroupsAllowed.kernelCode
  if reference.path.segments.any (·.star) then refuse "Having" KernelStaticDiagnostic.noWildcardsAllowed.kernelCode
  if operator != .asNumber && reference.category.isSome then refuse "Having" KernelStaticDiagnostic.categoryNotAllowed.kernelCode
  match operator with
  | .length =>
      if declaration.policy.kind != .string then refuse "Having" KernelStaticDiagnostic.noString.kernelCode
      pure (.number (.field 0))
  | .asString =>
      let .number _ := declaration.policy.kind | refuse "Having" KernelStaticDiagnostic.noNumber.kernelCode
      pure .stringLike
  | .rangeNumber | .rangeString =>
      let some (start, finish) := bounds | refuse "Having" "range bounds"
      -- The grammar supplies unsigned digits, but the parser decodes them as Java int
      -- (CheckFeldOpMitParamsImpl). Wider numerals have no retained refusal class here.
      if start > 2147483647 || finish > 2147483647 then refuse "Having" "unsupported range bound"
      if !validStringRange start finish then refuse "Having" KernelStaticDiagnostic.invalidInterval.kernelCode
      if declaration.policy.kind != .string then refuse "Having" KernelStaticDiagnostic.invalidType.kernelCode
      if declaration.isRawString then refuse "Having" KernelStaticDiagnostic.rawTypeOperandInvalid.kernelCode
      pure (if operator == .rangeNumber then .number (.field 0) else .stringLike)
  | .asNumber =>
      if declaration.customType.isSome then refuse "Having" KernelStaticDiagnostic.noConvertInNumber.kernelCode
      match declaration.policy.kind with
      | .string =>
          if declaration.stringPatternSource != some asciiDigitsPatternSource ||
              !declaration.stringPolicy.maxLength.any (· ≤ maxFieldValueAsNumberDigits) then
            refuse "Having" KernelStaticDiagnostic.noConvertInNumber.kernelCode
          if declaration.isRawString then refuse "Having" KernelStaticDiagnostic.rawTypeOperandInvalid.kernelCode
      | .enumeration => pure ()
      | _ => refuse "Having" KernelStaticDiagnostic.noConvertInNumber.kernelCode
      let source ← (declaration.resolveFieldValueAsNumberSource
        (reference.category.map EnumerationProjectionRef.category |>.getD .stored)).mapError fun error => {
          construct := "Having", detail := error.diagnostic?.map (·.kernelCode) |>.getD "unsupported number conversion" }
      pure (.number (.field source.scale))

end A12Kernel.Dm
