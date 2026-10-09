import A12Kernel.Reference.Dm.HavingTemporalAdmission
import A12Kernel.Elaboration.ConstructedDateComponents
import A12Kernel.Elaboration.TimeComponentAdmission
import A12Kernel.Elaboration.TemporalConstructorOperand

namespace A12Kernel.Dm

def rawTemporalConstructor? : String → Option TemporalConstructor
  | "Date" => some .date
  | "Time" => some .time
  | "DateTime" => some .dateTime
  | _ => none

/-- Component children finish their own reads before the enclosing constructor checks positions
(CheckBaseDateConstructionImpl; CheckDatumKonstruktImpl; CheckTimeKonstruktImpl). -/
inductive RawConstructorComponent where
  | literal (text : String)
  | field (reference : Reference) (entity : Sum FlatFieldDecl GroupPath)
  | extractor (operator : RawTemporalExtractor)

private def constructorPosition? (constructor : TemporalConstructor) (count position : Nat) :
    Option (Sum ConstructedDateComponentPosition TimeComponentPosition) :=
  match constructor with
  | .date => (if count == 4 then [.day, .month, .century, .shortYear] else [.day, .month, .year])[position]?.map Sum.inl
  | .time => [.hour, .minute, .second][position]?.map Sum.inr
  | .dateTime => none

private def numericComponent : TemporalNumericPart → TemporalComponent
  | .date .day => .day
  | .date .month => .month
  | .date .year => .year
  | .date .quarter => .quarter
  | .time .hour => .hours
  | .time .minute => .minutes
  | .time .second => .seconds

private def hasConstructorDigitPattern (declaration : FlatFieldDecl) : Bool :=
  declaration.stringPatternSource.any fun source =>
    match declaration.stringPolicy.maxLength with
    | some width => isTemporalComponentDigitPattern width source
    | none => ["[0-9]+", "[0-9]*", "\\d+", "\\d*"].contains source

/-- Ordered raw reads already check placement. Reusing the declaration's own scope isolates the
existing Date policy predicates without constructing an executable field certificate (spec/07 §3). -/
private def constructorFieldAdmitted (model : FlatModel)
    (position : Sum ConstructedDateComponentPosition TimeComponentPosition) (declaration : FlatFieldDecl) : Bool :=
  match position with
  | .inl position =>
      declaration.toNumberField?.any (fun source => model.admitsConstructedDateNumberField position source declaration.repeatableScope) ||
      declaration.toStringValueField?.any (fun source => model.admitsConstructedDateStringField position source declaration.repeatableScope) ||
      declaration.toTemporalField?.any (fun source => declaration.toTemporalTargetPolicy?.any fun policy =>
        model.admitsConstructedDateYearField position source policy declaration.repeatableScope)
  | .inr position =>
      declaration.toNumberField?.any (model.admitsTimeNumberComponentField position) ||
      declaration.toStringValueField?.any model.admitsTimeStringComponentField

private def checkRawConstructorComponent (model : FlatModel) (constructor : TemporalConstructor)
    (count index : Nat) (source : RawConstructorComponent) : Lowering Unit := do
  let some position := constructorPosition? constructor count index | refuse "Having" "constructor position"
  match source with
  | .literal text =>
      let admitted := match position with
        | .inl date => (date.decodeConstant? text).isSome
        | .inr time => (time.decodeConstant? text).isSome
      if !admitted then refuse "Having" KernelStaticDiagnostic.wrongDateFormatForOp.kernelCode
  | .extractor operator =>
      if constructor == .date && count == 4 && index ≥ 2 then
        refuse "Having" KernelStaticDiagnostic.extractOpNotAllowedForFourParamDateConstruct.kernelCode
      let .numeric part := operator | refuse "Having" ConstructorOperandRefusal.extractOpNotAllowed.catalogKey
      if let some fault := constructorOperandRefusal constructor index (numericComponent part) then
        refuse "Having" fault.catalogKey
  | .field reference entity =>
      let .inl declaration := entity | refuse "Having" KernelStaticDiagnostic.noGroupsAllowed.kernelCode
      if reference.path.segments.any (·.star) then refuse "Having" KernelStaticDiagnostic.noWildcardsAllowed.kernelCode
      if declaration.policy.kind == .string && declaration.customType.isNone && !declaration.stringExtensibleEnum &&
          !hasConstructorDigitPattern declaration then refuse "Having" KernelStaticDiagnostic.noDigitPattern.kernelCode
      if reference.category.isSome then refuse "Having" KernelStaticDiagnostic.categoryNotAllowed.kernelCode
      if !constructorFieldAdmitted model position declaration then refuse "Having" KernelStaticDiagnostic.wrongDateFormatForOp.kernelCode

def rawComponentConstructorType (model : FlatModel) (constructor : TemporalConstructor)
    (sources : List RawConstructorComponent) : Lowering NumericOperandType := do
  -- CheckDatumKonstruktImpl checks day and month before consulting the model Base Year.
  if constructor == .dateTime || !operandCountAdmitted constructor sources.length true then
    refuse "Having" "component constructor arity"
  for (source, index) in sources.zipIdx do
    checkRawConstructorComponent model constructor sources.length index source
  if !operandCountAdmitted constructor sources.length model.hasBaseYear then
    refuse "Having" KernelStaticDiagnostic.missingYear.kernelCode
  if constructor == .time then pure (.temporal .time .time)
  else pure (.temporal .date (if sources.length == 2 then TemporalComponents.ofFormat "MM-dd" else .fullDate))

def rawDateTimeConstructorType (model : FlatModel) (date : NumericOperandType)
    (direct : Option FlatFieldDecl) (time : NumericOperandType) : Lowering NumericOperandType := do
  let .temporal _ date := date | refuse "Having" KernelStaticDiagnostic.invalidDateForOp.kernelCode
  let .temporal _ time := time | refuse "Having" KernelStaticDiagnostic.invalidDateForOp.kernelCode
  if !temporalYearPresenceAgrees model.hasBaseYear date .fullDate || !date.hasDate || date.hasTime then
    refuse "Having" KernelStaticDiagnostic.wrongDateFormatForOp.kernelCode
  if direct.any (fun declaration => declaration.toTemporalTargetPolicy?.any (·.partialMode != .full)) then
    refuse "Having" KernelStaticDiagnostic.invalidDateType.kernelCode
  if time.hasDate || !time.hasTime then refuse "Having" KernelStaticDiagnostic.wrongDateFormatForOp.kernelCode
  pure (.temporal .dateTime .now)

/-- DateRange endpoints are bare entity reads. Both reads precede field/star/precision checks,
and BaseYear never supplements component agreement (CheckDatumBereichKonstruktImpl; spec/05 §8). -/
def rawDateRangeConstructorType (sources : List (Reference × Sum FlatFieldDecl GroupPath)) :
    Lowering NumericOperandType := do
  let components ← sources.mapM fun (reference, entity) => do
    let .inl declaration := entity | refuse "Having" KernelStaticDiagnostic.noGroupsAllowed.kernelCode
    if reference.path.segments.any (·.star) then refuse "Having" KernelStaticDiagnostic.noWildcardsAllowed.kernelCode
    let some policy := declaration.toTemporalTargetPolicy? |
      refuse "Having" KernelStaticDiagnostic.wrongDateFormatForOp.kernelCode
    let components := TemporalComponents.ofFormat policy.format
    if policy.partialMode != .full || !components.hasDate || components.hasTime then
      refuse "Having" KernelStaticDiagnostic.wrongDateFormatForOp.kernelCode
    pure components
  let [first, second] := components | refuse "Having" "DateRange endpoints"
  if first != second then refuse "Having" KernelStaticDiagnostic.wrongDateFormatForOp.kernelCode
  pure (.dateRange first)

end A12Kernel.Dm
