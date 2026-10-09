import A12Kernel.Reference.Dm.LowerCore
import A12Kernel.Elaboration.HavingNumericAtom
import A12Kernel.Elaboration.NumericComputation.OperationTyping
import A12Kernel.Elaboration.TemporalExtractorEntry

namespace A12Kernel.Dm

inductive RawTemporalExtractor where
  | numeric (part : TemporalNumericPart)
  | dateFromDateTime
  | timeFromDateTime

def rawTemporalExtractor? (name : String) : Option RawTemporalExtractor :=
  if let some part := datePart? name then some (.numeric (.date part))
  else if let some part := timePart? name then some (.numeric (.time part))
  else match name with
    | "DateFromDateTime" => some .dateFromDateTime
    | "TimeFromDateTime" => some .timeFromDateTime
    | _ => none

inductive RawTemporalArithmetic where
  | shift (unit : TemporalOperationUnit)
  | difference (unit : TemporalOperationUnit)

def rawTemporalArithmetic? : String → Option RawTemporalArithmetic
  | "AddDays" => some (.shift .days)
  | "AddMonths" => some (.shift .months)
  | "AddYears" => some (.shift .years)
  | "AddHours" => some (.shift .hours)
  | "AddMinutes" => some (.shift .minutes)
  | "AddSeconds" => some (.shift .seconds)
  | "DifferenceInDays" => some (.difference .days)
  | "DifferenceInMonths" => some (.difference .months)
  | "DifferenceInYears" => some (.difference .years)
  | "DifferenceInHours" => some (.difference .hours)
  | "DifferenceInMinutes" => some (.difference .minutes)
  | "DifferenceInSeconds" => some (.difference .seconds)
  | _ => none

def isRawRangeBound (name : String) : Bool := name == "StartOfDateRange" || name == "EndOfDateRange"

private def rawTemporalSpecialField (reference : Reference) (entity : Sum FlatFieldDecl GroupPath) :
    Lowering FlatFieldDecl := do
  let .inl declaration := entity | refuse "Having" KernelStaticDiagnostic.noGroupsAllowed.kernelCode
  if reference.path.segments.any (·.star) then refuse "Having" KernelStaticDiagnostic.noWildcardsAllowed.kernelCode
  if reference.category.isSome then refuse "Having" KernelStaticDiagnostic.categoryNotAllowed.kernelCode
  pure declaration

def rawRangeBoundType (reference : Reference) (entity : Sum FlatFieldDecl GroupPath) : Lowering NumericOperandType := do
  let declaration ← rawTemporalSpecialField reference entity
  let some policy := declaration.toDateRangeDeclarationPolicy? | refuse "Having" KernelStaticDiagnostic.noDateRange.kernelCode
  let components := if policy.interpretationOfYear.isSome then TemporalComponents.fullDate
    else TemporalComponents.ofFormat policy.format
  pure (.temporal .date components)

def rawValueAsDateType (reference : Reference) (entity : Sum FlatFieldDecl GroupPath) : Lowering NumericOperandType := do
  let declaration ← rawTemporalSpecialField reference entity
  if !declaration.toTemporalTargetPolicy?.any (·.partialMode != .full) then
    refuse "Having" KernelStaticDiagnostic.invalidDateTypeForOp.kernelCode
  pure (.temporal .date .fullDate)

def rawTemporalField (reference : Reference) (entity : Sum FlatFieldDecl GroupPath) :
    Lowering (NumericOperandType × FlatFieldDecl) := do
  if reference.category.isSome then refuse "Having" KernelStaticDiagnostic.categoryNotAllowed.kernelCode
  let .inl declaration := entity | refuse "Having" KernelStaticDiagnostic.noGroupsAllowed.kernelCode
  if reference.path.segments.any (·.star) then refuse "Having" KernelStaticDiagnostic.noWildcardsAllowed.kernelCode
  let .temporal kind components := declaration.policy.kind | refuse "Having" KernelStaticDiagnostic.noDate.kernelCode
  pure (.temporal kind components, declaration)

def rawTemporalLiteral (text : String) : Lowering NumericOperandType :=
  if (civilDateConstant? text).isSome then pure (.temporal .date .fullDate)
  else if (yearlessDateConstant? text).isSome then pure (.temporal .date (TemporalComponents.ofFormat "MM-dd"))
  else if (timeConstant? text).isSome then pure (.temporal .time .time)
  else if (dateTimeConstant? text).isSome then pure (.temporal .dateTime .now)
  else refuse "Having" KernelStaticDiagnostic.invalidDateString.kernelCode

/-- The temporal source closes before the extractor's precision/literal/format gates
(CheckDatumAngabeImpl, CheckDatumExtractOpImpl; spec/05 §3). A bare entity retains its
partial policy; an inner temporal operation contributes only its resulting component set. -/
def rawTemporalExtractorType (model : FlatModel) (operator : RawTemporalExtractor)
    (source : NumericOperandType) (literal : Bool) (direct : Option FlatFieldDecl) :
    Lowering NumericOperandType := do
  let .temporal kind components := source | refuse "Having" KernelStaticDiagnostic.invalidDateForOp.kernelCode
  let family := match operator with
    | .numeric _ => TemporalExtractorFamily.numeric
    | .dateFromDateTime => .dateFromDateTime
    | .timeFromDateTime => .timeFromDateTime
  if let .numeric part := operator then
    if direct.any (fun declaration => !declaration.admitsHavingTemporalPartPrecision part) then
      refuse "Having" KernelStaticDiagnostic.invalidDateType.kernelCode
  match checkTemporalExtractorEntry family (if literal then .literal (some kind) else .nonliteral) with
  | .error diagnostic => refuse "Having" diagnostic.kernelCode
  | .ok _ => pure ()
  match operator with
  | .numeric part =>
      if !part.admitsComponents components model.hasBaseYear then
        refuse "Having" KernelStaticDiagnostic.wrongDateFormatForOp.kernelCode
      pure (.number (.field 0))
  | .dateFromDateTime | .timeFromDateTime =>
      if !components.isFullDateTime then refuse "Having" KernelStaticDiagnostic.wrongDateFormatForOp.kernelCode
      match operator with
      | .dateFromDateTime => pure (.temporal .date .fullDate)
      | _ => pure (.temporal .time .time)

/-- Parent temporal arithmetic gates run after all child reads; precision for either direct
field precedes component checks for either source (CheckDatumAddOpImpl/CheckDatumDiffOpImpl,
spec/05 §2). Completed ValueAsDate and range endpoints no longer carry a direct partial policy. -/
private def checkRawTemporalArithmetic (model : FlatModel) (unit : TemporalOperationUnit)
    (sources : List (NumericOperandType × Option FlatFieldDecl)) : Lowering (List TemporalComponents) := do
  if sources.any (fun (_, declaration) => declaration.any fun field =>
      field.toTemporalTargetPolicy?.any (·.partialMode != .full)) then
    refuse "Having" KernelStaticDiagnostic.invalidDateType.kernelCode
  let components ← sources.mapM fun (type, _) => match type with
    | .temporal _ components => pure components
    | _ => refuse "Having" KernelStaticDiagnostic.invalidDateForOp.kernelCode
  if !components.all (unit.operandResolves model.hasBaseYear) then
    refuse "Having" KernelStaticDiagnostic.wrongDateFormatForOp.kernelCode
  if !components.all (·.hasDate) then refuse "Having" KernelStaticDiagnostic.invalidTime.kernelCode
  if (unit == .months || unit == .years) && components.any (·.hasTime) then
    refuse "Having" KernelStaticDiagnostic.wrongDateFormatForOp.kernelCode
  pure components

def rawTemporalShiftType (model : FlatModel) (unit : TemporalOperationUnit)
    (source : NumericOperandType) (direct : Option FlatFieldDecl) (amount : NumericOperandType) :
    Lowering NumericOperandType := do
  discard <| checkRawTemporalArithmetic model unit [(source, direct)]
  let .number _ := amount | refuse "Having" KernelStaticDiagnostic.nonNumeric.kernelCode
  pure source

def rawTemporalDifferenceType (model : FlatModel) (unit : TemporalOperationUnit)
    (left right : NumericOperandType × Option FlatFieldDecl) : Lowering NumericOperandType := do
  let [first, second] ← checkRawTemporalArithmetic model unit [left, right] | refuse "Having" "difference sources"
  if !temporalYearPresenceAgrees model.hasBaseYear first second then
    refuse "Having" KernelStaticDiagnostic.dateWithAndWithoutYear.kernelCode
  pure (.number (.field 0))

end A12Kernel.Dm
