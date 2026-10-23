import A12Kernel.Reference.Dm.LowerScalarTemporal
import A12Kernel.Reference.Dm.LowerString
import A12Kernel.Reference.Dm.LowerCore
import A12Kernel.Reference.Dm.LowerEntity
import A12Kernel.Reference.Dm.Parser
import A12Kernel.Elaboration.MixedComputationPlan

/-! # Lowering addressed non-Number computations

Target-instance tables share guarded selection for fixed and repeated temporal expressions,
Boolean/Confirm constants, bound String expressions and Enumeration operations. Temporal trees
use declaration-owned projection and read-back. Specialized field forms and `FirstFilledValue`
keep their existing carriers; each carrier owns source placement and target exclusion.
-/

namespace A12Kernel.Dm

/-- A row step for every pattern compiler, which the plan fixes when it assembles its steps. -/
abbrev RowStep (model : FlatModel) := ∀ compilePattern, CheckedRowComputationStep model compilePattern

/-- Turn one carrier's optional step into a lowering, refusing the read of its own target. -/
private def stepOf (construct : String) : Option (RowStep model) → Lowering (RowStep model)
  | some step => pure step
  | none => refuse construct "target self-read"

/-- A constant written into every row, by the carrier its literal's shape selects; the carrier owns
the target's admission, so a literal of one family into a target declared of another meets that
carrier's own gate. -/
def rowConstant (model : FlatModel) (group : GroupPath) (target : FlatFieldDecl) :
    Expr → Lowering (RowStep model)
  | .constant "True" => boolean true
  | .constant "False" => boolean false
  | .string literal =>
      match authoredDateLiteral? literal, timeConstant? literal, (dateTimeConstant? literal).bind (·.toLocal?) with
      | some date, _, _ => do
          let operation ← elaborated "DateComputation"
            (checkDateLiteralComputation model group target.id date)
          (CheckedRowComputationStep.ofDateLiteral? operation).getDM
            (refuse "DateComputation" "fixed target")
      | _, some time, _ => do
          let operation ← elaborated "TimeComputation"
            (checkRepeatableTimeConstantComputation model group target.id time)
          pure fun _ => .ofRepeatableTimeConstant operation
      | _, _, some label => do
          let operation ← elaborated "DateTimeComputation"
            (checkRepeatableDateTimeConstantComputation model group target.id label)
          -- The label is the same at every row, so one the model zone cannot resolve is known here.
          if operation.outcome?.isNone then refuse "DateTimeComputation" "label in a zone gap"
          pure fun _ => .ofRepeatableDateTimeConstant operation
      | none, none, none => do
          if isDateTimeConstant literal then refuse "DateTimeComputation" "label before the value floor"
          let operation ← elaborated "StringComputation"
            (checkRepeatableStringConstantComputation model group target.id literal)
          pure fun _ => .ofRepeatableStringConstant operation
  | other => refuse "RowComputation" other.construct
where
  boolean (value : Bool) : Lowering (RowStep model) := do
    let operation ← elaborated "BooleanComputation"
      (checkRepeatableBooleanConstantComputation model group target.id value)
    pure fun _ => .ofRepeatableBooleanConstant operation

/-- Temporal target profiles select expression projection; other kinds retain their established
carrier choice. FirstFilledValue and bare Date literals keep their entity-stream and year-presence gates. -/
def isRowAlternativeOperation (model : FlatModel) (group : GroupPath) (target : FlatFieldDecl) (expression : Expr) : Bool :=
  if let .call "FirstFilledValue" _ none none := expression then
    target.customType.isNone && (target.policy.kind == .string || target.policy.kind == .enumeration ||
      target.policy.kind == .boolean || target.policy.kind == .dateRange ||
      (target.temporalFirstFilledFamily?.any fun family => match family with
        | .time | .dateTime | .fullDate | .dateRange => true | .dateFragment => false))
  else if target.policy.kind == .dateRange then
    match expression with
    | .call "DateRange" [_, _] none none | .value { index := none, category := none, filter := none, .. } => true
    | _ => false
  else if target.temporalTargetPolicy.isSome then
    match expression with
    | .call "FirstFilledValue" _ _ _ => false
    | _ => true
  else if target.policy.kind == .string && (lowerSelectedStringExpr model group expression).isOk then true else
  match expression with
  | .constant "True" | .constant "False" => target.policy.kind == .boolean || target.policy.kind == .confirm
  | .string text => !isTemporalConstant text
  | .value { index := none, filter := none, .. } => target.policy.kind == .enumeration || target.policy.kind == .boolean || target.policy.kind == .confirm
  | .value { path, index := some _, filter := none, .. } =>
      target.policy.kind == .enumeration && !path.segments.any (·.star)
  | _ => false

private def lowerEnumerationAlternative (model : FlatModel) (group : GroupPath)
    (target : FlatFieldDecl) (source : SurfaceEnumerationComputationSource) :
    Lowering (CheckedRowComputationOperation model) := do
  if target.repeatableScope.isEmpty then
    pure (.fixedEnumeration (← elaborated "EnumerationComputation"
      (elaborateEnumerationComputation model group target.id source)))
  else
    pure (.enumeration (← elaborated "EnumerationComputation"
      (checkAddressedEnumerationComputation model group target.id source)))

/-- `arity := .soleAllowed` lowers a keyed column read, with or without a category, into an
Enumeration target as the one-operand scan: the Kernel clears that target on a missing or duplicated
key or a formally invalid selected cell exactly as the scan does ([checkpoint](../../../docs/sources/model-structure-and-declaration-probes.md#src-semantic-index-reads)). -/
private def lowerFirstFilledAlternative (model : FlatModel) (group : GroupPath) (target : FlatFieldDecl)
    (arguments : List Argument) (arity : EntityListArity := .manyRequired) (suppress : Bool := false) :
    Lowering (CheckedFirstFilledAlternative model) := do
  let bindingGroup? := if arguments.any Argument.hasHaving then some target.groupPath else none
  if target.policy.kind == .string && target.customType.isNone then
    return .string (← elaborated "FirstFilledValue" (checkStringFirstFilledComputation model group target.id
      (← lowerFirstFilledEntitySource model group arguments bindingGroup? suppress)))
  if target.policy.kind == .enumeration then
    let source ← lowerEnumerationFirstFilledSource model group arguments bindingGroup? suppress
    if hFixed : target.repeatableScope = [] then
      let operation ← elaboratedEnumerationFirstFilled (·.calculationRefusal?)
        (elaborateEnumerationFirstFilledComputation model group target.id source arity)
      if hField : target.id = operation.target.field then
        return .fixedEnumeration operation target hField hFixed
      else refuse "FirstFilledValue" "target identity"
    else
      return .addressedEnumeration (← elaboratedEnumerationFirstFilled (·.calculationRefusal?)
        (checkAddressedEnumerationFirstFilledComputation model group target.id source arity))
  let source ← lowerFirstFilledSource model group arguments bindingGroup? suppress
  match target.temporalFirstFilledFamily?, target.policy.kind with
  | some .time, _ =>
      pure (.time (← elaborated "FirstFilledValue" (checkTimeFirstFilledComputation model group target.id source)))
  | some .dateTime, _ =>
      pure (.dateTime (← elaborated "FirstFilledValue" (checkDateTimeFirstFilledComputation model group target.id source)))
  | some .fullDate, _ =>
      pure (.fullDate (← elaborated "FirstFilledValue" (checkFullDateFirstFilledComputation model group target.id source)))
  | some .dateRange, _ => do
      if target.repeatableScope.isEmpty then
        if let .list list := source then
          if !(list.first :: list.rest).any (fun | .field .. => false | _ => true) then
            return .directDateRange (← elaborated "FirstFilledValue"
              (checkDateRangeFirstFilledDirectComputation model group target.id list))
      pure (.dateRange (← elaborated "FirstFilledValue" (checkDateRangeFirstFilledSourceComputation model group target.id source)))
  | none, .boolean =>
      pure (.boolean (← elaborated "FirstFilledValue" (checkBooleanFirstFilledComputation model group target.id source)))
  | _, _ => refuse "FirstFilledValue" "target kind"

/-- Retain each admitted operation certificate before certifying row-local selection. -/
def lowerRowAlternativeOperation (model : FlatModel) (group : GroupPath) (target : FlatFieldDecl)
    (expression : Expr) (suppress : Bool := false) : Lowering (CheckedRowComputationOperation model) := do
  if let .call "FirstFilledValue" arguments none none := expression then
    return .firstFilled (← lowerFirstFilledAlternative model group target arguments (suppress := suppress))
  if target.policy.kind == .enumeration then
    if let .value reference@{ index := some _, filter := none, .. } := expression then
      -- Only a keyed column is a scalar read; a keyed star or group assigned directly draws
      -- `MVK_NO_WILDCARDS_ALLOWED` (`e5`, `e6` of the semantic-index checkpoint).
      let .indexed _ _ ← lowerEntityOperand model group (.mk (.entity reference) none)
        | refuse "EnumerationComputation" "keyed extent"
      return .firstFilled (← lowerFirstFilledAlternative model group target
        [.mk (.entity reference) none] (arity := .soleAllowed) (suppress := suppress))
  if target.policy.kind == .boolean || target.policy.kind == .confirm || target.policy.kind == .dateRange then
    if let .value { path, index := none, category := none, filter := none } := expression then
      let some source := path.toFieldPath? | refuse "ScalarCopy" "source path"
      return .scalarCopy (← elaborated "ScalarCopy" (checkScalarCopyComputation model group target.id source))
  if target.policy.kind == .dateRange then
    let .call "DateRange" [.mk start none, .mk finish none] none none := expression
      | refuse "DateRange" "constructor operands"
    let start ← lowerDateRangeEndpoint model group start
    let finish ← lowerDateRangeEndpoint model group finish
    return .dateRangeConstruction (← elaborated "DateRange"
      (checkBoundDateRangeConstructionSources model group target.id start finish))
  if target.temporalTargetPolicy.isSome then
    if let .string literal := expression then
      if let some source := authoredDateLiteral? literal then
        return .dateLiteral (← elaborated "DateComputation"
          (checkDateLiteralComputation model group target.id source))
    let surface ← lowerScalarTemporalExpression model group expression suppress
    let checked ← elaborated "TemporalExpression"
      (elaborateScalarTemporalExpression model group surface (some target.groupPath))
    let operation ← (checkTemporalExpressionComputation? checked target.id).getDM
      (refuse "TemporalExpression" "target, binding or dependency")
    return .temporalExpression operation
  if target.policy.kind == .string then
    return .stringExpression (← elaborated "StringExpression"
      (elaborateSelectedRowStringExpression model group target.id (← lowerSelectedStringExpr model group expression)))
  match expression with
  | .constant "True" | .constant "False" =>
      if target.repeatableScope.isEmpty then
        pure (.fixedBooleanConstant (← elaborated "BooleanComputation"
          (checkBooleanConstantComputation model group target.id (expression == .constant "True"))))
      else
        pure (.booleanConstant (← elaborated "BooleanComputation"
          (checkRepeatableBooleanConstantComputation model group target.id (expression == .constant "True"))))
  | .string text => do
      if isTemporalConstant text then refuse "RowComputation" "temporal literal"
      if target.policy.kind == .enumeration then
        return ← lowerEnumerationAlternative model group target (.literal text)
      return .stringConstant (← elaborated "StringComputation"
        (checkRepeatableStringConstantComputation model group target.id text))
  | .value { path, index := none, category, filter := none } => do
      let some field := path.toFieldPath? | refuse "EnumerationComputation" "source path"
      let source := match category with
        | none => SurfaceTextFieldOperand.direct field
        | some name => .category field name
      return ← lowerEnumerationAlternative model group target (.field source)
  | other => refuse "RowComputation" other.construct

/-- One `Time(...)` component: a quoted constant, an extractor over a field, or a Number or digit
String field. -/
private def timeComponent (model : FlatModel) (group : GroupPath) :
    Argument → Lowering SurfaceAddressedWorldTimeComponent
  | .mk (.string text) none => pure (.addressed (.constant text))
  | .mk (.call id [.mk field none] none none) none => do
      let part ← match id with
        | "HoursFromTime" => pure TimeNumericPart.hour
        | "MinutesFromTime" => pure .minute
        | "SecondsFromTime" => pure .second
        | _ => refuse "Time" id
      let some path := field.fieldEntity? | refuse "Time" "extractor operand"
      pure (.addressed (.extractor part path))
  | .mk expr none => do
      let some path := expr.fieldEntity? | refuse "Time" "component"
      let declaration ← elaborated "Time" (model.resolveFieldDeclarationUnchecked group path)
      match declaration.policy.kind.surfaceKind with
      | .number => pure (.addressed (.number path))
      | .string => pure (.addressed (.string path))
      | _ => refuse "Time" "component kind"
  | _ => refuse "Time" "component"

private def timeComponents (model : FlatModel) (group : GroupPath) :
    List Argument → Lowering SurfaceAddressedWorldTimeComponents
  | [] => pure .empty
  | [hour] => do pure (.hour (← timeComponent model group hour))
  | [hour, minute] => do
      pure (.minute (← timeComponent model group hour) (← timeComponent model group minute))
  | [hour, minute, second] => do
      pure (.second (← timeComponent model group hour) (← timeComponent model group minute)
        (← timeComponent model group second))
  | _ => refuse "Time" "arity"

/-- `FirstFilledValue` onto the carrier of the target's kind: a String one over any entity list,
the others over one sibling star. -/
private def firstFilledRow (model : FlatModel) (group : GroupPath) (target : FlatFieldDecl)
    (arguments : List Argument) (suppress : Bool) : Lowering (RowStep model) := do
  let bindingGroup? := if arguments.any Argument.hasHaving then some target.groupPath else none
  if target.policy.kind == .string && target.customType.isNone then
    return ← stepOf "FirstFilledValue" (CheckedRowComputationStep.ofStringFirstFilled?
      (← elaborated "FirstFilledValue" (checkStringFirstFilledComputation model group target.id
        (← lowerFirstFilledEntitySource model group arguments bindingGroup? suppress))))
  if target.policy.kind == .enumeration then
    return ← stepOf "FirstFilledValue" (CheckedRowComputationStep.ofAddressedEnumerationFirstFilled?
      (← elaboratedEnumerationFirstFilled (·.calculationRefusal?) (checkAddressedEnumerationFirstFilledComputation model group
        target.id (← lowerEnumerationFirstFilledSource model group arguments bindingGroup? suppress))))
  let source ← lowerFirstFilledSource model group arguments bindingGroup? suppress
  if target.customType.isSome then
    return ← stepOf "FirstFilledValue" (CheckedRowComputationStep.ofCustomFirstFilled?
      (← elaborated "FirstFilledValue" (checkCustomFirstFilledComputation model group target.id source)))
  match target.temporalFirstFilledFamily?, target.policy.kind with
  | some .time, _ => do
      stepOf "FirstFilledValue" (CheckedRowComputationStep.ofTimeFirstFilled?
        (← elaborated "FirstFilledValue" (checkTimeFirstFilledComputation model group target.id source)))
  | some .dateTime, _ => do
      stepOf "FirstFilledValue" (CheckedRowComputationStep.ofDateTimeFirstFilled?
        (← elaborated "FirstFilledValue" (checkDateTimeFirstFilledComputation model group target.id source)))
  | some .dateFragment, _ | some .fullDate, _ => do
      stepOf "FirstFilledValue" (CheckedRowComputationStep.ofFullDateFirstFilled?
        (← elaborated "FirstFilledValue" (checkFullDateFirstFilledComputation model group target.id source)))
  | some .dateRange, _ => do
      stepOf "FirstFilledValue" (CheckedRowComputationStep.ofDateRangeFirstFilled?
        (← elaborated "FirstFilledValue" (checkDateRangeFirstFilledSourceComputation model group target.id source)))
  | none, .boolean => do
      stepOf "FirstFilledValue" (CheckedRowComputationStep.ofBooleanFirstFilled?
        (← elaborated "FirstFilledValue" (checkBooleanFirstFilledComputation model group target.id source)))
  | none, _ => refuse "FirstFilledValue" "row target kind"

/-- The row step one unguarded operation into a repeatable target names. -/
def lowerRowStep (model : FlatModel) (group : GroupPath) (target : FlatFieldDecl) (suppress : Bool := false) :
    Expr → Lowering (RowStep model)
  | .call "FieldValueAsString" [.mk source none] none none => do
      let some path := source.fieldEntity? | refuse "FieldValueAsString" "operand"
      stepOf "FieldValueAsString" (CheckedRowComputationStep.ofAddressedFieldValueAsString?
        (← elaborated "FieldValueAsString" (checkAddressedFieldValueAsString model group target.id path)))
  | .call "FirstFilledValue" arguments none none => firstFilledRow model group target arguments suppress
  | .call "DateFromDateTime" [.mk source none] none none => do
      let some path := source.fieldEntity? | refuse "DateFromDateTime" "operand"
      stepOf "DateFromDateTime" (CheckedRowComputationStep.ofAddressedDateFromDateTime?
        (← elaborated "DateFromDateTime" (checkAddressedDateFromDateTime model group target.id path)))
  | .call "Time" arguments none none => do
      let components ← timeComponents model group arguments
      stepOf "Time" (CheckedRowComputationStep.ofAddressedTimeConstruction?
        (← elaborated "Time" (checkAddressedWorldTimeConstructionComputation model group target.id components)))
  | other => rowConstant model group target other

end A12Kernel.Dm
