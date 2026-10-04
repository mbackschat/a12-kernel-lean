import A12Kernel.Reference.Dm.LowerString
import A12Kernel.Reference.Dm.LowerCore
import A12Kernel.Reference.Dm.LowerEntity
import A12Kernel.Reference.Dm.Parser
import A12Kernel.Elaboration.MixedComputationPlan

/-! # Lowering a computation into a repeatable target of a kind other than Number

A row target computes one value per instantiated row, so its operation is lowered onto the row step
of the carrier that operation names. A constant is placed by its literal's shape, Boolean and Confirm
by `True` and `False`; `FieldValueAsString`, `DateFromDateTime` and the `Time(...)` construction each
have one addressed carrier, and `FirstFilledValue` the one carrier per kind that also serves a fixed
target, a temporal target's chosen by its profile. Each carrier owns its target's
admission, its sources' placement and its refusal of a read of its own target, so the reader only
names it; the step's certificate that it excludes its target restates what the carrier ensures.
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
      match authoredDateLiteral? literal, timeConstant? literal, dateTimeConstant? literal with
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
          let operation ← elaborated "StringComputation"
            (checkRepeatableStringConstantComputation model group target.id literal)
          pure fun _ => .ofRepeatableStringConstant operation
  | other => refuse "RowComputation" other.construct
where
  boolean (value : Bool) : Lowering (RowStep model) := do
    let operation ← elaborated "BooleanComputation"
      (checkRepeatableBooleanConstantComputation model group target.id value)
    pure fun _ => .ofRepeatableBooleanConstant operation

/-- Ordinary String expressions, Boolean/Confirm constants and Enumeration reads share row-local alternative selection.
Temporal literal classification stays with `rowConstant`, whose family gate precedes the target kind. -/
def isRowAlternativeOperation (target : FlatFieldDecl) (expression : Expr) : Bool :=
  if target.policy.kind == .string && (lowerStringExpr expression).isOk then true else
  match expression with
  | .constant "True" | .constant "False" => target.policy.kind == .boolean || target.policy.kind == .confirm
  | .string text => !isTemporalConstant text
  | .value { index := none, .. } => target.policy.kind == .enumeration
  | _ => false

/-- Retain each admitted operation certificate before certifying row-local selection. -/
def lowerRowAlternativeOperation (model : FlatModel) (group : GroupPath) (target : FlatFieldDecl)
    (expression : Expr) : Lowering (CheckedRowComputationOperation model) := do
  if target.policy.kind == .string then
    return .stringExpression (← elaborated "StringExpression"
      (elaborateRowStringExpression model group target.id (← lowerStringExpr expression)))
  match expression with
  | .constant "True" | .constant "False" =>
      pure (.booleanConstant (← elaborated "BooleanComputation"
        (checkRepeatableBooleanConstantComputation model group target.id (expression == .constant "True"))))
  | .string text => do
      if isTemporalConstant text then refuse "RowComputation" "temporal literal"
      if target.policy.kind == .enumeration then
        return .enumeration (← elaborated "EnumerationComputation"
          (checkAddressedEnumerationComputation model group target.id (.literal text)))
      return .stringConstant (← elaborated "StringComputation"
        (checkRepeatableStringConstantComputation model group target.id text))
  | .value { path, index := none, category } => do
      let some field := path.toFieldPath? | refuse "EnumerationComputation" "source path"
      let source := match category with
        | none => SurfaceTextFieldOperand.direct field
        | some name => .category field name
      return .enumeration (← elaborated "EnumerationComputation"
        (checkAddressedEnumerationComputation model group target.id (.field source)))
  | other => refuse "RowComputation" other.construct

/-- One `Time(...)` component: a quoted constant, an extractor over a field, or a Number or digit
String field. -/
private def timeComponent (model : FlatModel) (group : GroupPath) :
    Argument → Lowering SurfaceAddressedWorldTimeComponent
  | .mk (.string text) none none => pure (.addressed (.constant text))
  | .mk (.call id [.mk field none none] none none) none none => do
      let part ← match id with
        | "HoursFromTime" => pure TimeNumericPart.hour
        | "MinutesFromTime" => pure .minute
        | "SecondsFromTime" => pure .second
        | _ => refuse "Time" id
      let some path := field.fieldEntity? | refuse "Time" "extractor operand"
      pure (.addressed (.extractor part path))
  | .mk expr none none => do
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
    (arguments : List Argument) : Lowering (RowStep model) := do
  if target.policy.kind == .string && target.customType.isNone then
    return ← stepOf "FirstFilledValue" (CheckedRowComputationStep.ofStringFirstFilled?
      (← elaborated "FirstFilledValue" (checkStringFirstFilledComputation model group target.id
        (← lowerEntitySource model group arguments))))
  if target.policy.kind == .enumeration then
    return ← stepOf "FirstFilledValue" (CheckedRowComputationStep.ofAddressedEnumerationFirstFilled?
      (← elaborated "FirstFilledValue" (checkAddressedEnumerationFirstFilledComputation model group
        target.id (← lowerEnumerationFirstFilledSource model group arguments))))
  let star ← match arguments with
    | [.mk (.entity { path, index := none, category := none }) none none] =>
        match path.segments.any (·.star), path.toStarFieldPath? with
        | true, some star => pure star
        | _, _ => refuse "FirstFilledValue" "row source"
    | _ => refuse "FirstFilledValue" "row source"
  if target.customType.isSome then
    return ← stepOf "FirstFilledValue" (CheckedRowComputationStep.ofCustomFirstFilled?
      (← elaborated "FirstFilledValue" (checkCustomFirstFilledComputation model group target.id (.star star))))
  match target.temporalFirstFilledFamily?, target.policy.kind with
  | some .time, _ => do
      stepOf "FirstFilledValue" (CheckedRowComputationStep.ofTimeFirstFilled?
        (← elaborated "FirstFilledValue" (checkTimeFirstFilledComputation model group target.id (.star star))))
  | some .dateTime, _ => do
      stepOf "FirstFilledValue" (CheckedRowComputationStep.ofDateTimeFirstFilled?
        (← elaborated "FirstFilledValue" (checkDateTimeFirstFilledComputation model group target.id (.star star))))
  | some .dateFragment, _ => do
      stepOf "FirstFilledValue" (CheckedRowComputationStep.ofDateFragmentFirstFilled?
        (← elaborated "FirstFilledValue" (checkDateFragmentFirstFilledComputation model group target.id
          (.star star))))
  | some .fullDate, _ => do
      stepOf "FirstFilledValue" (CheckedRowComputationStep.ofFullDateFirstFilled?
        (← elaborated "FirstFilledValue" (checkFullDateFirstFilledComputation model group target.id (.star star))))
  | some .dateRange, _ => do
      stepOf "FirstFilledValue" (CheckedRowComputationStep.ofDateRangeFirstFilled?
        (← elaborated "FirstFilledValue" (checkDateRangeFirstFilledComputation model group target.id star)))
  | none, .boolean => do
      stepOf "FirstFilledValue" (CheckedRowComputationStep.ofBooleanFirstFilled?
        (← elaborated "FirstFilledValue" (checkBooleanFirstFilledComputation model group target.id (.star star))))
  | none, _ => refuse "FirstFilledValue" "row target kind"

/-- The row step one unguarded operation into a repeatable target names. -/
def lowerRowStep (model : FlatModel) (group : GroupPath) (target : FlatFieldDecl) :
    Expr → Lowering (RowStep model)
  | .call "FieldValueAsString" [.mk source none none] none none => do
      let some path := source.fieldEntity? | refuse "FieldValueAsString" "operand"
      stepOf "FieldValueAsString" (CheckedRowComputationStep.ofAddressedFieldValueAsString?
        (← elaborated "FieldValueAsString" (checkAddressedFieldValueAsString model group target.id path)))
  | .call "FirstFilledValue" arguments none none => firstFilledRow model group target arguments
  | .call "DateFromDateTime" [.mk source none none] none none => do
      let some path := source.fieldEntity? | refuse "DateFromDateTime" "operand"
      stepOf "DateFromDateTime" (CheckedRowComputationStep.ofAddressedDateFromDateTime?
        (← elaborated "DateFromDateTime" (checkAddressedDateFromDateTime model group target.id path)))
  | .call "Time" arguments none none => do
      let components ← timeComponents model group arguments
      stepOf "Time" (CheckedRowComputationStep.ofAddressedTimeConstruction?
        (← elaborated "Time" (checkAddressedWorldTimeConstructionComputation model group target.id components)))
  | other => rowConstant model group target other

end A12Kernel.Dm
