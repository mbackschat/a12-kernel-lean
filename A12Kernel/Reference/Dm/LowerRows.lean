import A12Kernel.Reference.Dm.LowerCore
import A12Kernel.Reference.Dm.Parser
import A12Kernel.Elaboration.MixedComputationPlan

/-! # Lowering a computation into a repeatable target of a kind other than Number

A row target computes one value per instantiated row, so its operation is lowered onto the row step
of the carrier that operation names. A constant is placed by its literal's shape, Boolean and Confirm
by `True` and `False`; `FieldValueAsString`, `FirstFilledValue` over one sibling star, `DateFromDateTime`
and the `Time(...)` construction each have one addressed carrier. Each carrier owns its target's
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
      match civilDateConstant? literal, timeConstant? literal, dateTimeConstant? literal with
      | some date, _, _ => do
          let operation ← elaborated "DateComputation"
            (checkRepeatableDateConstantComputation model group target.id date)
          pure fun _ => .ofRepeatableDateConstant operation
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
          -- An omitted-year date has no row carrier, and is no String constant.
          if isTemporalConstant literal then refuse "DateComputation" "omitted-year constant"
          let operation ← elaborated "StringComputation"
            (checkRepeatableStringConstantComputation model group target.id literal)
          pure fun _ => .ofRepeatableStringConstant operation
  | other => refuse "RowComputation" other.construct
where
  boolean (value : Bool) : Lowering (RowStep model) := do
    let operation ← elaborated "BooleanComputation"
      (checkRepeatableBooleanConstantComputation model group target.id value)
    pure fun _ => .ofRepeatableBooleanConstant operation

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

/-- `FirstFilledValue` over one sibling star, onto the addressed carrier of the target's kind. -/
private def firstFilledRow (model : FlatModel) (group : GroupPath) (target : FlatFieldDecl)
    (star : SurfaceStarFieldPath) : Lowering (RowStep model) :=
  match target.policy.kind with
  | .string => do
      stepOf "FirstFilledValue" (CheckedRowComputationStep.ofAddressedStringFirstFilled?
        (← elaborated "FirstFilledValue" (checkAddressedStringFirstFilledComputation model group target.id star)))
  | .temporal .time _ => do
      stepOf "FirstFilledValue" (CheckedRowComputationStep.ofAddressedTimeFirstFilled?
        (← elaborated "FirstFilledValue" (checkAddressedTimeFirstFilledComputation model group target.id star)))
  | .temporal .dateTime _ => do
      stepOf "FirstFilledValue" (CheckedRowComputationStep.ofAddressedDateTimeFirstFilled?
        (← elaborated "FirstFilledValue" (checkAddressedDateTimeFirstFilledComputation model group target.id star)))
  | .temporal .date _ => do
      stepOf "FirstFilledValue" (CheckedRowComputationStep.ofAddressedFullDateFirstFilled?
        (← elaborated "FirstFilledValue" (checkAddressedFullDateFirstFilledComputation model group target.id star)))
  | .dateRange => do
      stepOf "FirstFilledValue" (CheckedRowComputationStep.ofAddressedDateRangeFirstFilled?
        (← elaborated "FirstFilledValue" (checkAddressedDateRangeFirstFilledComputation model group target.id star)))
  | _ => refuse "FirstFilledValue" "row target kind"

/-- The row step one unguarded operation into a repeatable target names. -/
def lowerRowStep (model : FlatModel) (group : GroupPath) (target : FlatFieldDecl) :
    Expr → Lowering (RowStep model)
  | .call "FieldValueAsString" [.mk source none none] none none => do
      let some path := source.fieldEntity? | refuse "FieldValueAsString" "operand"
      stepOf "FieldValueAsString" (CheckedRowComputationStep.ofAddressedFieldValueAsString?
        (← elaborated "FieldValueAsString" (checkAddressedFieldValueAsString model group target.id path)))
  | .call "FirstFilledValue" [.mk (.entity { path, index := none, category := none }) none none] none none =>
      match path.segments.any (·.star), path.toStarFieldPath? with
      | true, some star => firstFilledRow model group target star
      | _, _ => refuse "FirstFilledValue" "row source"
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
