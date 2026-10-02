import A12Kernel.Reference.Dm.LowerNumeric
import A12Kernel.Elaboration.DocumentComputationStep

/-! # Lowering whole-document computation steps

A computation whose target is neither a Number nor a String table's carrier, or a String
`FirstFilledValue`, is lowered onto the whole-document step its operation names: `FirstFilledValue`
by its target's kind, the `Time(...)` construction, `DateFromDateTime` and `TimeFromDateTime`. A
step carries no precondition and one operation, so a guarded or multi-alternative computation is
refused here, as is every operation no step admits.
-/

namespace A12Kernel.Dm

/-- The scan source: one starred field alone is a star, anything else an entity list. -/
private def firstFilledSource (model : FlatModel) (group : GroupPath) (arguments : List Argument) :
    Lowering SurfaceFirstFilledSource :=
  match arguments with
  | [.mk (.entity { path, index := none, category := none }) none none] =>
      match path.segments.any (·.star), path.toStarFieldPath? with
      | true, some star => pure (.star star)
      | _, _ => (.list ·) <$> lowerEntitySource model group arguments
  | _ => (.list ·) <$> lowerEntitySource model group arguments

private def fieldOperand (model : FlatModel) (group : GroupPath) (construct : String) (expr : Expr) :
    Lowering FlatFieldDecl := do
  let some path := expr.fieldEntity? | refuse construct "operand"
  elaborated construct (model.resolveFieldDeclarationUnchecked group path)

private def timeComponent (model : FlatModel) (group : GroupPath) : Argument → Lowering SurfaceTimeComponent
  | .mk (.string text) none none => pure (.constant text)
  | .mk (.call id [.mk field none none] none none) none none => do
      let part ← match id with
        | "HoursFromTime" => pure TimeNumericPart.hour
        | "MinutesFromTime" => pure .minute
        | "SecondsFromTime" => pure .second
        | _ => refuse "Time" id
      pure (.extractor part (← fieldOperand model group "Time" field).id)
  | .mk expr none none => do
      let declaration ← fieldOperand model group "Time" expr
      match declaration.policy.kind.surfaceKind with
      | .number => pure (.number declaration.id)
      | .string => pure (.string declaration.id)
      | _ => refuse "Time" "component kind"
  | _ => refuse "Time" "component"

private def timeComponents (model : FlatModel) (group : GroupPath) :
    List Argument → Lowering SurfaceTimeComponents
  | [] => pure .empty
  | [hour] => do pure (.hour (← timeComponent model group hour))
  | [hour, minute] => do
      pure (.minute (← timeComponent model group hour) (← timeComponent model group minute))
  | [hour, minute, second] => do
      pure (.second (← timeComponent model group hour) (← timeComponent model group minute)
        (← timeComponent model group second))
  | _ => refuse "Time" "arity"

/-- `FirstFilledValue` onto the step of the target's kind. -/
private def firstFilledStep (model : FlatModel) (group : GroupPath) (target : FlatFieldDecl)
    (arguments : List Argument) : Lowering (CheckedDocumentComputationStep model) := do
  let source ← firstFilledSource model group arguments
  let check {ε α : Type} [Repr ε] (result : Except ε α) : Lowering α :=
    elaborated "FirstFilledValue" result
  match target.policy.kind.surfaceKind with
  | .boolean | .confirm =>
      let operation ← check (checkBooleanFirstFilledComputation model group target.id source)
      pure (.ofBooleanFirstFilled operation)
  | .temporal .time =>
      let operation ← check (checkTimeFirstFilledComputation model group target.id source)
      pure (.ofTimeFirstFilled operation)
  | .temporal .dateTime =>
      let operation ← check (checkDateTimeFirstFilledComputation model group target.id source)
      pure (.ofDateTimeFirstFilled operation)
  | .temporal .date =>
      if target.temporalFirstFilledStarCarrier?.any (·.isDateFragment) then
        let operation ← check (checkDateFragmentFirstFilledComputation model group target.id source)
        pure (.ofDateFragmentFirstFilled operation)
      else
        let operation ← check (checkFullDateFirstFilledComputation model group target.id source)
        pure (.ofFullDateFirstFilled operation)
  | .dateRange =>
      match source with
      | .list list =>
          let operation ←
            check (checkDateRangeFirstFilledDirectComputation model group target.id list)
          pure (.ofDateRangeFirstFilledDirect operation)
      | .star star =>
          let operation ← check (checkDateRangeFirstFilledComputation model group target.id star)
          pure (.ofDateRangeFirstFilled operation)
  | .string =>
      if target.customType.isSome then
        return .ofCustomFirstFilled (← check (checkCustomFirstFilledComputation model group target.id source))
      let operation ← check (checkStringFirstFilledComputation model group target.id
        (← lowerEntitySource model group arguments))
      pure (.ofStringFirstFilled operation)
  | .enumeration => do
      let operation ← check (elaborateEnumerationFirstFilledComputation model group target.id
        (← lowerEnumerationFirstFilledSource model group arguments))
      pure (.ofEnumerationFirstFilled operation)
  | .number => refuse "FirstFilledValue" "target kind"

/-- One unguarded operation onto its whole-document step, or a refusal naming its construct. -/
def lowerDocumentStep (model : FlatModel) (group : GroupPath) (target : FlatFieldDecl) :
    Expr → Lowering (CheckedDocumentComputationStep model)
  | .call "FirstFilledValue" arguments none none => firstFilledStep model group target arguments
  | .call "Time" arguments none none => do
      let components ← timeComponents model group arguments
      let operation ← elaborated "Time" (elaborateTimeConstructionComputation model components target.id)
      pure (.ofTimeConstruction operation)
  | .call "DateFromDateTime" [.mk source none none] none none => do
      let source ← fieldOperand model group "DateFromDateTime" source
      let operation ← elaborated "DateFromDateTime"
        (elaborateDateFromDateTimeComputation model source.id target.id)
      pure (.ofDateFromDateTime operation)
  | .call "TimeFromDateTime" [.mk source none none] none none => do
      let source ← fieldOperand model group "TimeFromDateTime" source
      let operation ← elaborated "TimeFromDateTime"
        (elaborateTimeFromDateTimeComputation model source.id target.id)
      pure (.ofTimeFromDateTime operation)
  | other => refuse other.construct

end A12Kernel.Dm
