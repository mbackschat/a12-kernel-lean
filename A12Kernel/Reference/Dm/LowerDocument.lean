import A12Kernel.Reference.Dm.LowerNumeric
import A12Kernel.Reference.Dm.LowerValidation
import A12Kernel.Elaboration.DocumentComputationStep

/-! # Lowering whole-document computation steps

A computation whose target is neither a Number nor a String table's carrier, or a String
`FirstFilledValue`, is lowered onto the whole-document step its operation names: `FirstFilledValue`
by its target's kind, date literals with or without a year, Boolean/Confirm constants, the `Time(...)` construction, `DateFromDateTime` and `TimeFromDateTime`. A
step carries one operation; the computation reader attaches checked guards and assembles multiple alternatives through the checked target-instance table. Operations no step admits remain refused.
-/

namespace A12Kernel.Dm

/-- A carrier's whole-document step, which exists only at a fixed target. -/
private def fixedStep : Option (CheckedDocumentComputationStep model) →
    Lowering (CheckedDocumentComputationStep model)
  | some step => pure step
  | none => refuse "FirstFilledValue" "row target"

/-- `FirstFilledValue` onto the step of the target's kind, a temporal target's chosen by its profile. -/
private def firstFilledStep (model : FlatModel) (group : GroupPath) (target : FlatFieldDecl)
    (arguments : List Argument) (suppress : Bool) : Lowering (CheckedDocumentComputationStep model) := do
  let bindingGroup? := if arguments.any Argument.hasHaving then some target.groupPath else none
  -- The carrier's class instance must reach `elaborated`; without it the low-priority classless
  -- instance answers for every carrier (row `c14` of k22-static-s4-2026-10-24).
  let check {ε α : Type} [Repr ε] [StaticClassified ε] (result : Except ε α) : Lowering α :=
    elaborated "FirstFilledValue" result
  if target.policy.kind == .enumeration then
    let operation ← elaboratedEnumerationFirstFilled (·.calculationRefusal?)
      (elaborateEnumerationFirstFilledComputation model group target.id
      (← lowerEnumerationFirstFilledSource model group arguments bindingGroup? suppress))
    return .ofEnumerationFirstFilled operation
  let source ← lowerFirstFilledSource model group arguments bindingGroup? suppress
  match target.temporalFirstFilledFamily? with
  | some .time =>
      let operation ← check (checkTimeFirstFilledComputation model group target.id source)
      return ← fixedStep (CheckedDocumentComputationStep.ofTimeFirstFilled? operation)
  | some .dateTime =>
      let operation ← check (checkDateTimeFirstFilledComputation model group target.id source)
      return ← fixedStep (CheckedDocumentComputationStep.ofDateTimeFirstFilled? operation)
  | some .dateFragment | some .fullDate =>
      let operation ← check (checkFullDateFirstFilledComputation model group target.id source)
      return ← fixedStep (CheckedDocumentComputationStep.ofFullDateFirstFilled? operation)
  | some .dateRange =>
      match source with
      | .list list =>
          if (list.first :: list.rest).any (fun | .field .. => false | _ => true) then
            let operation ← check (checkDateRangeFirstFilledSourceComputation model group target.id source)
            return ← fixedStep (CheckedDocumentComputationStep.ofDateRangeFirstFilled? operation)
          let operation ←
            check (checkDateRangeFirstFilledDirectComputation model group target.id list)
          return .ofDateRangeFirstFilledDirect operation
      | .star star =>
          let operation ← check (checkDateRangeFirstFilledComputation model group target.id star)
          return ← fixedStep (CheckedDocumentComputationStep.ofDateRangeFirstFilled? operation)
  | none => pure ()
  match target.policy.kind.surfaceKind with
  | .boolean | .confirm =>
      let operation ← check (checkBooleanFirstFilledComputation model group target.id source)
      fixedStep (CheckedDocumentComputationStep.ofBooleanFirstFilled? operation)
  | .temporal _ | .dateRange => refuse "FirstFilledValue" "target kind"
  | .string =>
      if target.customType.isSome then
        return ← fixedStep (CheckedDocumentComputationStep.ofCustomFirstFilled? (← check (checkCustomFirstFilledComputation model group target.id source)))
      let operation ← check (checkStringFirstFilledComputation model group target.id
        (← lowerFirstFilledEntitySource model group arguments bindingGroup? suppress))
      fixedStep (CheckedDocumentComputationStep.ofStringFirstFilled? operation)
  | .enumeration => refuse "FirstFilledValue" "target kind"
  | .number => refuse "FirstFilledValue" "target kind"

/-- One unguarded operation onto its whole-document step, or a refusal naming its construct. -/
def lowerDocumentStep (model : FlatModel) (group : GroupPath) (target : FlatFieldDecl) (suppress : Bool := false) :
    Expr → Lowering (CheckedDocumentComputationStep model)
  | .string text => do
      let some source := authoredDateLiteral? text | return ← temporal (.string text)
      let operation ← elaborated "DateComputation" (checkDateLiteralComputation model group target.id source)
      (CheckedDocumentComputationStep.ofDateLiteral? operation).getDM
        (refuse "DateComputation" "row target")
  | .constant "True" => boolean true
  | .constant "False" => boolean false
  | .call "FirstFilledValue" arguments none none => firstFilledStep model group target arguments suppress
  | other => temporal other

where
  temporal (source : Expr) : Lowering (CheckedDocumentComputationStep model) := do
    let surface ← lowerScalarTemporalExpression model group source suppress
    let expression ← elaborated "TemporalExpression"
      (elaborateScalarTemporalExpression model group surface)
    (CheckedDocumentComputationStep.ofScalarTemporalExpression? expression target.id).getDM
      (refuse source.construct "temporal target or dependency")

  boolean (value : Bool) : Lowering (CheckedDocumentComputationStep model) := do
    let operation ← elaborated "BooleanComputation"
      (checkBooleanConstantComputation model group target.id value)
    pure (.ofBooleanConstant operation)

end A12Kernel.Dm
