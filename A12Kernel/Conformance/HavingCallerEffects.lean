import A12Kernel.Elaboration.FirstFilledValue
import A12Kernel.Elaboration.TokenFirstFilledValue
import A12Kernel.Elaboration.NumericAggregate.Entities

namespace A12Kernel.Conformance.HavingCallerEffects
open A12Kernel

private def model : FlatModel := {
  fields := [
    { id := 1, groupPath := ["Form", "Rows"], name := "N", repeatableScope := [10]
      policy := { kind := .number { scale := 0, signed := false } } },
    { id := 2, groupPath := ["Form", "Rows"], name := "Label", repeatableScope := [10]
      policy := { kind := .string }, stringPolicy := { maxLength := some 2 }, stringExtensibleEnum := true }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 }] }

private def star (field : String) : SurfaceStarFieldPath := {
  base := .absolute, groups := [{ name := "Form" }, { name := "Rows", starred := true }], field }

private def predicate : SurfaceCorrelatedHaving := .typeValidity .valid {
  origin := .inner, field := { base := .absolute, groups := ["Form", "Rows"], field := "Label" } } "Code"

private def document : Document := {
  instantiatedRows := [{ group := 10, path := [1] }], rawCells := fun _ => none }

private def read (_ : Env) (field : FieldId) : CheckedCell := {
  rawPresent := true, findings := [], parsed := some (if field == 1 then .num 7 else .str "xx") }

private def world (registered : Bool) : World := {
  now := { epochMillis := 0 }
  customFieldValidator? := fun _ => if registered then some (fun _ _ => none) else none }

private def fault : Except StarAddressingError α → Option StarAddressingError
  | .error error => some error
  | .ok _ => none

private def callers (clock : Option World) (condition : SurfaceCorrelatedHaving := predicate)
    (input : Document := document) (label : String := "xx") : Option (List (Option StarAddressingError)) := do
  let numeric ← (elaborateNumberEntitySource model ["Form"] {
    first := .starHaving (star "N") condition, rest := [] }).toOption
  let token ← (elaborateFirstFilledTokenSource model ["Form"] {
    first := .starHaving (star "Label") condition, rest := [] }).toOption
  let cellRead := fun env field => if field == 2 then
    { read env field with parsed := some (.str label) } else read env field
  let direct : FlatContext := { read := cellRead [], world := clock }
  let raw := fun env field => match (cellRead env field).parsed with
    | some value => RawCell.parsed value
    | none => .empty
  pure [
    fault (numeric.first.resolvedAggregateSide input [] direct cellRead raw),
    fault (numeric.first.resolvedValidationAggregateSideIn input [] direct cellRead),
    fault (numeric.evaluateValidationIn input [] .full direct cellRead),
    fault (token.evaluatePartialFirstFilledValidation input [] .full (cellRead []) cellRead clock)]

example : callers (some (world true)) = some [none, none, none, none] := by native_decide

example : callers none = some (List.replicate 4 (some .worldUnavailable)) ∧
    callers (some (world false)) = some (List.replicate 4 (some .typeValidityValueFailure)) := by native_decide

private def numberText : SurfaceCorrelatedHaving := .compareStringExpression .equal
  (.fieldValueAsString (.field {
    origin := .inner, field := { base := .absolute, groups := ["Form", "Rows"], field := "N" } }))
  (.literal "7")

private def groupRead : SurfaceCorrelatedHaving := .groupPresence .filled .inner
  (.path { base := .absolute, groups := ["Form", "Rows"] })

example : callers none numberText = some (List.replicate 4 (some (.storedTextUnavailable 1))) ∧
    callers none groupRead = some (List.replicate 4 (some (.unsupportedGroupOperand ["Form", "Rows"]))) := by native_decide

example : [predicate, numberText, groupRead].all (fun condition =>
    callers none condition { document with instantiatedRows := [] } == some [none, none, none, none]) = true := by native_decide

private def presence (polarity : HavingPresencePolarity) : SurfaceCorrelatedHaving := .presence polarity {
  origin := .inner, field := { base := .absolute, groups := ["Form", "Rows"], field := "Label" } }

example : callers none (.and (presence .notFilled) predicate) = some [none, none, none, none] ∧
    callers none (.or (presence .filled) predicate) = some [none, none, none, none] ∧
    callers none (.and (presence .filled) predicate) = some (List.replicate 4 (some .worldUnavailable)) ∧
    callers none (.or (presence .notFilled) predicate) = some (List.replicate 4 (some .worldUnavailable)) := by native_decide

example : callers (some (world false)) (.and (presence .notFilled) predicate) = some [none, none, none, none] ∧
    callers (some (world false)) (.or (presence .filled) predicate) = some [none, none, none, none] ∧
    callers (some (world false)) (.and (presence .filled) predicate) =
      some (List.replicate 4 (some .typeValidityValueFailure)) ∧
    callers (some (world false)) (.or (presence .notFilled) predicate) =
      some (List.replicate 4 (some .typeValidityValueFailure)) := by native_decide

private def temporalFailure : SurfaceCorrelatedHaving := .dateValidity .valid {
  day := .constant "01"
  month := .field { origin := .inner, field := { base := .absolute, groups := ["Form", "Rows"], field := "Label" } }
  year := .complete (.constant "2024") }

example : callers none temporalFailure = some (List.replicate 4 (some .temporalValueFailure)) ∧
    callers none temporalFailure document "02" = some [none, none, none, none] ∧
    callers none (.and (presence .notFilled) temporalFailure) = some [none, none, none, none] ∧
    callers none (.and (presence .filled) temporalFailure) = some (List.replicate 4 (some .temporalValueFailure)) := by native_decide

private def checkedNumberText (changed : Bool) : Option (Option String × Option String × Bool) := do
  let prepared ← (prepareFlatStringContext (world true) builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" {
    instantiatedRows := document.instantiatedRows
    cells := [{ address := { field := 1, path := [1] }, stored := "7", raw := .parsed (.num 7) }] }).toOption
  let read := fun address => if changed && address.field == 1 then
    Except.ok ({ rawPresent := true, parsed := some (.num 8), findings := [] } : CheckedCell)
    else checked.read address
  let context := checked.resolvingCorrelationContextWithRead read
  let source : HavingStringComparison := {
    operator := .equal
    left := .fieldValueAsString (.field { origin := .inner, field := 1 })
    right := .literal "7" }
  let frame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [] }
  pure (checked.resolvingCorrelationContext.numberText frame.innerEnv 1,
    context.numberText frame.innerEnv 1,
    (source.evalValidationRead context frame).toOption == some (.fired .value) &&
      (source.evalComputationRead context frame).toOption == some .holds)

example : checkedNumberText false = some (some "7", some "7", true) ∧
    checkedNumberText true = some (some "7", none, false) := by native_decide

end A12Kernel.Conformance.HavingCallerEffects
