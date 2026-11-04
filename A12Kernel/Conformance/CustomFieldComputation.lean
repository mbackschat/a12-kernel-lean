import A12Kernel.Elaboration.StringComputation
import A12Kernel.Semantics.StringCascade
import A12Kernel.Semantics.StringApplication
import A12Kernel.Elaboration.StringComputationRun
import A12Kernel.Elaboration.StringComputationSourceTarget

namespace A12Kernel.Conformance.CustomFieldComputation

open A12Kernel

private def target : FlatFieldDecl := {
  id := 1, groupPath := ["Form"], name := "Code", policy := { kind := .string },
  customType := some { name := "Code" } }

private def model : FlatModel := { fields := [target] }

private def expectedContext : CustomFieldValidationContext := {
  locale := "de_DE", minLength := some 1, maxLength := some 999, isDisplayValue := false }

private def worldWith (answer : Option RegisteredCustomRejection) (text : String := "ABCD") : World := {
  now := { epochMillis := 0 }
  customFieldValidator? := fun name => some (fun value context =>
    if value == text && context == expectedContext then
      if name == "Next" then none else answer
    else some { projectCode := "wrong-callback-input" }) }

private def outcome (answer : Option RegisteredCustomRejection) (text : String := "ABCD") :
    Option StringTargetOutcome := do
  let world := worldWith answer text
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let input ← (checkDocument prepared "de_DE" { instantiatedRows := [], cells := [] }).toOption
  let operation ← (elaborateStringComputationOperation model ["Form"] target.id (.literal text)).toOption
  (operation.evaluateOutcome prepared.patterns input).toOption

example : (outcome (some { projectCode := "testIDNummer" })).map
    (fun | .errored _ _ => true | _ => false) = some true := by native_decide

private def nextTarget : FlatFieldDecl := {
  id := 2, groupPath := ["Form"], name := "Next", policy := { kind := .string },
  customType := some { name := "Next" } }

private def cascadeModel : FlatModel := { fields := [target, nextTarget] }

private def cascadeOutcome (answer : Option RegisteredCustomRejection) :
    Option (Except StringDirectCascadeFault StringDirectCascadeResult) := do
  let prepared ← (prepareFlatStringContext (worldWith answer) builtinStringPatternCompiler cascadeModel).toOption
  let input ← (checkDocument prepared "de_DE" { instantiatedRows := [], cells := [] }).toOption
  let cascade : StringDirectCascade := {
    producer := {
      targetField := target.id, expression := .literal "ABCD", targetPolicy := target.stringPolicy,
      targetRegime := target.stringTargetRegime, prior := .empty }
    consumer := {
      targetField := nextTarget.id, expression := .field target.id, targetPolicy := nextTarget.stringPolicy,
      targetRegime := nextTarget.stringTargetRegime, prior := .empty } }
  pure (cascade.evaluate input.stringComputationContext)

private def cascadeConsumer (code : String) : Option (Option StringTargetOutcome) :=
  (cascadeOutcome (some { projectCode := code })).map
    (fun result => result.toOption.map (·.consumer.outcome))

/- Locked: a12-dmkits `CustomTestRangeLawsTest` at `1124b523f` (`publicInterpreterSeparatesStoredAdmissionFromComputedTargetErrors`), kernel 31.1.1: a computed target rejected with `testIDNummer` poisons its dependent exactly as the ordinary code does. -/
example : cascadeConsumer "testIDNummer" = cascadeConsumer "ordinary-reject" ∧
    cascadeConsumer "testIDNummer" = some (some (.poison .computedDependency)) := by native_decide

private def testCodeRejection : RegisteredCustomRejection := {
  projectCode := "testIDNummer", messageTemplate := some "Computed $<fieldName>$" }

example : outcome none = some (.accepted ⟨"ABCD", by decide⟩) ∧
    outcome (some testCodeRejection) = some (.errored ⟨"ABCD", by decide⟩ (.custom testCodeRejection)) ∧
    outcome (some testCodeRejection) "A\r\nB" =
      some (.errored ⟨"A\r\nB", by decide⟩ (.custom testCodeRejection)) := by native_decide

/- Unmeasured on 31.1.1. The target is rejected and keeps its attempted text for `testIDNummer` exactly as for an ordinary code. -/
example : ["PROJECT_CODE_INVALID", "testIDNummer"].all
    (fun code => outcome (some { projectCode := code }) ==
      some (.errored ⟨"ABCD", by decide⟩ (.custom { projectCode := code }))) = true := by
  native_decide

example : (outcome (some testCodeRejection)).map
    (fun result => (result.applyTo (.presentValue ⟨"old", by decide⟩), result.appliedValue)) =
      some (.presentEmpty, none) ∧
    (cascadeOutcome (some { projectCode := "ordinary-reject" })).map
      (fun result => result.toOption.map (·.consumer.outcome)) =
      some (some (.poison .computedDependency)) := by native_decide

private def noCapability : StringComputationContext := { read := fun _ => malformedCheckedCell }

example : outcome (some testCodeRejection) "" = some .noValue ∧
    ((StringTargetRegime.custom { name := "Missing" }).check {} none .noValue noCapability).toOption = some .noValue ∧
    ((StringTargetRegime.custom { name := "Missing" }).check {} none
      (.poison .malformed) noCapability).toOption = some (.poison .malformed) := by native_decide

private def faultOf : Except StringComputationFault StringTargetOutcome → Option StringComputationFault
  | .ok _ => none
  | .error fault => some fault

example :
    faultOf ((StringTargetRegime.custom { name := "Code" }).check {} none
      (.produced ⟨"ABCD", by decide⟩) noCapability) =
      some (.targetCustomContextUnavailable "Code") ∧
    faultOf ((StringTargetRegime.custom { name := "Code" }).check {} none
      (.produced ⟨"ABCD", by decide⟩) { noCapability with world := some (worldWith none) }) =
      some (.targetCustomContextUnavailable "Code") ∧
    faultOf ((StringTargetRegime.custom { name := "Code" }).check {} none
      (.produced ⟨"ABCD", by decide⟩) {
        noCapability with world := some { now := { epochMillis := 0 } }, locale := some "de_DE" }) =
      some (.targetCustomValidatorUnavailable "Code") := by native_decide

private def independent : FlatFieldDecl := {
  id := 3, groupPath := ["Form"], name := "Independent", policy := { kind := .string } }

private def source : FlatFieldDecl := {
  id := 4, groupPath := ["Form"], name := "Source", policy := { kind := .string },
  customType := some { name := "Source" } }

private def runModel : FlatModel := { fields := [target, nextTarget, independent, source] }

private def sourceWorld (answer : Option RegisteredCustomRejection) : World := {
  now := { epochMillis := 0 }
  customFieldValidator? := fun name => some fun value context =>
    if context != expectedContext then some { projectCode := "wrong-callback-context" }
    else if name == "Source" then
      if value == "A\r\r\nB" then none else some { projectCode := "wrong-source-input" }
    else if value == "A\r\nB" then
      if name == "Next" then none else answer
    else some { projectCode := "wrong-target-input" } }

private def priorCells (prior : StringTargetState) (field : FieldId) : List ClassifiedCellInput :=
  match prior with
  | .absent => []
  | .presentEmpty => [{ address := { field, path := [] }, stored := "", raw := .presentEmpty }]
  | .presentValue value => [{ address := { field, path := [] }, stored := value.text, raw := .parsed (.str value.text) }]
  | .presentUnconverted value => [{ address := { field, path := [] }, stored := value.text, raw := .parsed (.str value.text), sourceRepresentation := .unconvertedText }]

private def checkedRunOutcome (answer : Option RegisteredCustomRejection)
    (prior : StringTargetState := .absent) (normalizedSource : Bool := false) :
    Option (List (FieldId × StringTargetOutcome) × List StringTargetState) := do
  let world := if normalizedSource then sourceWorld answer else worldWith answer
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler runModel).toOption
  let sourceCells : List ClassifiedCellInput := if normalizedSource then [
    { address := { field := source.id, path := [] }, stored := "A\r\r\nB", raw := .parsed (.str "A\r\r\nB") }] else []
  let input ← (checkDocument prepared "de_DE" {
    instantiatedRows := []
    cells := priorCells prior target.id ++ priorCells prior nextTarget.id ++ sourceCells }).toOption
  let expression : StringExpr SurfaceFieldPath String := if normalizedSource then
    .field { base := .absolute, groups := ["Form"], field := "Source" }
    else .literal "ABCD"
  let producer ← (elaborateStringComputationTable runModel ["Form"] target.id
    [(none, expression)]).toOption
  let consumer ← (elaborateStringComputationTable runModel ["Form"] nextTarget.id
    [(none, .field { base := .absolute, groups := ["Form"], field := "Code" })]).toOption
  let unrelated ← (elaborateStringComputationTable runModel ["Form"] independent.id
    [(none, .literal "free")]).toOption
  let run ← (certifyStringComputationRun [producer, consumer, unrelated]).toOption
  let outcomes ← (run.execute prepared.patterns input).toOption
  pure (outcomes, outcomes.map fun (field, result) =>
    result.applyTo (input.sourceStringTargetState field))

private def priorStates : List StringTargetState := [
  .absent, .presentEmpty, .presentValue ⟨"old", by decide⟩,
  .presentValue ⟨"ABCD", by decide⟩]

example : priorStates.all (fun prior => checkedRunOutcome none prior == some ([
    (1, .accepted ⟨"ABCD", by decide⟩), (2, .accepted ⟨"ABCD", by decide⟩),
    (3, .accepted ⟨"free", by decide⟩)], [
      .presentValue ⟨"ABCD", by decide⟩, .presentValue ⟨"ABCD", by decide⟩,
      .presentValue ⟨"free", by decide⟩])) = true := by native_decide

/- Locked: a12-dmkits `CustomTestRangeLawsTest` at `1124b523f` (`publicInterpreterSeparatesStoredAdmissionFromComputedTargetErrors`, `computedAdmissionDoesNotDependOnTheTargetsStoredValue`), kernel 31.1.1: a computed CUSTOM target rejected with `testIDNummer` is errored and poisons its dependent exactly as an ordinary code does, whatever the target held before; the peer swept `null`, empty and a stale text, and the `ABCD` prior state here is unmeasured on 31.1.1. -/
example : ["ordinary-reject", "testIDNummer"].all
    (fun projectCode => priorStates.all fun prior =>
      checkedRunOutcome (some { projectCode }) prior == some ([
        (1, .errored ⟨"ABCD", by decide⟩ (.custom { projectCode })),
        (2, .poison .computedDependency), (3, .accepted ⟨"free", by decide⟩)], [
          prior.clearValue, prior.clearValue, .presentValue ⟨"free", by decide⟩])) = true := by native_decide

/- Unmeasured on 31.1.1 for the normalized stored-source route; the `testIDNummer` rows equal their ordinary-code twins with only the code differing. -/
example : (checkedRunOutcome none .absent true).map (·.1) = some [
    (1, .accepted ⟨"A\r\nB", by decide⟩), (2, .accepted ⟨"A\r\nB", by decide⟩),
    (3, .accepted ⟨"free", by decide⟩)] ∧
    ["ordinary-reject", "testIDNummer"].all (fun projectCode =>
      (checkedRunOutcome (some { projectCode }) .absent true).map (·.1) == some [
        (1, .errored ⟨"A\r\nB", by decide⟩ (.custom { projectCode })),
        (2, .poison .computedDependency), (3, .accepted ⟨"free", by decide⟩)]) = true := by
  native_decide

end A12Kernel.Conformance.CustomFieldComputation
