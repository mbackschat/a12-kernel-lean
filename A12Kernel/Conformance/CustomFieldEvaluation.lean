import A12Kernel.Elaboration.StringContext
import A12Kernel.Elaboration.ComputationFormalInput
import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Semantics.CustomFieldFormalMessage

/-! # A12Kernel.Conformance.CustomFieldEvaluation — checked custom full-evaluation locks -/

namespace A12Kernel.Conformance.CustomFieldEvaluation

open A12Kernel

private def rejection : RegisteredCustomRejection where
  projectCode := "PROJECT_CODE_INVALID"

private def validator : RegisteredCustomFieldValidator := fun value context =>
  if value == "accepted" && context.locale == "en_US" then none else some rejection

private def worldWithValidator : World where
  now := { epochMillis := 0 }
  customFieldValidator? := fun name =>
    if name == "ProjectCode" then some validator else none

private def rawLinebreakWorld : World where
  now := { epochMillis := 0 }
  customFieldValidator? := fun name =>
    if name == "ProjectCode" then
      some (fun value _ => if value == "A\r\r\nB" then none else some rejection)
    else none

private def reportedWorld : World where
  now := { epochMillis := 0 }
  customFieldValidator? := fun name =>
    if name == "ProjectCode" then
      some (fun value _ => some { projectCode :=
        if value == "A\r\r\nB" then "testIDNummer" else "PROJECT_CODE_INVALID" })
    else none

private def emptyWorld : World :=
  { now := { epochMillis := 0 } }

private def compilePattern : StringPatternCompiler := fun source =>
  if source == "A+" then
    .compiled fun value =>
      !value.isEmpty && value.toList.all fun character => character == 'A'
  else
    .rejected

private def code : FlatFieldDecl :=
  {
    id := 1
    groupPath := ["Order"]
    name := "Code"
    policy := { kind := .string }
    customType := some { name := "ProjectCode" }
  }

private def ordinary : FlatFieldDecl :=
  { id := 2, groupPath := ["Order"], name := "Note",
    policy := { kind := .string } }

private def patterned : FlatFieldDecl :=
  {
    id := 4
    groupPath := ["Order"]
    name := "Patterned"
    policy := { kind := .string }
    stringPatternSource := some "A+"
  }

private def invalidCustomNumber : FlatFieldDecl :=
  {
    id := 3
    groupPath := ["Order"]
    name := "Count"
    policy := { kind := .number { scale := 0, signed := true } }
    customType := some { name := "ProjectCode" }
  }

private def path (name : String) : SurfaceFieldPath :=
  { base := .absolute, groups := ["Order"], field := name }

private def rawAt (id : FieldId) (cell : RawCell) : RawFlatContext where
  read candidate := if candidate == id then cell else .empty

private def rawPair (leftId : FieldId) (left : RawCell)
    (rightId : FieldId) (right : RawCell) : RawFlatContext where
  read candidate :=
    if candidate == leftId then left
    else if candidate == rightId then right
    else .empty

private def outcome (model : FlatModel) (world : World) (locale : String)
    (raw : RawFlatContext) (condition : SurfaceCondition) :
    Except FlatStringContextEvaluationError Verdict :=
  elaborateAndEvalFull compilePattern locale model world
    ["Order"] raw true condition

private def verdictOf (model : FlatModel) (world : World) (locale : String)
    (raw : RawFlatContext) (condition : SurfaceCondition) : Option Verdict :=
  match outcome model world locale raw condition with
  | .ok verdict => some verdict
  | .error _ => none

private def errorOf (model : FlatModel) (world : World) (locale : String)
    (raw : RawFlatContext) (condition : SurfaceCondition) :
    Option FlatStringContextEvaluationError :=
  match outcome model world locale raw condition with
  | .ok _ => none
  | .error error => some error

private def unpreparedVerdict (model : FlatModel) (world : World)
    (raw : RawFlatContext) (condition : SurfaceCondition) : Option Verdict :=
  match elaborateAndEvalUnpreparedFull model world ["Order"] raw true condition with
  | .ok verdict => some verdict
  | .error _ => none

example : verdictOf { fields := [code] } reportedWorld "en_US"
    (rawAt code.id (.parsed (.str "A\r\r\nB")))
    (.lengthCompare .greater (path "Code") { value := 3, authoredScale := 0 }) =
    some (.fired .value) := by native_decide

private def reportedModel : FlatModel := { fields := [code, ordinary] }

private def reportedInput? : Option (CheckedDocument reportedModel) := do
  let prepared ← (prepareFlatStringContext reportedWorld compilePattern reportedModel).toOption
  (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := [
      { address := { field := code.id, path := [] }, stored := "A\r\r\nB",
        raw := .parsed (.str "A\r\r\nB") },
      { address := { field := ordinary.id, path := [] }, stored := "bad",
        raw := .rejected .malformed }] }).toOption

example : (do
    let input ← reportedInput?
    let plan ← (checkComputationFormalInputPlan reportedModel [code.id, ordinary.id] []).toOption
    let prepared ← (plan.prepare input).toOption
    let cell ← (prepared.preliminary.readComputation { field := code.id, path := [] }).toOption
    pure (observeCell .computation cell, prepared.formalErrorsInOperands)) =
      some (.value (.str "A\r\nB"), [
        { address := { field := code.id, path := [] },
          cause := .registeredCustomValidation { projectCode := "testIDNummer" } },
        { address := { field := ordinary.id, path := [] }, cause := .malformed }]) := by
  native_decide

private def customInvalidPointerGuard : Option Bool := do
  let input ← reportedInput?
  let flat ← (elaborate reportedModel ["Order"] (.fieldFilled (path "Code"))).toOption
  let condition ← (CheckedValidationCondition.fromFlat flat).toOption
  let rule ← (assembleResolvedValidationRule reportedModel condition code.id
    "CUSTOM" .error { parts := [] }).toOption
  let context : AddressedValidationEvaluationContext reportedModel := {
    scalar := { fields := input.flatContext, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked input }
  let invoked := rule.withCustomConditions context .all {
    configured := some fun _ => some fun invocation =>
      invocation.formallyIncorrect == [{ field := ordinary.id, path := [] }] &&
      (invocation.data.read { field := code.id, path := [] }).toOption.map
        (·.formalReports) == some [.registeredCustomValidation { projectCode := "testIDNummer" }] }
  (invoked.scalar.customConditions "Check").toOption

example : customInvalidPointerGuard = some true := by native_decide

private def modeInputCells (relevant : Bool) (raw : RawCell String) : List ClassifiedCellInput :=
  let custom := if !relevant then [] else match raw with
    | .empty => []
    | .presentEmpty => [{ address := { field := code.id, path := [] }, stored := "", raw := .presentEmpty }]
    | .parsed text => [{ address := { field := code.id, path := [] }, stored := text, raw := .parsed (.str text) }]
    | .rejected cause => [{ address := { field := code.id, path := [] }, stored := "bad", raw := .rejected cause }]
  custom ++ [{ address := { field := ordinary.id, path := [] }, stored := "marker", raw := .parsed (.str "marker") }]

private def modeContinuation (mode : CustomFieldValidationMode)
    (relevant : Bool) (raw : RawCell String) (world : World) :
    Option (CellObservation Value × Option (Verdict × Bool)) := do
  let prepared ← (prepareFlatStringContext world compilePattern reportedModel).toOption
  let input ← (checkDocument prepared "en_US" {
    instantiatedRows := [], cells := modeInputCells relevant raw }).toOption
  let cell ← (input.read { field := code.id, path := [] }).toOption
  let output : CustomFieldValidationOutput := {
    cell := {
      rawPresent := cell.rawPresent
      parsed := cell.parsed.bind fun | .str text => some text | _ => none
      findings := cell.findings
      reports := cell.reports }
    message? := cell.registeredCustomRejection?.map fun cause =>
      cause.toFormalMessage (MessagePointer.ofCellAddr { field := code.id, path := [] })
        "Code" { text := "Invalid" } }
  let outputs := if relevant then [output] else []
  let continuation : Option (Verdict × Bool) :=
    if mode.continuesAfterIngestion outputs then do
      let flat ← (elaborate reportedModel ["Order"]
        (.lengthCompare .greater (path "Code") { value := 3, authoredScale := 0 })).toOption
      let condition ← (CheckedValidationCondition.fromFlat flat).toOption
      let rule ← (assembleResolvedValidationRule reportedModel condition code.id
        "LENGTH" .error { parts := [] }).toOption
      let context : AddressedValidationEvaluationContext reportedModel := {
        scalar := { fields := input.flatContext, groups := GroupPresenceContext.unavailable }
        outer := [], input := .checked input }
      let registry : CustomValidationRegistry reportedModel := {
        configured := some fun name => if name == "Check" then some fun invocation =>
          (invocation.data.read { field := ordinary.id, path := [] }).toOption.map
            (observeCell .validation) == some (.value (.str "marker")) else none }
      let authored ← (rule.evalAddressedFull context true registry).toOption
      let callback ← ((rule.withCustomConditions context .all registry).scalar.customConditions "Check").toOption
      pure (authored.verdict, callback)
    else none
  pure (observeCell .validation cell, continuation)

private def continuationModes : List CustomFieldValidationMode :=
  [.fullExamination, .abortOnFormalErrors]

example : continuationModes.map (fun mode =>
    modeContinuation mode true (.parsed "accepted") worldWithValidator) = [
      some (.value (.str "accepted"), some (.fired .value, true)),
      some (.value (.str "accepted"), some (.fired .value, true))] := by native_decide

example : continuationModes.map (fun mode =>
    modeContinuation mode true (.parsed "A\r\r\nB") reportedWorld) = [
      some (.value (.str "A\r\nB"), some (.fired .value, true)),
      some (.value (.str "A\r\nB"), none)] := by native_decide

example : continuationModes.map (fun mode =>
    modeContinuation mode true (.parsed "rejected") worldWithValidator) = [
      some (.unknown (.registeredCustomValidation rejection), some (.unknown, true)),
      some (.unknown (.registeredCustomValidation rejection), none)] := by native_decide

example : [
    (true, RawCell.empty), (true, .presentEmpty), (false, .parsed "rejected")].all
    (fun (relevant, raw) => continuationModes.map (fun mode =>
      modeContinuation mode relevant raw worldWithValidator) == [
        some (.empty, some (.notFired, true)),
        some (.empty, some (.notFired, true))]) = true := by native_decide

/- Accepted, rejected, and empty custom fields flow through one prepared checked context. -/
example : verdictOf { fields := [code] } worldWithValidator "en_US"
    (rawAt code.id (.parsed (.str "accepted"))) (.fieldFilled (path "Code")) =
    some (.fired .value) := by
  native_decide

example : verdictOf { fields := [code] } worldWithValidator "en_US"
    (rawAt code.id (.parsed (.str "rejected"))) (.fieldFilled (path "Code")) =
    some .unknown := by
  native_decide

example : verdictOf { fields := [code] } worldWithValidator "en_US"
    (rawAt code.id .empty) (.fieldFilled (path "Code")) =
    some .notFired := by
  native_decide

example : (do
    let prepared ← (prepareFlatStringContext rawLinebreakWorld compilePattern
      { fields := [code] }).toOption
    pure (observeCell .validation
      ((prepared.checkContext "en_US"
        (rawAt code.id (.parsed (.str "A\r\r\nB")))).read code.id))) =
    some (.value (.str "A\r\nB")) ∧
    verdictOf { fields := [code] } rawLinebreakWorld "en_US"
      (rawAt code.id (.parsed (.str "A\r\r\nB")))
      (.lengthCompare .greater (path "Code") { value := 4, authoredScale := 0 }) =
      some .notFired ∧
    verdictOf { fields := [code] } rawLinebreakWorld "en_US"
      (rawAt code.id (.parsed (.str "A\r\r\nB")))
      (.lengthCompare .greater (path "Code") { value := 3, authoredScale := 0 }) =
      some (.fired .value) := by
  native_decide

/- Ordinary no-custom models retain their existing full-evaluation result. -/
example : verdictOf { fields := [ordinary] } emptyWorld "en_US"
    (rawAt ordinary.id (.parsed (.str "note")))
    (.fieldFilled (path "Note")) = some (.fired .value) := by
  native_decide

/- A prepared custom entry point must not bypass an ordinary declared pattern on another field. -/
example : verdictOf { fields := [patterned] } emptyWorld "en_US"
    (rawAt patterned.id (.parsed (.str "BBB")))
    (.fieldFilled (path "Patterned")) = some .unknown := by
  native_decide

example : unpreparedVerdict { fields := [patterned] } emptyWorld
    (rawAt patterned.id (.parsed (.str "BBB")))
    (.fieldFilled (path "Patterned")) = some .unknown := by
  native_decide

example : verdictOf { fields := [patterned] } emptyWorld "en_US"
    (rawAt patterned.id (.parsed (.str "AAA")))
    (.fieldFilled (path "Patterned")) = some (.fired .value) := by
  native_decide

/- One mixed row dispatches the ordinary pattern and registered custom fields through their distinct prepared checkers before the shared condition tree. -/
example : verdictOf { fields := [patterned, code] } worldWithValidator "en_US"
    (rawPair patterned.id (.parsed (.str "AAA"))
      code.id (.parsed (.str "accepted")))
    (.and (.fieldFilled (path "Patterned")) (.fieldFilled (path "Code"))) =
      some (.fired .value) := by
  native_decide

example : verdictOf { fields := [patterned, code] } worldWithValidator "en_US"
    (rawPair patterned.id (.parsed (.str "BBB"))
      code.id (.parsed (.str "accepted")))
    (.and (.fieldFilled (path "Patterned")) (.fieldFilled (path "Code"))) =
      some .unknown := by
  native_decide

/- Preparation and condition elaboration failures remain distinct. -/
example : errorOf { fields := [code] } emptyWorld "en_US"
    (rawAt code.id (.parsed (.str "accepted"))) (.fieldFilled (path "Code")) =
    some (.preparation (.custom (.missingValidator "ProjectCode"))) := by
  native_decide

example : errorOf { fields := [invalidCustomNumber] } worldWithValidator "en_US"
    (rawAt invalidCustomNumber.id (.parsed (.num 1)))
    (.fieldFilled (path "Count")) =
    some (.preparation (.model
      (.customTypeRequiresString ["Order", "Count"]))) := by
  native_decide

example : errorOf { fields := [ordinary] } emptyWorld "en_US"
    (rawAt ordinary.id (.parsed (.str "note")))
    (.fieldFilled (path "Missing")) =
    some (.condition (.resolve (.invalidEntity (path "Missing")))) := by
  native_decide

end A12Kernel.Conformance.CustomFieldEvaluation
