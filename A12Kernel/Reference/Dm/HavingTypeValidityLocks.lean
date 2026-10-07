import A12Kernel.Reference.Dm.HavingFixture
import A12Kernel.Reference.Dm.Validate

namespace A12Kernel.Dm.HavingTypeValidityLocks
open A12Kernel A12Kernel.Dm
open Lean

private def readStatus (text : String) : Option Bool := do
  let parsed ← (parseText .english text).toOption
  pure (lowerHaving parsed.body).isOk


example : readStatus "Valid(Tag, \"Code\")" = some true := by native_decide
example : readStatus "Invalid($Tag, \"Code\")" = some true := by native_decide

private def world (registered : Bool) : World := {
  now := { epochMillis := 0 }
  customFieldValidator? := fun name =>
    if registered && name == "Code" then some (fun value context =>
      if value == "kept" && context == explicitCustomFieldValidationContext then none
      else some { projectCode := "TYPE_REJECTED" }) else none }

private structure Scenario where
  registered : Bool := true
  enumerated : Bool := false
  rows : Bool := false
  fresh : Bool := false
  tags : List String := ["kept", "drop", "kept"]
  targetKind : FieldKind := .number { scale := 0, signed := true }
  guard : Option String := none
  validation : Option String := none
  expected : String := "9"

private def enumeration : EnumerationDeclaration := {
  storedTokens := ["kept", "drop"]
  displayFacts := [{ locale := "en_US", stored := "kept", display := "DISPLAYED" },
    { locale := "en_US", stored := "drop", display := "REJECTED" }] }

private def model (scenario : Scenario) : FlatModel := {
  HavingFixture.model with
  fields := HavingFixture.model.fields.map (fun field =>
    if field.id == 3 then { field with
      policy := { kind := if scenario.enumerated then .enumeration else .string }
      stringPolicy := if scenario.enumerated then {} else { maxLength := some 4 }
      enumeration := if scenario.enumerated then some enumeration else none }
    else if field.id == 5 then { field with
      groupPath := if scenario.rows then ["Form", "Rows"] else ["Form"]
      repeatableScope := if scenario.rows then [10] else []
      policy := { kind := scenario.targetKind }
      enumeration := if scenario.targetKind == .enumeration then some enumeration else none
      temporalTargetPolicy := if scenario.targetKind == .temporal .date .fullDate then some { format := "yyyy-MM-dd" } else none }
    else field) ++ [
      { id := 6, name := "After", groupPath := if scenario.rows then ["Form", "Rows"] else ["Form"],
        repeatableScope := if scenario.rows then [10] else [],
        policy := { kind := .number { scale := 0, signed := true } } },
      { id := 7, name := "Tag", groupPath := ["Form"], policy := { kind := .string } },
      { id := 8, name := "Stamp", groupPath := ["Form", "Rows"], repeatableScope := [10],
        policy := { kind := .temporal .date .fullDate }, temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
      { id := 9, name := "Flag", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .boolean } }] }

private def input (scenario : Scenario) : Json :=
  let stored := match scenario.targetKind with
    | .temporal .date _ => "2000-01-01"
    | .boolean => "false"
    | .string | .enumeration => "drop"
    | _ => "99"
  let rows := (scenario.tags.zip [("2", "2024-03-01", "true"),
      ("5", "2024-03-02", "false"), ("7", "2024-03-03", "true")]).map fun (tag, n, stamp, flag) =>
    Json.mkObj ([("Tag", .str tag), ("N", .str n), ("Stamp", .str stamp), ("Flag", .str flag)] ++
      if scenario.rows then [("Out", .str stored), ("After", .str "99")] else [])
  Json.mkObj [("Form", Json.mkObj ([("Error", .str "ready"), ("Expected", .str "kept"),
    ("Tag", .str "drop"), ("Rows", .arr rows.toArray)] ++
      if scenario.rows then [] else [("Out", .str stored), ("After", .str "99")]))]

private inductive RunError where
  | input | inputRefusal | preparation | document | rule | validation | computation | execution
  deriving Repr, BEq, DecidableEq

private structure Fixture (scenario : Scenario) where
  prepared : PreparedFlatStringContext (model scenario) builtinStringPatternCompiler
  document : CheckedDocument (model scenario)

private def fixture (scenario : Scenario) : Except RunError (Fixture scenario) := do
  let dm : DmModel := { flat := model scenario, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let data ← (readDocument dm (input scenario)).mapError fun _ => .input
  if !data.refusals.isEmpty then throw .inputRefusal
  let prepared ← (prepareFlatStringContext (world scenario.registered) builtinStringPatternCompiler (model scenario)).mapError fun _ => .preparation
  let document ← (checkDocument prepared "en_US" data.data).mapError fun _ => .document
  pure { prepared, document }

private structure Execution where
  verdicts : List Verdict
  pointers : List String
  values : List String
  dependent : List String
  deriving Repr, BEq, DecidableEq

private def runCore (operation : String) (scenario : Scenario) : Except RunError Execution := do
  let model := model scenario
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let world := world scenario.registered
  let prepared ← fixture scenario
  let document := prepared.document
  let checked ← (checkRule dm .english {
    group := ["Form"], name := "Selected", errorCode := "SELECTED",
    errorEntityRelPath := if scenario.rows then "../Rows/N" else "../Error",
    condition := scenario.validation.getD (if scenario.rows then
      "FieldFilled(Rows/N) And " ++ operation ++ " > 0"
      else "FieldFilled(Error) And " ++ operation ++ " == " ++ scenario.expected), severity := "ERROR" } world).mapError fun _ => .rule
  let verdicts ← if scenario.rows then
      (checked.evalOrdinaryRepeatableFull document (some world)).map (fun rows => rows.map (·.2.verdict)) |>.mapError fun _ => .validation
    else
      (checked.evalAddressedFull {
        scalar := { fields := document.flatContext.withWorld world, groups := GroupPresenceContext.unavailable },
        outer := [], input := .checked document } true).map (fun outcome => [outcome.verdict]) |>.mapError fun _ => .validation
  let messages ← (runRule world document checked).mapError fun _ => .validation
  let definitions : List DmComputation := [
    { group := ["Form"], name := "Dependent", targetRelPath := if scenario.rows then "../Rows/After" else "../After",
      commonPrecondition := none, alternatives := [{
        precondition := none
        operation := "NumberOfFilledFields(" ++ (if scenario.rows then "Rows/Out" else "Out") ++ ", Expected)" }], errorCodesToSuppress := [] },
    { group := ["Form"], name := "Selected", targetRelPath := if scenario.rows then "../Rows/Out" else "../Out",
      commonPrecondition := scenario.guard, alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }]
  let definitions := definitions ++ if scenario.fresh then [{
    group := ["Form"], name := "Producer", targetRelPath := "../Rows/Tag", commonPrecondition := none,
    alternatives := [{ precondition := none, operation := "\"drop\"" }], errorCodesToSuppress := [] }] else []
  let lowered ← definitions.mapM fun definition => (lowerComputation model .english definition).mapError fun _ => .computation
  let outcomes ← (runComputations world prepared.prepared document (lowered.map (·.2))).mapError fun _ => .execution
  pure {
    verdicts, pointers := messages.map (fun message => (observe model message).pointer),
    values := (outcomes.filter (·.pointer.endsWith "/Out")).map (·.outcome),
    dependent := (outcomes.filter (·.pointer.endsWith "/After")).map (·.outcome) }

private def run (operation : String) (scenario : Scenario := {}) : Sum RunError Execution :=
  match runCore operation scenario with | .error error => .inl error | .ok outcome => .inr outcome

private def predicate (op : String) (field : String := "Rows/Tag") : String := op ++ "(" ++ field ++ ", \"Code\")"
private def sum (filter : String) : String := "Sum(Rows*/N Having " ++ filter ++ ")"
private def fired (value : String) : Execution := {
  verdicts := [.fired .omission], pointers := ["Form/Error"], values := ["value " ++ value], dependent := ["value 2"] }

example : [false, true].all (fun enumerated =>
    run (sum (predicate "Valid")) { enumerated } == .inr (fired "9") &&
    run (sum (predicate "Invalid")) { enumerated, expected := "5" } == .inr (fired "5")) = true := by native_decide

example : ["Valid", "Invalid"].all (fun op =>
    run (sum (predicate op)) { registered := false, expected := "14" } ==
      .inr { (fired "14") with values := ["cleared"], dependent := ["cleared"] } &&
    run (sum (predicate op)) { registered := false, tags := ["", "", ""], expected := "0" } == .inr (fired "0")) = true := by native_decide

example : run (sum (predicate "Valid")) { tags := ["", "drop", "kept"], expected := "7" } = .inr (fired "7") ∧
    run (sum (predicate "Invalid")) { tags := ["", "drop", "kept"], expected := "5" } = .inr (fired "5") ∧
    run (sum (predicate "Valid")) { tags := ["kept", "longer", "kept"] } =
      .inr { (fired "9") with values := ["cleared"], dependent := ["cleared"] } := by native_decide

example : run (sum ("[Rows/N] > 0 And " ++ predicate "Valid" "$Rows/Tag")) { rows := true } =
    .inr {
      verdicts := [.fired .omission, .notFired, .fired .omission],
      pointers := ["Form/Rows/N", "Form/Rows[3]/N"], values := ["value 14", "value 0", "value 14"],
      dependent := ["value 2", "value 2", "value 2"] } ∧
    run (sum ("[Rows/N] > 0 And " ++ predicate "Invalid" "$Rows/Tag")) { rows := true } =
    .inr {
      verdicts := [.notFired, .fired .omission, .notFired], pointers := ["Form/Rows[2]/N"],
      values := ["value 0", "value 14", "value 0"], dependent := ["value 2", "value 2", "value 2"] } := by native_decide

example : run (sum ("[Rows/N] > 0 And " ++ predicate "Valid" "Tag")) { expected := "0" } = .inr (fired "0") ∧
    run (sum ("[Rows/N] > 0 And " ++ predicate "Invalid" "Tag")) { expected := "14" } = .inr (fired "14") ∧
    run ("Sum(Rows/N, Rows*/N Having " ++ predicate "Valid" ++ ")") { rows := true } =
      .inr {
      verdicts := [.fired .omission, .fired .omission, .fired .omission],
        pointers := ["Form/Rows/N", "Form/Rows[2]/N", "Form/Rows[3]/N"],
        values := ["value 11", "value 14", "value 16"], dependent := ["value 2", "value 2", "value 2"] } := by native_decide

example : run (sum (predicate "Valid")) { fresh := true } = .inr (fired "0") ∧
    run (sum (predicate "Invalid")) { fresh := true, expected := "5" } = .inr (fired "14") := by native_decide

private def values (operation : String) (scenario : Scenario := {}) : Sum RunError (List String × List String) :=
  match run operation { scenario with validation := some (if scenario.rows then "FieldFilled(Rows/N)" else "FieldFilled(Error)") } with
  | .inl error => .inl error
  | .inr outcome => .inr (outcome.values, outcome.dependent)

private def carriers (op : String) : List (String × FieldKind × Bool) :=
  let filter := predicate op
  let number := FieldKind.number { scale := 0, signed := true }
  [(sum filter, number, false),
    ("NumberOfFilledFields(Rows*/N Having " ++ filter ++ ")", number, false),
    ("NumberOfDifferentValues(Rows*/N Having " ++ filter ++ ")", number, false),
    ("NumberOfValueInFields(True In Rows*/Flag Having " ++ filter ++ ")", number, false),
    ("NumberOfValueInFields(\"kept\" In Rows*/Tag Having " ++ filter ++ ")", number, false),
    ("NumberOfDifferentValues(Rows*/Stamp Having " ++ filter ++ ")", number, false),
    ("MinValue(Rows*/Stamp Having " ++ filter ++ ")", .temporal .date .fullDate, false),
    ("FirstFilledValue(Rows*/Tag Having " ++ filter ++ ")", .string, false),
    ("FirstFilledValue(Rows*/Tag Having " ++ filter ++ ")", .enumeration, true),
    ("FirstFilledValue(Rows*/Flag Having " ++ filter ++ ")", .boolean, false),
    ("FirstFilledValue(Rows*/Stamp Having " ++ filter ++ ")", .temporal .date .fullDate, false)]

example : ["Valid", "Invalid"].all (fun op =>
    (carriers op).all fun (operation, targetKind, enumerated) => [false, true].all fun rows =>
      values operation { registered := false, targetKind, enumerated, rows } ==
        .inr (List.replicate (if rows then 3 else 1) "cleared", List.replicate (if rows then 3 else 1) "cleared")) = true := by native_decide

private def positiveOutcomes (op : String) : List (Option String) :=
  if op == "Valid" then [some "9", some "2", some "2", some "2", some "2", some "2",
    some "2024-03-01", some "kept", some "kept", some "true", some "2024-03-01"]
  else [some "5", some "1", some "1", some "0", some "0", some "1",
    some "2024-03-02", none, none, none, some "2024-03-02"]

example : ["Valid", "Invalid"].all (fun op =>
    (carriers op).length == (positiveOutcomes op).length &&
    ((carriers op).zip (positiveOutcomes op)).all fun ((operation, targetKind, enumerated), expected) =>
      [false, true].all fun rows =>
        let count := if rows then 3 else 1
        values operation { targetKind, enumerated, rows } ==
          .inr (expected.toList.flatMap (fun value => List.replicate count ("value " ++ value)),
            List.replicate count "value 2")) = true := by native_decide

example : ["AtLeastOneFieldFilled", "FieldValuesNotUnique"].all (fun carrier =>
    ["Valid", "Invalid"].all fun op =>
      values "1" { registered := false, guard := some (carrier ++ "(Rows*/Tag Having " ++ predicate op ++ ")") } ==
        .inr (["cleared"], ["cleared"])) = true := by native_decide

example : values "1" { guard := some ("AtLeastOneFieldFilled(Rows*/Tag Having " ++ predicate "Valid" ++ ")") } =
      .inr (["value 1"], ["value 2"]) ∧
    values "1" { guard := some ("FieldValuesNotUnique(Rows*/Tag Having " ++ predicate "Invalid" ++ ")") } =
      .inr (["cleared"], ["value 1"]) := by native_decide

example : values "1" { registered := false, guard := some (
      "AtLeastOneFieldFilled(Rows*/N Having [Rows/N] > 100 And " ++ predicate "Valid" ++ ")") } =
      .inr (["cleared"], ["value 1"]) ∧
    values "1" { registered := false, guard := some (
      "AtLeastOneFieldFilled(Rows*/N Having " ++ predicate "Valid" ++ " And [Rows/N] > 100)") } =
      .inr (["cleared"], ["cleared"]) ∧
    values (sum ("[Rows/N] > 0 Or " ++ predicate "Valid")) { registered := false } = .inr (["value 14"], ["value 2"]) ∧
    values (sum (predicate "Valid" ++ " Or [Rows/N] > 0")) { registered := false } = .inr (["cleared"], ["cleared"]) := by native_decide

example : ["Valid", "Invalid"].all (fun op => [false, true].all fun rows =>
    values "1" {
      rows, registered := false,
      guard := some ("MinValue(Rows*/Stamp Having " ++ predicate op ++ ") == \"01.03.2024\"") } ==
      .inr (List.replicate (if rows then 3 else 1) "cleared", List.replicate (if rows then 3 else 1) "cleared")) = true := by native_decide

private inductive Admission where
  | syntax | reader | operand | refused (diagnostic : Option KernelStaticDiagnostic) | admitted
  deriving Repr, BEq, DecidableEq

private def admission (filter : String) (fixture : FlatModel := model {}) (binding : GroupPath := ["Form"]) : Admission :=
  match parseText .english filter with
  | .error _ => .syntax
  | .ok parsed => match lowerHaving parsed.body with
    | .error _ => .reader
    | .ok authored => match elaborateStarFieldPath fixture ["Form"] {
        base := .relative 0, groups := [{ name := "Rows", starred := true }], field := "N" } with
      | .error _ => .operand
      | .ok source => match elaborateStarHavingCore fixture ["Form"] source authored binding with
        | .error error => .refused error.diagnostic?
        | .ok _ => .admitted

example : admission "Valid(Rows/Tag, \"\")" = .refused (some .noEmpty) ∧
    admission "Invalid(Rows/N, \"Code\")" = .refused (some .noStringOrEnumOrExtEnum) ∧
    admission "Valid(Rows, \"Code\")" = .refused (some .noGroupsAllowed) ∧
    admission "Valid(Rows*/Tag, \"Code\")" = .reader ∧
    admission "Valid(Rows/Tag For \"A\", \"Code\")" = .reader ∧
    admission "Valid(Rows/Tag -> Label, \"Code\")" = .reader ∧
    admission "Valid(Tag, \"Code\")" = .refused (some .noIterationForWildcard) ∧
    admission "Valid($Rows/Tag, \"Code\")" = .refused (some .noWildcard) ∧
    admission "[Rows/N] > 0 And Valid($Rows/Tag, \"Code\")" (binding := ["Form", "Rows"]) = .admitted := by native_decide

example : admission "Valid(Rows/Tag, \"Code\")" { (model {}) with fields := (model {}).fields.map fun field =>
      if field.id == 3 then { field with stringValueMode := .raw, stringPolicy := { lineBreaksPermitted := true } } else field } = .refused (some .rawTypeOperandInvalid) ∧
    admission "Invalid(Rows/Tag, \"Code\")" { (model {}) with fields := (model {}).fields.map fun field =>
      if field.id == 3 then { field with customType := some { name := "Other" }, stringPolicy := {} } else field } =
      .refused (some .noStringOrEnumOrExtEnum) := by native_decide

private def noWorld (filter : String) (scenario : Scenario := {}) : Option (Sum CheckedAddressingError Verdict) := do
  let prepared ← (fixture scenario).toOption
  let parsed ← (parseText .english (sum filter ++ " > 0")).toOption
  let condition ← (lowerCondition (model scenario) ["Form"] false parsed.body).toOption
  pure (match condition.core.evalAddressed {
    scalar := { fields := prepared.document.flatContext, groups := GroupPresenceContext.unavailable },
    outer := [], input := .checked prepared.document } with | .error error => .inl error | .ok verdict => .inr verdict)

example : noWorld (predicate "Valid") = some (.inl .worldUnavailable) ∧
    noWorld (predicate "Invalid") { tags := ["", "", ""] } = some (.inr .notFired) ∧
    noWorld ("[Rows/N] > 100 And " ++ predicate "Valid") = some (.inr .notFired) ∧
    noWorld (predicate "Valid" ++ " And [Rows/N] > 100") = some (.inl .worldUnavailable) := by native_decide

private def temporalOutcome (suppliedWorld : Bool) : Option (Sum DocumentComputationStepFault DocumentTargetOutcome) := do
  let scenario : Scenario := { targetKind := .temporal .date .fullDate }
  let prepared ← (fixture scenario).toOption
  let parsed ← (parseText .english ("MinValue(Rows*/Stamp Having " ++ predicate "Valid" ++ ")")).toOption
  let surface ← (lowerScalarTemporalExpression (model scenario) ["Form"] parsed.body).toOption
  let expression ← (elaborateScalarTemporalExpression (model scenario) ["Form"] surface).toOption
  let operation ← checkTemporalExpressionComputation? expression 5
  pure (match operation.run { prepared.document.computationContext with
      world := if suppliedWorld then some (world false) else none } with
    | .error error => .inl error | .ok (outcome, _) => .inr outcome)

example : temporalOutcome false = some (.inl (.temporalExpressionAddressing .worldUnavailable)) ∧
    temporalOutcome true = some (.inr (.valueError .fullDate)) := by native_decide

private def partialSkipped : Option Bool := do
  let scenario : Scenario := { rows := true }
  let prepared ← (fixture scenario).toOption
  let checked ← (checkRule {
    flat := model scenario, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    .english {
      group := ["Form"], name := "Filtered", errorCode := "FILTERED", errorEntityRelPath := "../Rows/N",
      condition := "FieldFilled(Rows/N) And " ++ sum (predicate "Valid") ++ " > 0", severity := "ERROR" }).toOption
  pure (match checked.evalOrdinaryRepeatablePartial prepared.document .full with
    | .ok .skipped => true | _ => false)

example : partialSkipped = some true := by native_decide

private def otherGroup : FlatModel := { (model {}) with
  fields := (model {}).fields ++ [{
    id := 10, name := "Tag", groupPath := ["Form", "Other"],
    repeatableScope := [20], policy := { kind := .string } }]
  repeatableGroups := (model {}).repeatableGroups ++ [{ level := 20, path := ["Form", "Other"], repeatability := some 2 }] }

example : admission "[Rows/N] > 0 And Valid(Other/Tag, \"Code\")" otherGroup =
    .refused (some .invalidIterationInFilterCondition) := by native_decide

example : HavingFixture.referencesFor "Valid(Tag, \"Code\")" = some (true, false) ∧
    HavingFixture.referencesFor "[N] > 0 And Invalid($Tag, \"Code\")" = some (true, true) := by native_decide

end A12Kernel.Dm.HavingTypeValidityLocks
