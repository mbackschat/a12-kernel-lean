import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.NestedGroupCountLocks
open Lean A12Kernel

private def model : FlatModel :=
  let number (id : Nat) (group : GroupPath) (scope : List Nat) (name : String) : FlatFieldDecl :=
    { id, groupPath := group, repeatableScope := scope, name,
      policy := { kind := .number { scale := 0, signed := true } } }
  { fields := [
      { id := 1, groupPath := ["Form"], name := "Anchor", policy := { kind := .string } },
      number 2 ["Form", "Rows"] [10] "N", number 3 ["Form", "Rows"] [10] "M",
      number 4 ["Form", "Rows", "Items"] [10, 20] "N", number 5 ["Form", "Rows", "Items"] [10, 20] "M",
      number 6 ["Form", "Rows", "Items", "Detail"] [10, 20] "N",
      number 7 ["Form", "Rows", "Items", "Detail"] [10, 20] "M",
      number 8 ["Form", "Rows", "Items", "Desc"] [10, 20, 30] "N",
      number 9 ["Form", "Rows", "Items", "Desc"] [10, 20, 30] "M",
      number 10 ["Form"] [] "Target"]
    repeatableGroups := [
      { level := 10, path := ["Form", "Rows"], repeatability := some 2 },
      { level := 20, path := ["Form", "Rows", "Items"], repeatability := some 2 },
      { level := 30, path := ["Form", "Rows", "Items", "Desc"], repeatability := some 2 }] }

private def dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
private def world : World := { now := { epochMillis := 0 } }
private def item (bad : Bool := false) (extraDesc : Bool := false) (badExtra : Bool := false) : Json := Json.mkObj [
  ("N", .str (if bad then "bad" else "1")), ("M", .str "2"),
  ("Detail", Json.mkObj [("N", .str "3"), ("M", .str "4")]),
  ("Desc", .arr (#[Json.mkObj [("N", .str "5")], Json.mkObj [("N", .str "6")]] ++
    if extraDesc then #[Json.mkObj [("N", .str (if badExtra then "bad" else "7"))]] else #[]))]
private def row (items : Array Json) : Json := Json.mkObj [("N", .str "1"), ("M", .str "2"), ("Items", .arr items)]
private def full : Array Json := #[row #[item, item], row #[item, item]]
private def emptyPrefix : Array Json := #[row #[], row #[item, item]]
private def suffix : Array Json := #[row #[item, item], row #[]]
private def missing : Array Json := #[row #[item, item]]
private def input (rows : Array Json) : Json := Json.mkObj [("Form", Json.mkObj [
  ("Anchor", .str "on"), ("Target", .str "99"), ("Rows", .arr rows)])]

private def validate (rows : Array Json) (partialMode : Bool) (operand : String) (n : Nat)
    (scope : ValidationRelevanceScope := .partialSet [{ path := ["Form"], indices := [.all] }]) :
    Option (List Polarity) := do
  let data ← (readDocument dm (input rows)).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" data.data).toOption
  let rule ← (checkRule dm .english {
    name := "Count", group := ["Form"], errorCode := "Count", errorEntityRelPath := "../Anchor", severity := "ERROR",
    condition := "FieldFilled(Anchor) And NumberOfFilledGroups(" ++ operand ++ ") == " ++ toString n }).toOption
  let messages ← if partialMode then
    match ← (rule.evalAddressedPartial document scope (some world)).toOption with
    | .skipped => pure []
    | .evaluated outcome => pure outcome.message?.toList
  else (runRule world document rule).toOption
  pure (messages.map (·.messageType))

private def computeIn (dm : DmModel) (rows : Array Json) : Option (Nat × Verdict) := do
  let data ← (readDocument dm (input rows)).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let document ← (checkDocument prepared "en_US" data.data).toOption
  let lowered ← (lowerComputation dm.flat .english {
    group := ["Form"], name := "TargetComp", targetRelPath := "../Target", commonPrecondition := none,
    alternatives := [{ precondition := none, operation := "NumberOfFilledGroups(Rows*/Items*)" }], errorCodesToSuppress := [] }).toOption
  let .number table _ := lowered.2 | none
  let .atom atom@(.filledGroupCountMixed operands) := table.first.operation.operation.core.expression | none
  let read := fun env field => (document.checkedCellWithRead document.read env field).toOption.getD malformedCheckedCell
  let context : NumericComputationEvaluationContext := {
    scalar := { read := read [], world := some world }, document := document.source.toDocument,
    outer := [], filterRead := read, starRead := read }
  let .value computed ← (context.readCheckedNumericComputationAtom atom).toOption | none
  let channels ← (context.growthOfGroupCountOperands dm.flat operands).toOption
  let decided ← (context.groupCountOperandsDecided dm.flat operands).toOption
  let channels ← channels
  pure (computed.floor.toNat, computedNumberSelfValidationIfDecided decided 99 computed channels)

private def compute := computeIn dm

example : validate full false "Rows*/Items*" 4 = some [.value] := by native_decide
example : validate full true "Rows*/Items*" 4 = some [.value] := by native_decide
example : validate emptyPrefix false "Rows*/Items*" 2 = some [.omission] := by native_decide
example : validate emptyPrefix true "Rows*/Items*" 2 = some [.omission] := by native_decide
example : validate suffix false "Rows*/Items*" 2 = some [.omission] := by native_decide
example : validate suffix true "Rows*/Items*" 2 = some [.omission] := by native_decide
example : validate missing false "Rows*/Items*" 2 = some [.omission] := by native_decide
example : validate missing true "Rows*/Items*" 2 = some [.omission] := by native_decide
example : validate emptyPrefix true "Rows*/Items*/Detail" 2 = some [.omission] := by native_decide
example : validate full true "Rows*" 2 = some [.value] := by native_decide
example : validate #[row #[item true, item], row #[item, item]] false "Rows*/Items*" 4 = some [.value] := by native_decide
example : validate #[row #[item true, item], row #[item, item]] true "Rows*/Items*" 4 = some [] := by native_decide
example : validate #[row #[item, item], row #[item, item true]] true "Rows*/Items*" 4 = some [.value] := by native_decide
example : compute full = some (4, .fired .value) := by native_decide
example : compute emptyPrefix = some (2, .fired .omission) := by native_decide
example : compute suffix = some (2, .fired .omission) := by native_decide
example : compute missing = some (2, .fired .omission) := by native_decide

private def extraDescRows (bad : Bool) : Array Json :=
  #[row #[item false true bad, item], row #[item, item]]

example : validate (extraDescRows false) false "Rows*/Items*" 4 = some [.value] := by native_decide
example : validate (extraDescRows false) true "Rows*/Items*" 4 = some [.value] := by native_decide
example : validate (extraDescRows true) true "Rows*/Items*" 4 = some [.value] := by native_decide
example : validate (extraDescRows false) true "Rows*" 2 = some [.value] := by native_decide
example : validate (extraDescRows true) true "Rows*" 2 = some [.value] := by native_decide

private def boundModel (capacity : Nat := 2) : FlatModel := {
  model with
  fields := model.fields.map fun field => { field with
    groupPath := ["Form", "Parents"] ++ field.groupPath.drop 1
    repeatableScope := 1 :: field.repeatableScope }
  repeatableGroups := { level := 1, path := ["Form", "Parents"], repeatability := some 2 } ::
    model.repeatableGroups.map fun group => { group with
      path := ["Form", "Parents"] ++ group.path.drop 1, repeatability := some capacity } }

private def boundRun (condition : String) (isPartial : Bool) (capacity : Nat := 2)
    (first : Array Json := full) (second : Array Json := emptyPrefix)
    (scope : ValidationRelevanceScope := .partialSet [RelevantEntityPattern.allInstances ["Form"]]) :
    Option (List (String × String)) := do
  let model := boundModel capacity
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let parent := fun rows => Json.mkObj [("Anchor", .str "on"), ("Target", .str "99"), ("Rows", .arr rows)]
  let data ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Parents", .arr #[parent first, parent second])])])).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" data.data).toOption
  let rule ← (checkRule dm .english {
    name := "Bound", group := ["Form", "Parents"], errorCode := "BOUND", severity := "ERROR",
    errorEntityRelPath := "../Anchor", condition := "FieldFilled(Anchor) And " ++ condition }).toOption
  let messages ← if isPartial then
    match ← (rule.evalOrdinaryRepeatablePartial document scope (some world)).toOption with
    | .skipped => none
    | .evaluated outcomes => pure (outcomes.flatMap fun (_, outcome) => match outcome with
        | .skipped => [] | .evaluated result => result.message?.toList)
  else (runRule world document rule).toOption
  pure (messages.map fun message => let observed := observe model message
    (observed.pointer, observed.messageType))

example : [false, true].all (fun partialMode =>
    boundRun "NumberOfFilledGroups(Rows*/Items*/Desc*) == 8" partialMode ==
      some [("Form/Parents/Anchor", "VALUE_ERROR")] &&
    boundRun "NumberOfFilledGroups(Rows*/Items*/Desc*) == 4" partialMode ==
      some [("Form/Parents[2]/Anchor", "OMISSION_ERROR")]) = true := by native_decide

example : boundRun "NoGroupFilled(Rows*/Items*/Desc*)" true 40 #[] #[] =
    some [("Form/Parents/Anchor", "OMISSION_ERROR"),
      ("Form/Parents[2]/Anchor", "OMISSION_ERROR")] := by native_decide

private def boundTriples : List (Nat × Nat × Nat) :=
  [(1, 1, 1), (1, 1, 2), (1, 2, 1), (1, 2, 2),
    (2, 1, 1), (2, 1, 2), (2, 2, 1), (2, 2, 2)]

private def boundLeaves (outer : Nat) (triples : List (Nat × Nat × Nat)) :
    List RelevantEntityPattern :=
  triples.flatMap fun (row, item, desc) => ["N", "M"].map fun name => {
    path := ["Form", "Parents", "Rows", "Items", "Desc", name],
    indices := [.concrete 1, .concrete outer, .concrete row,
      .concrete item, .concrete desc, .all] }

private def boundAbsence (entities : List RelevantEntityPattern) :
    Option (List (String × String)) :=
  boundRun "NoGroupFilled(Rows*/Items*/Desc*)" true 2 #[] #[]
    (.partialSet (RelevantEntityPattern.allInstances ["Form", "Parents", "Anchor"] :: entities))

example : boundAbsence (boundLeaves 1 boundTriples) =
    some [("Form/Parents/Anchor", "OMISSION_ERROR")] := by native_decide
example : boundAbsence (boundLeaves 2 boundTriples) =
    some [("Form/Parents[2]/Anchor", "OMISSION_ERROR")] := by native_decide
example : boundAbsence (boundLeaves 1 [(1, 1, 1), (2, 2, 2)]) =
    some [] := by native_decide
example : boundAbsence (boundLeaves 1 [(1, 1, 1), (2, 2, 2), (1, 1, 1), (2, 2, 2)]) =
    some [] := by native_decide
example : boundAbsence (boundLeaves 1 (boundTriples.filter (· != (2, 2, 2)))) =
    some [] := by native_decide
example : boundAbsence (boundLeaves 1 ((boundTriples.filter (· != (2, 2, 2))) ++ [(2, 2, 3)])) =
    some [] := by native_decide
example : boundAbsence (boundLeaves 1 boundTriples ++ boundLeaves 2 boundTriples) =
    some [("Form/Parents/Anchor", "OMISSION_ERROR"),
      ("Form/Parents[2]/Anchor", "OMISSION_ERROR")] := by native_decide

private def boundCompute (operation : String) : Option (List (String × String)) := do
  let model := boundModel
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let parent := fun rows => Json.mkObj [("Anchor", .str "on"), ("Target", .str "99"), ("Rows", .arr rows)]
  let data ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Parents", .arr #[parent full, parent emptyPrefix])])])).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" data.data).toOption
  let (_, step) ← (lowerComputation model .english {
    group := ["Form", "Parents"], name := "Bound", targetRelPath := "../Target", commonPrecondition := none,
    alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
  pure ((← (runComputations world prepared document [step]).toOption).map fun result =>
    (result.pointer, result.outcome))

example : boundCompute "NumberOfFilledGroups(Rows*/Items*/Desc*)" =
    some [("Form/Parents/Target", "value 8"), ("Form/Parents[2]/Target", "value 4")] := by native_decide

/-- A starred group list keeps the declaring group it was resolved from when the error field binds
`Rows`, so the rule is admitted there as at the root; every computation generating its
self-validation rule at its target's row takes this shape (the `*StarDirectComp` rows of the
retained having-predicate-family capture). -/
private def boundGroupList (target condition : String) : Option (List (String × String)) := do
  let data ← (readDocument dm (input full)).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" data.data).toOption
  let rule ← (checkRule dm .english {
    name := "Listed", group := ["Form"], errorCode := "Listed", errorEntityRelPath := target, severity := "ERROR",
    condition := condition }).toOption
  pure ((← (runRule world document rule).toOption).map fun message =>
    let observed := observe model message
    (observed.pointer, observed.messageType))

-- The bare `[Rows/N]` read forces the error-field binding; without it the lexical attempt admits the
-- rule, so the first two rows guard nothing about the binding and only pin the shared values.
example :
    let fired := some [("Form/Rows/N", "VALUE_ERROR"), ("Form/Rows[2]/N", "VALUE_ERROR")]
    boundGroupList "../Rows/N" "FieldFilled(Rows/N) And AtLeastOneGroupFilled(Rows*/Items*)" = fired ∧
    boundGroupList "../Rows/N" "FieldFilled(Rows/N) And NoGroupFilled(Rows*/Items*)" = some [] ∧
    boundGroupList "../Rows/N" "FieldFilled(Rows/N) And AtLeastOneGroupFilled(Rows*/Items*) And [Rows/N] != 5" =
      fired ∧
    boundGroupList "../Rows/N" "FieldFilled(Rows/N) And NoGroupFilled(Rows*/Items*) And [Rows/N] != 5" = some [] ∧
    boundGroupList "../Anchor" "FieldFilled(Anchor) And AtLeastOneGroupFilled(Rows*/Items*)" =
      some [("Form/Anchor", "VALUE_ERROR")] := by native_decide

end A12Kernel.Dm.NestedGroupCountLocks
