import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.BoundTextComparisonLocks
open Lean

private def model (kind : FieldKind) : FlatModel := {
  fields := ([1, 2, 3] : List Nat).map fun id => {
    id, name := if id == 3 then "B" else "A"
    groupPath := if id == 1 then ["Form"] else ["Form", "Rows"]
    repeatableScope := if id == 1 then [] else [10]
    policy := { kind }
    stringPolicy := if kind == .string then { maxLength := some 1 } else {}
    enumeration := if kind == .enumeration then some {
      storedTokens := ["1", "2"], categories := [{ name := "Swap", tokens := ["2", "1"] }] } else none }
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 }] }

private def dm (kind : FieldKind) (candidate : FlatModel := model kind) : DmModel := {
  flat := candidate, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
private def world : World := { now := { epochMillis := 0 } }
private def rule (condition : String) : DmRule := {
  group := ["Form"], name := "Text", errorCode := "TEXT", severity := "ERROR"
  errorEntityRelPath := "../Rows/A", condition }

private def document (kind : FieldKind) (rows : List (String × String))
    (candidate : FlatModel := model kind) : Option (CheckedDocument candidate) := do
  let input ← (readDocument (dm kind candidate) (.mkObj [("Form", .mkObj [
    ("A", .str "2"), ("Rows", .arr (rows.map fun (a, b) =>
      Json.mkObj [("A", .str a), ("B", .str b)]).toArray)])])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler candidate).toOption
  (checkDocument prepared "en_US" input.data).toOption

private def run (kind : FieldKind) (condition : String)
    (rows : List (String × String) := [("1", "1"), ("2", "1")])
    (candidate : FlatModel := model kind) (definition? : Option DmRule := none) : Option (List String) := do
  let checked ← (checkRule (dm kind candidate) .english (definition?.getD (rule condition))).toOption
  let document ← document kind rows candidate
  pure ((← (runRule world document checked).toOption).map fun message => (observe candidate message).pointer)

example : (model .string).validate.isOk = true ∧ (model .enumeration).validate.isOk = true := by native_decide

example : run .string "[Rows/A] == \"1\"" = some ["Form/Rows/A"] ∧
    run .string "[Rows/A] != [Rows/B]" = some ["Form/Rows[2]/A"] := by native_decide

example : run .enumeration "[Rows/A] == \"1\"" = some ["Form/Rows/A"] ∧
    run .enumeration "[Rows/A -> Swap] == \"1\"" = some ["Form/Rows[2]/A"] := by native_decide

example :
    run .enumeration "[Rows/A -> Swap] == [Rows/B]" = some ["Form/Rows[2]/A"] ∧
    run .enumeration "[Rows/A] == [Rows/B -> Swap]" = some ["Form/Rows[2]/A"] ∧
    run .enumeration "[Rows/A -> Swap] == [Rows/B -> Swap]" = some ["Form/Rows/A"] := by native_decide

private def partialVerdicts (kind : FieldKind) (condition : String) (scope : ValidationRelevanceScope)
    (rows : List (String × String) := [("1", "1"), ("2", "1")])
    (candidate : FlatModel := model kind) : Option (List (Option Verdict)) := do
  let checked ← (checkRule (dm kind candidate) .english (rule condition)).toOption
  let document ← document kind rows candidate
  let .evaluated outcomes ← (checked.evalOrdinaryRepeatablePartial document scope (some world)).toOption | none
  pure (outcomes.map fun (_, outcome) => match outcome with
    | .skipped => none | .evaluated result => some result.verdict)

example : partialVerdicts .string "[Rows/A] == [Rows/B]" .full =
    some [some (.fired .value), some .notFired] ∧
    partialVerdicts .string "[Rows/A] == [Rows/B]"
      (.partialSet [{ path := ["Form", "Rows", "A"], indices := [.all, .all, .all] }]) =
    some [some .unknown, some .unknown] := by native_decide

example : run .string "GroupFilled(Rows) And ([Rows/A] == \"1\" Or Now < \"31.03.2024T02:30:00\")"
    [("1", "1"), ("1", "1")] { (model .string) with timeZoneId := "Europe/Berlin" } =
    some ["Form/Rows/A"] := by native_decide

private def kinds : List FieldKind := [.string, .enumeration]
private def operators := ["==", "!="]
private def first := ["Form/Rows/A"]
private def second := ["Form/Rows[2]/A"]
private def rowField (name : String) (row? : Option Nat := none) : RelevantEntityPattern := {
  path := ["Form", "Rows", name]
  indices := [.all, row?.map RelevanceIndex.concrete |>.getD .all, .all] }

example : kinds.all (fun kind => operators.all fun op =>
    let expected := if op == "==" then first else second
    run kind ("[Rows/A] " ++ op ++ " \"1\"") == some expected &&
    run kind ("\"1\" " ++ op ++ " [Rows/A]") == some expected &&
    run kind ("[Rows/A] " ++ op ++ " [Rows/B]") == some expected &&
    run kind ("[Rows/B] " ++ op ++ " [Rows/A]") == some expected &&
    run kind ("[Rows/A] " ++ op ++ " \"1\"") [("2", "1"), ("1", "1")] ==
      some (if op == "==" then second else first)) = true := by native_decide

example : operators.all (fun op =>
    let projected := if op == "==" then second else first
    run .enumeration ("[Rows/A -> Swap] " ++ op ++ " \"1\"") == some projected &&
    run .enumeration ("\"1\" " ++ op ++ " [Rows/A -> Swap]") == some projected &&
    run .enumeration ("[Rows/A -> Swap] " ++ op ++ " [Rows/B]") == some projected &&
    run .enumeration ("[Rows/A] " ++ op ++ " [Rows/B -> Swap]") == some projected &&
    run .enumeration ("[Rows/A -> Swap] " ++ op ++ " [Rows/B -> Swap]") ==
      some (if op == "==" then first else second)) = true := by native_decide

example : kinds.all (fun kind => operators.all fun op =>
    let expected := if op == "==" then second else first
    run kind ("[Rows/A] " ++ op ++ " [A]") == some expected &&
    run kind ("[A] " ++ op ++ " [Rows/A]") == some expected &&
    let ownCondition := "[A] " ++ op ++ " \"1\""
    run kind ownCondition (definition? := some {
      (rule ownCondition) with group := ["Form", "Rows"], errorEntityRelPath := "../A" }) ==
      some (if op == "==" then first else second) &&
    run kind ("FieldFilled(Rows/A) And ([A] " ++ op ++ " \"2\")") ==
      some (if op == "==" then first ++ second else [])) = true := by native_decide

-- The capacity is two rows, so the second partial environment is the absent row: its cells read
-- empty and it does not fire. The physical row's verdict is the first entry (spec/10 §5; partial
-- channel of the population replay, 2026-10-24).
example : kinds.all (fun kind => operators.all fun op =>
    let pair := "[Rows/A] " ++ op ++ " [Rows/B]"
    let literal := "[Rows/A] " ++ op ++ " \"1\""
    [(("", "1"), Verdict.notFired), (("bad", "1"), .unknown),
      (("1", ""), .notFired), (("1", "bad"), .unknown)].all (fun (row, expected) =>
      run kind pair [row] == some [] &&
      partialVerdicts kind pair .full [row] == some [some expected, some .notFired]) &&
    [("", Verdict.notFired), ("bad", .unknown)].all (fun (value, expected) =>
      run kind literal [(value, "1")] == some [] &&
      partialVerdicts kind literal .full [(value, "1")] == some [some expected, some .notFired]) &&
    run kind pair [] == some [] && run kind literal [] == some []) = true := by native_decide

example : kinds.all (fun kind => operators.all fun op =>
    let pair := "[Rows/A] " ++ op ++ " [Rows/B]"
    let firstVerdict := if op == "==" then .fired .value else Verdict.notFired
    let secondVerdict := if op == "==" then .notFired else Verdict.fired .value
    partialVerdicts kind pair .full == some [some firstVerdict, some secondVerdict] &&
    partialVerdicts kind pair (.partialSet [rowField "A", rowField "B"]) ==
      some [some firstVerdict, some secondVerdict] &&
    partialVerdicts kind pair (.partialSet [rowField "A"]) == some [some .unknown, some .unknown] &&
    partialVerdicts kind pair (.partialSet [rowField "A" (some 2), rowField "B" (some 2)]) ==
      some [none, some secondVerdict] &&
    partialVerdicts kind pair (.partialSet [rowField "A" (some 3), rowField "B" (some 3)]) ==
      some [none, none]) = true := by native_decide

private def defaultModel (field : FieldId) : FlatModel :=
  let base := model .enumeration
  { base with
    fields := base.fields.map fun declaration => if declaration.id != field then declaration else
      { declaration with enumeration := declaration.enumeration.map fun domain =>
          { domain with defaultStoredToken := some "2" } }
    repeatableGroups := base.repeatableGroups.map fun group => { group with indexField := some field } }

-- The second entry is the absent row of the two-row capacity: it reads empty and does not fire,
-- while the physical row stays unknown through its default token (spec/10 §5; partial channel of
-- the population replay, 2026-10-24).
example : (defaultModel 2).validate.isOk = true ∧ (defaultModel 3).validate.isOk = true ∧
    operators.all (fun op =>
      let body := "[Rows/A] " ++ op ++ " [Rows/B]"
      partialVerdicts .enumeration body (.partialSet [rowField "A", rowField "B"])
        [("1", "")] (defaultModel 3) == some [some .unknown, some .notFired] &&
      partialVerdicts .enumeration body (.partialSet [rowField "A", rowField "B"])
        [("", "1")] (defaultModel 2) == some [some .unknown, some .notFired]) = true := by native_decide

private def scalarAPI (kind : FieldKind) (op : String) (rows : Bool) : Option Bool := do
  let definition := { (rule ((if rows then "[Rows/A]" else "[A]") ++ " " ++ op ++ " \"1\"")) with
    errorEntityRelPath := if rows then "../Rows/A" else "../A" }
  let checked ← (checkRule (dm kind) .english definition).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler (model kind)).toOption
  let raw : RawFlatContext := { read := fun _ => .parsed (if kind == .enumeration then .enum "1" else .str "1") }
  let full := checked.evalFull prepared "en_US" raw GroupPresenceContext.unavailable true
  let part := checked.evalPartial prepared "en_US" raw GroupPresenceContext.unavailable .full
  pure (checked.requiresAddressedValidation == rows &&
    (match full, part with
    | .error .addressedContextRequired, .error .addressedContextRequired => rows
    | .ok full, .ok (.evaluated part) => !rows && full.verdict == part.verdict &&
        full.verdict == (if op == "==" then .fired .value else .notFired)
    | _, _ => false))

example : kinds.all (fun kind => operators.all fun op =>
    scalarAPI kind op true == some true && scalarAPI kind op false == some true) = true := by native_decide

private def metadata (kind : FieldKind) (condition : String) :
    Option (GroupPath × GroupPath × Option (List RepeatableLevel) × List FieldId × String) := do
  let checked ← (checkRule (dm kind) .english (rule condition)).toOption
  let .leaf (.flat (.compare comparison)) := checked.condition.core | none
  let form := match comparison with
    | .string _ _ _ => "string" | .textFields _ _ _ => "textFields"
    | .enumeration _ _ _ => "enumeration" | _ => "other"
  pure (checked.condition.declaringGroup, checked.condition.rowGroup,
    checked.iterationScope, comparison.fieldIds, form)

example : (metadata .string "[Rows/A] == \"1\"" ==
      some (["Form"], ["Form", "Rows"], some [10], [2], "string") &&
    metadata .enumeration "[Rows/A -> Swap] != \"1\"" ==
      some (["Form"], ["Form", "Rows"], some [10], [2], "enumeration") &&
    metadata .enumeration "[Rows/A -> Swap] == [A]" ==
      some (["Form"], ["Form", "Rows"], some [10], [2, 1], "textFields")) = true := by native_decide

private def admitted (kind : FieldKind) (condition : String) (candidate : FlatModel := model kind)
    (definition? : Option DmRule := none) : Bool :=
  (checkRule (dm kind candidate) .english (definition?.getD (rule condition))).isOk

private def mixedModel (kind : FieldKind) : FlatModel := { (model .string) with
  fields := (model .string).fields.map fun field => if field.id != 3 then field else {
    field with
    policy := { kind }
    stringPolicy := {}
    enumeration := if kind == .enumeration then some { storedTokens := ["1", "2"] } else none } }

private def displayModel (both : Bool) (conflict : Bool := false) : FlatModel := { (model .enumeration) with
  fields := (model .enumeration).fields.map fun field =>
    if field.id == 3 || (both && field.id == 2) then { field with
      enumeration := field.enumeration.map fun domain => { domain with displayFacts := [
        { locale := "en_US", stored := "1", display := if conflict && field.id == 3 then "two" else "one" },
        { locale := "en_US", stored := "2", display := if conflict && field.id == 3 then "one" else "two" }] } }
    else field }

example : (mixedModel .enumeration).validate.isOk = true ∧
    run .string "[Rows/A] == [Rows/B]" (candidate := mixedModel .enumeration) = some first ∧
    [FieldKind.number { scale := 0, signed := true }, .boolean].all (fun kind =>
      (mixedModel kind).validate.isOk && !admitted .string "[Rows/A] == [Rows/B]" (mixedModel kind)) = true ∧
    [displayModel false, displayModel true true, displayModel true].all (·.validate.isOk) = true ∧
    !admitted .enumeration "[Rows/A] == [Rows/B]" (displayModel false) ∧
    !admitted .enumeration "[Rows/A] == [Rows/B]" (displayModel true true) ∧
    admitted .enumeration "[Rows/A] == [Rows/B]" (displayModel true) ∧
    admitted .enumeration "[Rows/A -> Swap] == [Rows/B]" (displayModel false) := by native_decide

example : kinds.all (fun kind => operators.all fun op =>
    admitted kind ("[Rows/A] " ++ op ++ " \"1\"") &&
    ["<", "<=", ">", ">="].all (fun ordering => !admitted kind ("[Rows/A] " ++ ordering ++ " \"1\"")) &&
    !admitted kind ("[Rows/A] " ++ op ++ " [Rows/B]") (definition? := some {
      (rule ("FieldFilled(A) And ([Rows/A] " ++ op ++ " [Rows/B])")) with errorEntityRelPath := "../A" })) = true ∧
    operators.all (fun op =>
      !admitted .enumeration ("[Rows/A] " ++ op ++ " \"3\"") &&
      !admitted .enumeration ("[Rows/A -> Missing] " ++ op ++ " \"1\"")) = true := by native_decide

example :
    let rawModel := { (model .string) with fields := (model .string).fields.map fun field =>
      if field.id == 3 then { field with stringValueMode := .raw, stringPolicy := { lineBreaksPermitted := true } } else field }
    let sideModel := { (model .string) with fields := (model .string).fields ++ [{
      id := 4, name := "Marker", groupPath := ["Form", "Side"], policy := { kind := .string } }] }
    rawModel.validate.isOk && sideModel.validate.isOk &&
    admitted .string "[Rows/A] == [Rows/B]" &&
    !admitted .string "[Rows/A] == [Rows/B]" rawModel &&
    admitted .string "[Rows/A] == [Rows/B]" sideModel &&
    !admitted .string "[/Form/Rows/A] == [/Form/Rows/B]" sideModel (some {
      (rule "[/Form/Rows/A] == [/Form/Rows/B]") with
      group := ["Form", "Side"], errorEntityRelPath := "../../Rows/A" }) = true := by native_decide

example : run .string "[A] == \"1\" And (GroupFilled(Rows) And ([Rows/A] == \"1\" Or Now < \"31.03.2024T02:30:00\"))"
    [("1", "1"), ("1", "1")] { (model .string) with timeZoneId := "Europe/Berlin" } = some [] := by native_decide

end A12Kernel.Dm.BoundTextComparisonLocks
