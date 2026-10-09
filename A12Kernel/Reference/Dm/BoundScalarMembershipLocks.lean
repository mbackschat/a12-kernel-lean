import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.BoundScalarMembershipLocks
open Lean

private def model (kind : FieldKind) : FlatModel := {
  fields := ([1, 2, 3, 4, 5, 6, 7] : List Nat).map fun id => {
    id, name := if id <= 2 then "A" else if id == 3 then "B" else if id == 4 then "C"
      else if id == 5 then "RootB" else if id == 6 then "RootC" else "Marker"
    groupPath := if id >= 2 && id <= 4 then ["Form", "Rows"] else if id == 7 then ["Form", "Side"] else ["Form"]
    repeatableScope := if id >= 2 && id <= 4 then [10] else []
    policy := { kind }
    stringPolicy := if kind == .string then { maxLength := some 1 } else {}
    enumeration := if kind == .enumeration then some {
      storedTokens := ["1", "2"], categories := [{ name := "Swap", tokens := ["2", "1"] }] } else none }
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 }] }

private structure Row where
  a : String := "1"
  b : String := "1"
  c : String := "2"

private structure Inputs where
  a : String := "2"
  b : String := "1"
  c : String := "2"
  rows : List Row := [{}, { a := "2" }]

private def rule (condition : String) (rows : Bool := true) : DmRule := {
  group := ["Form"], name := "Membership", errorCode := "MEMBERSHIP", severity := "ERROR"
  errorEntityRelPath := if rows then "../Rows/A" else "../A", condition }

private def checkedDocument (kind : FieldKind) (inputs : Inputs)
    (candidate : FlatModel := model kind) : Option (CheckedDocument candidate) := do
  let model := candidate
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let row (value : Row) := Json.mkObj [("A", .str value.a), ("B", .str value.b), ("C", .str value.c)]
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("A", .str inputs.a), ("RootB", .str inputs.b), ("RootC", .str inputs.c),
    ("Rows", .arr (inputs.rows.map row).toArray)])])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" input.data).toOption

private def run (kind : FieldKind) (condition : String) (rows : Bool := true)
    (inputs : Inputs := {}) (candidate : FlatModel := model kind) : Option (List String) := do
  let model := candidate
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let checked ← (checkRule dm .english (rule condition rows)).toOption
  let document ← checkedDocument kind inputs model
  let world : World := { now := { epochMillis := 0 } }
  pure ((← (runRule world document checked).toOption).map fun message => (observe model message).pointer)

private def kinds : List FieldKind := [.number { scale := 0, signed := true }, .string, .enumeration]

example : kinds.all (fun kind => (model kind).validate.isOk) = true := by native_decide

example : run .string "FieldValueIncludedInValueList(A,\"2\")" false = some ["Form/A"] ∧
    run (.number { scale := 0, signed := true }) "FieldValueNotIncludedInValueList(A,1)" false = some ["Form/A"] := by native_decide

example : kinds.all (fun kind =>
    run kind "FieldValueIncludedInValueList(Rows/A,[Rows/B])" == some ["Form/Rows/A"] &&
    run kind "FieldValueNotIncludedInValueList(Rows/A,[Rows/B])" == some ["Form/Rows[2]/A"] &&
    let literal := if kind == .number { scale := 0, signed := true } then "1" else "\"1\""
    run kind ("FieldValueIncludedInValueList(Rows/A," ++ literal ++ ")") == some ["Form/Rows/A"]) = true := by native_decide

example : run .enumeration "FieldValueIncludedInValueList(Rows/A -> Swap,[Rows/B])" = some ["Form/Rows[2]/A"] := by native_decide

private def operators := ["FieldValueIncludedInValueList", "FieldValueNotIncludedInValueList"]
private def first := ["Form/Rows/A"]
private def second := ["Form/Rows[2]/A"]
private def admitted (kind : FieldKind) (condition : String) (rows : Bool := true)
    (error : String := "../Rows/A") : Bool :=
  (checkRule { flat := model kind, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    .english { (rule condition rows) with errorEntityRelPath := error }).isOk

example : kinds.all (fun kind => operators.all fun op =>
    let literal := if kind == .number { scale := 0, signed := true } then "1" else "\"1\""
    let expected := if op == "FieldValueIncludedInValueList" then first else second
    run kind (op ++ "(Rows/A,[Rows/B])") == some expected &&
    run kind (op ++ "(Rows/A," ++ literal ++ ")") == some expected &&
    run kind (op ++ "(Rows/A,[Rows/B])") true { rows := [{ a := "2" }, {}] } ==
      some (if op == "FieldValueIncludedInValueList" then second else first) &&
    run kind (op ++ "(Rows/A,[A])") ==
      some (if op == "FieldValueIncludedInValueList" then second else first)) = true := by native_decide

example : kinds.all (fun kind => operators.all fun op =>
    let body := op ++ "(A,[RootB])"
    run kind body false { a := "" } == some [] && run kind body false { a := "bad" } == some [] &&
    run kind body false { b := "" } == some (if op == "FieldValueIncludedInValueList" then [] else ["Form/A"]) &&
    run kind body false { b := "bad" } == some [] &&
    run kind (op ++ "(Rows/A,[Rows/B])") true { rows := [{ a := "" }, { a := "bad" }] } == some [] &&
    run kind (op ++ "(Rows/A,[Rows/B])") true { rows := [{ b := "" }, { a := "2", b := "" }] } ==
      some (if op == "FieldValueIncludedInValueList" then [] else first ++ second) &&
    run kind (op ++ "(Rows/A,[Rows/B])") true { rows := [{ b := "bad" }, { a := "2", b := "bad" }] } == some [] &&
    run kind (op ++ "(Rows/A,[Rows/B])") true { rows := [] } == some [] &&
    ["[Rows/B],[Rows/C]", "[Rows/C],[Rows/B]"].all fun members =>
      run kind (op ++ "(Rows/A," ++ members ++ ")") true { rows := [{ b := "bad" }, { a := "2", b := "bad" }] } ==
        some (if op == "FieldValueIncludedInValueList" then second else [])) = true := by native_decide

example : operators.all (fun op =>
    run .enumeration (op ++ "(Rows/A,[Rows/B -> Swap])") ==
      some (if op == "FieldValueIncludedInValueList" then second else first) &&
    run .enumeration (op ++ "(Rows/A -> Swap,[Rows/B -> Swap])") ==
      some (if op == "FieldValueIncludedInValueList" then first else second)) = true := by native_decide

example : kinds.all (fun kind =>
    admitted kind "FieldValueIncludedInValueList(A,[Rows/B],[Rows/C])" true "../Rows/B" &&
    !admitted kind "FieldValueIncludedInValueList(A,[Rows/B],[RootC])" true "../Rows/B" &&
    !admitted kind "FieldValueNotIncludedInValueList(A,[Rows/B])" true "../Rows/B" &&
    admitted kind "FieldFilled(Rows/B) And FieldValueIncludedInValueList(A,[Rows/B],[RootC])" true "../Rows/B" &&
    admitted kind "FieldFilled(Rows/B) And FieldValueNotIncludedInValueList(A,[Rows/B])" true "../Rows/B") = true := by native_decide

private def rowField (name : String) : RelevantEntityPattern := {
  path := ["Form", "Rows", name], indices := [.all, .all, .all] }

private def partiallyObserved (kind : FieldKind) (condition : String)
    (coverage : List RelevantEntityPattern) (inputs : Inputs := {})
    (candidate : FlatModel := model kind) (error : String := "../Rows/A") : Option (List Verdict) := do
  let model := candidate
  let checked ← (checkRule { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    .english { (rule condition) with errorEntityRelPath := error }).toOption
  let document ← checkedDocument kind inputs model
  let .evaluated results ← (checked.evalOrdinaryRepeatablePartial document (.partialSet coverage)).toOption | none
  results.mapM fun (_, result) => match result with
    | .skipped => none
    | .evaluated outcome => some outcome.verdict

example : kinds.all (fun kind => operators.all fun op =>
    let body := op ++ "(Rows/A,[Rows/B])"
    partiallyObserved kind body [rowField "A", rowField "B"] ==
      some (if op == "FieldValueIncludedInValueList" then [.fired .value, .notFired] else [.notFired, .fired .value]) &&
    partiallyObserved kind body [rowField "A"] ==
      some (if op == "FieldValueIncludedInValueList" then [.notFired, .notFired] else [.unknown, .unknown])) = true := by native_decide

private def scalarAPI (kind : FieldKind) (condition : String) (rows : Bool) : Option Bool := do
  let model := model kind
  let checked ← (checkRule { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    .english (rule condition rows)).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let raw : RawFlatContext := { read := fun _ => .parsed (match kind with
    | .number _ => .num 2 | .enumeration => .enum "2" | _ => .str "2") }
  let full := checked.evalFull prepared "en_US" raw GroupPresenceContext.unavailable true
  let part := checked.evalPartial prepared "en_US" raw GroupPresenceContext.unavailable .full
  pure (checked.requiresAddressedValidation == rows &&
    (if rows then match full, part with
      | .error .addressedContextRequired, .error .addressedContextRequired => true
      | _, _ => false
      else full.isOk && part.isOk))

example : kinds.all (fun kind => operators.all fun op =>
    let literal := if kind == .number { scale := 0, signed := true } then "1" else "\"1\""
    scalarAPI kind (op ++ "(Rows/A,[Rows/B])") true == some true &&
    scalarAPI kind (op ++ "(Rows/A," ++ literal ++ ")") true == some true &&
    scalarAPI kind (op ++ "(A,[RootB])") false == some true &&
    scalarAPI kind (op ++ "(A," ++ literal ++ ")") false == some true) = true := by native_decide

private def metadata (kind : FieldKind) (condition : String) : Option (ValueListAuthoredForm × Bool) := do
  let model := model kind
  let parsed ← (parseText .english condition).toOption
  let checked ← (lowerCondition model ["Form"] false parsed.body (bindingGroup := ["Form", "Rows"])).toOption
  let .leaf leaf := checked.core | none
  let form ← match leaf with
    | .flat (.numberValueList _ _ _ form) | .flat (.tokenValueList _ _ _ form) => some form
    | _ => none
  pure (form, leaf.requiresClassificationPass)

example : kinds.all (fun kind =>
    let literal := if kind == .number { scale := 0, signed := true } then "1" else "\"1\""
    metadata kind "FieldValueIncludedInValueList(Rows/A,[Rows/B])" == some (.membership, true) &&
    metadata kind ("FieldValueNotIncludedInValueList(Rows/A," ++ literal ++ ")") == some (.membership, false) &&
    metadata kind "AtLeastOneFieldValueIncludedInValueList(A In RootB)" == some (.quantifier, false) &&
    metadata kind "NoFieldValueIncludedInValueList(A In RootB)" == some (.quantifier, true)) = true := by native_decide

example : kinds.all (fun kind => operators.all fun op =>
    ["([Rows/A],[Rows/B])", "(Rows/A,Rows/B)", "(Rows/A)", "(Rows/A,[Rows/B],\"1\")",
      "(Rows,[Rows/B])", "(Rows*/A,[Rows/B])", "(Rows/A,[Rows])", "(Rows/A,[Rows*/B])"].all
      (fun args => !admitted kind (op ++ args)) &&
    !admitted kind (op ++ "(Rows/A,[Rows/B])") false "../A" &&
    !(checkRule { flat := model kind, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
      .english { (rule (op ++ "(/Form/Rows/A,[/Form/Rows/B])")) with
        group := ["Form", "Side"], errorEntityRelPath := "../../Rows/A" }).isOk) = true := by native_decide

example : operators.all (fun op =>
    admitted .enumeration (op ++ "(Rows/A -> Swap,\"2\")") &&
    !admitted .enumeration (op ++ "(Rows/A -> Missing,\"2\")") &&
    !admitted .enumeration (op ++ "(Rows/A,\"3\")") &&
    !admitted .string (op ++ "(Rows/A,1)")) = true := by native_decide

private def defaultModel (field : FieldId) : FlatModel :=
  let base := model .enumeration
  { base with
    fields := base.fields.map fun declaration => if declaration.id != field then declaration else
      { declaration with enumeration := declaration.enumeration.map fun domain =>
          { domain with defaultStoredToken := some "2" } }
    repeatableGroups := base.repeatableGroups.map fun group => { group with indexField := some field } }

example : (defaultModel 2).validate.isOk = true ∧ (defaultModel 3).validate.isOk = true := by native_decide

example :
    run .enumeration "FieldValueIncludedInValueList(Rows/A,[Rows/B],[Rows/C])" true
      { rows := [{ b := "", c := "1" }] } (defaultModel 3) = some first ∧
    partiallyObserved .enumeration "FieldValueIncludedInValueList(Rows/A,[Rows/B],[Rows/C])"
      [rowField "A", rowField "B", rowField "C"]
      { rows := [{ b := "", c := "1" }] } (defaultModel 3) = some [.fired .value] := by native_decide

example :
    partiallyObserved .enumeration "FieldValueNotIncludedInValueList(Rows/A,[Rows/C])"
      [rowField "A", rowField "C"] { rows := [{ a := "", c := "1" }] }
      (defaultModel 2) "../Rows/C" = some [.notFired] := by native_decide

example : operators.all (fun op =>
    let base := model (.number { scale := 0, signed := true })
    let mixed := { base with fields := base.fields.map fun declaration =>
      if declaration.id == 3 then { declaration with policy := { kind := .string } } else declaration }
    let dm candidate : DmModel := { flat := candidate, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    base.validate.isOk && mixed.validate.isOk &&
    (checkRule (dm base) .english (rule (op ++ "(Rows/A,[Rows/B])"))).isOk &&
    !(checkRule (dm mixed) .english (rule (op ++ "(Rows/A,[Rows/B])"))).isOk) = true := by native_decide

end A12Kernel.Dm.BoundScalarMembershipLocks
