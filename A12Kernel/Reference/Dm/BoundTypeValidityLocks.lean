import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.BoundTypeValidityLocks
open Lean

private def model : FlatModel := {
  fields := [
    { id := 1, name := "Out", groupPath := ["Form"], policy := { kind := .string } },
    { id := 2, name := "Text", groupPath := ["Form"], policy := { kind := .string } },
    { id := 3, name := "Out", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } },
    { id := 4, name := "Text", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .string }, stringPolicy := { maxLength := some 1 } },
    { id := 5, name := "Enum", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .enumeration }, enumeration := some {
        storedTokens := ["x", "y"]
        displayFacts := [{ locale := "en_US", stored := "x", display := "y" },
          { locale := "en_US", stored := "y", display := "x" }] } },
    { id := 6, name := "Id", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } },
    { id := 7, name := "Number", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 8, name := "Marker", groupPath := ["Form", "Side"], policy := { kind := .string } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2, indexField := some 6 }] }

private def world (registered : Bool) : World := {
  now := { epochMillis := 0 }
  customFieldValidator? := fun name => if registered && name == "Code" then
    some (fun value context => if value == "x" && context == explicitCustomFieldValidationContext then none
      else some { projectCode := "TYPE_REJECTED" }) else none }

private def dm : DmModel := {
  flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

private def rule (condition : String) (rows : Bool := true) : DmRule := {
  group := ["Form"], name := "Validity", errorCode := "VALIDITY", severity := "ERROR"
  errorEntityRelPath := if rows then "../Rows/Out" else "../Out"
  condition := if rows then "FieldFilled(Rows/Out) And (" ++ condition ++ ")" else condition }

private def checkedDocument (registered : Bool) (values : List String) :
    Option (CheckedDocument model) := do
  let world := world registered
  let data := values.zip ["A", "B"] |>.map fun (value, key) => Json.mkObj [
    ("Out", "ready"), ("Text", .str value), ("Enum", .str value), ("Id", .str key)]
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Out", "ready"), ("Text", "y"), ("Number", "1"),
    ("Side", Json.mkObj [("Marker", "ready")]), ("Rows", .arr data.toArray)])])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" input.data).toOption

private def observed (condition : String) (registered : Bool := true) (rows : Bool := true)
    (values : List String := ["x", "y"]) (definition? : Option DmRule := none) :
    Option (List (String × String)) := do
  let world := world registered
  let checked ← (checkRule dm .english (definition?.getD (rule condition rows)) world).toOption
  let document ← checkedDocument registered values
  pure ((← (runRule world document checked).toOption).map fun message =>
    let result := observe model message
    (result.pointer, result.messageType))

private def first := [("Form/Rows/Out", "VALUE_ERROR")]
private def second := [("Form/Rows[2]/Out", "VALUE_ERROR")]
private def root := [("Form/Out", "VALUE_ERROR")]

private def scalarVerdict (condition : String) (registered : Bool) : Option Verdict := do
  let checked ← (checkRule dm .english (rule condition false) (world registered)).toOption
  let document ← checkedDocument registered ["x", "y"]
  pure (checked.condition.core.evalFull {
    fields := document.flatContext.withWorld (world registered), groups := GroupPresenceContext.unavailable } true)

example : ["Valid", "Invalid"].all (fun op =>
    let leaf := s!"{op}(Text,\"Code\")"
    scalarVerdict (leaf ++ " And FieldNotFilled(Out)") false == some (.fired .value) &&
    scalarVerdict ("FieldNotFilled(Out) And " ++ leaf) false == some .notFired &&
    scalarVerdict (leaf ++ " And FieldNotFilled(Out)") true == some .notFired) = true := by native_decide

example : ["Text", "Enum"].all (fun field =>
    observed s!"Valid(Rows/{field},\"Code\")" == some first &&
    observed s!"Invalid(Rows/{field},\"Code\")" == some second) = true := by native_decide

example : ["Valid", "Invalid"].all (fun op =>
    observed s!"{op}(Text,\"Code\") And FieldNotFilled(Out)" false false == some root &&
    observed s!"{op}(Rows/Text For \"A\",\"Code\") And FieldNotFilled(Out)" false false == some root) = true := by native_decide

example : model.validate.isOk = true ∧
    ["Text", "Enum"].all (fun field =>
      observed s!"Valid(Rows/{field},\"Code\")" true true ["y", "x"] == some second &&
      observed s!"Invalid(Rows/{field},\"Code\")" true true ["y", "x"] == some first &&
      [false, true].all fun registered => ["Valid", "Invalid"].all fun op =>
        observed s!"{op}(Rows/{field},\"Code\")" registered true ["", "long"] == some [] &&
        observed s!"{op}(Rows/{field},\"Code\")" registered true [] == some []) = true := by native_decide

example : ["Valid", "Invalid"].all (fun op =>
    let expected := if op == "Valid" then [] else root
    observed s!"FieldFilled(Out) And {op}(Text,\"Code\")" true false == some expected &&
    observed s!"FieldFilled(Rows/Out) And {op}(Text,\"Code\")" ==
      some (if op == "Valid" then [] else first ++ second) &&
    ["Text", "Enum"].all fun field =>
      observed s!"{op}(Rows/{field},\"Code\")" false == some first) = true := by native_decide

example : ["Text", "Rows/Text For \"A\"", "Rows/Enum For \"A\""].all (fun source =>
    ["Valid", "Invalid"].all fun op =>
      let leaf := s!"{op}({source},\"Code\")"
      observed (leaf ++ " And FieldNotFilled(Out)") false false == some root &&
      observed ("FieldNotFilled(Out) And " ++ leaf) false false == some [] &&
      observed ("FieldFilled(Out) Or " ++ leaf) false false == some root &&
      observed (leaf ++ " Or FieldFilled(Out)") false false == some root &&
      observed (leaf ++ " And FieldNotFilled(Out)") true false == some [] &&
      observed ("FieldNotFilled(Out) And " ++ leaf) true false == some [] &&
      observed ("FieldFilled(Out) Or " ++ leaf) true false == some root &&
      observed (leaf ++ " Or FieldFilled(Out)") true false == some root) = true := by native_decide

example : ["Text", "Enum"].all (fun field => ["Valid", "Invalid"].all fun op =>
    let leaf := s!"{op}(Rows/{field},\"Code\")"
    observed (leaf ++ " And FieldNotFilled(Rows/Out)") false == some first &&
    observed ("FieldNotFilled(Rows/Out) And " ++ leaf) false == some [] &&
    observed ("FieldFilled(Rows/Out) Or " ++ leaf) false == some (first ++ second) &&
    observed (leaf ++ " Or FieldFilled(Rows/Out)") false == some first &&
    observed (leaf ++ " And FieldNotFilled(Rows/Out)") true == some [] &&
    observed (leaf ++ " Or FieldFilled(Rows/Out)") true == some (first ++ second)) = true := by native_decide

private def rootOut : RelevantEntityPattern := { path := ["Form", "Out"], indices := [.all, .all] }
private def rootText : RelevantEntityPattern := { path := ["Form", "Text"], indices := [.all, .all] }
private def rowField (name : String) : RelevantEntityPattern := {
  path := ["Form", "Rows", name], indices := [.all, .all, .all] }
private def rowsRelevant : RelevantEntityPattern := { path := ["Form", "Rows"], indices := [.all, .all] }

private def partiallyObserved (condition : String) (registered : Bool) (rows : Bool)
    (coverage : List RelevantEntityPattern) (values : List String := ["x", "y"]) :
    Option (List Verdict) := do
  let world := world registered
  let checked ← (checkRule dm .english (rule condition rows) world).toOption
  let document ← checkedDocument registered values
  let scope := ValidationRelevanceScope.partialSet coverage
  if rows then
    let result ← (checked.evalOrdinaryRepeatablePartial document scope (some world)).toOption
    match result with
    | .skipped => none
    | .evaluated results => results.mapM fun (_, result) => match result with
        | .skipped => none
        | .evaluated outcome => some outcome.verdict
  else
    let result ← (checked.evalAddressedPartial document scope (some world)).toOption
    match result with
    | .skipped => none
    | .evaluated outcome => some [outcome.verdict]

example : ["Text", "Enum"].all (fun field => ["Valid", "Invalid"].all fun op =>
    let leaf := s!"{op}(Rows/{field},\"Code\")"
    partiallyObserved leaf false true [rowField "Out", rowField field] == some [.fired .value] &&
    partiallyObserved leaf false true [rowField "Out"] == some [.unknown, .unknown] &&
    partiallyObserved leaf true true [rowField "Out", rowField field] ==
      some (if op == "Valid" then [.fired .value, .notFired] else [.notFired, .fired .value]) &&
    partiallyObserved leaf false true [rowField "Out", rowField field] ["", "long"] == some [.unknown, .unknown]) = true := by native_decide

example : ["Valid", "Invalid"].all (fun op =>
    let direct := s!"{op}(Text,\"Code\")"
    let indexed := s!"{op}(Rows/Text For \"A\",\"Code\")"
    [direct, indexed].all (fun leaf =>
      let coverage := if leaf == direct then [rootOut, rootText] else [rootOut, rowsRelevant]
      partiallyObserved ("FieldFilled(Out) And " ++ leaf) false false coverage == some [.fired .value] &&
      partiallyObserved ("FieldFilled(Out) And " ++ leaf) false false [rootOut, rowField "Id"] == some [.unknown] &&
      partiallyObserved ("FieldNotFilled(Out) And " ++ leaf) false false coverage == some [.notFired] &&
      partiallyObserved (leaf ++ " And FieldNotFilled(Out)") false false coverage == some [.fired .value] &&
      partiallyObserved ("FieldFilled(Out) Or " ++ leaf) false false coverage == some [.fired .value] &&
      partiallyObserved (leaf ++ " Or FieldFilled(Out)") false false coverage == some [.fired .value]) &&
    partiallyObserved ("FieldFilled(Out) And " ++ direct) true false [rootOut, rootText] ==
      some [if op == "Valid" then .notFired else .fired .value] &&
    partiallyObserved ("FieldFilled(Out) And " ++ indexed) true false [rootOut, rowsRelevant] ==
      some [if op == "Valid" then .fired .value else .notFired]) = true := by native_decide

example : ["Text", "Enum"].all (fun field => ["Valid", "Invalid"].all fun op =>
    let condition := s!"{op}(Rows/{field},\"Code\")"
    let definition : DmRule := { (rule condition) with
      condition, errorEntityRelPath := "../Rows/" ++ field }
    let expected := if op == "Valid" then "Form/Rows/" ++ field else "Form/Rows[2]/" ++ field
    observed condition true true (definition? := some definition) == some [(expected, "VALUE_ERROR")]) = true := by native_decide

example : ["Text", "Enum"].all (fun field => ["Valid", "Invalid"].all fun op =>
    let leaf := s!"{op}(Rows/{field},\"Code\")"
    (checkRule dm .english (rule leaf)).isOk &&
    !(checkRule dm .english (rule ("FieldFilled(Out) And " ++ leaf) false)).isOk &&
    !(checkRule dm .english { (rule leaf) with
      group := ["Form", "Side"], errorEntityRelPath := "../../Rows/" ++ field
      condition := s!"{op}(/Form/Rows/{field},\"Code\")" }).isOk &&
    !(checkRule dm .english (rule s!"{op}(Rows/{field},\"\")")).isOk &&
    !(checkRule dm .english (rule s!"FieldFilled(Out) And {op}(Number,\"Code\")" false)).isOk) = true := by native_decide

example : [4, 5].all (fun source => [CustomFieldValidityOp.valid, .invalid].all fun operation =>
    (CheckedValidationCondition.fromCustomFieldValidity model ["Form"] (world true)
      source "Code" operation ["Form", "Rows"]).isOk &&
    !(CheckedValidationCondition.fromCustomFieldValidity model ["Form", "Side"] (world true)
      source "Code" operation ["Form", "Rows"]).isOk) = true := by native_decide

private def scalarEntryBoundary (source : String) (operation : String) (rows : Bool) : Option Bool := do
  let condition := s!"{operation}({source},\"Code\")"
  let checked ← (checkRule dm .english { (rule condition rows) with
    condition, errorEntityRelPath := "../" ++ source } (world true)).toOption
  let prepared ← (prepareFlatStringContext (world true) builtinStringPatternCompiler model).toOption
  let raw : RawFlatContext := { read := fun _ => .empty }
  let full := checked.evalFull prepared "en_US" raw GroupPresenceContext.unavailable true
  let part := checked.evalPartial prepared "en_US" raw GroupPresenceContext.unavailable .full
  pure (checked.requiresAddressedValidation == rows &&
    (match full with | .error .addressedContextRequired => rows | .ok _ => !rows) &&
    (match part with | .error .addressedContextRequired => rows | .ok _ => !rows))

example : ["Valid", "Invalid"].all (fun operation =>
    scalarEntryBoundary "Text" operation false == some true &&
    ["Rows/Text", "Rows/Enum"].all fun source =>
      scalarEntryBoundary source operation true == some true) = true := by native_decide

end A12Kernel.Dm.BoundTypeValidityLocks
