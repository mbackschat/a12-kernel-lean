import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.PartialGroupOperandLocks
open Lean

private def parent (repeated : Bool) : GroupPath :=
  if repeated then ["Form", "Rows"] else ["Form"]

private def model (repeated : Bool) : FlatModel := {
  fields := {
    id := 0, groupPath := parent repeated, name := "Marker", policy := { kind := .string }
    repeatableScope := if repeated then [10] else [] } ::
    ([1, 2] : List Nat).map fun id => {
      id, groupPath := parent repeated ++ ["Pair"], name := if id == 1 then "A" else "B"
      repeatableScope := if repeated then [10] else []
      policy := { kind := .number { scale := 0, signed := id == 1 } } }
  repeatableGroups := if repeated then
    [{ level := 10, path := parent true, repeatability := some 2 }] else [] }

private inductive ReadFamily where
  | number | boolean | token | enumeration
  deriving DecidableEq

private def enumerationDomain (id : FieldId) : EnumerationDeclaration := {
  storedTokens := if id == 1 then ["X", "Y"] else ["Y", "X"]
  categories := [{ name := "Label", tokens := if id == 1 then ["AX", "AY"] else ["BY", "BX"] }] }

private def modelFor (family : ReadFamily) (repeated : Bool) : FlatModel :=
  let base := model repeated
  { base with
    fields := (base.fields.map fun field =>
      if field.id == 0 then field else
      match family with
      | .number => field
      | .boolean => { field with policy := { kind := .boolean } }
      | .token => { field with
          policy := { kind := .string }
          stringPolicy := { maxLength := some 1 } }
      | .enumeration => { field with
          policy := { kind := .enumeration }
          enumeration := some (enumerationDomain field.id) }) ++
      if family == .enumeration then [{
        id := 3, groupPath := parent repeated, name := "Other"
        repeatableScope := if repeated then [10] else []
        policy := { kind := .enumeration }
        enumeration := some { storedTokens := ["P", "Q"], categories := [{ name := "Label", tokens := ["X", "Y"] }] } }]
      else [] }

private def controlValues : ReadFamily → String × String
  | .number => ("1", "2")
  | .boolean => ("true", "false")
  | .token | .enumeration => ("X", "Y")

private def row (a b : String) : Json := Json.mkObj [
  ("Marker", .str "x"), ("Pair", Json.mkObj [("A", .str a), ("B", .str b)])]

private def result (repeated isPartial complete : Bool) (condition a b : String)
    (family : ReadFamily := .number) : Option (List (String × String)) := do
  let model := modelFor family repeated
  let dm : DmModel := {
    flat := model, rules := [], computations := []
    conditionLanguage := "en_US", refusals := [] }
  let row := fun a b => if family == .enumeration then Json.mkObj [
    ("Marker", .str "x"), ("Other", .str "P"), ("Pair", Json.mkObj [("A", .str a), ("B", .str b)])]
    else row a b
  let (controlA, controlB) := controlValues family
  let input ← (readDocument dm (Json.mkObj [("Form", if repeated then
    Json.mkObj [("Rows", .arr #[row a b, row controlA controlB])] else row a b)])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let checked ← (checkRule dm .english {
    name := "Group", group := parent repeated, errorCode := "GROUP", severity := "ERROR"
    errorEntityRelPath := "../Marker", condition := condition ++ " And FieldFilled(Marker)" }).toOption
  let scope := ValidationRelevanceScope.partialSet
    ((["Marker"] :: ((if complete then [["Pair", "A"], ["Pair", "B"]] else [["Pair", "A"]]) ++
      if family == .enumeration then [["Other"]] else [])).map
      fun suffix => RelevantEntityPattern.allInstances (parent repeated ++ suffix))
  let messages ← if isPartial then
    if repeated then
      match ← (checked.evalOrdinaryRepeatablePartial document scope (some world)).toOption with
      | .skipped => none
      | .evaluated outcomes => pure (outcomes.flatMap fun (_, outcome) => match outcome with
          | .skipped => [] | .evaluated result => result.message?.toList)
    else
      match ← (checked.evalAddressedPartial document scope (some world)).toOption with
      | .skipped => none
      | .evaluated result => pure result.message?.toList
  else (runRule world document checked).toOption
  pure (messages.map fun message => let observed := observe model message
    (observed.pointer, observed.messageType))

private def expected (repeated : Bool) (kind : String) : List (String × String) :=
  if repeated then [("Form/Rows/Marker", kind), ("Form/Rows[2]/Marker", "VALUE_ERROR")]
  else [("Form/Marker", kind)]

example : [false, true].all (fun repeated => [false, true].all fun isPartial =>
    result repeated isPartial true "Sum(Pair) > 2" "3" "" == some (expected repeated "VALUE_ERROR") &&
    result repeated isPartial true "Sum(Pair) > 2" "" "3" == some (expected repeated "OMISSION_ERROR") &&
    result repeated true false "Sum(Pair) > 2" "3" "" == some []) = true := by
  native_decide

private def messages (repeated : Bool) (firstKind : Option String) (secondFires : Bool) : List (String × String) :=
  (firstKind.toList.map fun kind => (if repeated then "Form/Rows/Marker" else "Form/Marker", kind)) ++
    if repeated && secondFires then [("Form/Rows[2]/Marker", "VALUE_ERROR")] else []

private def numericConditions : List (String × Bool) := [
  ("Sum(Pair) == 3", true), ("Sum(Pair) > 2", true),
  ("MinValue(Pair) == 3", false), ("MaxValue(Pair) == 3", false),
  ("NumberOfDifferentValues(Pair) == 1", false), ("NumberOfValueInFields(3 In Pair) == 1", false)]

private def numericCases (condition : String) : List (String × String × Option String) := [
  ("3", "", some (if condition == "Sum(Pair) > 2" then "VALUE_ERROR" else "OMISSION_ERROR")),
  ("", "3", some "OMISSION_ERROR"),
  ("1", "2", if condition == "Sum(Pair) == 3" || condition == "Sum(Pair) > 2" then some "VALUE_ERROR" else none),
  ("", "", none), ("bad", "3", none)]

example : numericConditions.all (fun (condition, secondFires) =>
    (numericCases condition).all (fun (a, b, kind) => [false, true].all (fun repeated =>
      [false, true].all (fun isPartial =>
        result repeated isPartial true condition a b == some (messages repeated kind secondFires)) &&
      result repeated true false condition a b == some []))) = true := by native_decide

private def tokenConditions : List (ReadFamily × String × String × String) := [
  (.boolean, "NumberOfValueInFields(True In Pair) == 1", "true", "false"),
  (.token, "NumberOfValueInFields(\"X\" In Pair) == 1", "X", "Y"),
  (.token, "NoFieldValueIncludedInValueList(Pair In \"Z\")", "X", "Y")]

example : tokenConditions.all (fun (family, condition, a, b) =>
    result false false true condition a b family == some (messages false (some "VALUE_ERROR") false) &&
    result false true true condition a b family == some (messages false (some "VALUE_ERROR") false)) = true := by native_decide

example : tokenConditions.all (fun (family, condition, a, b) => [false, true].all (fun isPartial =>
    result true isPartial true condition a b family == some (messages true (some "VALUE_ERROR") true))) = true := by native_decide

example : tokenConditions.all (fun (family, condition, a, b) => [false, true].all (fun repeated =>
    let emptyKind := if condition == "NoFieldValueIncludedInValueList(Pair In \"Z\")" then some "OMISSION_ERROR" else none
    let malformed := if family == .boolean then "bad" else "LONG"
    [false, true].all (fun isPartial =>
      result repeated isPartial true condition "" b family == some (messages repeated emptyKind true) &&
      result repeated isPartial true condition malformed b family == some (messages repeated none true)) &&
    result repeated true false condition a b family == some [] &&
    result repeated true false condition "" b family == some [] &&
    result repeated true false condition malformed b family == some [])) = true := by native_decide

example : [false, true].all (fun repeated => [false, true].all (fun isPartial =>
    result repeated isPartial true "NumberOfValueInFields(\"X\" In Pair, Other->Label) == 2" "X" "Y" .enumeration ==
      some (messages repeated (some "VALUE_ERROR") true)) &&
    result repeated true false "NumberOfValueInFields(\"X\" In Pair, Other->Label) == 2" "X" "Y" .enumeration == some []) = true := by native_decide

example : [false, true].all (fun repeated => [false, true].all (fun isPartial =>
    result repeated isPartial true "NumberOfDifferentValues(Pair) == 1" "X" "X" .token ==
      some (messages repeated (some "VALUE_ERROR") false) &&
    result repeated isPartial true "NumberOfDifferentValues(Pair) == 1" "" "Y" .token ==
      some (messages repeated (some "OMISSION_ERROR") false) &&
    result repeated isPartial true "NumberOfDifferentValues(Pair) == 1" "LONG" "Y" .token == some []) &&
    result repeated true false "NumberOfDifferentValues(Pair) == 1" "X" "X" .token == some []) = true := by
  native_decide

example : [false, true].all (fun repeated => [false, true].all (fun isPartial =>
    result repeated isPartial true "FirstFilledValue(Pair) == \"X\"" "X" "LONG" .token ==
      some (messages repeated (some "VALUE_ERROR") true) &&
    result repeated isPartial true "FirstFilledValue(Pair) == \"X\"" "" "X" .token ==
      some (messages repeated (some "OMISSION_ERROR") true) &&
    result repeated isPartial true "FirstFilledValue(Pair) == \"X\"" "LONG" "X" .token ==
      some (messages repeated none true)) &&
    result repeated true false "FirstFilledValue(Pair) == \"X\"" "X" "LONG" .token ==
      some (messages repeated (some "VALUE_ERROR") true) &&
    result repeated true false "FirstFilledValue(Pair) == \"X\"" "" "X" .token ==
      some (messages repeated none true)) = true := by native_decide

end A12Kernel.Dm.PartialGroupOperandLocks
