import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.BoundEntityListLocks
open A12Kernel A12Kernel.Dm Lean

private def number (id : FieldId) (group : GroupPath) (name : String)
    (scope : List RepeatableLevel := []) : FlatFieldDecl := {
  id, name, groupPath := group, repeatableScope := scope
  policy := { kind := .number { scale := 0, signed := true } } }

private def model : FlatModel := {
  fields := [number 1 ["Form"] "Out", number 2 ["Form", "Rows"] "Out" [10],
    number 3 ["Form", "Rows", "Pair"] "A" [10], number 4 ["Form", "Rows", "Pair"] "B" [10],
    number 5 ["Form", "Side"] "Marker",
    number 6 ["Form", "Rows", "Sub"] "C" [10],
    number 7 ["Form", "Rows", "Members"] "M" [10],
    number 8 ["Other"] "Marker",
    number 9 ["Form", "Rows", "Outer", "Inner"] "N" [10]]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 }] }

private def dm : DmModel := {
  flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }

private def rule (predicate : String) : DmRule := {
  group := ["Form"], name := "Rule", errorCode := "R", errorEntityRelPath := "../Rows/Out"
  condition := "FieldFilled(Rows/Out) And " ++ predicate, severity := "ERROR" }

private def row (a b : String) (c m : String := "") : Json := Json.mkObj [
  ("Out", "1"), ("Pair", Json.mkObj [("A", Json.str a), ("B", Json.str b)]),
  ("Sub", Json.mkObj [("C", Json.str c)]), ("Members", Json.mkObj [("M", Json.str m)])]

private def observed (predicate : String) (rows : List Json) (model : FlatModel := model) :
    Option (List (String × String)) := do
  let dm : DmModel := { dm with flat := model }
  let checked ← (checkRule dm .english (rule predicate)).toOption
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Out", "9"), ("Rows", Json.arr rows.toArray)])])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  pure ((← (runRule world document checked).toOption).map fun message =>
    let result := observe model message
    (result.pointer, result.messageType))

private def run (predicate : String) (rows : List Json) : Option (List String) :=
  (observed predicate rows).map (·.map Prod.fst)

example : model.validate.isOk = true := by native_decide

example : run "AllFieldsFilled(Rows/Pair)" [row "2" "3", row "2" ""] =
    some ["Form/Rows/Out"] := by native_decide

example : run "[Out] == 9 And AllFieldsFilled(Rows/Pair)" [row "2" "3", row "2" ""] =
    some ["Form/Rows/Out"] ∧
    run "AllFieldsFilled(Rows/Pair)" [row "2" "", row "2" "3"] =
    some ["Form/Rows[2]/Out"] := by native_decide

example :
    !(checkRule dm .english { (rule "AllFieldsFilled(Rows/Pair)") with
      errorEntityRelPath := "../Out"
      condition := "FieldFilled(Out) And FieldFilled(Rows/Out) And AllFieldsFilled(Rows/Pair)" }).isOk ∧
    !(checkRule dm .english { (rule "AllFieldsFilled(Rows/Pair)") with
      group := ["Form", "Side"], errorEntityRelPath := "../../Rows/Out"
      condition := "FieldFilled(/Form/Rows/Out) And AllFieldsFilled(/Form/Rows/Pair)" }).isOk := by native_decide

private def firstValue := [("Form/Rows/Out", "VALUE_ERROR")]
private def secondValue := [("Form/Rows[2]/Out", "VALUE_ERROR")]
private def firstOmission := [("Form/Rows/Out", "OMISSION_ERROR")]
private def secondOmission := [("Form/Rows[2]/Out", "OMISSION_ERROR")]

private def fieldOperators := ["AllFieldsFilled", "NoFieldFilled", "AtLeastOneFieldFilled",
  "MoreThanOneFieldFilled", "NotAllFieldsFilled", "NotExactlyOneFieldFilled", "FieldsNotCollectivelyFilled"]
private def groupOperators := ["AllGroupsFilled", "NoGroupFilled", "AtLeastOneGroupFilled",
  "NotAllGroupsFilled", "GroupsNotCollectivelyFilled"]
private def membershipOperators := ["AtLeastOneFieldValueIncludedInValueList", "NoFieldValueIncludedInValueList",
  "NotAllFieldValuesIncludedInValueList"]

private def matrix (operators : List String) (operands : String) (rows : List Json)
    (expected : List (List (String × String))) (model : FlatModel := model) : Bool :=
  operators.length == expected.length && (operators.zip expected).all fun (operator, messages) =>
    observed (operator ++ "(" ++ operands ++ ")") rows model == some messages

example : matrix fieldOperators "Rows/Pair" [row "2" "3", row "2" ""]
    [firstValue, [], firstValue ++ secondValue, firstValue, secondOmission, firstValue, secondOmission] = true ∧
    matrix fieldOperators "Rows/Pair" [row "2" "", row "2" "3"]
    [secondValue, [], firstValue ++ secondValue, secondValue, firstOmission, secondValue, firstOmission] = true := by native_decide

example : matrix fieldOperators "Rows/Pair" [row "" "", row "bad" ""]
    [[], firstOmission, [], [], firstOmission ++ secondOmission, firstOmission, []] = true := by native_decide

example : matrix groupOperators "Rows/Pair, Rows/Sub" [row "2" "3" "4", row "2" ""]
    [firstValue, [], firstValue ++ secondValue, secondOmission, secondOmission] = true ∧
    matrix groupOperators "Rows/Pair, Rows/Sub" [row "2" "", row "2" "3" "4"]
    [secondValue, [], firstValue ++ secondValue, firstOmission, firstOmission] = true := by native_decide

example : matrix groupOperators "Rows/Pair, Rows/Sub" [row "" "", row "bad" ""]
    [[], firstOmission, [], firstOmission ++ secondOmission, []] = true ∧
    observed "AtLeastOneGroupFilled(Rows/Pair)" [row "2" "", row "" ""] = some firstValue ∧
    observed "NoGroupFilled(Rows/Pair)" [row "2" "", row "" ""] = some secondOmission := by native_decide

private inductive Carrier where
  | number | string | enumeration | date
  deriving Repr, DecidableEq

private def carrierModel (carrier : Carrier) : FlatModel := { model with
  fields := model.fields.map fun field =>
    if field.id == 3 || field.id == 4 || field.id == 7 then
      match carrier with
      | .number => field
      | .string => { field with policy := { kind := .string }, stringPolicy := { maxLength := some 2 } }
      | .enumeration => { field with
          policy := { kind := .enumeration }
          enumeration := some { storedTokens := ["1", "2", "3", "4", "8"] } }
      | .date => { field with
          policy := { kind := .temporal .date .fullDate }
          temporalTargetPolicy := some { format := "yyyy-MM-dd" } }
    else field }

example : [Carrier.number, .string, .enumeration, .date].all (fun carrier =>
    let (a, b) := match carrier with
      | .date => ("2024-03-01", "2024-03-02")
      | _ => ("1", "2")
    let model := carrierModel carrier
    model.validate.isOk &&
    observed "FieldValuesNotUnique(Rows/Pair)" [row a a, row a b] model == some firstValue &&
    observed "FieldValuesNotUnique(Rows/Pair)" [row a b, row a a] model == some secondValue &&
    observed "FieldValuesNotUnique(Rows/Pair)" [row "" "", row a "bad"] model == some [] &&
    observed "[Out] == 9 And FieldValuesNotUnique(Rows/Pair)" [row a a, row a b] model == some firstValue) = true := by native_decide

example : [Carrier.number, .string, .enumeration].all (fun carrier =>
    let model := carrierModel carrier
    matrix membershipOperators "Rows/Pair In Rows/Members" [row "1" "2" "" "2", row "3" "4" "" "8"]
      [firstValue, secondValue, firstValue ++ secondValue] model &&
    matrix membershipOperators "Rows/Pair In Rows/Members" [row "3" "4" "" "8", row "1" "2" "" "2"]
      [secondValue, firstValue, firstValue ++ secondValue] model) = true := by native_decide

example : [Carrier.string, .enumeration].all (fun carrier =>
    matrix membershipOperators "Rows/Pair In \"2\"" [row "1" "2", row "3" "4"]
      [firstValue, secondValue, firstValue ++ secondValue] (carrierModel carrier)) = true := by native_decide

example : [Carrier.number, .string, .enumeration].all (fun carrier =>
    let model := carrierModel carrier
    matrix membershipOperators "Rows/Pair In Rows/Members" [row "" "" "" "2", row "1" "2"]
      [[], firstOmission ++ secondOmission, secondOmission] model &&
    matrix membershipOperators "Rows/Pair In Rows/Members" [row "bad" "2" "" "2", row "1" "2" "" "bad"]
      [firstValue, [], []] model &&
    membershipOperators.all fun operator =>
      let checked (operands : String) :=
        (checkRule { dm with flat := model } .english (rule (operator ++ "(" ++ operands ++ ")"))).isOk
      checked "Rows/Pair In Rows/Members/M" && checked "Rows/Pair/A In Rows/Members" &&
      !checked "Rows/Pair In Rows/Pair" && !checked "Rows/Pair In Rows/Pair/A" &&
      !checked "Rows/Pair/A In Rows/Pair") = true := by native_decide

private def boundPredicates := fieldOperators.map (· ++ "(Rows/Pair)") ++
  groupOperators.map (· ++ "(Rows/Pair, Rows/Sub)") ++ ["FieldValuesNotUnique(Rows/Pair)"] ++
  membershipOperators.map (· ++ "(Rows/Pair In Rows/Members)")

example : boundPredicates.all (fun predicate =>
    (checkRule dm .english (rule predicate)).isOk &&
    !(checkRule dm .english { (rule predicate) with
      errorEntityRelPath := "../Out"
      condition := "FieldFilled(Out) And " ++ predicate }).isOk &&
    !(checkRule dm .english { (rule predicate) with
      group := ["Form", "Side"]
      errorEntityRelPath := "../../Rows/Out", condition := "FieldFilled(/Form/Rows/Out) And " ++
        predicate.replace "Rows/" "/Form/Rows/" }).isOk &&
    observed predicate [] == some []) = true := by native_decide

example : [
    "AllGroupsFilled(Rows/Pair)", "AllGroupsFilled(Rows/Pair, Rows/Pair)",
    "AllGroupsFilled(/Other, Rows/Pair)",
    "FieldValuesNotUnique(Rows/Pair/A)", "FieldValuesNotUnique(Rows/Pair, Rows/Pair)",
    "FieldValuesNotUnique(Rows/Pair, Rows/Pair/A)", "FieldValuesNotUnique(/Other, Rows/Pair)",
    "AtLeastOneFieldValueIncludedInValueList(Rows/Pair In Rows/Pair)",
    "AtLeastOneFieldValueIncludedInValueList(Rows/Pair In Rows/Pair/A)",
    "AtLeastOneFieldValueIncludedInValueList(Rows/Pair/A In Rows/Pair)",
    "AtLeastOneFieldValueIncludedInValueList(Rows/Pair In /Other)"].all
      (fun predicate => !(checkRule dm .english (rule predicate)).isOk) = true := by native_decide

example : (groupOperators ++ ["FieldValuesNotUnique"]).all (fun operator =>
    let checked (operands : String) := (checkRule dm .english (rule (operator ++ "(" ++ operands ++ ")"))).isOk
    checked "Rows/Pair, Rows/Outer/Inner" && checked "Rows/Outer/Inner, Rows/Pair" &&
    !checked "Rows/Outer, Rows/Outer/Inner" && !checked "Rows/Outer/Inner, Rows/Outer") = true := by native_decide

end A12Kernel.Dm.BoundEntityListLocks
