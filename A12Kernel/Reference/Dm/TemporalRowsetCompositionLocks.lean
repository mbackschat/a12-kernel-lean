import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

/-! C15 checks the existing shared temporal tree across full/partial validation and computation.
Kernel grammar `datumDiffOp` consumes `datumAngabe2`, excluding list extrema as direct arguments;
a computed extremum read by field remains an ordinary difference operand (spec/05 and spec/09). -/
namespace A12Kernel.Dm.TemporalRowsetCompositionLocks
open Lean

private def model (yearless : Bool) : FlatModel :=
  let format := if yearless then "MM-dd" else "yyyy-MM-dd"
  let date (id : FieldId) (name : String) (group : GroupPath := ["Dates"])
      (scope : List RepeatableLevel := []) : FlatFieldDecl := {
    id, name, groupPath := group, repeatableScope := scope
    policy := { kind := .temporal .date (TemporalComponents.ofFormat format) }
    temporalTargetPolicy := some { format } }
  { fields := [date 1 "Low", date 2 "High", date 3 "Earliest", date 4 "Latest", date 5 "D" ["Dates", "Rows"] [10],
      { id := 6, name := "Ref", groupPath := ["Dates"], policy := { kind := .number { scale := 0, signed := true } } },
      { id := 7, name := "N", groupPath := ["Dates"], policy := { kind := .number { scale := 0, signed := true } } }]
    baseYear := some 2024, timeZoneId := "Europe/Berlin"
    repeatableGroups := [{ level := 10, path := ["Dates", "Rows"], repeatability := some 2 }] }

private def input (yearless : Bool) (values : List String) : Json :=
  Json.mkObj [("Dates", Json.mkObj [
    ("Low", if yearless then "03-30" else "2024-03-30"),
    ("High", if yearless then "04-01" else "2024-04-01"),
    ("Earliest", if yearless then "01-01" else "2024-01-01"),
    ("Latest", if yearless then "01-01" else "2024-01-01"),
    ("Ref", "1"), ("N", "99"),
    ("Rows", .arr (values.map fun value => Json.mkObj [("D", .str value)]).toArray)])]
private def values (yearless : Bool) : List String :=
  if yearless then ["04-01", "03-30"] else ["2024-04-01", "2024-03-30"]
private def world : World := { now := { epochMillis := 0 } }
private def dm (yearless : Bool) : DmModel := {
  flat := model yearless, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
private def checked (yearless : Bool) (rows : List String) : Option (CheckedDocument (model yearless)) := do
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler (model yearless)).toOption
  let input ← (readDocument (dm yearless) (input yearless rows)).toOption
  (checkDocument prepared "en_US" input.data).toOption
private def comparison (op : String) (star : Bool) : String :=
  op ++ (if star then "(Rows*/D)" else "(Low,High)") ++
    (if op == "MinValue" then " == [Low]" else " == [High]")
private def rule (yearless : Bool) (text : String) : Option (CheckedResolvedValidationRule (model yearless)) :=
  (checkRule (dm yearless) .english {
    name := "Compare", group := ["Dates"], errorCode := "COMPARE", errorEntityRelPath := "../Ref"
    condition := "FieldFilled(Ref) And (" ++ text ++ ")", severity := "ERROR" } world).toOption
private def validation (yearless : Bool) (text : String) (rows : List String)
    (scope : ValidationRelevanceScope := .full) : Option (List String × Verdict) := do
  let document ← checked yearless rows
  let rule ← rule yearless text
  let messages ← (runRule world document rule).toOption
  let .evaluated partialResult ← (rule.evalAddressedPartial document scope (some world)).toOption | none
  pure (messages.map (fun message => (observe (model yearless) message).messageType), partialResult.verdict)
private def definition (target operation : String) (guard : Option String := none) : DmComputation := {
  group := ["Dates"], name := target, targetRelPath := "../" ++ target, commonPrecondition := guard
  alternatives := [{ operation, precondition := none }], errorCodesToSuppress := [] }
private def compute (yearless : Bool) (definitions : List DmComputation) (rows : List String) : Option (List String) := do
  let document ← checked yearless rows
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler (model yearless)).toOption
  let steps ← definitions.mapM fun definition => (lowerComputation (model yearless) .english definition).toOption
  pure ((← (runComputations world prepared document (steps.map (·.2))).toOption).map (·.outcome))

example : [false,true].all (fun yearless => [false,true].all fun star => ["MinValue","MaxValue"].all fun op =>
    validation yearless (comparison op star) (values yearless) == some (["VALUE_ERROR"], .fired .value) &&
    compute yearless [definition "N" "7" (some (comparison op star))] (values yearless) == some ["value 7"]) = true := by native_decide

example : [false,true].all (fun yearless => ["MinValue","MaxValue"].all fun op =>
    validation yearless (comparison op true) ["bad"] == some ([], .unknown) &&
    compute yearless [definition "N" "7" (some (comparison op true))] ["bad"] == some ["cleared"] &&
    compute yearless [definition "Earliest" (op ++ "(Rows*/D)")] [] == some ["cleared"]) = true := by native_decide

example : [false,true].all (fun yearless => ["MinValue","MaxValue"].all fun op =>
    validation yearless (comparison op true) [] == some ([], .notFired) &&
    compute yearless [definition "N" "7" (some (comparison op true))] [] == some ["cleared"] &&
    let selected := if op == "MinValue" then (values yearless).getLast! else (values yearless).head!
    validation yearless (comparison op true) [selected, ""] == some (["OMISSION_ERROR"], .fired .omission) &&
    compute yearless [definition "N" "7" (some (comparison op true))] [selected, ""] == some ["value 7"]) = true := by native_decide

example : [false,true].all (fun yearless => [false,true].all fun star => ["MinValue","MaxValue"].all fun op =>
    let text := op ++ (if star then "(Rows*/D)" else "(Low,High)") ++
      (if op == "MinValue" then " == [High]" else " == [Low]")
    validation yearless text (values yearless) == some ([], .notFired) &&
    compute yearless [definition "N" "7" (some text)] (values yearless) == some ["cleared"]) = true := by native_decide

private def refOnly : ValidationRelevanceScope := .partialSet [
  { path := ["Dates", "Ref"], indices := [.all, .all] }]
example : [false,true].all (fun yearless => [false,true].all fun star => ["MinValue","MaxValue"].all fun op =>
    validation yearless (comparison op star) (values yearless) refOnly == some (["VALUE_ERROR"], .unknown)) = true := by native_decide

example : [false,true].all (fun yearless => [false,true].all fun star =>
    let operands := if star then "(Rows*/D)" else "(Low,High)"
    ["MinValue","MaxValue"].all fun op =>
      let operation := "DifferenceInDays(" ++ op ++ operands ++ ",High)"
      (rule yearless (operation ++ " == 0")).isNone &&
        !(lowerComputation (model yearless) .english (definition "N" operation)).isOk) = true := by native_decide

example : [false,true].all (fun yearless =>
    let early := if yearless then "value 03-30" else "value 2024-03-30"
    let late := if yearless then "value 04-01" else "value 2024-04-01"
    compute yearless [definition "N" "DifferenceInDays(Earliest,Latest)",
      definition "Earliest" "MinValue(Rows*/D)", definition "Latest" "MaxValue(Rows*/D)"]
        (values yearless) == some [early, late, "value 2"]) = true := by native_decide

end A12Kernel.Dm.TemporalRowsetCompositionLocks
