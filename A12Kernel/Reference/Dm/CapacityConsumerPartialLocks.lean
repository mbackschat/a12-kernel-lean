import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Document

/-! # The group-capacity grid's partial scope over rows 1 and 2, through the reader

The [group-capacity grid](../../../evidence/kernel-30.8.1/captures/group-capacity-consumers-2026-10-02/)
declares nine root rules over five groups of at most two rows and observes them under a partial scope
naming the root's fields and rows 1 and 2 of every group. The
[conformance module](../../Conformance/CapacityGroupConsumers.lean) checks the carriers below the
reader; these cases run the same rules as the reader lowers them, from their authored text. The
over-limit document answers as the one without its third row: the four value lists and the control
fire, `Sum` and both distinct counts stay silent, and the filtered scan is skipped, as the retained
`rows.tsv` records and the 2026-10-24 rerun of its request reproduces.
-/

namespace A12Kernel.Dm.CapacityConsumerPartialLocks
open A12Kernel A12Kernel.Dm Lean

private def field (name : String) (typeName : String) (body : List (String × Json) := []) : Json :=
  Json.mkObj [("type", "Field"), ("name", Json.str name), ("Field", Json.mkObj [("fieldType",
    Json.mkObj ([("type", Json.str typeName)] ++ if body.isEmpty then [] else [(typeName, Json.mkObj body)]))])]

private def number (name : String) : Json := field name "NumberType" [("maxFractionalDigits", toJson (0 : Nat))]

private def date (name : String) : Json :=
  field name "DateType" [("format", "yyyy-MM-dd"), ("datePrecision", "FULL")]

private def group (name : String) (count : Nat) (elements : List Json) : Json :=
  Json.mkObj [("type", "Group"), ("name", Json.str name),
    ("Group", Json.mkObj [("repeatability", toJson count), ("elements", Json.arr elements.toArray)])]

private def rule (code condition : String) : Json :=
  Json.mkObj [("type", "Rule"), ("name", Json.str code), ("Rule", Json.mkObj [
    ("errorEntityRelPath", "../W"), ("errorCode", Json.str code),
    ("errorCondition", Json.str s!"{condition} And FieldFilled(W)"), ("severity", "ERROR")])]

/-- The grid's rules, in its declaration order. -/
private def rules : List (String × String) := [
  ("DCG", "NumberOfDifferentValues(DRows*) == 1"), ("DCF", "NumberOfDifferentValues(DShell) == 1"),
  ("TVF", "NoFieldValueIncludedInValueList(TRows*/T In X)"), ("TVG", "NoFieldValueIncludedInValueList(TRows* In X)"),
  ("NVF", "NoFieldValueIncludedInValueList(NRows*/V In Y)"), ("NVG", "NoFieldValueIncludedInValueList(NRows* In Y)"),
  ("FFH", "FirstFilledValue(Rows*/M Having [Rows/Gate] > 0, F9) == 9"), ("SUM", "Sum(Rows*/N) == 5"),
  ("CTRL", "FieldFilled(W)")]

private def gcap : Json :=
  Json.mkObj [("header", Json.mkObj [("locales", Json.arr #[Json.mkObj [("code", "en_US")]])]),
    ("content", Json.mkObj [("modelConfig", Json.mkObj [("conditionLanguage", Json.mkObj [("code", "en_US")])]),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[group "Rg" 1 (
        [field "W" "StringType", field "X" "StringType", number "Y", number "F9"] ++
        rules.map (fun (code, condition) => rule code condition) ++
        [group "Rows" 2 [number "N", number "M", number "Gate"], group "DRows" 2 [date "D"],
         group "DShell" 1 [group "SRows" 2 [date "S"]], group "TRows" 2 [field "T" "StringType"],
         group "NRows" 2 [number "V"]])])])])]

/-- Each group's rows: the first holds `2020-01-01`, `a` or `5`; `middle` is the second row; `third`
adds a row beyond capacity holding `2021-01-01`, `x` or `100`. -/
private def document (middle : Bool) (third : Bool) : Json :=
  let rowsOf := fun (first later : Json) =>
    Json.arr ((#[first] ++ (if middle then #[later] else #[Json.mkObj []])) ++ if third then #[later] else #[])
  let one := fun (name value : String) => Json.mkObj [(name, Json.str value)]
  Json.mkObj [("Rg", Json.mkObj [("W", "w"), ("X", "x"), ("Y", "100"), ("F9", "9"),
    ("Rows", rowsOf (one "N" "5") (Json.mkObj [("N", "100"), ("M", "7"), ("Gate", "1")])),
    ("DRows", rowsOf (one "D" "2020-01-01") (one "D" "2021-01-01")),
    ("TRows", rowsOf (one "T" "a") (one "T" "x")),
    ("NRows", rowsOf (one "V" "5") (one "V" "100")),
    ("DShell", Json.mkObj [("SRows", rowsOf (one "S" "2020-01-01") (one "S" "2021-01-01"))])])]

private def groupPaths : List (List String) :=
  [["Rg", "Rows"], ["Rg", "DRows"], ["Rg", "DShell", "SRows"], ["Rg", "TRows"], ["Rg", "NRows"]]

/-- The root's own fields and rows 1 and 2 of every group, as the grid's `reps` entries name them. -/
private def firstTwoRows : ValidationRelevanceScope :=
  .partialSet ((["W", "X", "Y", "F9"].map fun name => { path := ["Rg", name], indices := [.all, .all] }) ++
    groupPaths.flatMap fun path => [1, 2].map fun row =>
      { path, indices := (path.dropLast.map fun _ => .concrete 1) ++ [.concrete row] })

/-- The codes that fire under `firstTwoRows`, a skipped rule marked as such. -/
private def partialCodes (middle third : Bool) : Except String (List String) := do
  let dm ← (readModel gcap).mapError reprStr
  let input ← (readDocument dm (document middle third)).mapError reprStr
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).mapError reprStr
  let checked ← (checkDocument prepared "en_US" input.data).mapError reprStr
  dm.rules.filterMapM fun rule => do
    let lowered ← (checkRule dm .english rule).mapError (·.detail)
    match ← (lowered.evalAddressedPartial checked firstTwoRows (some world)).mapError reprStr with
    | .skipped => pure (some s!"{rule.errorCode}:skipped")
    | .evaluated outcome => pure (outcome.message?.map fun _ => rule.errorCode)

-- The over-limit document, the in-capacity control and the document without its third row, against
-- the grid's `g1-over-limit-sub`, `g2-in-capacity-sub` and `g3-no-third-sub` rows.
example :
    ((partialCodes false true).toOption == some ["TVF", "TVG", "NVF", "NVG", "FFH:skipped", "CTRL"] &&
      (partialCodes true false).toOption == some ["FFH:skipped", "CTRL"] &&
      (partialCodes false false).toOption == some ["TVF", "TVG", "NVF", "NVG", "FFH:skipped", "CTRL"]) = true := by
  native_decide

end A12Kernel.Dm.CapacityConsumerPartialLocks
