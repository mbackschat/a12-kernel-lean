import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.EntryFrameFixture

/-! # Ordinary parallel leaves under a partial call, through the reader

The [cross-declaration capture](../../../evidence/kernel-30.8.1/captures/k22-cross-declaration-2026-10-24/)
joins `Supply` and `Demand` by `Department` and states nine rules on `Supply` beside the join:
`Length`, a text comparison, value-list membership, a filled-field count and the partner's own key
read an unmatched partner as empty, a starred uniqueness test reads every `Demand` row, and two rules
on `Supply/Note` fire on the unmatched `Demand` row when `Supply` has no free row. Full validation
is replayed by `lake exe a12-kernel-replay`; these cases run the same rules through the partial
evaluator under the request's four partial scopes. A joined row fires only when the call covers both
of its sides: one `Supply` row, one `Demand` row or one field alone fires nothing, while `Supply` row
three with all of `Demand` fires exactly that row's full messages. The unmatched error side's
placeholder row is outside every partial scope measured.
-/

namespace A12Kernel.Dm.ParallelLeafPartialLocks
open A12Kernel A12Kernel.Dm Lean

private def field (name typeName : String) : Json :=
  let body := if typeName == "NumberType" then [("NumberType", Json.mkObj [("maxFractionalDigits", toJson (0 : Nat))])]
    else if typeName == "DateType" then [("DateType", Json.mkObj [("format", "yyyy-MM-dd")])] else []
  Json.mkObj [("type", "Field"), ("name", Json.str name),
    ("Field", Json.mkObj [("fieldType", Json.mkObj ([("type", Json.str typeName)] ++ body))])]

private def group (name : String) (count : Nat) (key : String) (elements : List Json) : Json :=
  Json.mkObj [("type", "Group"), ("name", Json.str name), ("Group", Json.mkObj [
    ("repeatability", toJson count), ("indexFieldName", Json.str key), ("elements", Json.arr elements.toArray)])]

private def rule (code target condition : String) : Json :=
  Json.mkObj [("type", "Rule"), ("name", Json.str code), ("Rule", Json.mkObj [
    ("errorEntityRelPath", Json.str s!"../Supply/{target}"), ("errorCode", Json.str code),
    ("errorCondition", Json.str condition), ("severity", "ERROR")])]

/-- The capture's rules `v1`–`v9`, in its declaration order. -/
private def rules : List (String × String × String) := [
  ("v1", "Headcount", "FieldFilled(Supply/Headcount) And Length(Demand/Label) < 3"),
  ("v2", "Headcount", "FieldFilled(Supply/Headcount) And [Demand/Label] != \"LA\""),
  ("v3", "Headcount", "FieldFilled(Supply/Headcount) And NoFieldValueIncludedInValueList(Demand/Label In \"LA\", \"zz\")"),
  ("v4", "Headcount", "FieldFilled(Supply/Headcount) And NumberOfFilledFields(Demand/Label, Demand/Stamp) < 1"),
  ("v5", "Headcount", "FieldFilled(Supply/Headcount) And FieldNotFilled(Demand/Department)"),
  ("v6", "Headcount", "FieldFilled(Supply/Headcount) And FieldFilled(Demand/Base) And FieldValuesNotUnique(/Staffing/Demand*/Label)"),
  ("v7", "Note", "FieldFilled(Demand/Base) And FieldNotFilled(Supply/Note) And FieldNotFilled(/Staffing/Ledger/Amount For Supply/Note)"),
  ("v8", "Note", "FieldFilled(Demand/Base) And FieldNotFilled(Supply/Note) And FieldNotFilled(Supply/Department)"),
  ("v9", "Headcount", "FieldFilled(Supply/Headcount) And [Supply/Headcount] < [Demand/Base]")]

private def staffing : Json :=
  checkedEntryFrame <| Json.mkObj [("header", Json.mkObj [("locales", Json.arr #[Json.mkObj [("code", "en_US")]])]),
    ("content", Json.mkObj [("modelConfig", Json.mkObj [("conditionLanguage", Json.mkObj [("code", "en_US")])]),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[Json.mkObj [("type", "Group"), ("name", "Staffing"),
        ("Group", Json.mkObj [("repeatability", toJson (1 : Nat)), ("elements", Json.arr (
          [group "Demand" 50 "Department" [field "Department" "StringType", field "Base" "NumberType",
             field "Stamp" "DateType", field "Label" "StringType"],
           group "Supply" 3 "Department" [field "Department" "StringType", field "Headcount" "NumberType",
             field "Note" "StringType"],
           group "Ledger" 50 "Code" [field "Code" "StringType", field "Amount" "NumberType"]] ++
          rules.map fun (code, target, condition) => rule code target condition).toArray)])]])])])]

/-- The capture's `d1` staffing rows: `Supply` at capacity with `E` unmatched, and `Demand` row `D`
unmatched, its label repeating row `A`'s. -/
private def document : Json :=
  let row := fun (pairs : List (String × String)) => Json.mkObj (pairs.map fun (key, value) => (key, Json.str value))
  Json.mkObj [("Staffing", Json.mkObj [
    ("Ledger", Json.arr #[row [("Code", "k1"), ("Amount", "4")], row [("Code", "x"), ("Amount", "9")],
      row [("Code", "LA"), ("Amount", "5")]]),
    ("Demand", Json.arr #[row [("Department", "A"), ("Base", "10"), ("Label", "LA"), ("Stamp", "2026-10-01")],
      row [("Department", "B"), ("Base", "20"), ("Label", "zz")],
      row [("Department", "D"), ("Base", "7"), ("Label", "LA")]]),
    ("Supply", Json.arr #[row [("Department", "A"), ("Headcount", "1"), ("Note", "x")],
      row [("Department", "B"), ("Headcount", "2")], row [("Department", "E"), ("Headcount", "1"), ("Note", "q")]])])]

private def supplyRow (row : Nat) : RelevantEntityPattern :=
  { path := ["Staffing", "Supply"], indices := [.concrete 1, .concrete row] }

/-- Each fired message as its code, its `Supply` row (`0` for the placeholder) and its type. -/
private def partialMessages (relevant : List RelevantEntityPattern) : Except String (List (String × Nat × Polarity)) := do
  let dm ← (readModel staffing).mapError reprStr
  let input ← (readDocument dm document).mapError reprStr
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).mapError reprStr
  let checked ← (checkDocument prepared "en_US" input.data).mapError reprStr
  dm.rules.flatMapM fun rule => do
    let .parallel plan ← (checkValidationRule dm .english rule).mapError (·.detail)
      | throw s!"{rule.errorCode} is not a parallel rule"
    let messages ← runPartialParallelRule checked plan relevant none (some world)
    pure (messages.map fun message => (rule.errorCode,
      (match message.errorAddress.coordinates with | [.concrete row] => row | _ => 0), message.messageType))

-- Rows `d1`, `d1-sup1`, `d1-dem2`, `d1-hc` and `d1-sup3dem` of the capture's request.
example : (partialMessages [.allInstances ["Staffing"]]).toOption == some [
      ("v1", 1, .value), ("v1", 2, .value), ("v1", 3, .omission), ("v2", 2, .value), ("v3", 3, .omission),
      ("v4", 3, .omission), ("v5", 3, .omission), ("v6", 1, .value), ("v6", 2, .value), ("v7", 2, .omission),
      ("v7", 0, .omission), ("v8", 0, .omission), ("v9", 1, .value), ("v9", 2, .value)] &&
    [[supplyRow 1], [{ path := ["Staffing", "Demand"], indices := [.concrete 1, .concrete 2] }],
      [.allInstances ["Staffing", "Supply", "Headcount"]]].all (fun relevant =>
        (partialMessages relevant).toOption == some []) &&
    (partialMessages [supplyRow 3, .allInstances ["Staffing", "Demand"]]).toOption == some [
      ("v1", 3, .omission), ("v3", 3, .omission), ("v4", 3, .omission), ("v5", 3, .omission)] := by
  native_decide

end A12Kernel.Dm.ParallelLeafPartialLocks
