import Lean.Data.Json
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.GeneratedComputationRule
import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.EntryFrameFixture

/-! # Generated validation of Boolean alternative tables and keyed field-fill guards

Reader-to-evaluator locks for the rule a computation generates (spec/09 §6) where its alternatives
are Boolean constants or its guard reads a keyed row: a fixed and a row Boolean table, a table whose
alternatives overlap, and a positive and a negative keyed field-fill guard. The model and documents
are reductions of the retained Kernel 30.8.1 capture
`evidence/kernel-30.8.1/captures/generated-computation-validation-2026-10-14/`; every expectation is
the capture's own message.
-/

namespace A12Kernel.Dm.GeneratedTableLocks

open Lean A12Kernel

private def element (kind id name : String) (body : List (String × Json)) : Json :=
  Json.mkObj [("type", .str kind), ("id", .str id), ("name", .str name), (kind, Json.mkObj body)]

private def field (group name : String) (fieldType : Json) : Json :=
  element "Field" s!"{group}/{name}" name [("fieldType", fieldType)]

private def kind (name : String) : Json := Json.mkObj [("type", .str name)]
private def number : Json :=
  Json.mkObj [("type", "NumberType"), ("NumberType", Json.mkObj [("maxFractionalDigits", toJson 0)])]

private def computation (group name target : String) (alternatives : List (String × String)) : Json :=
  element "Computation" s!"{group}/{name}" name [("computedFieldRelPath", .str s!"../{target}"),
    ("computationAlternatives", Json.arr (alternatives.map fun (operation, guard) =>
      Json.mkObj [("precondition", .str guard), ("operation", .str operation)]).toArray),
    ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]])]

private def rows : Json :=
  element "Group" "/P/Rows" "Rows" [("repeatability", toJson 5), ("indexFieldName", "Key"),
    ("elements", Json.arr #[field "/P/Rows" "Key" (kind "StringType"), field "/P/Rows" "RGate" number,
      field "/P/Rows" "RFlag" (kind "BooleanType"),
      computation "/P/Rows" "CRB" "RFlag" [("True", "[RGate] > 0"), ("False", "[RGate] <= 0")]])]

private def root : Json :=
  element "Group" "/P" "P" [("repeatability", toJson 1), ("elements", Json.arr #[
    field "/P" "Gate" number, field "/P" "Flag" (kind "BooleanType"),
    field "/P" "Flag2" (kind "BooleanType"), field "/P" "Out" number, field "/P" "Out2" number, rows,
    computation "/P" "CB" "Flag" [("True", "[Gate] > 0"), ("False", "[Gate] <= 0")],
    computation "/P" "CBo" "Flag2" [("True", "[Gate] > 0"), ("False", "[Gate] > 1")],
    computation "/P" "CK" "Out" [("1", "AtLeastOneFieldFilled(Rows/RGate For \"a\", Gate)")],
    computation "/P" "CN" "Out2" [("2", "FieldNotFilled(Rows/RGate For \"b\")")]])]

private def dm? : Option DmModel :=
  (readModel (checkedEntryFrame <| Json.mkObj [("content", Json.mkObj [("modelRoot",
    Json.mkObj [("rootGroups", Json.arr #[root])])])])).toOption

private def row (entries : List (String × String)) : Json :=
  Json.mkObj (entries.map fun (key, value) => (key, Json.str value))

/-- Each generated rule's firings, as `code pointer type`. -/
private def fired (document : Json) : Option (List String) := do
  let dm ← dm?
  let world : World := { now := { epochMillis := 1791972000000 }, modelZoneRules := ModelZone.concreteRules }
  let input ← (readDocument dm document).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let generated ← dm.computations.mapM (·.generatedRule? .english)
  let messages ← generated.mapM fun source => do
    let plan ← (checkValidationRule dm .english source world).toOption
    let fired ← (runValidationRule world checked plan).toOption
    pure (fired.map fun message =>
      s!"{source.errorCode} {renderPointer dm.flat message.errorAddress} {reprStr message.messageType}")
  pure messages.flatten

private def document (fixed : List (String × String)) (rows : List (List (String × String))) : Json :=
  Json.mkObj [("P", Json.mkObj ((fixed.map fun (key, value) => (key, Json.str value)) ++
    [("Rows", Json.arr (rows.map row).toArray)]))]

-- `Gate` 2 selects `True` in both tables, but the overlapping table's second guard holds too, so its
-- `!= False` disjunct fires on the stored `true` that the computation leaves unchanged. Row `c` has
-- no `RGate`: both of its guards read the empty Number, and the `<=` one fires as an omission.
example : fired (document [("Gate", "2"), ("Flag", "false"), ("Flag2", "true"), ("Out", "9"), ("Out2", "9")]
    [[("Key", "a"), ("RGate", "1"), ("RFlag", "false")], [("Key", "b"), ("RGate", "0"), ("RFlag", "false")],
      [("Key", "c"), ("RFlag", "true")]]) = some [
    "CRB P/Rows/RFlag A12Kernel.Polarity.value", "CRB P/Rows[3]/RFlag A12Kernel.Polarity.omission",
    "CB P/Flag A12Kernel.Polarity.value", "CBo P/Flag2 A12Kernel.Polarity.value",
    "CK P/Out A12Kernel.Polarity.value"] := by native_decide

-- Without `Gate` the empty Number compares as zero with omission polarity: `<= 0` holds and `> 1`
-- does not, so only the first table fires. The negative keyed guard holds where row `b` has no `RGate`.
example : fired (document [("Flag", "true"), ("Flag2", "true"), ("Out2", "9")]
    [[("Key", "b"), ("RFlag", "false")]]) = some [
    "CB P/Flag A12Kernel.Polarity.omission", "CN P/Out2 A12Kernel.Polarity.omission"] := by native_decide

end A12Kernel.Dm.GeneratedTableLocks
