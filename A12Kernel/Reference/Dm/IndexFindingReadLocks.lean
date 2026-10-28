import Lean.Data.Json
import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.GeneratedComputationRule
import A12Kernel.Reference.Dm.ParallelValidation

/-! # Rule and computation reads of a generated index finding

Reader-to-evaluator locks for cells carrying a generated index finding: an empty key nominated by a
non-repeatable group, an empty key of a repeatable group, and a duplicated repeatable key. The model and
documents are reductions of the retained Kernel 30.8.1 capture
`evidence/kernel-30.8.1/captures/runtime-open-cells-2026-10-28/` (`q-*` rows of `request-rules.json`,
`hold-key-empty-seeded` of `request-prepass.json`); every expectation is the capture's own message or
change.

An authored rule reads each such cell as unknown, so a condition the empty or duplicated value would
satisfy does not fire, while the same condition over the unnominated `Plain` twin fires. A computation
reading the empty key stores nothing, and its generated rule does not fire against the stale target.
-/

namespace A12Kernel.Dm.IndexFindingReadLocks

open Lean A12Kernel

private def element (kind id name : String) (body : List (String × Json)) : Json :=
  Json.mkObj [("type", .str kind), ("id", .str id), ("name", .str name), (kind, Json.mkObj body)]

private def text : Json := Json.mkObj [("type", "StringType")]
private def number : Json :=
  Json.mkObj [("type", "NumberType"), ("NumberType", Json.mkObj [("maxFractionalDigits", toJson 0)])]

private def field (path name : String) (fieldType : Json) : Json :=
  element "Field" s!"{path}/{name}" name [("fieldType", fieldType)]

private def group (path name : String) (repeatability : Nat) (index : Option String)
    (elements : List Json) : Json :=
  element "Group" s!"{path}/{name}" name ([("repeatability", toJson repeatability),
    ("elements", Json.arr elements.toArray)] ++ (index.map fun key => [("indexFieldName", Json.str key)]).getD [])

private def message : Json := Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]]

private def rule (path name entity condition : String) : Json :=
  element "Rule" s!"{path}/{name}" name [("errorEntityRelPath", .str entity), ("errorCode", .str name),
    ("errorCondition", .str condition), ("severity", "ERROR"), ("errorMessage", message)]

private def dm? : Option DmModel :=
  (readModel (Json.mkObj [("content", Json.mkObj [("modelRoot", Json.mkObj [("rootGroups", Json.arr #[
    group "" "Hold" 1 none [
      field "/Hold" "HAnchor" text, field "/Hold" "Out" number,
      group "/Hold" "Holder" 1 (some "HKey")
        [field "/Hold/Holder" "HKey" number, field "/Hold/Holder" "HAlt" number, field "/Hold/Holder" "HText" text],
      group "/Hold" "Plain" 1 none [field "/Hold/Plain" "PKey" number, field "/Hold/Plain" "PAlt" number],
      group "/Hold" "Recs" 3 (some "RKey") [field "/Hold/Recs" "RKey" number, field "/Hold/Recs" "RAlt" number,
        rule "/Hold/Recs" "QR1" "../RAlt" "FieldFilled(RAlt) And FieldNotFilled(RKey)",
        rule "/Hold/Recs" "QR2" "../RAlt" "FieldFilled(RAlt) And FieldFilled(RKey)",
        rule "/Hold/Recs" "QR3" "../RAlt" "FieldFilled(RAlt) And [RKey] == 1"],
      element "Computation" "/Hold/COut" "COut" [("computedFieldRelPath", "../Out"),
        ("computationAlternatives", Json.arr #[Json.mkObj [("operation", "FirstFilledValue(Holder/HKey, Holder/HAlt)")]]),
        ("errorMessage", message)],
      rule "/Hold" "QN1" "../HAnchor" "FieldFilled(HAnchor) And FieldNotFilled(Holder/HKey)",
      rule "/Hold" "QN2" "../HAnchor" "FieldFilled(HAnchor) And FieldNotFilled(Plain/PKey)",
      rule "/Hold" "QN3" "../HAnchor" "FieldFilled(HAnchor) And FirstFilledValue(Holder/HKey, Holder/HAlt) == 5",
      rule "/Hold" "QN4" "../HAnchor" "FieldFilled(HAnchor) And FirstFilledValue(Plain/PKey, Plain/PAlt) == 5"]])])])])).toOption

private def world : World := { now := { epochMillis := 0 } }

private def row (entries : List (String × String)) : Json :=
  Json.mkObj (entries.map fun (key, value) => (key, Json.str value))

private def hold (holder plain : List (String × String)) (recs : List (List (String × String)))
    (out : Option String := none) : Json :=
  Json.mkObj [("Hold", Json.mkObj ([("HAnchor", Json.str "h"), ("Holder", row holder), ("Plain", row plain),
    ("Recs", Json.arr (recs.map row).toArray)] ++ (out.map fun value => [("Out", Json.str value)]).getD []))]

/-- Every authored and generated rule's firings, as `code pointer`, over full validation's document. -/
private def fired (document : Json) : Option (List String) := do
  let dm ← dm?
  let input ← (readDocument dm document).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let validated ← checked.fullValidationDocument.toOption
  let generated ← dm.computations.mapM (·.generatedRule? .english)
  let messages ← (dm.rules ++ generated).mapM fun source => do
    let plan ← (checkValidationRule dm .english source world).toOption
    let fired ← (runValidationRule world validated plan).toOption
    pure (fired.map fun message => s!"{source.errorCode} {renderPointer dm.flat message.errorAddress}")
  pure messages.flatten

/-- Every reported target change, as `pointer outcome`. -/
private def computed (document : Json) : Option (List String) := do
  let dm ← dm?
  let input ← (readDocument dm document).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let lowered ← dm.computations.mapM fun source => (lowerComputation dm.flat .english source).toOption
  let outcomes ← (runComputations world prepared checked (lowered.map (·.2))).toOption
  pure (outcomes.map fun outcome => s!"{outcome.pointer} {outcome.outcome}")

/- `q-key-empty`: only the unnominated twins fire. -/
example : fired (hold [("HAlt", "5"), ("HText", "t")] [("PAlt", "5")] [[("RAlt", "5")]]) =
    some ["QN2 Hold/HAnchor", "QN4 Hold/HAnchor"] := by native_decide

/- `q-key-filled`: a definite key fires its filled condition and nothing else. -/
example : fired (hold [("HKey", "1"), ("HAlt", "5")] [("PKey", "1"), ("PAlt", "5")] [[("RKey", "2"), ("RAlt", "5")]]) =
    some ["QR2 Hold/Recs/RAlt"] := by native_decide

/- `q-key-duplicate`: both participants of the duplicated key are unknown; the third row stays definite. -/
example : fired (hold [("HKey", "1"), ("HAlt", "5")] [("PKey", "1"), ("PAlt", "5")]
      [[("RKey", "1"), ("RAlt", "5")], [("RKey", "1"), ("RAlt", "6")], [("RKey", "2"), ("RAlt", "7")]]) =
    some ["QR2 Hold/Recs[3]/RAlt"] := by native_decide

/- `hold-key-empty-seeded`: the computation clears its stale target, and its generated rule stays silent. -/
example : (fired (hold [("HAlt", "5"), ("HText", "t")] [] [] (some "9"))).map (·.filter (·.startsWith "COut")) = some [] ∧
    computed (hold [("HAlt", "5"), ("HText", "t")] [] [] (some "9")) = some ["Hold/Out cleared"] := by
  native_decide

end A12Kernel.Dm.IndexFindingReadLocks
