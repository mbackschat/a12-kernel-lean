import Lean.Data.Json
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Replay

/-! # Keys over a root or fixed-group index

Reader-to-evaluator locks for a key whose index lies on the root or on a fixed group. The key
selects that group's one instance: a stored index equal to the key reads as the unkeyed read does,
a different one reads as a clean no-match and names the instance `-5` in the references, and an
empty index is unavailable, so neither the condition nor its negation fires and the computation has
no outcome. Partial validation over the capture's relevant set fires exactly as full validation does,
the field-fill quantifiers included, and a filled root group references only the key's index. The
documents and expectations are those of the retained Kernel 30.8.1 capture
`evidence/kernel-30.8.1/captures/single-instance-key-2026-10-28/` (`request.json` for `K1`, `K1N`, `KD`,
`KDN` and `Q1`; `request-carriers.json` for `LFA`, `LFN` and `LG2`) for the rules and computation the
model keeps, without message types or fill-to-fix lists.
-/

namespace A12Kernel.Dm.SingleInstanceKeyLocks

open Lean A12Kernel

private def element (kind id name : String) (body : List (String × Json)) : Json :=
  Json.mkObj [("type", .str kind), ("id", .str id), ("name", .str name), (kind, Json.mkObj body)]

private def text : Json := Json.mkObj [("type", "StringType")]
private def number : Json :=
  Json.mkObj [("type", "NumberType"), ("NumberType", Json.mkObj [("maxFractionalDigits", toJson 0)])]

private def field (path name : String) (fieldType : Json) : Json :=
  element "Field" s!"{path}/{name}" name [("fieldType", fieldType)]

private def group (path name : String) (index : Option String) (elements : List Json) : Json :=
  element "Group" s!"{path}/{name}" name ([("repeatability", toJson 1),
    ("elements", Json.arr elements.toArray)] ++ (index.map fun key => [("indexFieldName", Json.str key)]).getD [])

private def message : Json := Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]]

private def rule (path name condition : String) : Json :=
  element "Rule" s!"{path}/{name}" name [("errorEntityRelPath", "../Note"), ("errorCode", .str name),
    ("errorCondition", .str s!"FieldFilled(Note) And {condition}"), ("severity", "ERROR"), ("errorMessage", message)]

/-- `IxRoot` is indexed on the root and keyed by a literal, `IxFix` on its fixed `Cover` and keyed by
its own `KeyF`. -/
private def dm? : Option DmModel :=
  let root := group "" "IxRoot" (some "RootKey") [field "/IxRoot" "Note" text, field "/IxRoot" "RootKey" text,
    field "/IxRoot" "ROut" number,
    group "/IxRoot" "Cover" none [field "/IxRoot/Cover" "CAmt" number, field "/IxRoot/Cover" "CNote" text],
    rule "/IxRoot" "K1" "[Cover/CAmt For \"X\"] > 0", rule "/IxRoot" "K1N" "FieldNotFilled(Cover/CAmt For \"X\")",
    rule "/IxRoot" "LFA" "AtLeastOneFieldFilled(Cover/CAmt For \"X\", Cover/CNote For \"X\")",
    rule "/IxRoot" "LFN" "NoFieldFilled(Cover/CAmt For \"X\", Cover/CNote For \"X\")",
    rule "/IxRoot" "LG2" "GroupFilled(/IxRoot For \"X\")",
    element "Computation" "/IxRoot/Q1" "Q1" [("computedFieldRelPath", "../ROut"),
      ("computationAlternatives", Json.arr #[Json.mkObj [("operation", "[Cover/CAmt For \"X\"]")]]),
      ("errorMessage", message)]]
  let fixed := group "" "IxFix" none [field "/IxFix" "Note" text, field "/IxFix" "KeyF" text,
    group "/IxFix" "Cover" (some "CoverKey") [field "/IxFix/Cover" "CAmt" number, field "/IxFix/Cover" "CoverKey" text],
    rule "/IxFix" "KD" "[Cover/CAmt For KeyF] > 0", rule "/IxFix" "KDN" "FieldNotFilled(Cover/CAmt For KeyF)"]
  (readModel (Json.mkObj [("content", Json.mkObj [("modelRoot", Json.mkObj [
    ("rootGroups", Json.arr #[root, fixed])])])])).toOption

private def world : World := { now := { epochMillis := 0 } }

/-- The capture's documents: the root and fixed indexes store `key?`, the fixed group's key field `X`. -/
private def document (key? : Option String) : Json :=
  let keyed (name : String) : List (String × Json) := (key?.map fun key => [(name, Json.str key)]).getD []
  let amount : List (String × Json) := [("CAmt", "5")]
  Json.mkObj [
    ("IxRoot", Json.mkObj ([("Note", Json.str "n"), ("Cover", Json.mkObj (amount ++ [("CNote", Json.str "n")]))] ++
      keyed "RootKey")),
    ("IxFix", Json.mkObj [("Note", "n"), ("KeyF", "X"), ("Cover", Json.mkObj (amount ++ keyed "CoverKey"))])]

private def checked? (key? : Option String) : Option ((dm : DmModel) × CheckedDocument dm.flat) := do
  let dm ← dm?
  let input ← (readDocument dm (document key?)).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  pure ⟨dm, ← (checkDocument prepared "en_US" input.data).toOption⟩

/-- Every rule's firings with their sorted references, then the computed outcomes. -/
private def observed (key? : Option String) : Option (List String × List String) := do
  let ⟨dm, checked⟩ ← checked? key?
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let inputs ← checked.applyFullIndexPreliminary.toOption.bind (·.messageReferenceInputs.toOption)
  let messages ← dm.rules.mapM fun source => do
    let rule ← (checkRule dm .english source).toOption
    let fired ← (runRuleAt world checked rule).toOption
    fired.mapM fun (environment, message) => do
      let found ← (rule.condition.core.messageReferences message environment (some inputs)).toOption
      let sorted := (found.referenced.map (renderFieldPointer dm.flat)).eraseDups.mergeSort (compare · · != .gt)
      pure s!"{source.errorCode} {renderPointer dm.flat message.errorAddress} {sorted}"
  let lowered ← dm.computations.mapM fun definition => (lowerComputation dm.flat .english definition).toOption
  let reported ← (runComputations world prepared checked (lowered.map (·.2))).toOption
  pure (messages.flatten.mergeSort (compare · · != .gt), reported.map toString)

/-- Every rule's partial-validation firings over the capture's relevant set for this model. -/
private def partialFired (key? : Option String) : Option (List String) := do
  let ⟨dm, checked⟩ ← checked? key?
  let relevant := [["IxRoot", "Note"], ["IxRoot", "RootKey"], ["IxRoot", "Cover"], ["IxFix", "Note"],
    ["IxFix", "KeyF"], ["IxFix", "Cover"], ["IxFix", "Cover", "CoverKey"]].map RelevantEntityPattern.allInstances
  let fired ← dm.rules.mapM fun source => do
    let rule ← (checkValidationRule dm .english source).toOption
    let messages ← (runRulePartial world checked relevant rule).toOption
    pure (messages.map fun message => s!"{source.errorCode} {renderPointer dm.flat message.errorAddress}")
  pure (fired.flatten.mergeSort (compare · · != .gt))

private def fullFired (key? : Option String) : Option (List String) :=
  (observed key?).map fun (messages, _) => messages.map fun message =>
    " ".intercalate ((message.splitOn " ").take 2)

/- `a-match`: an equal stored index reads as the unkeyed read and references the index field. -/
example : observed (some "X") = some ([
    "K1 IxRoot/Note [IxRoot/Cover/CAmt, IxRoot/Note, IxRoot/RootKey]",
    "KD IxFix/Note [IxFix/Cover/CAmt, IxFix/Cover/CoverKey, IxFix/KeyF, IxFix/Note]",
    "LFA IxRoot/Note [IxRoot/Cover/CAmt, IxRoot/Cover/CNote, IxRoot/Note, IxRoot/RootKey]",
    "LG2 IxRoot/Note [IxRoot/Note, IxRoot/RootKey]"],
    ["IxRoot/ROut=value 5"]) := by native_decide

/- `a-other`: a different stored index reads as a clean no-match, whose references write `-5` at
the index group's own level, the root or `Cover`, and `[1]` at every other nonrepeatable one. -/
example : observed (some "Y") = some ([
    "K1N IxRoot/Note [/IxRoot[-5]/Cover[1]/CAmt, /IxRoot[-5]/RootKey, IxRoot/Note]",
    "KDN IxFix/Note [/IxFix[1]/Cover[-5]/CAmt, /IxFix[1]/Cover[-5]/CoverKey, IxFix/KeyF, IxFix/Note]",
    "LFN IxRoot/Note [/IxRoot[-5]/Cover[1]/CAmt, /IxRoot[-5]/Cover[1]/CNote, /IxRoot[-5]/RootKey, IxRoot/Note]"],
    ["IxRoot/ROut=value 0"]) := by native_decide

/- `a-absent`: an empty index is unavailable, so neither the condition nor its negation fires and
the copy has no outcome. -/
example : observed none = some ([], []) := by native_decide

/- Partial validation fires as full validation does on every document: a no-match reads the one
instance's payload as absent rather than as its stored cell, so `LFN` fires and `LFA` does not. -/
example : [some "X", some "Y", none].all (fun key => (partialFired key).isSome && partialFired key == fullFired key) := by
  native_decide

example : partialFired (some "Y") = some ["K1N IxRoot/Note", "KDN IxFix/Note", "LFN IxRoot/Note"] := by native_decide

end A12Kernel.Dm.SingleInstanceKeyLocks
