import A12Kernel.Reference.Dm.PossibleCauseCheck
import A12Kernel.Reference.Dm.FieldTypeDeclarationRead

/-! # A rule's possible-cause filter

Kernel 31.3.1 reads a rule's `filterForPossiblyCausingEntities` and judges it twice: the metamodel refuses a
repeated entry within one slot, never withheld, and the model pass's last check refuses an entry that is
not the shortest relative path to an entity the condition references (a12-dmkits KF682,
`CheckerPossibleCauseFilterAgreementTest`; [inbound record](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-11-07)
§6). The rows are the letter's, on its carrier: `/Policy` holding `Premium`, `Holder`, a group `Rider` holding
`Code` and a repeatable `Lines` keyed by `Key` holding `Key` and `Amount`, and a second root `Agent` holding
`Name`.
-/

namespace A12Kernel.Dm.PossibleCauseFilterLocks

open Lean A12Kernel

private def string : Json := Json.mkObj [("type", "StringType")]
private def number : Json := Json.mkObj [("type", "NumberType"), ("NumberType", Json.mkObj [("maxFractionalDigits", toJson 0)])]

private def field (parent name : String) (type : Json := string) : Json :=
  Json.mkObj [("type", "Field"), ("id", .str s!"{parent}/{name}"), ("name", .str name), ("Field", Json.mkObj [("fieldType", type)])]

private def group (parent name : String) (members : List (String × Json)) (elements : List Json) : Json :=
  Json.mkObj [("type", "Group"), ("id", .str s!"{parent}/{name}"), ("name", .str name),
    ("Group", Json.mkObj (members ++ [("elements", Json.arr elements.toArray)]))]

/-- A rule `name` with error path `target`, `condition`, and `filter` as the member's JSON, if any. -/
private def rule (parent name target condition : String) (filter : Option Json) : Json :=
  Json.mkObj [("type", "Rule"), ("id", .str s!"{parent}/{name}"), ("name", .str name), ("Rule", Json.mkObj (
    [("errorCode", Json.str name), ("errorEntityRelPath", Json.str target), ("errorCondition", Json.str condition),
      ("severity", "ERROR")] ++ (filter.map fun filter => [("filterForPossiblyCausingEntities", filter)]).getD []))]

/-- The carrier with `policyRules` in `/Policy`, `lineRules` in `/Policy/Lines`, and `sorts` as `Lines`'
sort entries by name. -/
private def carrier (policyRules lineRules : List Json) (sorts : List String := []) : Json :=
  let sortFields := if sorts.isEmpty then [] else
    [("sortFields", Json.arr (sorts.map fun name => Json.mkObj [("name", .str name), ("order", "ASC")]).toArray)]
  Json.mkObj [
    ("header", Json.mkObj [("id", "P_DM"), ("modelType", "document"), ("modelVersion", "29.8.0"),
      ("locales", Json.arr #[Json.mkObj [("code", "en_US")]])]),
    ("content", Json.mkObj [("modelInfo", Json.mkObj [("name", "P")]),
      ("modelConfig", Json.mkObj [("timeZone", "UTC"), ("conditionLanguage", Json.mkObj [("code", "en_US")])]),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[
        group "" "Policy" [] ([field "/Policy" "Premium" number, field "/Policy" "Holder",
          group "/Policy" "Rider" [] [field "/Policy/Rider" "Code"],
          group "/Policy" "Lines" ([("repeatability", toJson 5), ("indexFieldName", "Key")] ++ sortFields)
            ([field "/Policy/Lines" "Key", field "/Policy/Lines" "Amount" number] ++ lineRules)] ++ policyRules),
        group "" "Agent" [] [field "/Agent" "Name"]])])])]

/-- A filter of the two slots, each entry a `relativePath` member. -/
private def filter (ifFilled ifNotFilled : List Json) : Json :=
  let slot (entries : List Json) := Json.arr (entries.map fun path => Json.mkObj [("relativePath", path)]).toArray
  Json.mkObj [("entitiesEnabledAsPossibleCauseIfFilled", slot ifFilled),
    ("entitiesEnabledAsPossibleCauseIfNotFilled", slot ifNotFilled)]

private def texts (paths : List String) : List Json := paths.map Json.str

/-- The reference classes the first rule of the model draws, `no model`, or why it is not judged. -/
private def referenceClasses (json : Json) (earlierModelCheckRefused : Bool := false) : String :=
  match readModel json with
  | .error _ => "no model"
  | .ok dm => match dm.rules.head? with
    | none => "no rule"
    | some first => match possibleCauseRefusals dm .english first earlierModelCheckRefused with
      | .ok refusals => ", ".intercalate (refusals.map (·.kernelCode))
      | .error reason => s!"unjudged: {reason}"

/-- The entries of the first rule's *if filled* slot the class names, spelled. -/
private def unreferenced (json : Json) : Option (List String) := do
  let dm ← (readModel json).toOption
  let first ← dm.rules.head?
  let candidates ← (possibleCauseCandidates dm.flat .english first).toOption
  pure (unreferencedPaths candidates ((first.possibleCauses.map (·.ifFilled)).getD []))

/-- A rule in `/Policy` reading `condition`, reporting on `target`, with `ifFilled` entries. -/
private def policyRow (condition : String) (ifFilled : List String) (target : String := "../Premium")
    (ifNotFilled : List String := []) : Json :=
  carrier [rule "/Policy" "Flagged" target condition (some (filter (texts ifFilled) (texts ifNotFilled)))] []

/-- The same rule in `/Policy/Lines`. -/
private def lineRow (condition : String) (ifFilled : List String) (target : String := "../Amount") : Json :=
  carrier [] [rule "/Policy/Lines" "Flagged" target condition (some (filter (texts ifFilled) []))]

private def filledClass : String := KernelStaticDiagnostic.refErrorEntityIfFilledNotReferenced.kernelCode
private def bothClasses : String :=
  s!"{filledClass}, {KernelStaticDiagnostic.refErrorEntityIfNotFilledNotReferenced.kernelCode}"

private def presence : String := "FieldFilled(Premium) And FieldFilled(Holder)"

/-- Row 1: the referenced fields by their shortest path, in either slot and in both; every other spelling
of them, and the own group and the root, which the condition does not reference, is refused, the empty
path reported as `./`. -/
example :
    referenceClasses (policyRow presence ["Premium"]) = "" ∧
    referenceClasses (policyRow presence [] (ifNotFilled := ["Holder"])) = "" ∧
    referenceClasses (policyRow presence ["Premium"] (ifNotFilled := ["Premium"])) = "" ∧
    unreferenced (policyRow presence ["./Premium", "../Policy/Premium", "Premium/", " Premium", "Lines/../Premium",
      "Rider//Code", "Premium/..", ".", "../", "Rider", ""]) =
      some ["./Premium", "../Policy/Premium", "Premium/", " Premium", "Lines/../Premium", "Rider//Code",
        "Premium/../", ".", "../", "Rider", "./"] ∧
    referenceClasses (policyRow presence ["Premium/"]) = filledClass ∧
    referenceClasses (policyRow presence ["Holder", "Rider"] (ifNotFilled := ["."])) = bothClasses := by
  native_decide

/-- Rows 2 to 7: a parent's field by its climb, a starred iteration's field but not its group, a group
operand but not its field, the own group and the index field a semantic index keys on, a `Having` body's
field, and another root's field through the technical root. -/
example :
    unreferenced (lineRow "[Amount] > [../Premium]" ["Amount", "../Premium", "Premium", ".."]) =
      some ["Premium", "../"] ∧
    unreferenced (policyRow "Sum(Lines*/Amount) > 5" ["Lines/Amount", "Lines", "Lines*/Amount"]
      (target := "../Premium")) = some ["Lines", "Lines*/Amount"] ∧
    unreferenced (policyRow "GroupFilled(Rider)" ["Rider", "Rider/Code"] (target := "../Rider")) =
      some ["Rider/Code"] ∧
    unreferenced (lineRow "GroupFilled(/Policy/Lines) And [Amount] > [Amount For \"K1\"]"
      ["Key", "Amount", "", "./", ".."]) = some ["../"] ∧
    unreferenced (policyRow "Sum(Lines*/Amount Having [Lines/Amount] > 0) > 5" ["Lines/Amount", "Lines"]) =
      some ["Lines"] ∧
    unreferenced (policyRow "FieldFilled(Premium) And FieldFilled(/Agent/Name)" ["../Agent/Name", "Agent/Name"]) =
      some ["Agent/Name"] := by
  native_decide

/-- The rows above are judged: each rule's own check admits it, so its classes are the filter's alone. -/
example :
    referenceClasses (lineRow "[Amount] > [../Premium]" ["Amount"]) = "" ∧
    referenceClasses (policyRow "Sum(Lines*/Amount) > 5" ["Lines/Amount"]) = "" ∧
    referenceClasses (policyRow "GroupFilled(Rider)" ["Rider"] (target := "../Rider")) = "" ∧
    referenceClasses (lineRow "GroupFilled(/Policy/Lines) And [Amount] > [Amount For \"K1\"]" ["Key", "./"]) = "" ∧
    referenceClasses (policyRow "Sum(Lines*/Amount Having [Lines/Amount] > 0) > 5" ["Lines/Amount"]) = "" ∧
    referenceClasses (policyRow "FieldFilled(Premium) And FieldFilled(/Agent/Name)" ["../Agent/Name"]) = "" := by
  native_decide

/-- The rule's own class withholds the check: an unresolved reference, an incomplete condition and an
unreferenced error field. So does an earlier model check: a sort field naming nothing, and an invalid time
zone, which the host reports. A sort field named twice and another rule's unresolved reference do not. -/
example :
    referenceClasses (policyRow "FieldFilled(Nope)" ["Rider"]) = "" ∧
    referenceClasses (policyRow "FieldFilled(Premium) And" ["Rider"]) = "" ∧
    referenceClasses (policyRow "FieldFilled(Holder)" ["Rider"]) = "" ∧
    referenceClasses (carrier [rule "/Policy" "Flagged" "../Premium" presence (some (filter (texts ["Rider"]) []))]
      [] ["Nope"]) = "" ∧
    referenceClasses (policyRow presence ["Rider"]) (earlierModelCheckRefused := true) = "" ∧
    referenceClasses (carrier [rule "/Policy" "Flagged" "../Premium" presence (some (filter (texts ["Rider"]) []))]
      [] ["Key", "Key"]) = filledClass ∧
    referenceClasses (carrier [rule "/Policy" "Flagged" "../Premium" presence (some (filter (texts ["Rider"]) [])),
      rule "/Policy" "Other" "../Premium" "FieldFilled(Nope)" none] []) = filledClass := by
  native_decide

/-- The metamodel's labels the model draws, `none` when no model is read. -/
private def slotLabels (json : Json) : Option (List String) :=
  ((fieldTypeDeclarationNotifications json fun _ => .compiled fun _ => true).toOption).map
    fun reported => (reported.map (·.1)).filter fun label =>
      label.startsWith "CUSTOM_REF" || label.startsWith "codeless:possible-cause"

/-- A repeat once spelled is the slot's duplicate class, beside a condition class too; a slot of 1 001
entries draws the codeless capacity notification and one of 1 000 does not. -/
example :
    slotLabels (policyRow presence ["", "./"]) = some ["CUSTOM_REF_ERROR_ENTITY_IF_FILLED_DUPLICATE"] ∧
    slotLabels (policyRow presence ["Rider/..", "Rider/../"]) = some ["CUSTOM_REF_ERROR_ENTITY_IF_FILLED_DUPLICATE"] ∧
    slotLabels (policyRow presence [] (ifNotFilled := ["Premium..", "Premium../"])) =
      some ["CUSTOM_REF_ERROR_ENTITY_IF_NOT_FILLED_DUPLICATE"] ∧
    slotLabels (policyRow "FieldFilled(Nope)" ["Premium", "Premium"]) =
      some ["CUSTOM_REF_ERROR_ENTITY_IF_FILLED_DUPLICATE"] ∧
    slotLabels (policyRow presence ["Premium", "Holder"]) = some [] ∧
    slotLabels (policyRow presence ((List.range 1001).map toString)) =
      some ["codeless:possible-cause-if-filled-capacity"] ∧
    slotLabels (policyRow presence ((List.range 1000).map toString)) = some [] := by
  native_decide

/-- A rule in `/Policy` carrying `member` as its filter's JSON. -/
private def shaped (member : Json) (parent : String := "/Policy") : Json :=
  if parent == "/Policy" then carrier [rule "/Policy" "Flagged" "../Premium" presence (some member)] []
  else carrier [] [rule "/Policy/Lines" "Flagged" "../Amount" "FieldFilled(Amount)" (some member)]

private def slotOf (value : Json) : Json := Json.mkObj [("entitiesEnabledAsPossibleCauseIfFilled", value)]
private def entryOf (entry : Json) : Json := slotOf (Json.arr #[entry])

/-- The shapes the reader refuses leave no model: a filter, a slot or an entry of the wrong kind, a path
that is absent or no scalar, an absolute path and a climb above the technical root. A `null` filter, an
absent slot, an unknown key and an extra entry member are read past, and a numeric path is its text. -/
example :
    ([Json.str "x", Json.arr #[], toJson (5 : Nat), Json.bool true].all fun member =>
      referenceClasses (shaped member) == "no model") ∧
    ([Json.str "x", Json.mkObj [], Json.null].all fun value => referenceClasses (shaped (slotOf value)) == "no model") ∧
    ([Json.str "Premium", toJson (5 : Nat), Json.null].all fun entry =>
      referenceClasses (shaped (entryOf entry)) == "no model") ∧
    ([Json.mkObj [], Json.mkObj [("relativePath", .null)], Json.mkObj [("relativePath", Json.arr #[])],
        Json.mkObj [("relativePath", Json.mkObj [])]].all fun entry =>
      referenceClasses (shaped (Json.mkObj [("entitiesEnabledAsPossibleCauseIfFilled", Json.arr #[entry])])) ==
        "no model") ∧
    referenceClasses (shaped (filter (texts ["/Policy/Premium"]) [])) = "no model" ∧
    referenceClasses (shaped (filter (texts ["../.."]) [])) = "no model" ∧
    referenceClasses (shaped (filter (texts ["../../.."]) []) "/Policy/Lines") = "no model" ∧
    referenceClasses (shaped (filter (texts ["../.."]) []) "/Policy/Lines") = filledClass ∧
    referenceClasses (shaped .null) = "" ∧
    referenceClasses (shaped (Json.mkObj [("unknown", toJson (1 : Nat))])) = "" ∧
    referenceClasses (shaped (entryOf (Json.mkObj [("relativePath", "Premium"), ("extra", toJson (1 : Nat))]))) = "" ∧
    unreferenced (shaped (filter [toJson (5 : Nat)] [])) = some ["5"] := by
  native_decide

end A12Kernel.Dm.PossibleCauseFilterLocks
