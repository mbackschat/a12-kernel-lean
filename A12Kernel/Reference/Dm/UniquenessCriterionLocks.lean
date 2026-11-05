import Lean.Data.Json
import A12Kernel.Reference.Dm.EntryFrameFixture
import A12Kernel.Reference.Dm.ModelConsistencyRead

/-! # Document uniqueness criteria in the model check

Kernel 31.1.1's consistency check refuses a model whose `content.documentUniquenessCriteria` holds a criterion
that lacks a name, a field, a field it can read, an admissible field or an error text for the model locale
(spec/01 §1.5). Every refusal row differs from the admitted control in one member of one criterion, on one
fixture, and asserts the whole class list the model check draws: the criterion rows below are the peer's
admission rows, written into the stored model as text because the kits do not author them. The fixture is
this repository's own insurance-policy domain.

The peer states every class but one as a sentence with no class key, so a row's label is the codeless
class this check names it by, and only the dollar count is the keyed class. The rows pin the class list and
no payload, so the notification path the check attaches, the criterion's name, is this module's choice and
no observation (the last example). The expansion, rename and move rows of the same peer test need a host
that expands or moves a model, which this check does not model, so they are not locked here.

Locked: a12-dmkits DocumentUniquenessCriterionLawsTest at 1124b523f, kernel 31.1.1; the reach and order rows
below: `DocumentUniquenessCriterionReachLawsTest` and `CheckerUniquenessCriterionAgreementTest` at
`da388eeac`, kernel 31.1.1 (KF671).
-/

namespace A12Kernel.Dm.UniquenessCriterionLocks

open Lean A12Kernel

/-! ## The carrier -/

private def named (kind id name : String) (body : List (String × Json)) : Json :=
  Json.mkObj [("type", .str kind), ("id", .str id), ("name", .str name), (kind, Json.mkObj body)]

private def absolute : String := "absoluteOrRelativeToNextRepAncestor"

private def withParent : String := "relativeToParent"

/-- A String field under `parent`, required in the mode written, if any, and transient when asked. -/
private def stringField (parent name : String) (mode : Option String := none)
    (transient : Bool := false) : Json :=
  named "Field" s!"{parent}/{name}" name
    ([("fieldType", Json.mkObj [("type", "StringType")])] ++
      (mode.map fun written => [("requirednessConfig", Json.mkObj [("mode", .str written)])]).getD [] ++
      (if transient then [("transient", Json.bool true)] else []))

private def groupOf (id name : String) (repeatability : Nat) (children : List Json) : Json :=
  named "Group" id name [("repeatability", toJson repeatability), ("elements", Json.arr children.toArray)]

/-- `PolicyNo` and `Product` required, `Holder` optional, `Branch` required only when its parent is,
`Draft` transient, `Scratch` optional and transient, and a repeatable `Claims` of three whose `ClaimRef` and
its fixed `Parts`' `PartRef` are required. -/
private def policy : Json :=
  groupOf "/Policy" "Policy" 1
    [stringField "/Policy" "PolicyNo" (some absolute), stringField "/Policy" "Product" (some absolute),
      stringField "/Policy" "Holder",
      groupOf "/Policy/Office" "Office" 1 [stringField "/Policy/Office" "Branch" (some withParent)],
      stringField "/Policy" "Draft" (some absolute) (transient := true),
      stringField "/Policy" "Scratch" (transient := true),
      groupOf "/Policy/Claims" "Claims" 3 [stringField "/Policy/Claims" "ClaimRef" (some absolute),
        groupOf "/Policy/Claims/Parts" "Parts" 1 [stringField "/Policy/Claims/Parts" "PartRef" (some absolute)]]]

/-- A criterion as the model stores it; no text is an empty message list. -/
private def criterion (name : String) (fields : List String) (text : Option String) : Json :=
  Json.mkObj [("name", .str name),
    ("fields", Json.arr (fields.map fun path => Json.mkObj [("fullName", .str path)]).toArray),
    ("errorMessage", Json.arr (text.toList.map fun written =>
      Json.mkObj [("locale", "en_US"), ("text", .str written)]).toArray)]

/-- The policy model declaring "en_US", with these criteria, or without the member. -/
private def modelWith (criteria : Option (List Json)) : Json :=
  checkedEntryFrame <| Json.mkObj [("content", Json.mkObj (
    [("modelConfig", Json.mkObj [("conditionLanguage", Json.mkObj [("code", "en_US")])]),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[policy])])] ++
    (criteria.map fun listed => [("documentUniquenessCriteria", Json.arr listed.toArray)]).getD []))]

/-! ## The rows -/

private def nameMissing : String := "codeless:uniqueness-criterion-name-missing"
private def noField : String := "codeless:uniqueness-criterion-no-field"
private def fieldNotFound : String := "codeless:uniqueness-criterion-field-not-found"
private def fieldNotRequired : String := "codeless:uniqueness-criterion-field-not-required"
private def fieldRepeatable : String := "codeless:uniqueness-criterion-field-repeatable"
private def fieldTransient : String := "codeless:uniqueness-criterion-field-transient"
private def textMissing : String := "codeless:uniqueness-criterion-text-missing"
private def nameDuplicate : String := "codeless:uniqueness-criterion-name-duplicate"
private def parameterInvalid : String := "codeless:uniqueness-criterion-parameter-invalid"
/-- The one keyed class, the kernel's code for an odd dollar count. -/
private def wrongNumberOfDollars : String := "WRONG_NUMBER_OF_DOLLARS"

private def control : Json :=
  criterion "PolicyKey" ["/Policy/PolicyNo"] (some "Key $/Policy/PolicyNo.value$ is taken")

/-- The peer's rows: a label, the model's criteria and the class labels the check draws in order. -/
private def rows : List (String × List Json × List String) := [
  ("control: one required field, one text naming it", [control], []),
  ("control: two required fields",
    [criterion "PolicyKey" ["/Policy/PolicyNo", "/Policy/Product"]
      (some "Key $/Policy/PolicyNo$ of $/Policy/Product.value$ is taken")], []),
  ("no criteria at all", [], []),
  ("an empty name", [criterion "" ["/Policy/PolicyNo"] (some "Taken")], [nameMissing]),
  ("no field", [criterion "PolicyKey" [] (some "Taken")], [noField]),
  ("a field that does not exist",
    [criterion "PolicyKey" ["/Policy/Missing"] (some "Taken")], [fieldNotFound]),
  ("a group in the field slot",
    [criterion "PolicyKey" ["/Policy/Office"] (some "Taken")], [fieldNotFound]),
  ("a relative field path", [criterion "PolicyKey" ["PolicyNo"] (some "Taken")], [fieldNotFound]),
  ("an optional field",
    [criterion "PolicyKey" ["/Policy/Holder"] (some "Taken")], [fieldNotRequired]),
  ("a field required only with its parent",
    [criterion "PolicyKey" ["/Policy/Office/Branch"] (some "Taken")], [fieldNotRequired]),
  ("a field in a repeatable group",
    [criterion "PolicyKey" ["/Policy/Claims/ClaimRef"] (some "Taken")], [fieldRepeatable]),
  ("a transient field",
    [criterion "PolicyKey" ["/Policy/Draft"] (some "Taken")], [fieldTransient]),
  ("no error text", [criterion "PolicyKey" ["/Policy/PolicyNo"] none], [textMissing]),
  ("two criteria of one name",
    [control, criterion "PolicyKey" ["/Policy/Product"] (some "Taken")], [nameDuplicate, nameDuplicate]),
  ("a text naming a field outside the criterion",
    [criterion "PolicyKey" ["/Policy/PolicyNo"] (some "Key $/Policy/Product$ is taken")], [parameterInvalid]),
  ("a text naming the field relatively",
    [criterion "PolicyKey" ["/Policy/PolicyNo"] (some "Key $PolicyNo$ is taken")], [parameterInvalid]),
  ("an unterminated parameter",
    [criterion "PolicyKey" ["/Policy/PolicyNo"] (some "Key $/Policy/PolicyNo is taken")],
    [wrongNumberOfDollars])]

private def labelsOf (criteria : Option (List Json)) : Option (List String) :=
  match checkModelConsistency (modelWith criteria) with
  | .ok (.checked notifications) => some (notifications.map (·.kind.observedLabel))
  | _ => none

/-- The rows whose model draws other classes than the oracle's, named so a regression shows its row. -/
private def disagreeing : List String :=
  (rows.filter fun (_, criteria, expected) => labelsOf (some criteria) != some expected).map (·.1)

example : disagreeing = [] := by native_decide

/-- The rows are distinct models: every refusal class of the check is drawn by some row, so no row stands
for a class another row already guards. -/
example : ([nameMissing, noField, fieldNotFound, fieldNotRequired, fieldRepeatable, fieldTransient,
    textMissing, nameDuplicate, parameterInvalid, wrongNumberOfDollars].all fun label =>
      rows.any fun (_, _, expected) => expected.contains label) = true := by native_decide

/-- A model without the member and one with an empty list admit alike. -/
example : labelsOf none = some [] ∧ labelsOf (some []) = some [] := by native_decide

/-- The refusal names its criterion as its path and, for a repeated name, once for each of the two. This
pins the check's choice of path, which the oracle's class sets leave unmeasured. -/
example : (checkModelConsistency (modelWith (some
      [control, criterion "PolicyKey" ["/Policy/Product"] (some "Taken")]))).toOption =
    some (.checked [
      { path := ["PolicyKey"], kind := .uniquenessCriterionNameDuplicate },
      { path := ["PolicyKey"], kind := .uniquenessCriterionNameDuplicate }]) := by
  native_decide

/-- Two names shared twice, interleaved: `ProductKey` is authored first, and the shared names still come in the
iteration order of the map the Kernel groups the criteria into, `PolicyKey` first (a12-dmkits
`CheckerUniquenessCriterionAgreementTest` at `c7afca597`, kernel 31.1.1). -/
example : ((checkModelConsistency (modelWith (some [criterion "ProductKey" ["/Policy/Product"] (some "Taken"),
      criterion "PolicyKey" ["/Policy/PolicyNo"] (some "Taken"), criterion "ProductKey" ["/Policy/PolicyNo"] (some "Taken"),
      criterion "PolicyKey" ["/Policy/Product"] (some "Taken")]))).toOption.map fun
        | .checked notifications => notifications.filterMap fun notification =>
            if notification.kind == .uniquenessCriterionNameDuplicate then notification.path.head? else none
        | _ => []) =
    some ["PolicyKey", "PolicyKey", "ProductKey", "ProductKey"] := by
  native_decide

/-! ## Reach and order -/

/-- A criterion whose fields and texts are written as the model stores them. -/
private def stored (name : String) (fields : List Json) (texts : List (String × String)) : Json :=
  Json.mkObj [("name", .str name), ("fields", Json.arr fields.toArray),
    ("errorMessage", Json.arr (texts.map fun (locale, text) =>
      Json.mkObj [("locale", .str locale), ("text", .str text)]).toArray)]

private def fullName (path : String) : Json := Json.mkObj [("fullName", .str path)]

/-- The policy model declaring "en_US" and "de_DE", with these criteria. -/
private def bilingual (criteria : List Json) : Json :=
  match modelWith (some criteria) with
  | .obj members => match members.get? "header" with
    | some header => .obj (members.insert "header" (header.setObjVal! "locales"
        (Json.arr #[Json.mkObj [("code", "en_US")], Json.mkObj [("code", "de_DE")]])))
    | none => .null
  | _ => .null

private def key : String := "Key $/Policy/PolicyNo$ is taken"

/-- An item without `fullName` is skipped beside a field that decides the criterion, and a text whose locale is
spelled `en-US` is the model locale's text. An empty text is no text, a blank one is a text, and a line break
or a control character draws the shared gate's keyed class. -/
example :
    labelsOf (some [stored "PolicyKey" [fullName "/Policy/PolicyNo", Json.mkObj []] [("en_US", key)]]) = some [] ∧
    labelsOf (some [stored "PolicyKey" [fullName "/Policy/PolicyNo"] [("en-US", key)]]) = some [] ∧
    labelsOf (some [stored "PolicyKey" [fullName "/Policy/PolicyNo"] [("en_US", "")]]) = some [textMissing] ∧
    labelsOf (some [stored "PolicyKey" [fullName "/Policy/PolicyNo"] [("en_US", " ")]]) = some [] ∧
    labelsOf (some [stored "PolicyKey" [fullName "/Policy/PolicyNo"] [("en_US", "Key\ntaken")]]) =
      some ["INVALID_LINEBREAK"] ∧
    labelsOf (some [stored "PolicyKey" [fullName "/Policy/PolicyNo"] [("en_US", "Key\u0007taken")]]) =
      some ["INVALID_CHARACTERS"] ∧
    labelsOf (some [stored "PolicyKey" [fullName "/Policy/PolicyNo.value"] [("en_US", "Taken")]]) =
      some [fieldNotFound] ∧
    labelsOf (some [stored "PolicyKey" [fullName "/Policy/PolicyNo", fullName "/Policy/PolicyNo"] [("en_US", key)]]) =
      some [] := by native_decide

/-- Each parameter naming no field of the criterion draws its own refusal, and a lone surrogate, read as the
stand-in `parseModelJson` writes for its escape, draws the encoding gate's keyed class. -/
example :
    labelsOf (some [stored "PolicyKey" [fullName "/Policy/PolicyNo"]
        [("en_US", "No $/Policy/Product$ and $PolicyNo$")]]) = some [parameterInvalid, parameterInvalid] ∧
    labelsOf (some [stored "PolicyKey" [fullName "/Policy/PolicyNo"]
        [("en_US", "Key " ++ String.singleton loneSurrogateStandIn ++ " taken")]]) = some ["WRONG_ENCODING"] := by
  native_decide

/-- A field below a fixed group inside a repeatable one is repeatable, an optional transient field draws both
refusals, requiredness first, and the same field named twice draws them once. -/
example :
    labelsOf (some [stored "PolicyKey" [fullName "/Policy/Claims/Parts/PartRef"] [("en_US", "Taken")]]) =
      some [fieldRepeatable] ∧
    labelsOf (some [stored "PolicyKey" [fullName "/Policy/Scratch"] [("en_US", "Taken")]]) =
      some [fieldNotRequired, fieldTransient] ∧
    labelsOf (some [stored "PolicyKey" [fullName "/Policy/Scratch", fullName "/Policy/Scratch"] [("en_US", "Taken")]]) =
      some [fieldNotRequired, fieldTransient] := by native_decide

private def bilingualLabels (criteria : List Json) : Option (List String) :=
  match checkModelConsistency (bilingual criteria) with
  | .ok (.checked notifications) => some (notifications.map (·.kind.observedLabel))
  | _ => none

/-- Every declared locale is asked for a text, and the locales holding none are stated before each stored
text's own refusal. -/
example :
    bilingualLabels [stored "PolicyKey" [fullName "/Policy/PolicyNo"] [("en_US", key), ("de_DE", key)]] = some [] ∧
    bilingualLabels [stored "PolicyKey" [fullName "/Policy/PolicyNo"] [("en_US", key)]] = some [textMissing] ∧
    bilingualLabels [stored "PolicyKey" [fullName "/Policy/PolicyNo"] [("de_DE", "Key\ntaken")]] =
      some [textMissing, "INVALID_LINEBREAK"] := by native_decide

/-- The names two criteria share come first, once for each of the two, before every criterion's own
refusals. -/
example :
    labelsOf (some [stored "PolicyKey" [fullName "/Policy/PolicyNo"] [("en_US", "Taken")],
        stored "Other" [] [("en_US", "Taken")],
        stored "PolicyKey" [fullName "/Policy/Holder"] [("en_US", "Taken")]]) =
      some [nameDuplicate, nameDuplicate, noField, fieldNotRequired] := by native_decide

end A12Kernel.Dm.UniquenessCriterionLocks
