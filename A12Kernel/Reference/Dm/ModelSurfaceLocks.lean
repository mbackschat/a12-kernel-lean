import A12Kernel.Reference.Dm.Model
import A12Kernel.Reference.Dm.EntryFrameFixture
import A12Kernel.Reference.Dm.ModelVerdictFixture
import A12Kernel.Reference.Dm.Replay

/-! # Locks for the model reader's declaration surface

Three members of a DM-JSON declaration decide what the model contains before any condition is read: an
inline type definition, the global flag and a group's index and sort nominations. Each case pins one of
them against the reading that ignores the member. The last section locks the two members the reader
ignores altogether, a declaration's `variantFilter` and a rule's `variantErrorMessages`.
-/

namespace A12Kernel.Dm.ModelSurfaceLocks

open Lean A12Kernel A12Kernel.Dm

/-- A model whose root group `Form` holds the given elements, with optional extra content members. -/
private def model (elements : String) (content : String := "") : Option Json :=
  (Json.parse ("{\"content\":{" ++ content ++ "\"modelRoot\":{\"rootGroups\":[{\"type\":\"Group\"," ++
    "\"name\":\"Form\",\"Group\":{\"elements\":[" ++ elements ++ "]}}]}}}")).toOption.map checkedEntryFrame

private def field (name body : String) (extra : String := "") : String :=
  "{\"type\":\"Field\",\"name\":\"" ++ name ++ "\",\"Field\":{" ++ extra ++ "\"fieldType\":" ++ body ++ "}}"

private def string : String := "{\"type\":\"StringType\"}"

private def read (json : Option Json) : Option DmModel :=
  json.bind fun json => (readModel json).toOption

/- A kept field's refusals by the model reader: a duplicated Enumeration value is refused, while an inverted
   fractional pair is not. An unknown type leaves no model at all, since binding refuses it before the field
   is read (a12-dmkits `FieldTypeBindingLawsTest` at `1124b523f`, kernel 31.1.1), and so does an Enumeration
   with an empty domain, where kernel 30.8.1 and this reader refused only the field (Locked: a12-dmkits
   `EnumDeclarationShapeLawsTest` at `1124b523f`; [the declaration-shape locks](DeclarationShapeLocks.lean)). -/
example :
    let refusals (body : String) := (read (model (field "Value" string ++ "," ++ field "B" body))).map
      (·.refusals.length)
    refusals "{\"type\":\"NoSuchType\"}" = none ∧
      refusals "{\"type\":\"EnumerationType\",\"EnumerationType\":{\"values\":[{\"value\":\"a\"},{\"value\":\"a\"}]}}" =
        some 1 ∧
      refusals "{\"type\":\"EnumerationType\",\"EnumerationType\":{\"values\":[]}}" = none ∧
      refusals "{\"type\":\"NumberType\",\"NumberType\":{\"minFractionalDigits\":3,\"maxFractionalDigits\":2}}" =
        some 0 := by
  native_decide

private def typedefs : String :=
  "\"typeDefinitions\":[{\"id\":\"NumTd\",\"name\":\"NumTd\",\"fieldType\":{\"type\":\"NumberType\"," ++
    "\"NumberType\":{\"maxFractionalDigits\":2}}}],"

private def typedefField (id : String) : String :=
  field "T" ("{\"type\":\"TypeDefType\",\"TypeDefType\":{\"typeDefinitionId\":\"" ++ id ++ "\"}}")

/- A type definition field is its definition's base kind, so it reads as that Number. An id naming no
   definition of this model, as an imported one would, and a reference without an id leave the field a
   plain String and draw the converter's sentence as a refusal (kernel 31.1.1, where 30.8.1 built no model;
   [the converter locks](ConverterSentenceLocks.lean) lock the whole set of classes). -/
example :
    ((read (model (typedefField "NumTd") typedefs)).bind (·.flat.fields.head?)).map (·.policy.kind) =
        some (.number { scale := 2, signed := true }) ∧
      ((read (model (typedefField "Elsewhere") typedefs)).map fun dm =>
        (dm.refusals, dm.flat.fields.map (·.policy.kind))) =
        some ([(["Form", "T"], "codeless:type-definition-not-found")], [.string]) ∧
      ((read (model (field "T" "{\"type\":\"TypeDefType\",\"TypeDefType\":{}}") typedefs)).map fun dm =>
        (dm.refusals, dm.flat.fields.map (·.policy.kind))) =
        some ([(["Form", "T"], "codeless:type-definition-not-found")], [.string]) := by
  native_decide

/- The global flag reaches the declaration that partial validation reads (spec/10 §relevant set). -/
example :
    ((read (model (field "G" string "\"global\":true,"))).bind (·.flat.fields.head?)).map (·.isGlobal) = some true ∧
      ((read (model (field "G" string))).bind (·.flat.fields.head?)).map (·.isGlobal) = some false := by
  native_decide

/-- `Form` with a String `Value`, and a four-row `Items` holding `K`, a raw String `NVV`, which must
permit line breaks, and the given member text on the group. -/
private def nominating (members : String) (kField : String := field "K" string) : Option Json :=
  model (field "Value" string ++ ",{\"type\":\"Group\",\"name\":\"Items\",\"Group\":{\"repeatability\":4," ++
    members ++ "\"elements\":[" ++ kField ++ "," ++
    field "NVV" "{\"type\":\"StringType\",\"StringType\":{\"noValueValidation\":true,\"lineBreaksPermitted\":true}}" ++ "]}}")

private def nominationCodes (json : Option Json) : Option (List String) :=
  (read json).map (·.refusals.map (·.2))

/- The reader judges nominations by the shared row-key cascade: the raw String's class, a name carried only
   by the parent, a name carried by no group, and the duplicate and capacity judgements. A name no direct
   child field carries draws the role's class whatever it lands on, where kernel 30.8.1 built no model for
   one landing nowhere; the spellings that still leave none are
   [the ordering locks](OrderingMemberLocks.lean)' (Locked: a12-dmkits GroupIndexAndSortReferenceLawsTest at
   1124b523f, kernel 31.1.1). -/
example :
    nominationCodes (nominating "\"sortFields\":[{\"name\":\"K\"}],") = some [] ∧
      nominationCodes (nominating "\"sortFields\":[{\"name\":\"NVV\"}],") =
        some ["MVK_SORT_FIELD_NO_VALUE_VALIDATION"] ∧
      nominationCodes (nominating "\"sortFields\":[{\"name\":\"../Value\"}],") = some ["MVK_INVALID_SORT_FIELD"] ∧
      nominationCodes (nominating "\"sortFields\":[{\"name\":\"K\"},{\"name\":\"K\"}],") =
        some ["MVK_SORT_FIELD_DUPLICATE"] ∧
      nominationCodes (nominating
          "\"sortFields\":[{\"name\":\"K\"},{\"name\":\"K\"},{\"name\":\"K\"},{\"name\":\"K\"}],") =
        some ["MVK_SORT_FIELD_DUPLICATE", "codeless:sort-list-capacity"] ∧
      nominationCodes (nominating "\"indexFieldName\":\"Nope\",") = some ["MVK_INVALID_INDEX_FIELD"] ∧
      nominationCodes (nominating "\"indexFieldName\":\"/Form/Items/K\",") =
        some ["nomination /Form/Items/K leaves no model"] ∧
      nominationCodes (nominating "\"sortFields\":[{\"name\":\"\"}],") = some ["nomination  leaves no model"] := by
  native_decide

/-! ## Retired variant members

DM 29.1 retired a declaration's `variantFilter` and a rule's `variantErrorMessages`; kernel 31.1.1 reads
past both in every shape, exactly as past an unknown member. Each row compares a model carrying the member
with the same model without it, on every carrier and on two twins: one the Kernel admits, and one it
refuses because the rule or computation names a field that exists nowhere (`MVK_INVALID_ENTITY`). The
field carrier's twin is a rule that names the field, so a retired deletion would break the admitted twin
and leave the refused one refused.

Locked: a12-dmkits RetiredVariantMembersLawsTest at 1124b523f, kernel 31.1.1. -/

private inductive Carrier where
  | rule | field | computation
  deriving DecidableEq

private def Carrier.all : List Carrier := [.rule, .field, .computation]

private def numberField (name : String) : Json :=
  Json.mkObj [("type", "Field"), ("id", .str s!"/Form/{name}"), ("name", .str name),
    ("Field", Json.mkObj [("fieldType", Json.mkObj [("type", "NumberType"), ("NumberType", Json.mkObj [("maxFractionalDigits", toJson (0 : Nat))])])])]

private def stringField (name : String) (members : List (String × Json)) : Json :=
  Json.mkObj [("type", "Field"), ("id", .str s!"/Form/{name}"), ("name", .str name), ("Field", Json.mkObj (members ++
    [("fieldType", Json.mkObj [("type", "StringType")])]))]

/-- A rule reporting at `entity`, with the given members beside the authored ones. -/
private def ruleElement (name entity condition : String) (members : List (String × Json)) : Json :=
  Json.mkObj [("type", "Rule"), ("id", .str s!"/Form/{name}"), ("name", .str name), ("Rule", Json.mkObj (([("errorCondition", .str condition),
    ("errorEntityRelPath", .str s!"../{entity}"), ("errorCode", "C"), ("severity", "ERROR"),
    ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]])] : List (String × Json)) ++
      members))]

private def computationElement (name operation : String) (members : List (String × Json)) : Json :=
  Json.mkObj [("type", "Computation"), ("id", .str s!"/Form/{name}"), ("name", .str name), ("Computation", Json.mkObj (([
    ("computedFieldRelPath", "../Total"),
    ("computationAlternatives", Json.arr #[Json.mkObj [("operation", .str operation)]])] :
      List (String × Json)) ++ members))]

/-- One model of a carrier and twin, the carrier's declaration holding `members`: `Form` with a String
`Value` and Numbers `Amount` and `Total`, then a rule over `Value`, a String field `B` with a rule over
it, or a computation of `Total` from `Amount`. The refused twin reads a field named `Missing`. -/
private def carrierModel (carrier : Carrier) (refused : Bool) (members : List (String × Json)) : Json :=
  let read (existing : String) := if refused then "Missing" else existing
  let elements : List Json := [stringField "Value" [], numberField "Amount", numberField "Total"] ++
    match carrier with
    | .rule => [ruleElement "R" "Value" s!"FieldFilled({read "Value"})" members]
    | .field => [stringField "B" members, ruleElement "RB" "B" s!"FieldFilled({read "B"})" []]
    | .computation => [computationElement "C" s!"[{read "Amount"}]" members]
  checkedEntryFrame <| Json.mkObj [("content", Json.mkObj [("modelRoot", Json.mkObj [("rootGroups", Json.arr #[
    Json.mkObj [("type", "Group"), ("id", "/Form"), ("name", "Form"),
      ("Group", Json.mkObj [("elements", Json.arr elements.toArray)])]])])])]

/-- Whether a model carrying `members` has the verdict of the same model without them, on both twins. -/
private def ignored (carrier : Carrier) (members : List (String × Json)) : Bool :=
  [false, true].all fun refused =>
    modelVerdict (carrierModel carrier refused members) == modelVerdict (carrierModel carrier refused [])

/-- The twins differ, so equality with the member removed is not vacuous: the admitted twin passes its
static check on each carrier, and the refused twin draws `MVK_INVALID_ENTITY`. -/
example :
    Carrier.all.map (fun carrier => ((modelVerdict (carrierModel carrier false [])).statics,
      (modelVerdict (carrierModel carrier true [])).statics)) =
      [(["ok"], ["refused FieldFilled MVK_INVALID_ENTITY"]), (["ok"], ["refused FieldFilled MVK_INVALID_ENTITY"]),
        (["ok"], ["refused NumberComputation MVK_INVALID_ENTITY"])] := by
  native_decide

private def filter (members : List (String × Json)) : List (String × Json) :=
  [("variantFilter", Json.mkObj members)]

/-- The twelve shapes of a `variantFilter` the retired member was written as. -/
private def filterShapes : List (List (String × Json)) := [
  filter [("filterType", "ONLY"), ("variants", Json.arr #["v1"])],
  filter [("filterType", "ONLY"), ("variants", Json.arr #["default"])],
  filter [("filterType", "ONLY"), ("variants", Json.arr #[])],
  filter [("filterType", "ONLY")],
  filter [("filterType", "ALL_EXCEPT"), ("variants", Json.arr #["v1"])],
  filter [("filterType", "UNKNOWN")],
  filter [("variants", Json.arr #["v1"])],
  filter [("filterType", Json.null)],
  filter [("filterType", Json.mkObj [])],
  filter [("filterType", toJson (7 : Nat))],
  [("variantFilter", Json.null)],
  [("variantFilter", "ONLY")]]

/-- A `variantFilter` of every shape is read past on a rule, a field and a computation. -/
example : filterShapes.length = 12 ∧
    Carrier.all.all (fun carrier => filterShapes.all (ignored carrier ·)) = true := by
  native_decide

private def messageEntry (members : List (String × Json)) : Json := Json.mkObj members

private def fixIt : List (String × Json) := [("locale", "en_US"), ("text", "Fix it.")]

/-- The eight shapes of a rule's `variantErrorMessages`: an empty object, one message, `null`, an entry with
no locale and one with no text, an array, a `null` value and a single entry written as an object. -/
private def messageShapes : List (List (String × Json)) := [
  [("variantErrorMessages", Json.mkObj [])],
  [("variantErrorMessages", Json.mkObj [("v1", Json.arr #[messageEntry fixIt])])],
  [("variantErrorMessages", Json.null)],
  [("variantErrorMessages", Json.mkObj [("v1", Json.arr #[messageEntry [("text", "Fix it.")]])])],
  [("variantErrorMessages", Json.mkObj [("v1", Json.arr #[messageEntry [("locale", "en_US")]])])],
  [("variantErrorMessages", Json.arr #[messageEntry fixIt])],
  [("variantErrorMessages", Json.mkObj [("v1", Json.null)])],
  [("variantErrorMessages", Json.mkObj [("v1", messageEntry fixIt)])]]

example : messageShapes.length = 8 ∧ messageShapes.all (ignored .rule ·) = true := by
  native_decide

/-- A locale-keyed map of plain text, the shape of an ordinary localized message written under the member. -/
example : ignored .rule [("variantErrorMessages", Json.mkObj [("en_US", "Fix it.")])] = true := by
  native_decide

/-- The control: a member the model declares nothing for. -/
example : Carrier.all.all (ignored · [("colourScheme", Json.mkObj [("hue", "teal")])]) = true := by
  native_decide

/-- The runtime route of the `fired` rows of the written-member locks: the `code@pointer` messages full
validation reports over a document whose `Value` is filled, for the rule `R` of a `Form` model carrying
`members`. -/
private def fired (members : List (String × Json)) : Option (List String) := do
  let dm ← (readModel (carrierModel .rule false members)).toOption
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [("Value", "x")])])).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let validated ← checked.fullValidationDocument.toOption
  let messages ← dm.rules.mapM fun definition => do
    let rule ← (checkValidationRule dm .english definition world).toOption
    (runValidationRule world validated rule).toOption
  pure (messages.flatten.map fun message => s!"{message.errorCode}@{(observe dm.flat message).pointer}")

/-- A rule `ONLY` for a variant fires on a document that violates it, as the rule without the member does. -/
example :
    fired (filter [("filterType", "ONLY"), ("variants", Json.arr #["v1"])]) = some ["C@Form/Value"] ∧
      fired [] = some ["C@Form/Value"] := by
  native_decide

end A12Kernel.Dm.ModelSurfaceLocks
