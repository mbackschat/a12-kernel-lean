import A12Kernel.Reference.Dm.Model
import A12Kernel.Reference.Dm.EntryFrameFixture

/-! # Locks for the model reader's declaration surface

Four members of a DM-JSON declaration decide what the default-variant model contains before any
condition is read: a variant filter, an inline type definition, the global flag and a group's index
and sort nominations. Each case pins one of them against the reading that ignores the member.
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

private def rule (name : String) (extra : String := "") : String :=
  "{\"type\":\"Rule\",\"name\":\"" ++ name ++ "\",\"Rule\":{" ++ extra ++
    "\"errorCondition\":\"FieldFilled(Value)\",\"errorEntityRelPath\":\"../Value\",\"errorCode\":\"C\"}}"

private def only : String := "\"variantFilter\":{\"filterType\":\"ONLY\",\"variants\":[\"V1\"]},"
private def allExcept : String := "\"variantFilter\":{\"filterType\":\"ALL_EXCEPT\",\"variants\":[\"V1\"]},"

private def read (json : Option Json) (variant : Option String := none) : Option DmModel :=
  json.bind fun json => (readModel json none variant).toOption

private def fieldNames (json : Option Json) (variant : Option String := none) : Option (List String) :=
  (read json variant).map (·.flat.fields.map (·.name))

/- At the default variant `ONLY` removes a field and `ALL_EXCEPT` keeps it, whichever variants are
   named; a `null` filter is no filter. Naming the active variant flips both (spec/01 §3). -/
example :
    fieldNames (model (field "Value" string ++ "," ++ field "B" string only)) = some ["Value"] ∧
      fieldNames (model (field "Value" string ++ "," ++ field "B" string allExcept)) = some ["Value", "B"] ∧
      fieldNames (model (field "Value" string ++ "," ++ field "B" string "\"variantFilter\":null,")) =
        some ["Value", "B"] ∧
      fieldNames (model (field "Value" string ++ "," ++ field "B" string only)) (some "V1") =
        some ["Value", "B"] ∧
      fieldNames (model (field "Value" string ++ "," ++ field "B" string allExcept)) (some "V1") =
        some ["Value"] := by
  native_decide

/- A filtered rule is not read at all, so a malformed name it carries draws nothing; the unfiltered
   twin is refused. A filter whose type is unknown, absent or not an object fails the whole model. -/
example :
    ((read (model (field "Value" string ++ "," ++ rule "1Hidden" only))).map (·.rules.length)) = some 0 ∧
      (read (model (field "Value" string ++ "," ++ rule "1Hidden"))).isNone ∧
      (read (model (field "Value" string ++ "," ++ rule "Kept" allExcept))).map (·.rules.length) = some 1 ∧
      [ "\"variantFilter\":{\"filterType\":\"SOME\"},", "\"variantFilter\":{\"variants\":[]},",
        "\"variantFilter\":\"ONLY\",", "\"variantFilter\":{\"filterType\":7},"].all
        (fun filter => (read (model (field "Value" string ++ "," ++ rule "R" filter))).isNone) := by
  native_decide

/- A filtered field keeps only the authored-model refusals: an unknown type and a duplicated
   Enumeration value are refused, while a check the default variant makes, here an empty Enumeration
   domain and an inverted fractional pair, goes with the field. -/
example :
    let refusals (body : String) := (read (model (field "Value" string ++ "," ++ field "B" body only))).map
      (·.refusals.length)
    refusals "{\"type\":\"NoSuchType\"}" = some 1 ∧
      refusals "{\"type\":\"EnumerationType\",\"EnumerationType\":{\"values\":[{\"value\":\"a\"},{\"value\":\"a\"}]}}" =
        some 1 ∧
      refusals "{\"type\":\"EnumerationType\",\"EnumerationType\":{\"values\":[]}}" = some 0 ∧
      refusals "{\"type\":\"NumberType\",\"NumberType\":{\"minFractionalDigits\":3,\"maxFractionalDigits\":2}}" =
        some 0 := by
  native_decide

private def typedefs : String :=
  "\"typeDefinitions\":[{\"id\":\"NumTd\",\"name\":\"NumTd\",\"fieldType\":{\"type\":\"NumberType\"," ++
    "\"NumberType\":{\"maxFractionalDigits\":2}}}],"

private def typedefField (id : String) : String :=
  field "T" ("{\"type\":\"TypeDefType\",\"TypeDefType\":{\"typeDefinitionId\":\"" ++ id ++ "\"}}")

/- A type definition field is its definition's base kind, so it reads as that Number. An id naming no
   definition of this model, as an imported one would, and a reference without an id are refused. -/
example :
    ((read (model (typedefField "NumTd") typedefs)).bind (·.flat.fields.head?)).map (·.policy.kind) =
        some (.number { scale := 2, signed := true }) ∧
      (read (model (typedefField "Elsewhere") typedefs)).map (·.refusals.length) = some 1 ∧
      (read (model (field "T" "{\"type\":\"TypeDefType\",\"TypeDefType\":{}}") typedefs)).map
        (·.refusals.length) = some 1 := by
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

/- The reader judges nominations by the shared row-key cascade: the raw String's class, a name bound
   in the parent but absent here, the duplicate and capacity judgements, and a field the variant filter
   removed, which is still bound but judged absent. A name binding nowhere is codeless. -/
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
      nominationCodes (nominating "\"indexFieldName\":\"K\"," (field "K" string only)) =
        some ["MVK_INVALID_INDEX_FIELD"] ∧
      nominationCodes (nominating "\"indexFieldName\":\"Nope\",") = some ["nomination Nope names no field"] := by
  native_decide

end A12Kernel.Dm.ModelSurfaceLocks
