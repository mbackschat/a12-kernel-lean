import Lean.Data.Json
import A12Kernel.Reference.Dm.Model
import A12Kernel.Reference.Dm.EntryFrameFixture

/-! # Reader integration for ordinary Enumeration declaration notifications

Each row mirrors one model in the retained real-Kernel capture of ordinary Enumeration
declaration notifications (`evidence/kernel-30.8.1/captures/enumeration-declaration-findings-2026-10-13/`):
a root group `Store` with a String field `Reference` and an Enumeration field `Tier`, whose declaration
and optional restricted charset are set from the row. The assertion is the retained observation: the
ordered notification classes the reader records (a codeless class is named by its constructor), that an
unaffected declaration keeps its field, and that an affected one is refused rather than evaluated.
-/

namespace A12Kernel.Dm.EnumerationDeclarationNotificationLocks

open Lean A12Kernel

/-- One retained declaration: stored tokens, categories, a display text for chosen tokens, whether the
model restricts its supported characters, to `charset`, and the ordered notification classes observed. -/
private structure Row where
  values : List String
  categories : List (String × List String) := []
  labels : List (String × String) := []
  restricted : Bool := false
  charset : List String := ["A-Z"]
  expected : List String

private def missingCategory : String := "MVK_MISSING_CATEGORY_VALUE"
private def missingInternal : String := "MVK_MISSING_INTERNAL_VALUE"
private def categoryDuplicate : String := "MVK_CATEGORY_VALUE_DUPLICATE"
private def internalDuplicate : String := "MVK_INTERNAL_VALUES_DUPLICATE"
private def invalidCharacter : String := "MVK_ENUM_VALUE_WITH_INVALID_CHARACTER"
private def supplementary : String := "codeless:supplementary-character"
private def repeated : String := "codeless:repeated-value"

private def valueEntry (labels : List (String × String)) (value : String) : Json :=
  Json.mkObj ([("value", .str value)] ++ (labels.lookup value).toList.map fun text =>
    ("label", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", .str text)]]))

private def enumerationBody (row : Row) : Json :=
  Json.mkObj ([("values", Json.arr (row.values.map (valueEntry row.labels)).toArray)] ++
    if row.categories.isEmpty then []
    else [("categories", Json.arr (row.categories.map fun (name, tokens) =>
      Json.mkObj [("name", .str name), ("values", toJson tokens)]).toArray)])

private def field (name typeName : String) (body : Json := Json.mkObj []) : Json :=
  Json.mkObj [("type", "Field"), ("name", .str name),
    ("Field", Json.mkObj [("fieldType", Json.mkObj [("type", .str typeName), (typeName, body)])])]

private def source (row : Row) : Json :=
  checkedEntryFrame <| Json.mkObj [("content", Json.mkObj [
    ("modelConfig", Json.mkObj (if row.restricted then
      [("supportedCharacters", toJson row.charset)] else [])),
    ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[Json.mkObj [
      ("type", "Group"), ("name", "Store"),
      ("Group", Json.mkObj [("repeatability", toJson (1 : Nat)),
        ("elements", Json.arr #[field "Reference" "StringType",
          field "Tier" "EnumerationType" (enumerationBody row)])])]])])])]

private def tier : List String := ["Store", "Tier"]

private def recorded (row : Row) : Option (List EnumerationDeclarationNotification) :=
  (readModel (source row)).toOption.map fun dm => dm.enumerationNotifications.flatMap (·.2)

/-- The retained observation for one row: the ordered classes, and the field's fate. A model with no
class keeps `Tier` and records nothing; any class refuses exactly `Tier` and records its path. -/
private def matchesObservation (row : Row) : Bool :=
  match readModel (source row) with
  | .error _ => false
  | .ok dm =>
      let classes := (dm.enumerationNotifications.flatMap (·.2)).map (·.observedLabel)
      let keepsTier := dm.flat.fields.any (·.name == "Tier")
      classes == row.expected &&
        (if row.expected.isEmpty then
          keepsTier && dm.refusals.isEmpty && dm.enumerationNotifications.isEmpty
        else
          !keepsTier && dm.refusals.map (·.1) == [tier] &&
            dm.enumerationNotifications.map (·.1) == [tier])

private def disagreeing (rows : List (String × Row)) : List String :=
  (rows.filter fun (_, row) => !matchesObservation row).map (·.1)

/-- Arity direction and multiplicity, the duplicate classes, and their one-per-category product. The mixed rows, `surplus-category-with-duplicate` and `surplus-shortfall-surplus` above all, fix the shortfall block before the surplus block. -/
private def arityAndDuplicateRows : List (String × Row) := [
  ("control", { values := ["AA", "BB", "CC"], categories := [("Band", ["X", "Y", "Z"]), ("Segment", ["P", "Q", "R"])], expected := [] }),
  ("one-category-short-two", { values := ["AA", "BB", "CC"], categories := [("Band", ["X"])], expected := [missingCategory, missingCategory] }),
  ("two-categories-short-two", { values := ["AA", "BB", "CC"], categories := [("Band", ["X"]), ("Segment", ["P"])], expected := [missingCategory, missingCategory, missingCategory, missingCategory] }),
  ("empty-category", { values := ["AA", "BB", "CC"], categories := [("Band", [])], expected := [missingCategory, missingCategory, missingCategory] }),
  ("repeated-unclassified-value", { values := ["AA", "BB", "BB"], categories := [("Band", ["X"])], expected := [missingCategory, categoryDuplicate, internalDuplicate, repeated] }),
  ("repeated-unclassified-two-categories", { values := ["AA", "BB", "BB"], categories := [("Band", ["X"]), ("Segment", ["P"])], expected := [missingCategory, missingCategory, categoryDuplicate, categoryDuplicate, internalDuplicate, repeated] }),
  ("surplus-repeated-token", { values := ["AA"], categories := [("Band", ["X", "Y", "Y"])], expected := [missingInternal] }),
  ("surplus-distinct-tokens", { values := ["AA"], categories := [("Band", ["X", "Y", "Z"])], expected := [missingInternal, missingInternal] }),
  ("repeated-category-tokens", { values := ["AA", "BB"], categories := [("Band", ["X", "X"])], expected := [] }),
  ("duplicate-without-category", { values := ["AA", "AA"], expected := [internalDuplicate, repeated] }),
  ("triple-duplicate", { values := ["AA", "AA", "AA"], categories := [("Band", ["X", "Y", "Z"])], expected := [categoryDuplicate, internalDuplicate, repeated] }),
  ("two-duplicates-two-categories", { values := ["AA", "AA", "BB", "BB"], categories := [("Band", ["X", "Y"]), ("Segment", ["P", "Q"])], expected := [missingCategory, missingCategory, categoryDuplicate, categoryDuplicate, categoryDuplicate, categoryDuplicate, internalDuplicate, internalDuplicate, repeated, repeated] }),
  ("duplicate-mapped-earlier", { values := ["AA", "AA"], categories := [("Band", ["X"])], expected := [missingCategory, categoryDuplicate, internalDuplicate, repeated] }),
  ("surplus-token-repeats-mapped", { values := ["AA"], categories := [("Band", ["X", "X"])], expected := [missingInternal] }),
  ("duplicate-unmapped-then-mapped", { values := ["BB", "AA", "BB"], categories := [("Band", ["X", "Y"])], expected := [missingCategory, categoryDuplicate, internalDuplicate, repeated] }),
  ("surplus-two-repeat-one", { values := ["AA", "BB"], categories := [("Band", ["X", "Y", "Z", "Z", "W"])], expected := [missingInternal, missingInternal] }),
  ("surplus-category-with-duplicate", { values := ["AA", "AA"], categories := [("Band", ["X", "Y", "Z"]), ("Segment", ["P"])], expected := [missingCategory, missingInternal, categoryDuplicate, categoryDuplicate, internalDuplicate, repeated] }),
  ("shortfall-then-surplus", { values := ["AA", "BB"], categories := [("Band", ["P"]), ("Segment", ["X", "Y", "Z"])], expected := [missingCategory, missingInternal] }),
  ("surplus-shortfall-surplus", { values := ["AA", "BB"], categories := [("Band", ["X", "Y", "Z"]), ("Segment", ["P"]), ("Extra", ["Q", "R", "S"])], expected := [missingCategory, missingInternal, missingInternal] }),
  ("shortfall-surplus-shortfall", { values := ["AA", "BB"], categories := [("Band", ["P"]), ("Segment", ["X", "Y", "Z"]), ("Extra", ["Q"])], expected := [missingCategory, missingCategory, missingInternal] })]

example : disagreeing arityAndDuplicateRows = [] := by native_decide

/-- Restricted-charset rejection is one class per UTF-16 unit, repeated units collapse, and the default
charset admits what a restricted one rejects. -/
private def restrictedCharsetRows : List (String × Row) := [
  ("bad-distinct-characters", { values := ["AA", "pq"], restricted := true, expected := [invalidCharacter, invalidCharacter] }),
  ("bad-repeated-character", { values := ["AA", "pp"], restricted := true, expected := [invalidCharacter] }),
  -- The October 21 letter's §2.4: the charset check reads a value untrimmed, unlike the text laws.
  ("padded-value-untrimmed", { values := ["PLUS ", "BB"], restricted := true, expected := [invalidCharacter] }),
  ("bad-repeated-value", { values := ["AA", "pq", "pq"], restricted := true, expected := [invalidCharacter, invalidCharacter, internalDuplicate, repeated] }),
  ("bad-before-short-category", { values := ["AA", "pq"], categories := [("Band", ["X"])], restricted := true, expected := [invalidCharacter, invalidCharacter, missingCategory] }),
  ("bad-charset-control", { values := ["AA", "BB"], categories := [("Band", ["X", "Y"])], restricted := true, expected := [] }),
  ("lowercase-default-charset", { values := ["AA", "pq"], expected := [] }),
  ("bad-supplementary-character", { values := ["AA", "p😀"], restricted := true, expected := [invalidCharacter, invalidCharacter, invalidCharacter, supplementary] }),
  -- A range spanning the low-surrogate block admits a supplementary scalar's low unit, and two scalars
  -- sharing a high unit in one value collapse to one class: rows of the retained capture
  -- `declaration-report-r1-supplement-2026-10-13`, which starts from this capture's model.
  ("e-bmp-range-supp", { values := ["😀", "BB"], restricted := true, charset := [" -\uFFFD"], expected := [invalidCharacter, supplementary] }),
  ("e-bmp-range-two-supp", { values := ["😀😁", "BB"], restricted := true, charset := [" -\uFFFD"], expected := [invalidCharacter, supplementary] }),
  -- Two values sharing that high unit keep one class each, since the collapse is per value and unit:
  -- peer `CheckerEnumDeclarationStreamAgreementTest` with U+1F6D2 and U+1F6CD, a12-dmkits `058750e73`.
  ("peer-two-values-shared-high-unit", { values := ["🛒", "🛍"], restricted := true, charset := [" -\uFFFD"], expected := [invalidCharacter, invalidCharacter, supplementary] }),
  ("e-az-supp", { values := ["A😀", "BB"], restricted := true, expected := [invalidCharacter, invalidCharacter, supplementary] })]

example : disagreeing restrictedCharsetRows = [] := by native_decide

/-- A supplementary-plane scalar in a stored token or a display text raises one codeless class,
suppresses the per-value classes for that value, and still counts as a repeat. -/
private def supplementaryRows : List (String × Row) := [
  ("signs-value-under-full-category", { values := ["AA", "😀"], categories := [("Band", ["X", "Y"])], expected := [supplementary] }),
  ("signs-value-duplicated", { values := ["😀", "😀"], categories := [("Band", ["X", "Y"])], expected := [supplementary, repeated] }),
  ("signs-value-first", { values := ["😀", "AA"], categories := [("Band", ["X"])], expected := [supplementary, missingCategory] }),
  ("two-supplementary-values", { values := ["😀", "🙂"], expected := [supplementary] }),
  ("supplementary-in-label", { values := ["AA"], labels := [("AA", "x😀")], expected := [supplementary] }),
  ("bmp-non-ascii-default", { values := ["Ä", "é"], expected := [] }),
  ("supplementary-twice-one-value", { values := ["😀😀"], expected := [supplementary] }),
  ("signs-with-arity-and-duplicate", { values := ["AA", "AA", "😀"], categories := [("Band", ["X"])], expected := [supplementary, missingCategory, categoryDuplicate, internalDuplicate, repeated] }),
  ("signs-with-restricted-arity-duplicate", { values := ["pq", "pq", "😀"], categories := [("Band", ["X"])], restricted := true, expected := [invalidCharacter, invalidCharacter, invalidCharacter, invalidCharacter, supplementary, missingCategory, categoryDuplicate, internalDuplicate, repeated] }),
  ("signs-value-duplicated-unclassified", { values := ["AA", "😀", "😀"], categories := [("Band", ["X"])], expected := [supplementary, repeated] })]

example : disagreeing supplementaryRows = [] := by native_decide

/-! The payloads behind the retained class sequences. -/

private def rowNamed (id : String) (rows : List (String × Row)) : Option Row :=
  (rows.find? (·.1 == id)).map (·.2)

private def payloads (id : String) : Option (List EnumerationDeclarationNotification) :=
  (rowNamed id (arityAndDuplicateRows ++ restrictedCharsetRows ++ supplementaryRows)).bind recorded

example : payloads "two-categories-short-two" = some [
    .missingCategoryValue "Band" "BB", .missingCategoryValue "Band" "CC",
    .missingCategoryValue "Segment" "BB", .missingCategoryValue "Segment" "CC"] := by
  native_decide

example : payloads "surplus-two-repeat-one" = some [
    .missingInternalValue "Band" "Z", .missingInternalValue "Band" "W"] := by
  native_decide

example : payloads "bad-supplementary-character" = some [
    .invalidCharacter "p😀" 0x70, .invalidCharacter "p😀" 0xD83D,
    .invalidCharacter "p😀" 0xDE00, .supplementaryCharacter] := by
  native_decide

example : payloads "duplicate-unmapped-then-mapped" = some [
    .missingCategoryValue "Band" "BB", .categoryValueDuplicate "BB" "Band",
    .internalValuesDuplicate "BB", .repeatedValue "BB"] := by
  native_decide

end A12Kernel.Dm.EnumerationDeclarationNotificationLocks
