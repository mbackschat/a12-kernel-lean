import A12Kernel.Reference.Dm.FieldTypeDeclarationRead
import A12Kernel.Reference.Dm.ComputationCheck

/-! # Whole-model rows of the October 21 letter

The element walk's path, count, ordering and blank-name laws, the field-type laws the letter corrected,
and the computed-path class, each locked on the letter's own host shape
([October 21 letter](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), §2.1, §2.3,
§2.4, §2.7, §2.8, §2.11, §2.12, §2.16, §2.17). A row reads `label@path` pairs from
`fieldTypeDeclarationNotifications`, the path shortened by its host prefix; `unbuilt` is the one
unbuilt-model label. -/

namespace A12Kernel.Dm.DeclarationWalkLocks

open Lean A12Kernel

private def only : Json := Json.mkObj [("filterType", "ONLY"), ("variants", Json.arr #["Other"])]

private def field (name : String) (typeName := "StringType") (body : List (String × Json) := [])
    (deleted := false) : Json :=
  Json.mkObj [("type", "Field"), ("name", Json.str name), ("Field", Json.mkObj ([("fieldType",
    Json.mkObj ([("type", Json.str typeName)] ++ if body.isEmpty then [] else [(typeName, Json.mkObj body)]))] ++
    if deleted then [("variantFilter", only)] else []))]

private def group (name : String) (elements : List Json) (body : List (String × Json) := []) : Json :=
  Json.mkObj [("type", "Group"), ("name", Json.str name),
    ("Group", Json.mkObj (body ++ [("elements", Json.arr elements.toArray)]))]

private def rule (name : String) (deleted := false) : Json :=
  Json.mkObj [("type", "Rule"), ("name", Json.str name), ("Rule", Json.mkObj (([
    ("errorEntityRelPath", "../Slot"), ("errorCode", "C"), ("errorCondition", "FieldFilled(Slot)"),
    ("severity", "ERROR")] : List (String × Json)) ++ if deleted then [("variantFilter", only)] else []))]

private def model (roots : List Json) : Json :=
  Json.mkObj [("header", Json.mkObj [("locales", Json.arr #[Json.mkObj [("code", "en_US")]])]),
    ("content", Json.mkObj [("modelConfig", Json.mkObj [("conditionLanguage", Json.mkObj [("code", "en_US")])]),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr roots.toArray)])])]

private def unbuilt : List String := ["codeless:model-not-built@"]

private def report (prefix_ : String) (json : Json) : List String :=
  match fieldTypeDeclarationNotifications json (fun _ => .compiled fun _ => true) with
  | .ok reported => reported.map fun (label, at_) =>
      s!"{label}@{if at_.startsWith prefix_ then (at_.drop prefix_.length).toString else at_}"
  | .error reason => [s!"unreadable {reason}"]

private def G : String := "codeless:group-name-shape"

/-! ## §2.7 and §2.11: the group-path law and blank names -/

/-- §2.7's host, trimmed: `/Order` holds `Reference` and group `part`, which holds `Code` and group
`bin`, which holds `Slot` and the rule `Check`. -/
private def host (root := "Order") (part := "Part") (bin := "Bin") (code := "Code")
    (binElements : List Json := [field "Slot", rule "Check"]) : Json :=
  model [group root [field "Reference", group part [field code, group bin binElements]]]

/- A refused nested name draws its path class at the group and the group-path notification at the
   group and every element below it, a rule included; a padded name passes its own path and its
   fields', since the joined path is trimmed whole, while every path through it fails; a refused
   root fails every path below it; a field named like a refused group keeps its own shape beside the
   path's, without a second path class. -/
example :
    report "/Order/" (host (part := "Codeé")) =
      ["MVK_PATH_INVALID@Codeé", s!"{G}@Codeé", s!"{G}@Codeé/Code", s!"{G}@Codeé/Bin",
        s!"{G}@Codeé/Bin/Slot", s!"{G}@Codeé/Bin/Check"] ∧
    report "/Order/" (host (part := "Code\t")) =
      ["MVK_PATH_INVALID@Code\t", s!"{G}@Code\t/Bin", s!"{G}@Code\t/Bin/Slot", s!"{G}@Code\t/Bin/Check"] ∧
    report "/" (host (root := " Code")) =
      ["MVK_PATH_INVALID@ Code", s!"{G}@ Code/Reference", s!"{G}@ Code/Part", s!"{G}@ Code/Part/Code",
        s!"{G}@ Code/Part/Bin", s!"{G}@ Code/Part/Bin/Slot", s!"{G}@ Code/Part/Bin/Check"] ∧
    report "/Order/" (host (part := "Codeé") (code := "Codeé")) =
      ["MVK_PATH_INVALID@Codeé", s!"{G}@Codeé", "codeless:field-name-shape@Codeé/Codeé", s!"{G}@Codeé/Codeé",
        s!"{G}@Codeé/Bin", s!"{G}@Codeé/Bin/Slot", s!"{G}@Codeé/Bin/Check"] ∧
    report "/Order/" (host (part := "Coäde")) = [] := by
  native_decide

/- A refused path still reaches no element the variant filter deletes, and a supplementary scalar
   draws the repertoire notification in place of the path's. -/
example :
    report "/Order/" (host (part := "Codeé") (binElements := [field "Slot", rule "Check" true])) =
      ["MVK_PATH_INVALID@Codeé", s!"{G}@Codeé", s!"{G}@Codeé/Code", s!"{G}@Codeé/Bin", s!"{G}@Codeé/Bin/Slot"] ∧
    (report "/Order/" (host (part := "Gr😀"))).all (fun entry => entry == "MVK_PATH_INVALID@Gr😀" ||
      entry.startsWith "codeless:supplementary-character@") := by
  native_decide

/- A Java-blank group, field or rule name fails the build, a deleted field or rule only after the
   variant filter, while a no-break space is an ordinary refused name. -/
example :
    report "" (host (bin := " ")) = unbuilt ∧ report "" (host (bin := " ")) = unbuilt ∧
    report "" (host (code := "\t")) = unbuilt ∧
    report "" (host (binElements := [field "Slot", rule "\n"])) = unbuilt ∧
    report "" (host (binElements := [field "Slot", rule "\n" true, field " " (deleted := true)])) = [] ∧
    (report "/Order/Part/" (host (bin := " "))).head? = some "MVK_PATH_INVALID@ " := by
  native_decide

/-! ## §2.17: a count below one -/

/-- §2.17's host: `/Policy` holds `Coverages` (`Amount` and `Riders` holding `Code`) and `Holder`. -/
private def policy (root coverages riders : Option Json) : Json :=
  let count := fun (value : Option Json) => value.toList.map (("repeatability", ·))
  model [group "Policy" [group "Coverages" [field "Amount", group "Riders" [field "Code"] (count riders)]
    (count coverages), field "Holder"] (count root)]

private def M : String := "MVK_MAX_VALUES_INVALID"

/- The class falls at the group and once at every group and field beneath it, never outside; the group
   alone draws the sentence of the count's sign, a present `null` counting as not positive. -/
example :
    report "/Policy/" (policy none (some (toJson (0 : Int))) (some (toJson (3 : Int)))) =
      [s!"{M}@Coverages", "codeless:count-not-positive@Coverages", s!"{M}@Coverages/Amount",
        s!"{M}@Coverages/Riders", s!"{M}@Coverages/Riders/Code"] ∧
    report "/Policy/" (policy none (some .null) (some (toJson (3 : Int)))) =
      report "/Policy/" (policy none (some (toJson (0 : Int))) (some (toJson (3 : Int)))) ∧
    report "/Policy/" (policy none (some (toJson (4 : Int))) (some (toJson (-7 : Int)))) =
      [s!"{M}@Coverages/Riders", "codeless:count-signed@Coverages/Riders", s!"{M}@Coverages/Riders/Code"] ∧
    report "/Policy/" (policy none (some (toJson (0 : Int))) (some (toJson (0 : Int)))) =
      [s!"{M}@Coverages", "codeless:count-not-positive@Coverages", s!"{M}@Coverages/Amount",
        s!"{M}@Coverages/Riders", "codeless:count-not-positive@Coverages/Riders", s!"{M}@Coverages/Riders/Code"] ∧
    (report "/Policy" (policy (some (toJson (-1 : Int))) (some (toJson (4 : Int))) (some (toJson (3 : Int))))).contains
      s!"{M}@/Holder" ∧
    report "" (policy none (some (toJson (4 : Int))) (some (toJson (3 : Int)))) = [] := by
  native_decide

/-! ## §2.16: ordering members -/

/-- §2.16's host: `/Order` holds `Channel` and `Archive`, and the repeatable `Items` its `fields`
under `members`. -/
private def order (members : List (String × Json)) (fields : List Json := [field "Sku", field "Note"])
    (archive : List (String × Json) := []) : Json :=
  model [group "Order" [field "Channel", group "Archive" [field "Old"] archive,
    group "Items" fields (("repeatability", toJson (5 : Int)) :: members)]]

private def index (name : String) : List (String × Json) := [("indexFieldName", Json.str name)]

private def sorts (names : List String) : List (String × Json) :=
  [("sortFields", Json.arr (names.map fun name => Json.mkObj [("name", Json.str name)]).toArray)]

private def skipsValidation (name : String) : Json :=
  field name (body := [("noValueValidation", true), ("lineBreaksPermitted", true)])

private def F : String := "codeless:field-name-shape"

/- The member draws the field-name sentence once at the group for the short name it keeps, judged by
   the field-name shape and not by its digit or colon classes; the ordering gates wait on a walk that
   refused nothing, while the duplicate class skips only a refused name. -/
example :
    report "/Order/" (order (index "../Items/Sku")) = [] ∧
    report "/Order/" (order (index "Sk-u") [field "Sk-u"]) =
      [s!"{F}@Items", "MVK_PATH_INVALID@Items/Sk-u", s!"{F}@Items/Sk-u"] ∧
    report "/Order/" (order (index "1Sku") [field "1Sku"]) =
      ["MVK_PATH_INVALID@Items/1Sku", "MVK_NAME_STARTS_WITH_DIGIT_A12_DV@Items/1Sku"] ∧
    report "/Order/" (order (index "Sk-u") [field "Sku", field "Sk-u" (deleted := true)]) =
      ["MVK_INVALID_INDEX_FIELD@Items", s!"{F}@Items"] ∧
    report "/Order/" (order (index "Sku") [skipsValidation "Sku"]) =
      ["MVK_INDEX_FIELD_NO_VALUE_VALIDATION@Items/Sku"] ∧
    report "/Order/" (order (index "Sku") [skipsValidation "Sku", field "No-te"]) =
      ["MVK_PATH_INVALID@Items/No-te", s!"{F}@Items/No-te"] ∧
    report "/Order/" (order (index "../Channel") [field "Sku"] [("repeatability", toJson (0 : Int))]) =
      [s!"{M}@Archive", "codeless:count-not-positive@Archive", s!"{M}@Archive/Old"] ∧
    report "/Order/" (order (sorts ["Sku", "Sku"]) [field "Sku", field "No-te"]) =
      ["MVK_SORT_FIELD_DUPLICATE@Items", "MVK_PATH_INVALID@Items/No-te", s!"{F}@Items/No-te"] ∧
    report "/Order/" (order (sorts ["Sk-u", "Sk-u"]) [field "Sku", field "Sk-u"]) =
      [s!"{F}@Items", "MVK_PATH_INVALID@Items/Sk-u", s!"{F}@Items/Sk-u"] ∧
    report "/Order/" (order (sorts ["Sku", "Note", "Qty", "Sk-u"])
        [field "Sku", field "Note", field "Qty", field "Sk-u"]) =
      ["codeless:sort-list-capacity@Items", "MVK_PATH_INVALID@Items/Sk-u", s!"{F}@Items/Sk-u"] ∧
    report "" (order (index " Sku")) = unbuilt := by
  native_decide

/-! ## §2.1, §2.3, §2.4, §2.8, §2.12: field types -/

/-- The labels one field `/Policy/F` of `typeName` and `body` draws, or the unbuilt label. -/
private def typed (typeName : String) (body : List (String × Json)) (deleted := false) : List String :=
  (report "/Policy/F" (model [group "Policy" [field "F" typeName body deleted]])).map fun entry =>
    if unbuilt.contains entry then entry else entry.dropRight 1

private def range (format separator : Option String) : List String :=
  typed "DateRangeType" (format.toList.map (fun text => ("format", Json.str text)) ++
    separator.toList.map fun text => ("rangeSeparator", Json.str text))

private def P : String := "codeless:date-range-format-invalid"
private def S : String := "codeless:date-range-separator-invalid"

/- A range is judged on its composed format: a composite that trims to nothing is the missing class
   alone, an omitted separator being `/`; the separator notification trims its value while the pair
   allowlist does not; a supplementary scalar draws the repertoire notification alone. -/
example :
    range (some "") (some "") = ["MVK_FORMAT_DATE_RANGE_MISSING"] ∧
    range (some " ") (some "\t") = ["MVK_FORMAT_DATE_RANGE_MISSING"] ∧
    range (some "") none = [P] ∧ range none none = [P] ∧
    range (some "dd.MM.yyyy") (some ".") = [P, S] ∧ range (some "dd.MM.yyyy") (some " ") = [P, S] ∧
    range (some "dd.MM.yyyy") (some " - ") = [P] ∧ range (some "yyyy-MM-dd") none = [] ∧
    range (some "yyyy-MM-dd") (some "🛒") = ["codeless:supplementary-character"] := by
  native_decide

/- A Java-blank format fails the Date constructor the three kinds share, an empty fragment format the
   build too, unless the variant filter deletes the field; a no-break space is an invalid format. -/
example :
    ["DateType", "TimeType", "DateTimeType"].all (fun kind =>
      ["", " ", "\t", "\n", " "].all (fun format => typed kind [("format", Json.str format)] == unbuilt) &&
      typed kind [("format", " ")] == ["codeless:date-format-invalid"] &&
      typed kind [("format", "")] (deleted := true) == []) ∧
    typed "DateFragmentType" [("formatOfFragment", "")] = unbuilt := by
  native_decide

private def number (maximum : String) (scale : Int) : List String :=
  typed "NumberType" [("minValue", toJson (1 : Int)), ("maxValue", (Json.parse maximum).toOption.getD .null),
    ("maxFractionalDigits", toJson scale)]

/- The inversion is not judged beside a bound whose printed form fails its own check: `-0.4` prints
   `-0` at no fractional digit, and seventeen printed digits are too many, while the printed `-1` of
   `-0.5` and a scale that prints `-0.4` compare. -/
example :
    number "-0.4" 0 = [] ∧ number "0.30000000000000004" 1 = [] ∧
    number "-0.5" 0 = ["MVK_MIN_VALUE_BIGGER_THAN_MAX_VALUE"] ∧
    number "-0.4" 1 = ["MVK_MIN_VALUE_BIGGER_THAN_MAX_VALUE"] := by
  native_decide

private def enumeration (values : List (String × Option String)) (categories : List (List String) := [])
    (sValue : Option String := none) : List String :=
  typed "EnumerationType" ([("values", Json.arr (values.map fun (value, label) => Json.mkObj ([("value", Json.str value)] ++
      label.toList.map fun text => ("label", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", Json.str text)]]))).toArray)] ++
    (if categories.isEmpty then [] else [("categories", Json.arr (categories.map fun tokens =>
      Json.mkObj [("name", "Kind"), ("values", toJson tokens)]).toArray)]) ++
    sValue.toList.map fun text => ("sValue", Json.str text))

/- The text laws read each text trimmed, and none names a text holding a supplementary scalar; the
   duplicate and arity blocks read trimmed values, while the repeated-value notification compares them
   as written. -/
example :
    enumeration [("o\t", none), ("B", none)] = [] ∧ enumeration [("o\n", none), ("B", none)] = [] ∧
    enumeration [("o\t ", none), ("B", none)] = ["MVK_INTERNAL_VALUE_INVALID"] ∧
    enumeration [("o\tk🛒", none), ("B", none)] = ["codeless:supplementary-character"] ∧
    enumeration [("A", some "Tier"), ("B", some "Tier ")] = ["MVK_DISPLAY_VALUES_DUPLICATE"] ∧
    enumeration [("A", none), ("B", none)] [["ST|🛒", "X"]] = ["codeless:supplementary-character"] ∧
    enumeration [("A", none), ("B", none)] [] (some "o🛒") = ["codeless:supplementary-character"] ∧
    enumeration [("BASIC", none), ("BASIC\t", none)] = ["MVK_INTERNAL_VALUES_DUPLICATE"] ∧
    enumeration [("ST", none), ("BASIC", none), ("BASIC ", none)] [["X"]] =
      ["MVK_MISSING_CATEGORY_VALUE", "MVK_CATEGORY_VALUE_DUPLICATE", "MVK_INTERNAL_VALUES_DUPLICATE"] ∧
    enumeration [("A", none)] [["X", "HI", "HI "]] = ["MVK_MISSING_INTERNAL_VALUE"] := by
  native_decide

/-! ## §2.11: the computed path -/

/-- The verdict on a computation `Fill` of `../label` in `/Order/part/Bin`: `admitted`, the refusal's
class, or its construct when it has none. -/
private def computed (part label : String) (operation := "\"bin\"") : String :=
  let json := model [group "Order" [group part [group "Bin" [field "Slot", field label]]]]
  match readModel json with
  | .error reason => s!"unread {reason}"
  | .ok dm =>
      let computation : DmComputation := {
        group := ["Order", part, "Bin"]
        name := "Fill"
        targetRelPath := "../" ++ label
        commonPrecondition := some "FieldFilled(Slot)"
        alternatives := [{ precondition := none, operation }]
        errorCodesToSuppress := [] }
      match checkComputation dm .english computation with
      | .ok _ => "admitted"
      | .error refusal => refusal.kernelClass?.getD refusal.construct

/- A dot or colon anywhere on the computed field's full path is judged after the computation's other
   checks: a dotted group or field name draws it, a computed field's own dotted name is still read as
   the target, and a hyphen does not; a no-break space keeps the lexer's class. -/
example :
    computed "Co.de" "Label" = "MVK_ERROR_INVALID_FIELDNAME" ∧
    computed "Part" "La.bel" = "MVK_ERROR_INVALID_FIELDNAME" ∧
    computed "Part" "Ns:Label" = "MVK_ERROR_INVALID_FIELDNAME" ∧
    computed "Co-de" "Label" = "admitted" ∧ computed "Part" "Label" = "admitted" ∧
    computed "Part" "La\u00A0bel" = "MVK_LEXER_STANDARD_ERROR" := by
  native_decide

end A12Kernel.Dm.DeclarationWalkLocks
