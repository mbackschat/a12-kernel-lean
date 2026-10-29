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
    report "" (host (bin := " ")) = unbuilt ∧ report "" (host (bin := "\u2003")) = unbuilt ∧
    report "" (host (code := "\t")) = unbuilt ∧
    report "" (host (binElements := [field "Slot", rule "\n"])) = unbuilt ∧
    report "" (host (binElements := [field "Slot", rule "\n" true, field " " (deleted := true)])) = [] ∧
    (report "/Order/Part/" (host (bin := "\u00A0"))).head? = some "MVK_PATH_INVALID@\u00A0" := by
  native_decide

/-! ## §2.17: a count below one -/

/-- §2.17's host: `/Policy` holds `Coverages` (`Amount` and `Riders` holding `Code`) and `Holder`. -/
private def policy (root coverages riders : Option Json) (beside : List Json := []) : Json :=
  let count := fun (value : Option Json) => value.toList.map (("repeatability", ·))
  model [group "Policy" [group "Coverages" ([field "Amount", group "Riders" [field "Code"] (count riders)] ++ beside)
    (count coverages), field "Holder"] (count root)]

/-- A rule and a computation declared in `Coverages`, the elements the October 24a handback injected. -/
private def coverageRules : List Json :=
  [Json.mkObj [("type", "Rule"), ("name", "AmountSet"), ("Rule", Json.mkObj [("errorEntityRelPath", "../Amount"),
      ("errorCode", "AMOUNT_SET"), ("errorCondition", "FieldFilled(Amount)"), ("severity", "ERROR")])],
   Json.mkObj [("type", "Computation"), ("name", "NoteFromAmount"), ("Computation", Json.mkObj [
      ("computedFieldRelPath", "../Holder"), ("computationAlternatives", Json.arr #[Json.mkObj [("operation", "[Amount]")]])])]]

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

/- A rule and a computation beneath the refused group draw nothing: the walk visits groups and fields
   only ([inbound](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-24a), 13 rows). -/
example :
    report "/Policy/" (policy none (some (toJson (0 : Int))) (some (toJson (3 : Int))) coverageRules) =
      report "/Policy/" (policy none (some (toJson (0 : Int))) (some (toJson (3 : Int)))) := by
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
    report "/Order/" (order (sorts ["Sku", "Sku", "Sk-u"]) [field "Sku", field "Sk-u"]) =
      ["MVK_SORT_FIELD_DUPLICATE@Items", s!"{F}@Items", "MVK_PATH_INVALID@Items/Sk-u", s!"{F}@Items/Sk-u"] ∧
    report "" (order (index " Sku")) = unbuilt := by
  native_decide

/-- An Enumeration field `Kind` whose invalid-value message is `text`. -/
private def kind (text : String) : Json :=
  field "Kind" "EnumerationType" [("values", Json.arr #[Json.mkObj [("value", "A")]]),
    ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", Json.str text)]])]

/- A field's error text is judged inside the entity walk in source, so its control-character class
   withholds the ordering gates as a refused path does; this carrier is source-read, not measured. -/
example :
    report "/Order/" (order (index "Sku") [skipsValidation "Sku", kind "a\tb"]) = ["INVALID_CHARACTERS@Items/Kind"] ∧
    report "/Order/" (order (index "Sku") [skipsValidation "Sku", kind "ab"]) =
      ["MVK_INDEX_FIELD_NO_VALUE_VALIDATION@Items/Sku"] := by
  native_decide

/- §2.11: a group named with the `xml` prefix in any case draws its class at itself and at an
   underscore group beneath it, which also draws the underscore class; below a root the class falls
   at every group beneath, as peer [KF558](../../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf558)'s
   ancestor law states. -/
example :
    ["xmlCode", "XMLCode", "xml"].all (fun part => report "/Order/" (host (part := part) (bin := "_Bin")) ==
      [s!"MVK_NAME_STARTS_WITH_XML@{part}", s!"NAME_STARTS_WITH_UNDERSCORE_AND_WRONG_PATTERN@{part}/_Bin",
        s!"MVK_NAME_STARTS_WITH_XML@{part}/_Bin"]) ∧
    report "/" (host (root := "xmlOrder") (part := "_Part")) =
      ["MVK_NAME_STARTS_WITH_XML@xmlOrder", "NAME_STARTS_WITH_UNDERSCORE_AND_WRONG_PATTERN@xmlOrder/_Part",
        "MVK_NAME_STARTS_WITH_XML@xmlOrder/_Part", "MVK_NAME_STARTS_WITH_XML@xmlOrder/_Part/Bin"] := by
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
    range (some "dd.MM.yyyy") (some ".") = [P, S] ∧ range (some "dd.MM.yyyy") (some "\u00A0") = [P, S] ∧
    range (some "dd.MM.yyyy") (some " - ") = [P] ∧ range (some "yyyy-MM-dd") none = [] ∧
    range (some "yyyy-MM-dd") (some "🛒") = ["codeless:supplementary-character"] := by
  native_decide

/- A Java-blank format fails the Date constructor the three kinds share, an empty fragment format the
   build too, unless the variant filter deletes the field; a no-break space is an invalid format. -/
example :
    ["DateType", "TimeType", "DateTimeType"].all (fun kind =>
      ["", " ", "\t", "\n", "\u2003"].all (fun format => typed kind [("format", Json.str format)] == unbuilt) &&
      typed kind [("format", "\u00A0")] == ["codeless:date-format-invalid"] &&
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
    enumeration [("o\t\u00A0", none), ("B", none)] = ["MVK_INTERNAL_VALUE_INVALID"] ∧
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

/-- The verdict on a computation `Fill` of `../label` in `/Order/part/Bin`, `Bin` keyed by `label`
when `keyed`: `admitted`, the refusal's class, or its construct when it has none. -/
private def computed (part label : String) (operation := "\"bin\"") (keyed := false) : String :=
  let bin := if keyed then [("repeatability", toJson (3 : Int)), ("indexFieldName", Json.str label)] else []
  let json := model [group "Order" [group part [group "Bin" [field "Slot", field label] bin]]]
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

/- The classes before the path stage are drawn beneath a refused group name as anywhere: the
   operation's unknown entity, and the index stage, which a String computation reaches as a Number one
   does, so either replaces the path class. -/
example :
    computed "Co.de" "Label" "[Nope]" = "MVK_INVALID_ENTITY" ∧
    computed "Co.de" "Label" (keyed := true) = "MVK_ERROR_INDEX_AS_CALCULATED_FIELD" ∧
    computed "Part" "Label" (keyed := true) = "MVK_ERROR_INDEX_AS_CALCULATED_FIELD" ∧
    computed "Part" "Label" "[Nope]" = "MVK_INVALID_ENTITY" := by
  native_decide

/- The index stage follows the condition read in source, so a condition class the generated rule
   draws precedes it even where the computation's own carrier stops at the index field first. -/
example :
    computed "Part" "Label" "[Nope]" (keyed := true) = "MVK_INVALID_ENTITY" ∧
    computed "Part" "Label" "AddDays(Slot, 1)" (keyed := true) = "MVK_NO_DATE" ∧
    computed "Part" "Label" "AddDays(Slot, 1)" = "MVK_NO_DATE" := by
  native_decide

/-- The class a rule in `/Order/part/Bin` reporting on `Label` draws for `condition`, `admitted`, or
its construct when the refusal has no class. -/
private def ruled (part condition : String) (label := "Label") (entity := s!"../{label}") : String :=
  match readModel (model [group "Order" [group part [group "Bin" [field "Slot", field label]]]]) with
  | .error reason => s!"unread {reason}"
  | .ok dm =>
      let checked : DmRule := {
        group := ["Order", part, "Bin"]
        name := "R"
        errorCode := "R"
        errorEntityRelPath := entity
        condition
        severity := "ERROR" }
      match checkValidationRule dm .english checked with
      | .ok _ => "admitted"
      | .error refusal => refusal.kernelClass?.getD refusal.construct

/- A rule's error entity is resolved by the model's own segments, which the condition lexer never
   reads, so a refused group name above it changes no condition class. -/
example :
    ruled "Co-de" "[Label] == \"x\"" = "admitted" ∧ ruled "Co.de" "FieldFilled(Label)" = "admitted" ∧
    ruled "Co-de" "[Nope] == \"x\"" = "MVK_INVALID_ENTITY" ∧
    ruled "Co-de" "[Nope] == \"x\"" = ruled "Part" "[Nope] == \"x\"" := by
  native_decide

/- §2.13: a field or group name holding a character the lexer has no terminal for draws no lexer
   class as the error entity, while the same name as a computed target does. The letter states only
   the absent class, so these rows assert nothing about the class the unreferenced target draws. -/
example :
    ruled "Part" "FieldFilled(Slot)" (label := "La\u00A0bel") ≠ "MVK_LEXER_STANDARD_ERROR" ∧
    ruled "B\u00A0in" "FieldFilled(Slot)" (entity := "../../../B\u00A0in") ≠ "MVK_LEXER_STANDARD_ERROR" ∧
    computed "Part" "La\u00A0bel" = "MVK_LEXER_STANDARD_ERROR" := by
  native_decide

private def formatMember : String → String
  | "DateFragmentType" => "formatOfFragment"
  | _ => "format"

private def refusedFormats : List String :=
  ["HH:mm", "MM.yyyy", "yyyy/MM", "dd.MM", "YYYY-MM-DD", "DD.MM.YYYY", "yy", "HH.mm.ss", "hh:mm:ss a",
    "yyyy-MM-dd HH:mm", "yyyy-MM-dd'T'HH:mm:ss.SSS", "QQQ"]

private def admittedFormats : List String :=
  ["yyyy-MM-dd", "dd.MM.yyyy", "yyyyMMdd", "yyyy", "yyyy-MM", "yyyyMM", "MM", "MM-dd", "MMdd", "ddMM", "dd.MM.",
    "HH:mm:ss", "yyyy-MM-dd'T'HH:mm:ss"]

private def timeDefinition (id : String) : Json :=
  Json.mkObj [("id", Json.str id), ("name", Json.str id), ("fieldType", Json.mkObj [("type", "TimeType"),
    ("TimeType", Json.mkObj [("format", "HH:mm")])])]

private def definedField (deleted : Bool) : Json :=
  Json.mkObj [("type", "Field"), ("name", "F"), ("Field", Json.mkObj ([("fieldType", Json.mkObj [
    ("type", "TypeDefType"), ("TypeDefType", Json.mkObj [("typeDefinitionId", "T")])])] ++
    if deleted then [("variantFilter", only)] else []))]

private def defined (fields definitions : List Json) : List String :=
  let json := model [group "Policy" fields]
  report "/Policy/" (json.setObjVal! "content"
    ((json.getObjValD "content").setObjVal! "typeDefinitions" (Json.arr definitions.toArray)))

/- A refused format draws the codeless date-format class on a kept Date, Time, DateTime or fragment
   field and nothing on a deleted one, `QQQ` included; an admitted format draws nothing either way. A type definition is judged only through a kept field that
   uses it, and two definitions sharing an id leave no model (peer KF648 and KF647,
   [inbound 2026-10-29](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-29)). -/
example :
    ["DateType", "TimeType", "DateTimeType", "DateFragmentType"].all (fun kind =>
      refusedFormats.all (fun format =>
        typed kind [(formatMember kind, Json.str format)] == ["codeless:date-format-invalid"] &&
        typed kind [(formatMember kind, Json.str format)] (deleted := true) == []) &&
      admittedFormats.all fun format =>
        typed kind [(formatMember kind, Json.str format)] == [] &&
        typed kind [(formatMember kind, Json.str format)] (deleted := true) == []) ∧
    defined [field "Other"] [timeDefinition "T"] = [] ∧
    defined [definedField false] [timeDefinition "T"] = ["codeless:date-format-invalid@F"] ∧
    defined [definedField true] [timeDefinition "T"] = [] ∧
    defined [field "Other"] [timeDefinition "T", timeDefinition "T"] = unbuilt ∧
    defined [field "Other"] [timeDefinition "", timeDefinition ""] = unbuilt := by
  native_decide

end A12Kernel.Dm.DeclarationWalkLocks
