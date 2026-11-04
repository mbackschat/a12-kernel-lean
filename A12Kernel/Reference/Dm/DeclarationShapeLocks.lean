import Lean.Data.Json
import A12Kernel.Reference.Dm.ComputationCheck
import A12Kernel.Reference.Dm.EntryFrameFixture
import A12Kernel.Reference.Dm.FieldTypeDeclarationRead
import A12Kernel.Reference.Dm.LoneSurrogate
import A12Kernel.Reference.Dm.ModelConsistencyRead

/-! # What kernel 31.1.1 makes of an Enumeration's members, shared element ids, the type-definition order, an empty range pair and a Number bound

Six settled readings of kernel 31.1.1, each locked on the carrier its peer oracle names. A row is one model
with one declaration varied, and asserts what the readers draw together: the coded classes the declaration
walk and the consistency check report, with their multiplicity and no class beyond them, or no model on all
three. The model reader must keep its field exactly when no class is drawn; a row where the three readers
part is `split`, which no row expects.

* An Enumeration declaring no values, two categories whose names read as one key, or a category whose `name`
  is `null` leaves no model. A category named by nothing, by the empty text or by Java-blank text is one
  `MVK_NAME_MISSING` at its field and takes no part in the pairing, and a category token that is absent,
  empty, blank or `null` is no token (a number or a boolean binds as its text, an object or an array leaves no
  model).
* A value entry with no `value` member is a value with no token that keeps its position, and a label in any
  locale, declared or not, makes a value carry labels.
* Every element sharing an id is stated by the basic check, at its own path.
* The basic check walks a model's own type definitions as declared unless the model has something to expand,
  and by id in UTF-16 code-unit order when it has.
* A range declaring the empty pair reads as the absent one.
* A Number bound is judged by no magnitude its fractional digits allow, and a bound written as text or as a
  number token of more than 1000 characters leaves no model.

Locked: the a12-dmkits tests each cluster names, at 1124b523f, kernel 31.1.1.
-/

namespace A12Kernel.Dm.DeclarationShapeLocks

open Lean A12Kernel

/-! ## The carrier -/

private def literal (text : String) : Json := (Json.parse text).toOption.getD (Json.str s!"unparsable {text}")

private def named (kind id name : String) (body : List (String × Json)) : Json :=
  Json.mkObj [("type", .str kind), ("id", .str id), ("name", .str name), (kind, Json.mkObj body)]

private def string : Json := Json.mkObj [("type", "StringType")]

private def fieldIn (id name : String) (type : Json) : Json := named "Field" id name [("fieldType", type)]

private def typed (name body : String) : Json :=
  Json.mkObj [("type", .str name), (name, literal body)]

private def typedBody (name : String) (body : Json) : Json := Json.mkObj [("type", .str name), (name, body)]

/-- A model whose one root group holds `elements`, with the given type definitions and header references. -/
private structure Carrier where
  rootId : String := "/Policy"
  rootName : String := "Policy"
  elements : List Json := [fieldIn "/Policy/Ref" "Ref" string]
  rootMembers : List (String × Json) := []
  typeDefinitions : List Json := []
  /-- The header's `modelReferences`, written only when given; an entry stands for a library to import. -/
  references : Option (List Json) := none

private def Carrier.json (carrier : Carrier) : Json :=
  let root := named "Group" carrier.rootId carrier.rootName
    (carrier.rootMembers ++ [("elements", Json.arr carrier.elements.toArray)])
  checkedEntryFrame <| Json.mkObj [
    ("header", Json.mkObj (carrier.references.toList.map fun entries => ("modelReferences", Json.arr entries.toArray))),
    ("content", Json.mkObj ([("modelConfig", Json.mkObj [("conditionLanguage", Json.mkObj [("code", "en_US")])]),
      ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[root])])] ++
      (if carrier.typeDefinitions.isEmpty then [] else
        [("typeDefinitions", Json.arr carrier.typeDefinitions.toArray)])))]

/-! ## What the readers draw -/

private def compile : StringPatternCompiler := fun _ => .compiled fun _ => true

private def walkOf (json : Json) : Option (List (String × String)) :=
  match fieldTypeDeclarationNotifications json compile with
  | .ok labels => if labels.any (·.1 == modelNotBuiltLabel) then none else some labels
  | .error _ => none

private def consistencyOf (json : Json) : Option (List (String × String)) :=
  match checkModelConsistency json with
  | .ok (.checked notifications) =>
      some (notifications.map fun notification => (notification.kind.observedLabel, "/" ++ "/".intercalate notification.path))
  | _ => none

/-- The model reader's refusals, none when it leaves no model. -/
private def builtOf (json : Json) : Option DmModel := (readModelWithAdmission json).toOption

/-- What the readers make of a model together; `split` is a model some readers build and others do not, or a
model the model reader refuses without a class beside it. -/
private inductive Verdict where
  | noModel
  | classes (codes : List String)
  | split (detail : String)
  deriving BEq, Repr

private def cls (codes : List String) : Verdict := .classes (codes.mergeSort (· ≤ ·))

private def admitted : Verdict := .classes []

private def coded (labels : List String) : List String :=
  (labels.filter fun label => !label.startsWith "codeless:").mergeSort (· ≤ ·)

private def verdictOf (json : Json) : Verdict :=
  match walkOf json, consistencyOf json, builtOf json with
  | none, none, none => .noModel
  | some walk, some consistency, some model =>
      let classes := coded ((walk ++ consistency).map (·.1))
      if model.refusals.isEmpty == classes.isEmpty then .classes classes
      else .split s!"the model reader refuses {model.refusals.map (·.2)} beside {classes}"
  | walk, consistency, built =>
      .split s!"walk {walk.isSome}, consistency {consistency.isSome}, model reader {built.isSome}"

/-- The labels of the rows whose verdict is not the expected one, with what they drew. -/
private def failures (rows : List (String × Json × Verdict)) : List (String × Verdict) :=
  rows.filterMap fun (label, json, expected) =>
    let actual := verdictOf json
    if actual == expected then none else some (label, actual)

private def nameMissing : String := "MVK_NAME_MISSING"
private def missingCategory : String := "MVK_MISSING_CATEGORY_VALUE"
private def missingInternal : String := "MVK_MISSING_INTERNAL_VALUE"
private def categoryDuplicate : String := "MVK_CATEGORY_VALUE_DUPLICATE"
private def internalDuplicate : String := "MVK_INTERNAL_VALUES_DUPLICATE"

/-! ## An Enumeration's values and its tables

Locked: a12-dmkits `EnumDeclarationShapeLawsTest` at 1124b523f, kernel 31.1.1. An Enumeration with nothing to
enumerate is no model, a table member no stored Enumeration declares is read past, and categories keyed by
one name are no model. A repeated value draws the category class once per category, and only the value's
own list is asked to be unique, never a category's tokens. -/

private def tierModel (body : String) : Json :=
  ({ elements := [fieldIn "/Policy/Ref" "Ref" string, fieldIn "/Policy/Tier" "Tier" (typed "EnumerationType" body)] } :
    Carrier).json

private def two : String := "\"values\":[{\"value\":\"BASIC\"},{\"value\":\"PLUS\"}]"

private def shapeRows : List (String × Json × Verdict) :=
  let row (label body : String) (verdict : Verdict) := (label, tierModel s!"\{{body}}", verdict)
  [row "two declared values, the control" two admitted,
   row "an empty value list" "\"values\":[]" .noModel,
   row "no values member at all" "\"alphabeticalSorting\":false" .noModel,
   row "an sValue naming a declared value" (two ++ ",\"sValue\":\"BASIC\"") admitted,
   row "an sValue naming no declared value" (two ++ ",\"sValue\":\"NOPE\"") (cls ["MVK_S_VALUE_INVALID"]),
   row "a blank sValue" (two ++ ",\"sValue\":\"\"") admitted,
   row "a table name beside the inline values" (two ++ ",\"tableName\":\"TIERS\"") admitted,
   row "a table and column name beside them" (two ++ ",\"tableName\":\"TIERS\",\"columnName\":\"CODE\"") admitted,
   row "a table name and no values" "\"tableName\":\"TIERS\"" .noModel,
   row "two categories sharing a name"
     (two ++ ",\"categories\":[{\"name\":\"Band\",\"values\":[\"LOW\",\"HIGH\"]},{\"name\":\"Band\",\"values\":[\"A\",\"B\"]}]")
     .noModel,
   row "a repeated value with a category declared"
     "\"values\":[{\"value\":\"BASIC\"},{\"value\":\"BASIC\"}],\"categories\":[{\"name\":\"Band\",\"values\":[\"LOW\",\"HIGH\"]}]"
     (cls [categoryDuplicate, internalDuplicate]),
   row "the same repeated value with no category" "\"values\":[{\"value\":\"BASIC\"},{\"value\":\"BASIC\"}]"
     (cls [internalDuplicate]),
   row "the same repeated value with two categories"
     ("\"values\":[{\"value\":\"BASIC\"},{\"value\":\"BASIC\"}],\"categories\":[{\"name\":\"Band\",\"values\":" ++
       "[\"LOW\",\"HIGH\"]},{\"name\":\"Zone\",\"values\":[\"A\",\"B\"]}]")
     (cls [categoryDuplicate, categoryDuplicate, internalDuplicate]),
   row "a repeated category token over distinct values"
     (two ++ ",\"categories\":[{\"name\":\"Band\",\"values\":[\"LOW\",\"LOW\"]}]") admitted,
   row "a category holding fewer tokens than the enum has values"
     (two ++ ",\"categories\":[{\"name\":\"Band\",\"values\":[\"LOW\"]}]") (cls [missingCategory]),
   row "a value carrying a character XML cannot hold" "\"values\":[{\"value\":\"BASIC\"},{\"value\":\"A<B\"}]" admitted,
   row "a category token carrying one"
     (two ++ ",\"categories\":[{\"name\":\"Band\",\"values\":[\"LOW\",\"A<B\"]}]") admitted,
   row "a value carrying a control character" "\"values\":[{\"value\":\"BASIC\"},{\"value\":\"A\\u0001B\"}]" admitted]

example : failures shapeRows = [] := by native_decide

/-! ## A category token that is no plain string

Locked: a12-dmkits `CheckerCategoryTokenAgreementTest` at 1124b523f, kernel 31.1.1 (peer KF660), on values
`GOLD` and `SILVER` under one category `Band`. A token is paired with the value at its position, and one that
is absent from its position, empty, blank as Java's `isBlank` (an em space included) or `null` leaves that
value unclassified, once for each. Past the values a blank token is admitted and a filled one is a surplus. A
number or a boolean binds as its text; an object or an array is no string, so the model is not built. -/

private def tokenModel (tokens : String) : Json :=
  tierModel s!"\{\"values\":[\{\"value\":\"GOLD\"},\{\"value\":\"SILVER\"}],\"categories\":[\{\"name\":\"Band\",\"values\":{tokens}}]}"

private def tokenRows : List (String × Json × Verdict) :=
  let row (label tokens : String) (verdict : Verdict) := (label, tokenModel tokens, verdict)
  [row "two plain tokens, the control" "[\"HIGH\",\"LOW\"]" admitted,
   row "two empty" "[\"\",\"\"]" (cls [missingCategory, missingCategory]),
   row "one empty" "[\"HIGH\",\"\"]" (cls [missingCategory]),
   row "one blank" "[\" \",\"LOW\"]" (cls [missingCategory]),
   row "one em space" "[\"\\u2003\",\"LOW\"]" (cls [missingCategory]),
   row "one null" "[null,\"LOW\"]" (cls [missingCategory]),
   row "a number and a boolean" "[1,true]" admitted,
   row "a blank token, one token short" "[\" \"]" (cls [missingCategory, missingCategory]),
   row "a blank token past the values" "[\"HIGH\",\"LOW\",\" \"]" admitted,
   row "a plain token past the values, the surplus control" "[\"HIGH\",\"LOW\",\"MID\"]" (cls [missingInternal]),
   row "object entries" "[{\"value\":\"HIGH\"},{\"value\":\"LOW\"}]" .noModel,
   row "one object entry" "[{\"value\":\"HIGH\"},\"LOW\"]" .noModel,
   row "an array token" "[[\"HIGH\"],\"LOW\"]" .noModel]

example : failures tokenRows = [] := by native_decide

/-- The values the shortfall names, in order, as the model reader records them. -/
private def unclassified (json : Json) : Option (List String) :=
  (builtOf json).map fun model => (model.enumerationNotifications.flatMap (·.2)).filterMap fun
    | .missingCategoryValue _ value => some value
    | _ => none

example :
    unclassified (tokenModel "[\"\",\"\"]") = some ["GOLD", "SILVER"] ∧
    unclassified (tokenModel "[\" \"]") = some ["GOLD", "SILVER"] ∧
    unclassified (tokenModel "[null,\"LOW\"]") = some ["GOLD"] ∧
    unclassified (tokenModel "[\"HIGH\",\"\"]") = some ["SILVER"] := by
  native_decide

/-! ## A category without a name

Locked: a12-dmkits `CheckerEmptyMemberAgreementTest` at 1124b523f, kernel 31.1.1 (peer KF367's unreachable
carrier, now measured). A category whose `name` is absent, empty or blank is stated once for its field and
pairs with nothing, so its own shortfall draws no class while the field's named categories are still judged.
The empty name and an absent one are the one key `null`, so two such categories collide; two blank names that
differ as text do not. An explicit `null` name is no model. An absent token list is the empty one. -/

private def nameModel (categories : String) : Json :=
  tierModel s!"\{\"values\":[\{\"value\":\"GOLD\"},\{\"value\":\"SILVER\"}],\"categories\":{categories}}"

private def nameRows : List (String × Json × Verdict) :=
  let row (label categories : String) (verdict : Verdict) := (label, nameModel categories, verdict)
  [row "an empty name" "[{\"name\":\"\",\"values\":[\"HIGH\",\"LOW\"]}]" (cls [nameMissing]),
   row "an absent name" "[{\"values\":[\"HIGH\",\"LOW\"]}]" (cls [nameMissing]),
   row "a blank name" "[{\"name\":\" \",\"values\":[\"HIGH\",\"LOW\"]}]" (cls [nameMissing]),
   row "an em space name" "[{\"name\":\"\\u2003\",\"values\":[\"HIGH\",\"LOW\"]}]" (cls [nameMissing]),
   row "two blank names that differ"
     "[{\"name\":\" \",\"values\":[\"HIGH\",\"LOW\"]},{\"name\":\"\\u2003\",\"values\":[\"A\",\"B\"]}]" (cls [nameMissing]),
   row "a blank name, one token short" "[{\"name\":\" \",\"values\":[\"HIGH\"]}]" (cls [nameMissing]),
   row "a named category one token short, the control" "[{\"name\":\"Band\",\"values\":[\"HIGH\"]}]"
     (cls [missingCategory]),
   row "a nameless category beside a named one a token short"
     "[{\"values\":[\"HIGH\",\"LOW\"]},{\"name\":\"Band\",\"values\":[\"HIGH\"]}]" (cls [nameMissing, missingCategory]),
   row "an absent name and an empty one" "[{\"values\":[\"HIGH\",\"LOW\"]},{\"name\":\"\",\"values\":[\"A\",\"B\"]}]" .noModel,
   row "an empty name twice" "[{\"name\":\"\",\"values\":[\"HIGH\",\"LOW\"]},{\"name\":\"\",\"values\":[\"A\",\"B\"]}]" .noModel,
   row "one blank name written twice"
     "[{\"name\":\" \",\"values\":[\"HIGH\",\"LOW\"]},{\"name\":\" \",\"values\":[\"A\",\"B\"]}]" .noModel,
   row "a null name" "[{\"name\":null,\"values\":[\"HIGH\",\"LOW\"]}]" .noModel,
   row "no token list" "[{\"name\":\"Band\"}]" (cls [missingCategory, missingCategory])]

example : failures nameRows = [] := by native_decide

/-! ## Value entries without a token, and a label in any locale

Locked: a12-dmkits `CheckerReaderBindingAgreementTest`, `CheckerDeclarationAdmissionAgreementTest` and
`EnumCategoryWireShapeLawsTest` at 1124b523f, kernel 31.1.1 (peer KF654, KF655). A row asserts every class the
declaration walk and the basic check draw together, sorted and codeless ones included, and for a token-less
body whether the model reader keeps the field. The peer compares class sets, so each row's multiplicity is derived, unmeasured on 31.1.1: once per field for `MVK_INTERNAL_VALUE_MISSING` and the codeless repeated-value class. The one row the Kernel admits with a token-less entry is a model
the reader refuses all the same: a stored token the entry does not declare has no account in a document
(the runtime meaning of such an entry is unmeasured), so `EnumerationDeclaration.validate` leaves no checked
declaration for it.

The label rows assert the model reader too, except the two where it parts from the Kernel: it reads labels as the
declaration validator does, blind to the model's declared locales, so it keeps a model whose every label is for an
undeclared locale and refuses one whose label repeats only there. -/

private def valuesMissing : String := "MVK_INTERNAL_VALUES_MISSING"
private def valueMissing : String := "MVK_INTERNAL_VALUE_MISSING"
private def displayValues : String := "MVK_INTERNAL_VALUES_AND_DISPLAY_VALUES"
private def countOfValues : String := "MVK_COUNT_OF_VALUES_INVALID"
private def displayDuplicate : String := "MVK_DISPLAY_VALUES_DUPLICATE"
private def repeatedValue : String := "codeless:repeated-value"

/-- One `values` entry written as JSON text: the token under `value`, or under the misspelled member `valu`
for a token-less entry, and its labels as `(locale, text)` pairs. -/
private def entryText (token : Option String) (labels : List (String × String) := []) : String :=
  let member := match token with
    | some text => s!"\"value\":\"{text}\""
    | none => "\"valu\":\"X\""
  let label := if labels.isEmpty then "" else
    ",\"label\":[" ++ ",".intercalate (labels.map fun (locale, text) =>
      s!"\{\"locale\":\"{locale}\",\"text\":\"{text}\"}") ++ "]"
  s!"\{{member}{label}}"

private def categoryText (name : String) (tokens : List String) : String :=
  s!"\{\"name\":\"{name}\",\"values\":[" ++ ",".intercalate (tokens.map fun token => s!"\"{token}\"") ++ "]}"

/-- A `Tier` Enumeration over `entries`, with the categories `(name, tokens)` beside them. -/
private def entriesModel (entries : List String) (categories : List (String × List String) := []) : Json :=
  let categoryMember := if categories.isEmpty then "" else
    ",\"categories\":[" ++ ",".intercalate (categories.map fun (name, tokens) => categoryText name tokens) ++ "]"
  tierModel (s!"\{\"values\":[" ++ ",".intercalate entries ++ s!"]{categoryMember}}")

/-- Every class the walk and the basic check draw, sorted, or none when either leaves no model. -/
private def drawnClasses (json : Json) : Option (List String) :=
  match walkOf json, consistencyOf json with
  | some walk, some consistency => some (((walk ++ consistency).map (·.1)).mergeSort (· ≤ ·))
  | _, _ => none

/-- Whether the model reader keeps the `Tier` field, none when it reads no model. -/
private def readerKeepsTier (json : Json) : Option Bool :=
  (builtOf json).map fun model => model.flat.fields.any (·.name == "Tier")

private def entryFailures (rows : List (String × Json × List String × Option Bool)) :
    List (String × Option (List String) × Option Bool) :=
  rows.filterMap fun (label, json, expected, keeps) =>
    if drawnClasses json == some (expected.mergeSort (· ≤ ·)) && keeps.all (readerKeepsTier json == some ·) then none
    else some (label, drawnClasses json, readerKeepsTier json)

private def tokenlessRows : List (String × Json × List String × Option Bool) :=
  let tokenless := entryText none
  let open_ := entryText (some "OPEN")
  [("no entry carries a token", entriesModel [tokenless, tokenless], [valuesMissing, repeatedValue], some false),
   ("no entry carries a token, both labelled",
    entriesModel [entryText none [("en_US", "Open")], entryText none [("en_US", "Closed")]],
    [valuesMissing, displayValues, valueMissing, repeatedValue], some false),
   ("one entry without a token, beside a category",
    entriesModel [tokenless] [("State", ["OPEN"])], [valuesMissing, missingInternal], some false),
   ("a value entry's member misspelled, beside a category",
    entriesModel ["{\"sValue\":\"BASIC\"}", "{\"sValue\":\"PLUS\"}"] [("Band", ["STANDARD"])],
    [valuesMissing, missingInternal, repeatedValue], some false),
   ("one of two entries without a token, unlabelled", entriesModel [open_, tokenless], [], some false),
   ("two of three entries without a token", entriesModel [open_, tokenless, tokenless], [repeatedValue], some false),
   ("one of two entries without a token, both labelled",
    entriesModel [entryText (some "OPEN") [("en_US", "Open")], entryText none [("en_US", "Closed")]],
    [valueMissing, displayValues], some false),
   ("a token-less entry between two, beside a two-token category",
    entriesModel [open_, tokenless, entryText (some "CLOSED")] [("State", ["A", "B"])],
    [missingCategory, missingInternal], some false),
   ("a token-less entry first, beside a one-token category",
    entriesModel [tokenless, open_] [("State", ["A"])], [missingCategory, missingInternal], some false)]

example : entryFailures tokenlessRows = [] := by native_decide

private def labelRows : List (String × Json × List String × Option Bool) :=
  let labelled (token : String) (labels : List (String × String)) := entryText (some token) labels
  let plus := entryText (some "PLUS")
  [("one value labelled for an undeclared locale only, beside an unlabelled one",
    entriesModel [labelled "BASIC" [("fr_FR", "Base")], plus], [countOfValues, displayValues], some false),
   ("one value blank-labelled for an undeclared locale",
    entriesModel [labelled "BASIC" [("fr_FR", "")], plus], [countOfValues, displayValues], some false),
   ("declared beside undeclared, against undeclared alone",
    entriesModel [labelled "BASIC" [("en_US", "Basic"), ("fr_FR", "Base")], labelled "PLUS" [("fr_FR", "Plus")]],
    [displayValues], some false),
   ("every value labelled for an undeclared locale only",
    entriesModel [labelled "BASIC" [("fr_FR", "Base")], labelled "PLUS" [("fr_FR", "Plus")]], [displayValues], none),
   ("one value labelled for the declared locale, the control",
    entriesModel [labelled "BASIC" [("en_US", "Basic")], plus], [countOfValues], some false),
   ("a label repeated only in an undeclared locale",
    entriesModel [labelled "BASIC" [("en_US", "Basic"), ("fr_FR", "Same")],
      labelled "PLUS" [("en_US", "Plus"), ("fr_FR", "Same")]], [], none),
   ("a label repeated in the declared locale, the control",
    entriesModel [labelled "BASIC" [("en_US", "Same"), ("fr_FR", "Base")],
      labelled "PLUS" [("en_US", "Same"), ("fr_FR", "Plus")]], [displayDuplicate], some false)]

example : entryFailures labelRows = [] := by native_decide

/-! ## Elements sharing an id

Locked: a12-dmkits `CheckerDuplicateIdAgreementTest` at 1124b523f, kernel 31.1.1 (peer KF661), the rows that
involve no mount: a mount's own rows belong to the host that expands it. The basic check states every element
sharing an id once at its own path, whatever the kinds, and a type definition shares nothing. A blank-named
sharer the converter drops still counts, and the rule check goes on beside it: a rule naming no field is
refused and one naming a sharer is judged as if nothing were wrong. -/

private def shared : String := "codeless:id-not-unique"
private def emptyId : String := "codeless:id-empty"
private def missingName : String := "codeless:element-name-missing"

/-- `Policy` holding `Ref`, `Code`, `Note`, a repeatable `Items` of `Label` and the rule `RefCheck` reporting at
`entity`, each element's id replaced where the row names it (`Items/Label` for the nested field, `Policy` for the
root), with `extra` elements after them. -/
private def policy (ids : List (String × String)) (rule : String := "FieldFilled(Ref)") (entity : String := "../Ref")
    (extra : List Json := []) (blankNote : Bool := false) (typeDefinitions : List Json := []) : Json :=
  let id (key default : String) := (ids.lookup key).getD default
  ({ rootId := id "Policy" "/Policy"
     elements := [fieldIn (id "Ref" "/Policy/Ref") "Ref" string, fieldIn (id "Code" "/Policy/Code") "Code" string,
       fieldIn (id "Note" "/Policy/Note") (if blankNote then " " else "Note") string,
       named "Group" (id "Items" "/Policy/Items") "Items" [("repeatability", toJson (3 : Nat)),
         ("elements", Json.arr #[fieldIn (id "Items/Label" "/Policy/Items/Label") "Label" string])],
       named "Rule" (id "RefCheck" "/Policy/RefCheck") "RefCheck" [("errorEntityRelPath", .str entity),
         ("errorCode", "REF"), ("errorCondition", .str rule), ("severity", "ERROR"),
         ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]])]] ++ extra
     typeDefinitions } : Carrier).json

private def computation (id : String) : Json :=
  named "Computation" id "NoteCalc" [("computedFieldRelPath", "../Note"),
    ("computationAlternatives", Json.arr #[Json.mkObj [("operation", "\"x\"")]]),
    ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]])]

/-- The classes the model's rules and computations draw as `class@path`, none when the flat validation
refuses the model, which is no class. -/
private def staticListing (model : DmModel) : List String :=
  if !model.flat.validate.isOk then [] else
  (model.rules.filterMap fun rule => (match checkValidationRule model .english rule with
    | .ok _ => none
    | .error refusal => refusal.kernelClass?).map fun class_ =>
      s!"{class_}@/{"/".intercalate (rule.group ++ [rule.name])}") ++
  (model.computations.filterMap fun computation => (match checkComputation model .english computation with
    | .ok _ => none
    | .error refusal => refusal.kernelClass?).map fun class_ =>
      s!"{class_}@/{"/".intercalate (computation.group ++ [computation.name])}")

/-- Every notification and refusal of the model as `class@path`, sorted: the declaration walk's and the basic
check's, then the rules'; `UNBUILT` when no reader builds one and `SPLIT` when they disagree. -/
private def listingOf (json : Json) : List String :=
  match walkOf json, consistencyOf json, builtOf json with
  | none, none, none => ["UNBUILT"]
  | some walk, some consistency, some model =>
      ((walk ++ consistency).map (fun entry => s!"{entry.1}@{entry.2}") ++ staticListing model).mergeSort (· ≤ ·)
  | _, _, _ => ["SPLIT"]

private def listing (entries : List (String × String)) : List String :=
  (entries.map fun (label, path) => s!"{label}@{path}").mergeSort (· ≤ ·)

/-- Every row but one is the peer's carrier as measured; the rule naming the second sharer is pinned
separately below. -/
private def idRows : List (String × Json × List String) :=
  let both := [(shared, "/Policy/Code"), (shared, "/Policy/Note")]
  [("the base, the control", policy [], []),
   ("two fields", policy [("Code", "x"), ("Note", "x")], listing both),
   ("three fields", policy [("Ref", "x"), ("Code", "x"), ("Note", "x")],
    listing [(shared, "/Policy/Ref"), (shared, "/Policy/Code"), (shared, "/Policy/Note")]),
   ("two pairs", policy [("Ref", "a"), ("Code", "a"), ("Note", "b"), ("Items", "b")],
    listing [(shared, "/Policy/Ref"), (shared, "/Policy/Code"), (shared, "/Policy/Note"), (shared, "/Policy/Items")]),
   ("a field and a rule", policy [("Code", "x"), ("RefCheck", "x")], listing [(shared, "/Policy/Code"), (shared, "/Policy/RefCheck")]),
   ("a field and a group", policy [("Code", "x"), ("Items", "x")], listing [(shared, "/Policy/Code"), (shared, "/Policy/Items")]),
   ("a field and a nested field", policy [("Code", "x"), ("Items/Label", "x")],
    listing [(shared, "/Policy/Code"), (shared, "/Policy/Items/Label")]),
   ("the root group and a field", policy [("Code", "x"), ("Policy", "x")], listing [(shared, "/Policy"), (shared, "/Policy/Code")]),
   ("a field and a computation", policy [("Code", "x")] (extra := [computation "x"]),
    listing [(shared, "/Policy/Code"), (shared, "/Policy/NoteCalc")]),
   ("a field taking another's id", policy [("Note", "/Policy/Code")], listing both),
   ("two fields with an empty id", policy [("Code", ""), ("Note", "")],
    listing (both ++ [(emptyId, "/Policy/Code"), (emptyId, "/Policy/Note")])),
   ("two fields, the second named with a space", policy [("Code", "x"), ("Note", "x")] (blankNote := true),
    listing [(shared, "/Policy/Code"), (shared, "/Policy/ "), (missingName, "/Policy")]),
   ("a field and a type definition", policy [("Code", "x")]
      (typeDefinitions := [Json.mkObj [("id", "x"), ("name", "CodeType"), ("fieldType", string)]]), []),
   ("two fields, beside a rule naming no field", policy [("Code", "x"), ("Note", "x")] (rule := "FieldFilled(Nowhere)"),
    listing (both ++ [("MVK_INVALID_ENTITY", "/Policy/RefCheck")]))]

private def listingFailures (rows : List (String × Json × List String)) : List (String × List String) :=
  rows.filterMap fun (label, json, expected) =>
    let actual := listingOf json
    if actual == expected then none else some (label, actual)

example : listingFailures idRows = [] := by native_decide

/- Recorded deviation, not a law. The peer's rule naming the second sharer keeps its error field at `Ref`
   beside the condition `FieldFilled(Note)`, and the Kernel's check states the two id sentences alone, while
   this account's rule check adds `MVK_ERROR_FIELD_NOT_REFERENCED`, a class the Kernel draws on other measured
   carriers. Which carriers the Kernel's model check asks it on is the open discriminator, SG9 in
   `docs/gaps/paths-and-groups.md`. -/
example :
    listingOf (policy [("Code", "x"), ("Note", "x")] (rule := "FieldFilled(Note)")) =
      listing [(shared, "/Policy/Code"), (shared, "/Policy/Note"),
        ("MVK_ERROR_FIELD_NOT_REFERENCED", "/Policy/RefCheck")] := by
  native_decide

/-! ## Type definitions in declared order

Locked: a12-dmkits `CheckerBasicSentenceOrderAgreementTest` at 1124b523f, kernel 31.1.1, and the source reading
of its Letter E (§3a, §4). The basic check states a model's own type definitions as declared, each one's empty
id and then its empty name, ahead of the elements, and sorted by id in UTF-16 code-unit order once the model has
something to expand: a header entry naming a model to import, or a group carrying an `includeConfig` that is
not `null`. A header entry here stands for a library whose definitions the host would add, the only part of
expansion these rows need; a row that needs a definition of the library itself, or an expansion failure,
belongs to the host and is not locked. That the flag is a non-empty list of entries and a mount that is not
`null` is the source reading, which no row measures. -/

private def importLibrary : List Json := [Json.mkObj [("purpose", "typeDefinitions"), ("reference", "library")]]

/-- The basic check's notifications in the order it states them, as `class@path`, when every reader builds the
model. -/
private def stated (json : Json) : Option (List String) :=
  if (walkOf json).isNone || (builtOf json).isNone then none else
  (checkModelConsistency json).toOption.bind fun
    | .checked notifications =>
        some (notifications.map fun notification => s!"{notification.kind.observedLabel}@/{"/".intercalate notification.path}")
    | .notBuilt .. => none

private def nameless : String := "codeless:typedef-name-empty"
private def idless : String := "codeless:id-empty"
private def unnamed : String := "codeless:element-name-empty"

private def definition (id : String) (name : String := "") : Json :=
  Json.mkObj [("id", .str id), ("name", .str name), ("fieldType", typed "StringType" "{}")]

private def sentences (ids : List String) : List String := ids.map fun id => s!"{nameless}@/{id}"

/-- Each definition is judged by its own empty id and then its empty name, so the id sentence of the definition
named `Alpha` comes between its neighbours' name sentences, and the field with no name follows them all. -/
private def orderRows : List (String × Json × List String) :=
  let ids := ["deductible", "Prämie", "Coverage", "Überschuss"]
  let carrier (definitions : List String) (references : Option (List Json) := none)
      (members : List (String × Json) := []) : Json :=
    ({ typeDefinitions := definitions.map (definition ·), references, rootMembers := members } : Carrier).json
  [("declared, nothing to expand", carrier ids, sentences ids),
   ("the same four, importing a library", carrier ids importLibrary, sentences ["Coverage", "Prämie", "deductible", "Überschuss"]),
   ("declared Gamma, Beta, Delta, nothing to expand", carrier ["Gamma", "Beta", "Delta"], sentences ["Gamma", "Beta", "Delta"]),
   ("declared Gamma, Beta, Delta, importing a library", carrier ["Gamma", "Beta", "Delta"] importLibrary,
    sentences ["Beta", "Delta", "Gamma"]),
   ("the import list written empty", carrier ["Gamma", "Beta"] (some []), sentences ["Gamma", "Beta"]),
   ("a mount on the root group", carrier ["Gamma", "Beta"] (members := [("includeConfig", Json.mkObj [("reference", "library")])]),
    sentences ["Beta", "Gamma"]),
   ("a mount written null", carrier ["Gamma", "Beta"] (members := [("includeConfig", .null)]), sentences ["Gamma", "Beta"]),
   ("one defect each, a field with no name, nothing to expand",
    ({ typeDefinitions := [definition "Beta", definition "" "Alpha", definition "Gamma"],
       elements := [fieldIn "/Policy/Ref" "" string] } : Carrier).json,
    [s!"{nameless}@/Beta", s!"{idless}@/Alpha", s!"{nameless}@/Gamma", s!"{unnamed}@/Policy/"])]

private def orderFailures : List (String × Option (List String)) :=
  orderRows.filterMap fun (label, json, expected) =>
    if stated json == some expected then none else some (label, stated json)

example : orderFailures = [] := by native_decide

/-- Two definitions of one id, the empty one included, leave no model in every reader, as the build that keys
the definitions by id fails before any sentence is stated. -/
example :
    ["", "Beta"].all (fun id =>
      verdictOf ({ typeDefinitions := [definition id "Alpha", definition id "Delta"] } : Carrier).json == .noModel) = true := by
  native_decide

/-! ## An empty range pair

Locked: a12-dmkits `DateRangePairAdmissionLawsTest` and `TemporalDeclarationWithoutFormatLawsTest` at
1124b523f, kernel 31.1.1, the rows the declaration reads on the model as authored. A range's declaration is
judged on the format the Kernel composes from its members, an empty member composing as an absent one, so the
pair of two empty members is the range-format sentence where kernel 30.8.1 drew the missing-format class, and a
blank pair, which is not empty, still draws it. The allowlist asks the pair as written: `yyyy-MM-dd` and
`dd.MM.yyyy` with an empty separator draw the range-format sentence on the authored model, measured raw by
a12-dmkits `ExpandCopyEmptyMemberLawsTest`. Month with an empty separator is admitted here as kernel 30.8.1
admitted it as written; the peer's 31.1.1 row for it runs after the expansion, so the raw row is unmeasured on
31.1.1. A Date format written empty or as one space leaves no model as written (measured raw); the tab and em
space on a Date, and every empty or blank Time and DateTime format, are derived from that row and unmeasured
as written on 31.1.1, the peer's rows for them running after the expansion. The rows the peer observes only
after the expansion drops an empty member belong to the host. -/

private def labelsOf (type : Json) : List String :=
  match fieldTypeDeclarationNotifications ({ elements := [fieldIn "/Policy/Ref" "Ref" type] } : Carrier).json compile with
  | .ok labels => labels.map (·.1)
  | .error reason => [s!"unreadable {reason}"]

private def range (format separator : Option String) : List String :=
  labelsOf (typedBody "DateRangeType" (Json.mkObj (format.toList.map (fun text => ("format", Json.str text)) ++
    separator.toList.map fun text => ("rangeSeparator", Json.str text))))

private def pairInvalid : String := "codeless:date-range-format-invalid"
private def formatMissing : String := "MVK_FORMAT_DATE_RANGE_MISSING"

example :
    range (some "yyyy-MM-dd") (some "/") = [] ∧ range (some "dd.MM.yyyy") (some "-") = [] ∧
    range (some "yyyy-MM-dd") (some "-") = [pairInvalid] ∧ range (some "dd.MM.yyyy") (some "/") = [pairInvalid] ∧
    range (some "yyyy-MM-dd") none = [] ∧ range (some "dd.MM.yyyy") none = [pairInvalid] ∧
    range (some "MM") (some "") = [] ∧ range (some "MM") none = [] ∧
    range (some "yyyyMM") (some "/") = [pairInvalid] ∧ range (some "dd.MM") (some "-") = [] := by
  native_decide

/-- The pair of two empty members, which kernel 31.1.1 states as the range-format sentence, beside the blank pair
that is not it, and the empty separator beside the two formats a `/` is admitted with on the authored model. -/
example :
    range (some "") (some "") = [pairInvalid] ∧ range (some " ") (some "\t") = [formatMissing] ∧
    range (some "yyyy-MM-dd") (some "") = [pairInvalid] ∧ range (some "dd.MM.yyyy") (some "") = [pairInvalid] := by
  native_decide

private def temporal (kind member : String) (format : Option String) : List String :=
  labelsOf (typedBody kind (Json.mkObj (format.toList.map fun text => (member, Json.str text))))

example :
    (["DateType", "TimeType", "DateTimeType"].all fun kind =>
      temporal kind "format" none == [] &&
      ["", " ", "\t", "\u2003"].all fun format => temporal kind "format" (some format) == [modelNotBuiltLabel]) ∧
    temporal "DateFragmentType" "formatOfFragment" (some "") = [modelNotBuiltLabel] := by
  native_decide

/-! ## A Number bound judged by no magnitude

Locked: a12-dmkits `CheckerNumberBoundMagnitudeAgreementTest` at 1124b523f, kernel 31.1.1 (peer KF582). Kernel
31.1.0 deleted the rule that judged a bound by the magnitude its fractional digits allow, so the rows the rule
was measured on draw only what the printed-bound check, the member ranges and the inversion draw. Each row is
one Number field `Premium` with its bounds written, and asserts the whole label set of the declaration walk and
the consistency check with its multiplicity, codeless classes included, while the model reader builds. The
printed-bound class of two bounds is stated once, and a row reaching a member range keeps its class beside it. -/

private def tooLong : String := ModelConsistencyClass.boundTotalDigitsTooLong.observedLabel
private def signedZero : String := ModelConsistencyClass.boundSignedZero.observedLabel
private def aboveScale : String := FieldTypeNotificationKind.memberAbove14.label
private def signedMember : String := FieldTypeNotificationKind.memberSigned.label
private def inverted : String := FieldTypeNotificationKind.minValueBiggerThanMaxValue.label

/-- The whole label set of the walk and the check, which `verdictOf` narrows to the coded classes. -/
private def allLabelsOf (json : Json) : Verdict :=
  match walkOf json, consistencyOf json, builtOf json with
  | none, none, none => .noModel
  | some walk, some consistency, some _ => cls ((walk ++ consistency).map (·.1))
  | walk, consistency, built =>
      .split s!"walk {walk.isSome}, consistency {consistency.isSome}, model reader {built.isSome}"

private def premiumModel (body : String) (typeDefinition : Bool := false) : Json :=
  ({ elements := [fieldIn "/Policy/Number" "Number" string,
       fieldIn "/Policy/Premium" "Premium"
         (if typeDefinition then typed "TypeDefType" "{\"typeDefinitionId\":\"PremiumType\"}"
          else typed "NumberType" body)]
     typeDefinitions := if typeDefinition then
       [Json.mkObj [("id", "PremiumType"), ("name", "PremiumType"), ("revision", "1"),
         ("fieldType", typed "NumberType" body)]] else [] } : Carrier).json

/-- The members of a Number body: the maximum fractional digits, the two bounds as written, then extras. -/
private def bounds (places : Option Int) (lowest highest : Option String)
    (extra : List (String × String) := []) : String :=
  "{" ++ ",".intercalate (places.toList.map (fun count => s!"\"maxFractionalDigits\":{count}") ++
    lowest.toList.map (fun bound => s!"\"minValue\":{bound}") ++
    highest.toList.map (fun bound => s!"\"maxValue\":{bound}") ++
    extra.map fun (key, value) => s!"\"{key}\":{value}") ++ "}"

private def magnitudeRows : List (String × Json × Verdict) :=
  let row (label : String) (body : String) (labels : List String) := (label, premiumModel body, cls labels)
  [row "max 1e14 at scale 1" (bounds (some 1) none (some "1e14")) [],
   row "max 99999999999999.9 at scale 1, the limit itself" (bounds (some 1) none (some "99999999999999.9")) [],
   row "max 1e15 at scale 0" (bounds (some 0) none (some "1e15")) [tooLong],
   row "max 999999999999999 at scale 0, the limit itself" (bounds (some 0) none (some "999999999999999")) [],
   row "max 999999999999999.4 at scale 0, unrounded" (bounds (some 0) none (some "999999999999999.4")) [],
   row "min 1e15 at scale 0, by absolute value" (bounds (some 0) (some "1e15") none) [tooLong],
   row "min -1e15 at scale 0" (bounds (some 0) (some "-1e15") none) [tooLong],
   row "min -999999999999999 at scale 0, the limit itself" (bounds (some 0) (some "-999999999999999") none) [],
   row "max -1e15 at scale 0, signed" (bounds (some 0) none (some "-1e15")) [tooLong],
   row "max 1e15, scale absent" (bounds none none (some "1e15")) [tooLong],
   row "max 1e15 at scale -1" (bounds (some (-1)) none (some "1e15")) [tooLong],
   row "max 9999999999999990 at scale -1, the limit itself" (bounds (some (-1)) none (some "9999999999999990")) [tooLong],
   row "max 9999999999999991 at scale -1" (bounds (some (-1)) none (some "9999999999999991")) [tooLong],
   row "max 10 at scale 14" (bounds (some 14) none (some "10")) [],
   row "max 9.99999999999999 at scale 14, the limit itself" (bounds (some 14) none (some "9.99999999999999")) [],
   row "max 2 at scale 15, outside its range" (bounds (some 15) none (some "2")) [aboveScale],
   row "max 0.5 at scale 15" (bounds (some 15) none (some "0.5")) [aboveScale],
   row "max 1 at scale 20" (bounds (some 20) none (some "1")) [aboveScale],
   row "max 1e15 at scale -2" (bounds (some (-2)) none (some "1e15")) [tooLong, signedMember],
   row "max 1e17 at scale -2" (bounds (some (-2)) none (some "1e17")) [tooLong, signedMember],
   row "max 1e6 at scale 2 beside 3 integer places" (bounds (some 2) none (some "1e6") [("maxIntegerDigits", "3")]) [],
   row "max 1e13 at scale 2, an amount" (bounds (some 2) none (some "1e13") [("trait", "\"amount\"")]) [],
   row "max 9999999999999.99 at scale 2, an amount, the limit itself"
     (bounds (some 2) none (some "9999999999999.99") [("trait", "\"amount\"")]) [],
   row "both bounds at scale 0" (bounds (some 0) (some "-1e15") (some "1e15")) [tooLong],
   row "min 1e15 over max 1 at scale 0" (bounds (some 0) (some "1e15") (some "1")) [tooLong],
   row "min 1e14 over max 1 at scale 1, beside the inversion" (bounds (some 1) (some "1e14") (some "1")) [inverted],
   row "max -0.4 beside min -1e15 at scale 0" (bounds (some 0) (some "-1e15") (some "-0.4")) [signedZero, tooLong],
   row "max 999999999999.9995 at scale 3" (bounds (some 3) none (some "999999999999.9995")) [tooLong],
   row "max 1e8 at scale 7" (bounds (some 7) none (some "1e8")) []]

private def magnitudeFailures : List (String × Verdict) :=
  magnitudeRows.filterMap fun (label, json, expected) =>
    if allLabelsOf json == expected then none else some (label, allLabelsOf json)

example : magnitudeFailures = [] := by native_decide

/-- A definition's bound is judged through the field that resolves to it, which states the printed-bound class
and no magnitude class: its maximum of 1e15 at no fractional digits (the type-definition test of the same
peer class). -/
example :
    (allLabelsOf (premiumModel (bounds (some 0) none (some "1e15")) (typeDefinition := true)) == cls [tooLong]) = true := by
  native_decide

/-! ### The text a bound is read from

Locked: a12-dmkits `ModelTextReadingDiffTest.aNumberBoundIsReadAsJavaReadsADecimal` at 1124b523f, kernel 31.1.1
(peer KF593), the rows inside this reader's represented profile: a bound text reads as a decimal after Java's
`trim`, the text `null` declares no bound, and text of more than 1000 characters leaves no model, as does a
number token of that length, which every model file passes through `parseModelJson`. The three readers read the
bound alike, or the model file does not parse. The rows beyond the profile, a bound or token exponent past
this reader's range, are not locked. That the token limit reaches a number outside a bound is Jackson's one
limit applied everywhere and is unmeasured here. -/

private def boundFile (written : String) : String :=
  "{\"header\":{\"id\":\"F\",\"modelVersion\":\"28.4.0\",\"locales\":[{\"code\":\"en_US\"}]},\"content\":" ++
  "{\"modelInfo\":{\"name\":\"F\"},\"modelConfig\":{\"conditionLanguage\":{\"code\":\"en_US\"}},\"modelRoot\":" ++
  "{\"rootGroups\":[{\"type\":\"Group\",\"id\":\"/Cover\",\"name\":\"Cover\",\"Group\":{\"elements\":[{\"type\":" ++
  "\"Field\",\"id\":\"/Cover/Amount\",\"name\":\"Amount\",\"Field\":{\"fieldType\":{\"type\":\"NumberType\"," ++
  "\"NumberType\":{\"maxFractionalDigits\":0,\"minValue\":" ++ written ++ "}}}}]}}]}}}"

/-- Whether the model whose `minValue` is written as given is read: the file parses, and the walk, the
consistency reader and the model reader each read the bound. `none` when they disagree. The model reader
refuses a bound it cannot read with the member's name, which tells it from its profile limit on a bound
outside the double range. -/
private def reads? (written : String) : Option Bool :=
  match parseModelJson (boundFile written) with
  | .error _ => some false
  | .ok json =>
      let walk := (fieldTypeDeclarationNotifications json compile).toOption.isSome
      let consistency := (readConsistencyModel json).toOption.isSome
      let model := (readModelWithAdmission json).toOption.any fun read =>
        !read.refusals.any (·.2.startsWith "minValue ")
      if walk == consistency && consistency == model then some walk else none

private def digits (count : Nat) : String := "".pushn '1' count

private def textRows : List (String × String × Bool) :=
  [("\"5\", the control", "\"5\"", true), ("\" 5 \"", "\" 5 \"", true), ("\"5.0\"", "\"5.0\"", true),
   ("5", "5", true), ("a no-break space and 5", "\"\\u00A05\"", false),
   ("an Arabic-Indic digit", "\"\\u0665\"", false), ("\"abc\"", "\"abc\"", false),
   ("\"null\"", "\"null\"", true),
   ("1000 digits as text", s!"\"{digits 1000}\"", true), ("1001 digits as text", s!"\"{digits 1001}\"", false),
   ("a 1000-digit token", digits 1000, true), ("a 1001-digit token", digits 1001, false),
   ("\"5.\"", "\"5.\"", true), ("\".5\"", "\".5\"", true), ("\"1e5\"", "\"1e5\"", true), ("\"+5\"", "\"+5\"", true)]

private def textFailures : List (String × Option Bool) :=
  textRows.filterMap fun (label, written, built) =>
    if reads? written == some built then none else some (label, reads? written)

example : textFailures = [] := by native_decide

/-- A number token anywhere in the model file is held to the limit too: Jackson's one limit, applied beyond a
bound. Unmeasured outside a bound. -/
example :
    (parseModelJson s!"[{digits 1000}]").isOk = true ∧ (parseModelJson s!"[{digits 1001}]").isOk = false ∧
    (parseModelJson s!"\{\"baseYear\":{digits 1001}}").isOk = false := by
  native_decide

end A12Kernel.Dm.DeclarationShapeLocks
