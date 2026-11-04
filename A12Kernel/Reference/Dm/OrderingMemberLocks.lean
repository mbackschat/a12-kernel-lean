import A12Kernel.Reference.Dm.EntryFrameFixture
import A12Kernel.Reference.Dm.ModelConsistencyRead
import A12Kernel.Reference.Dm.FieldTypeDeclarationRead
import A12Kernel.Reference.Dm.ModelVerdictFixture

/-! # What kernel 31.1.1 makes of a group's ordering members

Kernel 30.8.1 bound a group's `indexFieldName` and each `sortFields[].name` against the model and left no
model when the spelling bound nowhere. Kernel 31.1.1 keeps the last segment of the spelling joined to the
group's own path, wherever it lands, and judges that name against the group's own direct children; only an
absolute spelling, a climb above the root, a landing on a group and a sort name written empty leave no model.
Each row is one model of the carrier below with one ordering member written, and asserts what the three
readers draw together: the coded classes the declaration walk and the consistency check report, with their
multiplicity and no class beyond them, or no model on all three. The model reader's own row-key refusals must
equal the walk's wherever it can judge them; a model the flat validation refuses (a no-value-validation
String with no line-break permission) is a limit of that reader and not asserted. The codeless sentences are
the last cluster's.

Locked: the four a12-dmkits tests each cluster names, at 1124b523f, kernel 31.1.1.
-/

namespace A12Kernel.Dm.OrderingMemberLocks

open Lean A12Kernel

/-! ## The carrier -/

private def named (kind id name : String) (body : List (String × Json)) : Json :=
  Json.mkObj [("type", .str kind), ("id", .str id), ("name", .str name), (kind, Json.mkObj body)]

private def literal (text : String) : Json := (Json.parse text).toOption.getD .null

private def string : Json := Json.mkObj [("type", "StringType")]

private def number : Json := Json.mkObj [("type", "NumberType"),
  ("NumberType", Json.mkObj [("maxFractionalDigits", toJson (0 : Nat))])]

/-- A String that switches value validation off and permits no line break, which is the combination the
String type's own class refuses. -/
private def rawString : Json := literal "{\"type\":\"StringType\",\"StringType\":{\"noValueValidation\":true}}"

/-- The same flag with the line-break permission it requires, so only the ordering gate refuses it. -/
private def permittedOpaque : Json := literal
  "{\"type\":\"StringType\",\"StringType\":{\"noValueValidation\":true,\"lineBreaksPermitted\":true}}"

private def fieldIn (path name : String) (type : Json) : Json :=
  named "Field" s!"{path}/{name}" name [("fieldType", type)]

private def groupIn (path name : String) (members : List (String × Json)) (children : List Json) : Json :=
  named "Group" s!"{path}/{name}" name (members ++ [("elements", Json.arr children.toArray)])

private def itemCheck : Json :=
  named "Rule" "/Order/Items/ItemCheck" "ItemCheck" [("errorEntityRelPath", "../Sku"), ("errorCode", "PROBE"),
    ("errorCondition", "FieldFilled(Sku)"), ("severity", "ERROR"),
    ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]])]

/-- The carrier: `Order` with String `CustomerName`, a repeatable `Items` of three holding String `Sku` and
Number `Count` (and the rule `ItemCheck` when asked), and a nonrepeatable `Address` holding String `Street`.
A row writes its members on one of the three groups. -/
private structure Carrier where
  root : List (String × Json) := []
  items : List (String × Json) := []
  address : List (String × Json) := []
  sku : Json := string
  rule : Bool := false
  itemExtras : List Json := []
  rootExtras : List Json := []

private def Carrier.json (carrier : Carrier) : Json :=
  let items := groupIn "/Order" "Items" (("repeatability", toJson (3 : Nat)) :: carrier.items)
    ([fieldIn "/Order/Items" "Sku" carrier.sku, fieldIn "/Order/Items" "Count" number] ++
      (if carrier.rule then [itemCheck] else []) ++ carrier.itemExtras)
  let address := groupIn "/Order" "Address" carrier.address [fieldIn "/Order/Address" "Street" string]
  let order := groupIn "" "Order" carrier.root ([fieldIn "/Order" "CustomerName" string, items, address] ++ carrier.rootExtras)
  checkedEntryFrame <| Json.mkObj [("content", Json.mkObj [
    ("modelConfig", Json.mkObj [("conditionLanguage", Json.mkObj [("code", "en_US")])]),
    ("modelRoot", Json.mkObj [("rootGroups", Json.arr #[order])])])]

/-- `value` written as `member` of the group named `group`; `none` writes nothing. -/
private def written (group member : String) (value : Option Json) (carrier : Carrier := {}) : Carrier :=
  let members := value.toList.map (member, ·)
  match group with
  | "Order" => { carrier with root := members }
  | "Address" => { carrier with address := members }
  | _ => { carrier with items := members }

private def sortList (names : List String) : Json :=
  Json.arr (names.map fun name => Json.mkObj [("name", .str name)]).toArray

/-! ## What the three readers draw -/

private def compile : StringPatternCompiler := fun _ => .compiled fun _ => true

/-- What the readers make of a model together. `split` is a model some readers build and others do not, or
a model reader that judges the nominations differently from the walk; no row expects it. -/
private inductive Verdict where
  | noModel
  | classes (codes : List String)
  | split
  deriving BEq, Repr

private def cls (codes : List String) : Verdict := .classes (codes.mergeSort (· ≤ ·))

private def admitted : Verdict := .classes []

/-- The coded labels of a notification list, sorted, with their multiplicity. -/
private def coded (labels : List String) : List String :=
  (labels.filter fun label => !label.startsWith "codeless:").mergeSort (· ≤ ·)

private def orderingLabels (labels : List String) : List String :=
  (labels.filter (RowFieldRefusal.all.map (·.label)).contains).mergeSort (· ≤ ·)

/-- The walk's labels, and none when it leaves no model. -/
private def walkOf (json : Json) : Option (List String) :=
  match fieldTypeDeclarationNotifications json compile with
  | .ok labels => if labels.any (·.1 == modelNotBuiltLabel) then none else some (labels.map (·.1))
  | .error _ => none

private def consistencyOf (json : Json) : Option (List String) :=
  match checkModelConsistency json with
  | .ok (.checked notifications) => some (notifications.map (·.kind.observedLabel))
  | _ => none

/-- The model reader's refusals as labels, and none when it builds no model: a read error, or a nomination
refused for leaving none. A nomination it could not judge on a model the flat validation refuses is reported
as `judged := false`. -/
private def builtOf (json : Json) : Option (List String × Bool) :=
  match readModelWithAdmission json with
  | .error _ => none
  | .ok model =>
      let reasons := model.refusals.map (·.2)
      if reasons.any (·.endsWith "leaves no model") then none
      else some (reasons, !reasons.any (·.endsWith "is not judged on an invalid model"))

private def verdictOf (json : Json) : Verdict :=
  match walkOf json, consistencyOf json, builtOf json with
  | none, none, none => .noModel
  | some walk, some consistency, some (built, judged) =>
      if !judged || orderingLabels walk == orderingLabels built then .classes (coded (walk ++ consistency))
      else .split
  | _, _, _ => .split

/-- The labels of the rows whose verdict is not the expected one. -/
private def failures (rows : List (String × Json × Verdict)) : List String :=
  rows.filterMap fun (label, json, expected) => if verdictOf json == expected then none else some label

private def indexMissing : String := "MVK_INVALID_INDEX_FIELD"
private def sortMissing : String := "MVK_INVALID_SORT_FIELD"
private def indexOpaque : String := "MVK_INDEX_FIELD_NO_VALUE_VALIDATION"
private def sortOpaque : String := "MVK_SORT_FIELD_NO_VALUE_VALIDATION"
private def sortDuplicate : String := "MVK_SORT_FIELD_DUPLICATE"
private def sortInfoMissing : String := "MVK_SORT_INFO_MISSING"
private def stringLineBreak : String := "MVK_STRING_TYPE_NO_VAL_AND_NO_LINE_BREAK"

/-! ## Where a spelling lands

Locked: a12-dmkits `GroupIndexAndSortReferenceLawsTest` at 1124b523f, kernel 31.1.1. A name is judged
against the group's own children whatever it lands on: the parent's field, a rule and nothing are only names,
and the empty and blank index spellings keep the group's name and a blank. Only an absolute spelling, one
climbing past the root and one landing on a group leave no model. -/

private def indexRows : List (String × Json × Verdict) :=
  let index (spelling : String) (group : String := "Items") : Json :=
    (written group "indexFieldName" (some (.str spelling))).json
  [("Sku, the control", index "Sku", admitted),
   ("another field of the group", index "Count", admitted),
   ("absent", ({} : Carrier).json, admitted),
   ("empty", index "", cls [indexMissing]),
   ("whitespace only", index "   ", cls [indexMissing]),
   ("a field that does not exist", index "Missing", cls [indexMissing]),
   ("a field of the parent group", index "CustomerName", cls [indexMissing]),
   ("a relative path to one", index "../CustomerName", cls [indexMissing]),
   ("on a nonrepeatable group", index "Street" "Address", admitted),
   ("unresolvable on a nonrepeatable group", index "Missing" "Address", cls [indexMissing]),
   ("a .. that climbs to the root", index "../../Sku", admitted),
   ("a .. that climbs past the root", index "../../../Sku", .noModel),
   ("a .. landing on the parent group", index "..", .noModel),
   ("a rule of the group", ({ written "Items" "indexFieldName" (some (.str "ItemCheck")) with rule := true } : Carrier).json,
    cls [indexMissing]),
   ("a descending path with no ..", index "Items/Sku", admitted),
   ("a child group of the named group", index "Items" "Order", .noModel),
   ("a descending path that does resolve", index "Items/Sku" "Order", cls [indexMissing]),
   ("an absolute path to the group's own field", index "/Order/Items/Sku", .noModel),
   ("the number 5", (written "Items" "indexFieldName" (some (toJson (5 : Nat)))).json, cls [indexMissing])]

example : failures indexRows = [] := by native_decide

private def sortRows : List (String × Json × Verdict) :=
  let sorted (name : String) (group : String := "Items") : Json :=
    (written group "sortFields" (some (sortList [name]))).json
  [("Sku, the control", sorted "Sku", admitted),
   ("an empty list", (written "Items" "sortFields" (some (sortList []))).json, admitted),
   ("a field that does not exist", sorted "Missing", cls [sortMissing]),
   ("an empty name", sorted "", .noModel),
   ("an entry with no name", (written "Items" "sortFields" (some (Json.arr #[Json.mkObj []]))).json, .noModel),
   ("an absolute path", sorted "/Order/Items/Sku", .noModel),
   ("a numeric name",
    (written "Items" "sortFields" (some (Json.arr #[Json.mkObj [("name", toJson (5 : Nat))]]))).json,
    cls [sortMissing]),
   ("a field outside the group that resolves", sorted "../CustomerName", cls [sortMissing]),
   ("a child group of the named group", sorted "Items" "Order", .noModel),
   ("a blank name", sorted "   ", cls [sortMissing, sortInfoMissing]),
   ("a rule of the group", ({ written "Items" "sortFields" (some (sortList ["ItemCheck"])) with rule := true } : Carrier).json,
    cls [sortMissing]),
   ("a .. that climbs to the root", sorted "../../Sku", admitted)]

example : failures sortRows = [] := by native_decide

/-- A second `Sku` beside the group's own separates the landing from the name: `../Sku` lands on the parent's
field, outside the group, and is admitted because the group carries a `Sku` of its own. A spelling landing
outside on a name the group does not carry is still refused in the same model. -/
private def duplicateShortNameRows : List (String × Json × Verdict) :=
  let withParentSku (carrier : Carrier) : Carrier := { carrier with rootExtras := [fieldIn "/Order" "Sku" string] }
  let index (spelling : String) (carrier : Carrier) : Carrier :=
    written "Items" "indexFieldName" (some (.str spelling)) carrier
  [("index ../Sku, no /Order/Sku, the control", (index "../Sku" {}).json, admitted),
   ("index ../Sku, with /Order/Sku", (withParentSku (index "../Sku" {})).json, admitted),
   ("sort ../Sku, with /Order/Sku",
    (withParentSku (written "Items" "sortFields" (some (sortList ["../Sku"])))).json, admitted),
   ("index ../CustomerName, with /Order/Sku", (withParentSku (index "../CustomerName" {})).json, cls [indexMissing])]

example : failures duplicateShortNameRows = [] := by native_decide

/-- Locked: a12-dmkits `GroupIndexAndSortReferenceLawsTest` at 1124b523f, kernel 31.1.1. A sort list on a group
holding at most one row has no order to declare, and the member's presence is not the gate: an empty list is
admitted. An index member holding two names is no text and leaves no model, while a plural member name is
read past as any unknown member is. -/
private def carrierRows : List (String × Json × Verdict) :=
  [("a sort list on a repeatable group, the control", (written "Items" "sortFields" (some (sortList ["Sku"]))).json,
    admitted),
   ("a sort list on a nonrepeatable group",
    (written "Address" "sortFields" (some (sortList ["Street"]))).json, cls ["MVK_INVALID_SORTINFO"]),
   ("an empty sort list on a nonrepeatable group", (written "Address" "sortFields" (some (sortList []))).json,
    admitted),
   ("an index member holding two names",
    (written "Items" "indexFieldName" (some (Json.arr #[.str "Sku", .str "Count"]))).json, .noModel),
   ("a plural index member repeating one name",
    (written "Items" "indexFieldNames" (some (Json.arr #[.str "Sku", .str "Sku"]))).json, admitted)]

example : failures carrierRows = [] := by native_decide

/-! ## The semantic index over a group's index field

Locked: a12-dmkits `GroupIndexAndSortReferenceLawsTest` at 1124b523f, kernel 31.1.1, the condition-side rows.
A rule using a semantic index over a group asks for that group's index field, so two indexed groups on one
path are legal until a condition asks, and a plural member name is read past. -/

private def semantic (index : Option String) (ancestorIndex : Option String := none)
    (extra : List (String × Json) := []) (rule : Bool := true) : Json :=
  let condition := named "Rule" "/Order/R" "R" [("errorEntityRelPath", "../CustomerName"), ("errorCode", "PROBE"),
    ("errorCondition", "AllFieldsFilled(Items For \"SKU-1\", CustomerName)"), ("severity", "ERROR"),
    ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]])]
  ({ root := ancestorIndex.toList.map fun name => ("indexFieldName", Json.str name)
     items := (index.toList.map fun name => ("indexFieldName", Json.str name)) ++ extra
     rootExtras := if rule then [condition] else [] } : Carrier).json

private def semanticRows : List (String × Json × List String × Verdict) :=
  [("a usable index, the control", semantic (some "Sku"), ["ok"], admitted),
   ("an ancestor group also declaring an index", semantic (some "Sku") (some "CustomerName"),
    ["refused ParallelAdmission MVK_MULTIPLE_INDEX_FIELDS"], admitted),
   ("two indexed groups and no semantic index", semantic (some "Sku") (some "CustomerName") (rule := false), [],
    admitted),
   ("a plural index member beside the index", semantic (some "Sku") (extra := [("indexFieldNames",
      Json.arr #[.str "Sku", .str "Count"])]), ["ok"], admitted)]

example : semanticRows.filterMap (fun (label, json, statics, verdict) =>
    if (modelVerdict json).statics == statics && verdictOf json == verdict then none else some label) = [] := by
  native_decide

/- Recorded deviation, not a law. An index resolving outside its group is declared and unusable: the Kernel
   draws `MVK_INVALID_INDEX_FIELD` and, for a rule using a semantic index over it, `MVK_INDEX_FIELD_INVALID`
   beside it, while the model reader keeps no index field for the group and the rule check refuses it as a
   group declaring none. The flat model has no way to tell a declared index that names no field from none
   declared, which is a change to its representation and not to the ordering reader. -/
example :
    ((modelVerdict (semantic (some "../CustomerName"))).statics == ["refused ParallelAdmission MVK_NO_INDEX_FIELD"] &&
      verdictOf (semantic (some "../CustomerName")) == cls [indexMissing]) = true := by
  native_decide

/-! ## Both members defective at once

Locked: a12-dmkits `GroupOrderingMultipleDefectLawsTest` at 1124b523f, kernel 31.1.1. Neither member
withholds the other, the sort list's repeat class is drawn once and its type class once per opaque field, and
a name resolving to nothing draws its code beside the other member's verdict instead of stopping the build. -/

private def ordering (opaqueSku : Bool) (index : Option String) (sorts : List String) : Json :=
  ({ items := (index.toList.map fun name => ("indexFieldName", Json.str name)) ++
        (if sorts.isEmpty then [] else [("sortFields", sortList sorts)])
     sku := if opaqueSku then rawString else string } : Carrier).json

private def batch : Json := fieldIn "/Order/Items" "Batch" rawString

private def bothMembersRows : List (String × Json × Verdict) :=
  [("both members on a plain field, the control", ordering false (some "Sku") ["Sku"], admitted),
   ("an opaque index field alone", ordering true (some "Sku") [], cls [indexOpaque, stringLineBreak]),
   ("an opaque sort field alone", ordering true none ["Sku"], cls [sortOpaque, stringLineBreak]),
   ("both members on the opaque field", ordering true (some "Sku") ["Sku"],
    cls [indexOpaque, sortOpaque, stringLineBreak]),
   ("an opaque index with a plain sort field", ordering true (some "Sku") ["Count"],
    cls [indexOpaque, stringLineBreak])]

example : failures bothMembersRows = [] := by native_decide

private def sortListRows : List (String × Json × Verdict) :=
  [("one field sorted twice, plain", ordering false none ["Sku", "Sku"], cls [sortDuplicate]),
   ("one field sorted three times", ordering false none ["Sku", "Sku", "Sku"], cls [sortDuplicate]),
   ("two fields each sorted twice", ordering false none ["Sku", "Sku", "Count", "Count"], cls [sortDuplicate]),
   ("the opaque field sorted twice", ordering true none ["Sku", "Sku"],
    cls [sortOpaque, sortDuplicate, stringLineBreak]),
   ("two different opaque fields sorted",
    ({ items := [("sortFields", sortList ["Sku", "Batch"])], sku := rawString, itemExtras := [batch] } : Carrier).json,
    cls [sortOpaque, sortOpaque, stringLineBreak, stringLineBreak]),
   ("the added field alone, sorted, the control",
    ({ items := [("sortFields", sortList ["Batch"])], itemExtras := [batch] } : Carrier).json,
    cls [sortOpaque, stringLineBreak]),
   ("two opaque fields and no ordering member",
    ({ sku := rawString, itemExtras := [batch] } : Carrier).json, cls [stringLineBreak, stringLineBreak])]

example : failures sortListRows = [] := by native_decide

private def unresolvableRows : List (String × Json × Verdict) :=
  [("an unresolvable index alone", ordering false (some "NoSuchField") [], cls [indexMissing]),
   ("an unresolvable sort field alone", ordering false none ["NoSuchField"], cls [sortMissing]),
   ("an unresolvable index beside an opaque sort field", ordering true (some "NoSuchField") ["Sku"],
    cls [indexMissing, sortOpaque, stringLineBreak]),
   ("an opaque index beside an unresolvable sort field", ordering true (some "Sku") ["NoSuchField"],
    cls [indexOpaque, sortMissing, stringLineBreak])]

example : failures unresolvableRows = [] := by native_decide

/-! ## The type of the field a name lands on

Locked: a12-dmkits `GroupOrderingFieldTypeLawsTest` at 1124b523f, kernel 31.1.1. The no-value-validation
String is refused as either key, a flag the String body does not declare is read past, and a table-referencing
Enumeration, which reads as an Enumeration with no values, leaves no model whatever it is used for. -/

private def typed (type : String) (member : Option (String × Json)) : Json :=
  ({ items := member.toList, sku := literal type } : Carrier).json

private def byIndex : Option (String × Json) := some ("indexFieldName", .str "Sku")

private def bySort : Option (String × Json) := some ("sortFields", sortList ["Sku"])

private def stringFlag (value : String) : String :=
  "{\"type\":\"StringType\",\"StringType\":{\"noValueValidation\":" ++ value ++ "}}"

private def typeRows : List (String × Json × Verdict) :=
  [("a plain string field, the control", ({ items := [("indexFieldName", .str "Sku")] } : Carrier).json, admitted),
   ("a field declared noValueValidation", ({ items := [("indexFieldName", .str "Sku")], sku := permittedOpaque } :
      Carrier).json, cls [indexOpaque]),
   ("the same, as a sort field", ({ items := [("sortFields", sortList ["Sku"])], sku := permittedOpaque } :
      Carrier).json, cls [sortOpaque]),
   ("an empty fieldType object", typed "{}" byIndex, .noModel),
   ("a number type carrying the same flag",
    typed "{\"type\":\"NumberType\",\"NumberType\":{\"noValueValidation\":true}}" byIndex, admitted),
   ("a plain number type", typed "{\"type\":\"NumberType\",\"NumberType\":{}}" byIndex, admitted),
   ("the flag as a string rather than a boolean", typed (stringFlag "\"true\"") byIndex,
    cls [indexOpaque, stringLineBreak]),
   ("the flag as the string false", typed (stringFlag "\"false\"") byIndex, admitted),
   ("the flag as the number 1", typed (stringFlag "1") byIndex, cls [indexOpaque, stringLineBreak]),
   ("the flag as the number 0", typed (stringFlag "0") byIndex, admitted),
   ("the flag as the number 2", typed (stringFlag "2") byIndex, cls [indexOpaque, stringLineBreak]),
   ("the flag as an arbitrary string", typed (stringFlag "\"yes\"") byIndex, .noModel),
   ("a type name the Kernel does not have", typed "{\"type\":\"NotAType\",\"NotAType\":{}}" byIndex, .noModel),
   ("a discriminator naming a body that is absent", typed "{\"type\":\"StringType\"}" byIndex, admitted),
   ("the flag explicitly null", typed (stringFlag "null") byIndex, .noModel),
   ("a plain value-list enumeration, as the index",
    typed "{\"type\":\"EnumerationType\",\"EnumerationType\":{\"values\":[{\"value\":\"RED\"}]}}" byIndex, admitted)]

example : failures typeRows = [] := by native_decide

/-- An Enumeration naming a value table and declaring no values leaves no model in all three readers, whatever
role its field plays: ordering nothing, as the index and as a sort key (kernel 31.1.1 reads the consistency
check and the model reader alike; they refused no model for it on 30.8.1). -/
example : [byIndex, bySort, none].all (fun member =>
    verdictOf (typed "{\"type\":\"EnumerationType\",\"EnumerationType\":{\"tableName\":\"Colours\"}}" member) ==
      .noModel) =
  true := by
  native_decide

/-! ## The sentences, with the classes they stand beside

Locked: a12-dmkits `CheckerOrderingNameSentenceAgreementTest` at 1124b523f, kernel 31.1.1. A row is one
model of an order's line items with one member varied, and states the whole notification list as
`class@path`, with its multiplicity and sorted, because the Kernel states each sentence at the element it is
about. The group's field-name sentence is the short name's, judged trimmed and never for a blank one; the
index written empty draws the basic check's own sentence beside `MVK_INVALID_INDEX_FIELD`, and an index or
sort name that is blank without being empty does not. A refused element anywhere withholds the ordering
gates and nothing else. The rows that put a refused name in a field of their own state that field's classes
as it draws them alone, the baseline, so that the member's sentence shows as one more.

Provenance limit: the peer test asserts that its checker agrees with the Kernel on every row, while the lists
here were derived from that agreed account and the mechanism rather than copied from a Kernel observation;
only the three rows of its `a12sAnswerOnTheDiscriminatingRows` read the Kernel's own answer. -/

private structure Row where
  field : String
  index : Option String := none
  sorts : List String := []
  orderField : String := "Channel"
  note : String := "Note"
  noValueValidation : Bool := false
  archiveRepeatability : Option Nat := none

private def Row.json (row : Row) : Json :=
  let members := (row.index.toList.map fun name => ("indexFieldName", Json.str name)) ++
    (if row.sorts.isEmpty then [] else [("sortFields", sortList row.sorts)])
  let items := groupIn "/Order" "Items" (("repeatability", toJson (5 : Nat)) :: members)
    [fieldIn "/Order/Items" row.field (if row.noValueValidation then permittedOpaque else string),
      fieldIn "/Order/Items" row.note string, fieldIn "/Order/Items" "Qty" string,
      fieldIn "/Order/Items" "Lot" string]
  let archive := groupIn "/Order" "Archive" (row.archiveRepeatability.toList.map fun count =>
      ("repeatability", toJson count)) [fieldIn "/Order/Archive" "Text" string]
  checkedEntryFrame <| Json.mkObj [("content", Json.mkObj [
    ("modelConfig", Json.mkObj [("conditionLanguage", Json.mkObj [("code", "en_US")])]),
    ("modelRoot", Json.mkObj [("rootGroups", Json.arr
      #[groupIn "" "Order" [] [items, fieldIn "/Order" row.orderField string, archive]])])])]

/-- Every notification of the model as `class@path`, sorted, from the declaration walk and the consistency
check, which draw disjoint classes; `UNBUILT@` when all three readers leave no model and `SPLIT@` when they
disagree, as the verdicts above do. The model reader judges no withholding, so its ordering refusals are
compared with the walk's only where the walk withholds none. -/
private def listingOf (json : Json) : List String :=
  let walked : Option (List (String × String)) := (fieldTypeDeclarationNotifications json compile).toOption
  let checked : Except String ModelConsistencyOutcome := checkModelConsistency json
  match walked, checked, builtOf json with
  | some walk, .ok (.checked (consistency : List ModelConsistencyNotification)), some (built, judged) =>
      let withheld := walk.any fun entry =>
        ["MVK_PATH_INVALID", "MVK_PATHS_INCONSISTENT", "MVK_MAX_VALUES_INVALID"].contains entry.1
      if walk.any (·.1 == modelNotBuiltLabel) then ["SPLIT@"]
      else if judged && !withheld && orderingLabels (walk.map (·.1)) != orderingLabels built then ["SPLIT@"]
      else
        let walkEntries : List String := walk.map fun entry => s!"{entry.1}@{entry.2}"
        let checkEntries : List String := consistency.map fun notification =>
          s!"{notification.kind.observedLabel}@/{"/".intercalate notification.path}"
        (walkEntries ++ checkEntries).mergeSort (· ≤ ·)
  | some walk, .ok (.notBuilt ..), none =>
      if walk.any (·.1 == modelNotBuiltLabel) then ["UNBUILT@"] else ["SPLIT@"]
  | _, _, _ => ["SPLIT@"]

private def itemsPath : String := "/Order/Items"
private def under (name : String) : String := s!"{itemsPath}/{name}"
private def listing (entries : List (String × String)) : List String :=
  (entries.map fun (label, path) => s!"{label}@{path}").mergeSort (· ≤ ·)

private def unbuilt : List (String × String) := [("UNBUILT", "")]
private def shape : String := "codeless:field-name-shape"
private def pathInvalid : String := "MVK_PATH_INVALID"
private def digitInitial : String := "MVK_NAME_STARTS_WITH_DIGIT_A12_DV"
private def maxInvalid : String := "MVK_MAX_VALUES_INVALID"
private def countNotPositive : String := "codeless:count-not-positive"
private def indexEmpty : String := "codeless:index-field-name-empty"
private def capacity : String := "codeless:sort-list-capacity"

private def nbsp : String := "Sk u"
private def emSpace : String := " "

/-- The Kernel's own answer on the rows that separate the readings, so agreement on a broken fixture cannot
pass. -/
example :
    listingOf (Row.json { field := "Sku", index := some "../Items/Sku" }) = [] ∧
    listingOf (Row.json { field := "Sk-u", index := some "Sk-u" }) =
      listing [(pathInvalid, under "Sk-u"), (shape, itemsPath), (shape, under "Sk-u")] ∧
    listingOf (Row.json { field := "Sku", index := some "../Channel" }) = listing [(indexMissing, itemsPath)] := by
  native_decide

/-- The rows A12 holds one member of, each beside the notification list it draws. -/
private def memberRows : List (String × Row × List String) :=
  let sku (index : Option String := none) (sorts : List String := []) : Row := { field := "Sku", index, sorts }
  let refusedNote := [(pathInvalid, under "No-te"), (shape, under "No-te")]
  let refusedKey := [(pathInvalid, under nbsp), (shape, itemsPath), (shape, under nbsp)]
  let countBelowOne := [(maxInvalid, "/Order/Archive"), (countNotPositive, "/Order/Archive"),
    (maxInvalid, "/Order/Archive/Text")]
  let blankSort := [(sortMissing, itemsPath), (sortInfoMissing, itemsPath)]
  let rows : List (String × Row × List (String × String)) := [
   ("the index, the control", sku (some "Sku"), []),
   ("a sort, the control", sku none ["Sku"], []),
   ("an index through the group", sku (some "../Items/Sku"), []),
   ("a sort through the group", sku none ["../Items/Sku"], []),
   ("a padded index", sku (some " Sku"), [(indexMissing, itemsPath)]),
   ("a padded sort", sku none [" Sku"], [(sortMissing, itemsPath)]),
   ("an index padded behind", sku (some "Sku "), [(indexMissing, itemsPath)]),
   ("a sort padded behind", sku none ["Sku "], [(sortMissing, itemsPath)]),
   ("a no-break-space field, as the index through the group",
    { field := nbsp, index := some s!"../Items/{nbsp}" }, refusedKey),
   ("a no-break-space field, as a sort through the group",
    { field := nbsp, sorts := [s!"../Items/{nbsp}"] }, refusedKey),
   ("an index landing on a parent field of a refused name",
    { field := "Sku", index := some s!"../{nbsp}", orderField := nbsp },
    [(pathInvalid, s!"/Order/{nbsp}"), (shape, s!"/Order/{nbsp}"), (shape, itemsPath)]),
   ("a sort landing on a parent field of a refused name",
    { field := "Sku", sorts := [s!"../{nbsp}"], orderField := nbsp },
    [(pathInvalid, s!"/Order/{nbsp}"), (shape, s!"/Order/{nbsp}"), (shape, itemsPath)]),
   ("an opaque index key", { field := "Sku", index := some "Sku", noValueValidation := true },
    [("MVK_INDEX_FIELD_NO_VALUE_VALIDATION", under "Sku")]),
   ("a refused opaque index key", { field := nbsp, index := some nbsp, noValueValidation := true }, refusedKey),
   ("a refused opaque sort key", { field := nbsp, sorts := [nbsp], noValueValidation := true }, refusedKey),
   ("a digit-initial opaque index key", { field := "1Sku", index := some "1Sku", noValueValidation := true },
    [(pathInvalid, under "1Sku"), (digitInitial, under "1Sku")]),
   ("an opaque index key beside a refused element",
    { field := "Sku", index := some "Sku", noValueValidation := true, note := "No-te" }, refusedNote),
   ("an index outside the group", sku (some "../Channel"), [(indexMissing, itemsPath)]),
   ("an index outside the group, beside a refused element",
    { field := "Sku", index := some "../Channel", note := "No-te" }, refusedNote),
   ("a sort outside the group, beside a refused element",
    { field := "Sku", sorts := ["../Channel"], note := "No-te" }, refusedNote),
   ("an opaque key beside a count below one",
    { field := "Sku", index := some "Sku", noValueValidation := true, archiveRepeatability := some 0 },
    countBelowOne),
   ("an index outside the group, beside a count below one",
    { field := "Sku", index := some "../Channel", archiveRepeatability := some 0 }, countBelowOne),
   ("a sort listed twice", sku none ["Sku", "Sku"], [(sortDuplicate, itemsPath)]),
   ("a sort listed twice, beside a refused element",
    { field := "Sku", sorts := ["Sku", "Sku"], note := "No-te" }, (sortDuplicate, itemsPath) :: refusedNote),
   ("a refused name repeated beside a sound repeat",
    { field := "Sku", sorts := ["Sku", "Sku", "Sk-u"], note := "Sk-u" },
    [(sortDuplicate, itemsPath), (shape, itemsPath), (pathInvalid, under "Sk-u"), (shape, under "Sk-u")]),
   ("a refused name at the fourth entry",
    { field := "Sku", sorts := ["Sku", "Sku", "Qty", "Sk-u"], note := "Sk-u" },
    [(sortDuplicate, itemsPath), (capacity, itemsPath), (pathInvalid, under "Sk-u"), (shape, under "Sk-u")]),
   ("an index written empty", sku (some ""), [(indexMissing, itemsPath), (indexEmpty, itemsPath)]),
   ("an index of three spaces", sku (some "   "), [(indexMissing, itemsPath)]),
   ("an index of one em space", sku (some emSpace), [(indexMissing, itemsPath)]),
   ("an index climbing to the root", sku (some "../../Sku"), []),
   ("an index descending from the group", sku (some "Items/Sku"), []),
   ("an index naming nothing", sku (some "Missing"), [(indexMissing, itemsPath)]),
   ("an index landing on the parent group", sku (some ".."), unbuilt),
   ("a sort written empty", sku none [""], unbuilt),
   ("a sort of three spaces", sku none ["   "], blankSort),
   ("a sort of one tab", sku none ["\t"], blankSort),
   ("a sort of one em space", sku none [emSpace], blankSort),
   ("two blank sorts", sku none ["   ", "\t"], (sortMissing, itemsPath) :: blankSort),
   ("a sort climbing to the root", sku none ["../../Sku"], []),
   ("a sort naming nothing", sku none ["Missing"], [(sortMissing, itemsPath)]),
   ("a sort landing on the parent group", sku none [".."], unbuilt),
   ("a refused name sorted twice", { field := "Sk-u", sorts := ["Sk-u", "Sk-u"] },
    [(shape, itemsPath), (pathInvalid, under "Sk-u"), (shape, under "Sk-u")]),
   ("a refused name at the fourth entry among plain ones",
    { field := "Sk-u", sorts := ["Note", "Qty", "Lot", "Sk-u"] },
    [(capacity, itemsPath), (pathInvalid, under "Sk-u"), (shape, under "Sk-u")])]
  rows.map fun (label, row, expected) => (label, row, listing expected)

/-- The names A12's field-name pattern refuses beside the ones it admits, each held as a field's own name
and as an ordering member's. The group's sentence is stated for a refused one and for no admitted one. -/
private def refusedNames : List String := [nbsp, "Sk-u", "Sku.1", "Ské"]

private def admittedNames : List String :=
  [String.ofList (List.replicate 61 'S'), "1Sku", "Ns:Sku", "Sku.a", "Sku.value"]

/-- Five rows per name: the field alone, which is the baseline, then the name as the index and as a sort of
that field, and as the index and as a sort of a group whose field is a plain `Sku`. -/
private def nameRows : List (String × Row × List String) :=
  (refusedNames ++ admittedNames).flatMap fun name =>
    let baseline := listingOf (Row.json { field := name })
    let sentence := if refusedNames.contains name then [(shape, itemsPath)] else []
    let stated (extra : List (String × String)) := (baseline ++ listing extra).mergeSort (· ≤ ·)
    [(s!"{name} alone", { field := name }, baseline),
     (s!"{name} as its own index", { field := name, index := some name }, stated sentence),
     (s!"{name} as the index of a plain field", { field := "Sku", index := some name },
      listing ((indexMissing, itemsPath) :: sentence)),
     (s!"{name} as its own sort", { field := name, sorts := [name] }, stated sentence),
     (s!"{name} as the sort of a plain field", { field := "Sku", sorts := [name] },
      listing ((sortMissing, itemsPath) :: sentence))]

private def disagreeing (rows : List (String × Row × List String)) : List String :=
  rows.filterMap fun (label, row, expected) => if listingOf row.json == expected then none else some label

example : disagreeing memberRows = [] := by native_decide

example : disagreeing nameRows = [] := by native_decide

end A12Kernel.Dm.OrderingMemberLocks
