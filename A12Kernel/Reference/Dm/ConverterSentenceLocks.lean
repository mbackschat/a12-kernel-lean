import A12Kernel.Reference.Dm.ComputationCheck
import A12Kernel.Reference.Dm.EntryFrameFixture
import A12Kernel.Reference.Dm.ModelConsistencyRead
import A12Kernel.Reference.Dm.FieldTypeDeclarationRead

/-! # What kernel 31.1.1's validation-model converter makes of a defective declaration

Kernel 30.8.1 threw while converting a model into its validation model, so a blank name, a missing type
definition, an unnamed or unresolvable computed field or a repeated child name left no model. Kernel 31.1.1
states a codeless sentence and goes on without the declaration and its subtree, and its other checks then
read the converted model while the basic check still reads the authored one. Each row is one model of the
oracle's carrier with one edit, and asserts the whole set of classes the three readers and the static
checks draw together, as the oracle's column does: no class beyond it, and `UNBUILT` only when all three
readers leave no model. A model whose flat validation refuses (a fraction count above the scale limit)
judges no rule here, which is the reader's own limit and no class, so such a row's static column is not
asserted.

Sentence paths are derived from the element each sentence is stated for, not measured: the oracle compares
sets of classes.

Locked: a12-dmkits CheckerConverterSentenceAgreementTest at 1124b523f, kernel 31.1.1.
-/

namespace A12Kernel.Dm.ConverterSentenceLocks

open Lean A12Kernel

/-! ## The carrier -/

private def named (kind id name : String) (body : List (String × Json)) : Json :=
  Json.mkObj [("type", .str kind), ("id", .str id), ("name", .str name), (kind, Json.mkObj body)]

private def stringField (name : String) : Json :=
  named "Field" s!"/Policy/{name}" name [("fieldType", Json.mkObj [("type", "StringType")])]

private def numberField (name : String) : Json :=
  named "Field" s!"/Policy/{name}" name [("fieldType", Json.mkObj [("type", "NumberType"),
    ("NumberType", Json.mkObj [("maxFractionalDigits", toJson (0 : Nat))])])]

private def ruleElement (id name condition errorRelPath : String) : Json :=
  named "Rule" id name [("errorEntityRelPath", .str errorRelPath), ("errorCode", "PROBE"),
    ("errorCondition", .str condition), ("severity", "ERROR"),
    ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]])]

private def groupElement (id name : String) (members : List (String × Json)) (children : List Json) : Json :=
  named "Group" id name (members ++ [("elements", Json.arr children.toArray)])

/-- The carrier: `Policy` with String `Ref` and `Code`, Numbers `Total` and `Fee` of no fraction digits, a
repeatable `Items` of three holding `Label`, and the rule `RefCheck` reporting at `Ref`. -/
private def policy : Json :=
  groupElement "/Policy" "Policy" []
    [stringField "Ref", stringField "Code", numberField "Total", numberField "Fee",
      groupElement "/Policy/Items" "Items" [("repeatability", toJson (3 : Nat))]
        [named "Field" "/Policy/Items/Label" "Label" [("fieldType", Json.mkObj [("type", "StringType")])]],
      ruleElement "/Policy/RefCheck" "RefCheck" "FieldFilled(Ref)" "../Ref"]

private def noSuchField : String := "FieldFilled(NoSuchFieldAnywhere)"

/-- The model a list of root groups makes. -/
private def modelOf (roots : List Json) : Json :=
  checkedEntryFrame <| Json.mkObj [("content", Json.mkObj [
    ("modelConfig", Json.mkObj [("conditionLanguage", Json.mkObj [("code", "en_US")])]),
    ("modelRoot", Json.mkObj [("rootGroups", Json.arr roots.toArray)])])]

/-! ## The edits a row applies -/

private def nameOf (element : Json) : Option String := (element.getObjValAs? String "name").toOption

private def dropMember (json : Json) (key : String) : Json :=
  match json with
  | .obj members => .obj (members.erase key)
  | other => other

private def childrenOf (group : Json) : List Json :=
  (((group.getObjValD "Group").getObjValAs? (Array Json) "elements").toOption.getD #[]).toList

private def withChildren (change : List Json → List Json) (group : Json) : Json :=
  group.setObjVal! "Group"
    ((group.getObjValD "Group").setObjVal! "elements" (Json.arr (change (childrenOf group)).toArray))

/-- `change` applied to the first element of that name. -/
private def onNamed (name : String) (change : Json → Json) (elements : List Json) : List Json :=
  match elements.findIdx? (nameOf · == some name) with
  | some index => elements.modify index change
  | none => elements

private def renamed (name to : String) : List Json → List Json := onNamed name (·.setObjVal! "name" (.str to))

private def inItems (change : List Json → List Json) : List Json → List Json := onNamed "Items" (withChildren change)

/-- A rule appended after every element of the list it is given. -/
private def withRule (name condition errorRelPath : String) (elements : List Json) : List Json :=
  elements ++ [ruleElement s!"rule-{name}-{elements.length}" name condition errorRelPath]

private def withComputation (target operation : String) (name : String := "Calc") (elements : List Json) :
    List Json :=
  elements ++ [named "Computation" s!"computation-{name}" name [("computedFieldRelPath", .str target),
    ("computationAlternatives", Json.arr #[Json.mkObj [("operation", .str operation)]]),
    ("errorMessage", Json.arr #[Json.mkObj [("locale", "en_US"), ("text", "m")]])]]

/-- A field retyped as a reference to the type definition `id`; `none` writes a reference without an id. -/
private def typedBy (field : String) (id : Option String) : List Json → List Json :=
  onNamed field fun element =>
    element.setObjVal! "Field" ((element.getObjValD "Field").setObjVal! "fieldType"
      (Json.mkObj [("type", "TypeDefType"), ("TypeDefType", Json.mkObj (id.toList.map fun id =>
        ("typeDefinitionId", Json.str id)))]))

/-- A second copy of the element, with an id of its own, after every other element. -/
private def duplicated (name : String) (elements : List Json) : List Json :=
  elements ++ (elements.find? (nameOf · == some name)).toList.map fun element =>
    element.setObjVal! "id" (.str s!"{(element.getObjValAs? String "id").toOption.getD ""}-twin")

/-- `element`'s Number body with the members written. -/
private def withNumberMembers (members : List (String × Json)) (element : Json) : Json :=
  let body := element.getObjValD "Field"
  let type := body.getObjValD "fieldType"
  let number := members.foldl (fun number (key, value) => number.setObjVal! key value) (type.getObjValD "NumberType")
  element.setObjVal! "Field" (body.setObjVal! "fieldType" (type.setObjVal! "NumberType" number))

private def numberMembers (field : String) (members : List (String × Json)) : List Json → List Json :=
  onNamed field (withNumberMembers members)

/-- The Number body of the last element, the copy `duplicated` appends. -/
private def lastNumberMembers (members : List (String × Json)) (elements : List Json) : List Json :=
  elements.modify (elements.length - 1) (withNumberMembers members)

private def withoutRule (elements : List Json) : List Json := elements.filter (nameOf · != some "RefCheck")

private def withGroupMember (key : String) (value : Json) : List Json → List Json :=
  onNamed "Items" fun items => items.setObjVal! "Group" ((items.getObjValD "Group").setObjVal! key value)

private def secondRoot (name : String) : Json :=
  groupElement s!"root-{name}" name []
    [named "Field" s!"{name}-note" "Note" [("fieldType", Json.mkObj [("type", "StringType")])],
      ruleElement s!"{name}-rule" "NoteCheck" "FieldFilled(Note)" "../Note"]

/-- A witness edits the root group's elements, then the root group itself, and adds roots after it. -/
private structure Witness where
  elements : List Json → List Json := id
  root : Json → Json := id
  extraRoots : List Json := []

private def Witness.json (witness : Witness) : Json :=
  modelOf (witness.root (withChildren witness.elements policy) :: witness.extraRoots)

/-- The edits in order, the first one first. -/
private def edits (changes : List (List Json → List Json)) (elements : List Json) : List Json :=
  changes.foldl (fun elements change => change elements) elements

private def rootNamed (name : Json) (root : Json) : Json := root.setObjVal! "name" name

/-! ## What the readers and static checks draw -/

private def compile : StringPatternCompiler := fun _ => .compiled fun _ => true

private def converterClass : String → Option String
  | "codeless:root-group-name-missing" => some "RK_ROOT_GROUP_NAME_MISSING"
  | "codeless:element-name-missing" => some "RK_ELEMENT_NAME_MISSING"
  | "codeless:child-name-duplicate" => some "RK_CHILD_NAME_DUPLICATE"
  | "codeless:computed-field-not-specified" => some "RK_COMPUTED_FIELD_NOT_SPECIFIED"
  | "codeless:computed-field-not-found" => some "RK_COMPUTED_FIELD_NOT_FOUND"
  | "codeless:type-definition-not-found" => some "RK_TYPE_DEFINITION_NOT_FOUND"
  | _ => none

/-- A declaration-walk label as the oracle names its class; any other label stays as it is, so a class
the oracle does not list shows. -/
private def declarationClass (label : String) : String :=
  match converterClass label with
  | some class_ => class_
  | none => if label == "codeless:member-above-14" then "RK_MEMBER_ABOVE_SCALE_LIMIT" else label

private def consistencyClass : String → String
  | "codeless:element-name-empty" => "RK_NAME_EMPTY"
  | "codeless:computed-field-empty" => "RK_COMPUTED_FIELD_EMPTY"
  | "codeless:typedef-reference-empty" => "RK_TYPE_REFERENCE_EMPTY"
  | "codeless:error-entity-not-set" => "RK_ERROR_ENTITY_EMPTY"
  | other => other

/-- The classes of a refused rule or computation. A refusal with no class shows as such. -/
private def refusalClasses (refusal : Refusal) : List String :=
  match refusal.kernelClasses with
  | [] => [s!"unclassed {refusal.construct}"]
  | classes => classes

/-- Whether the computations of the model form a calculation cycle, by the plan the Kernel sorts first. -/
private def cycle (model : DmModel) : Bool :=
  match model.computations.mapM fun computation => (lowerComputation model.flat .english computation).toOption with
  | none => false
  | some lowered =>
      match certifyAuthoredMixedComputationPlan
          (lowered.map fun (_, computation) => computation.toMixedStep builtinStringPatternCompiler) with
      | .error (.cycle _ _) => true
      | _ => false

/-- The classes the rules and computations of a model draw. A model whose flat validation refuses judges
none, which is no class. -/
private def staticClasses (model : DmModel) : List String :=
  if !model.flat.validate.isOk then [] else
  model.rules.flatMap (fun rule => match checkValidationRule model .english rule with
    | .ok _ => []
    | .error refusal => refusalClasses refusal) ++
  model.computations.flatMap (fun computation => match checkComputation model .english computation with
    | .ok _ => []
    | .error refusal => refusalClasses refusal) ++
  if cycle model then ["MVK_ERROR_CALC_CYCLE"] else []

private def sentenceLabels (labels : List String) : List String :=
  (labels.filter (converterClass · |>.isSome)).mergeSort (· ≤ ·)

/-- What each reader makes of a model; `none` when it leaves no model. The built model is its refusals and
the classes its rules and computations draw. -/
private structure Observed where
  walk : Option (List String)
  consistency : Option (List String)
  built : Option (List String × List String)

private def observe (json : Json) : Observed where
  walk := match fieldTypeDeclarationNotifications json compile with
    | .ok labels => if labels.any (·.1 == modelNotBuiltLabel) then none else some (labels.map (·.1))
    | .error _ => none
  consistency := match checkModelConsistency json with
    | .ok (.checked notifications) => some (notifications.map (·.kind.observedLabel))
    | _ => none
  built := match readModelWithAdmission json with
    | .ok model => some (model.refusals.map (·.2), staticClasses model)
    | .error _ => none

/-- The combined class set of a model, or the one `UNBUILT` class when all three readers leave no model. A
model one reader builds and another does not shows the readers apart, as a class no row expects. -/
private def classes (json : Json) : List String :=
  let observed := observe json
  let missing := [observed.walk.isNone, observed.consistency.isNone, observed.built.isNone]
  if missing.all id then ["UNBUILT"]
  else if missing.any id then [s!"SPLIT {missing}"]
  else
    let walk := (observed.walk.getD []).map declarationClass
    let consistency := (observed.consistency.getD []).map consistencyClass
    let (refusals, statics) := observed.built.getD ([], [])
    ((walk ++ consistency ++ refusals.map declarationClass ++ statics).eraseDups).mergeSort (· ≤ ·)

/-- The converter's sentences, in the declaration walk and in the model reader's refusals, each reader's
sorted. -/
private def sentences (json : Json) : List String × List String :=
  let observed := observe json
  (sentenceLabels (observed.walk.getD []), sentenceLabels ((observed.built.getD ([], [])).1))

/-! ## The oracle's witnesses -/

private def row (label : String) (witness : Witness) (expected : List String) :
    String × Json × List String :=
  (label, witness.json, expected.mergeSort (· ≤ ·))

private def ghostRule : List Json → List Json := withRule "Broken" noSuchField "../Ref"

private def emptyRoot : Witness :=
  { root := rootNamed (.str ""), elements := withoutRule }

private def rows : List (String × Json × List String) := [
  row "the base" {} [],
  row "a field named with a space" { elements := renamed "Code" " " } ["RK_ELEMENT_NAME_MISSING"],
  row "a field named with a space, beside a rule naming no field"
    { elements := edits [renamed "Code" " ", ghostRule] } ["RK_ELEMENT_NAME_MISSING", "MVK_INVALID_ENTITY"],
  row "a field with an empty name" { elements := renamed "Code" "" } ["RK_ELEMENT_NAME_MISSING", "RK_NAME_EMPTY"],
  row "a field with no name"
    { elements := onNamed "Code" (dropMember · "name") } ["RK_ELEMENT_NAME_MISSING", "RK_NAME_EMPTY"],
  row "a field whose name is null"
    { elements := onNamed "Code" (·.setObjVal! "name" .null) } ["RK_ELEMENT_NAME_MISSING", "RK_NAME_EMPTY"],
  row "a field whose name is an object"
    { elements := onNamed "Code" (·.setObjVal! "name" (Json.mkObj [])) } ["UNBUILT"],
  row "a field whose name is an array"
    { elements := onNamed "Code" (·.setObjVal! "name" (Json.arr #[])) } ["UNBUILT"],
  row "a group with no name, holding a rule naming no field"
    { elements := edits [inItems (withRule "Inner" noSuchField "../Label"), onNamed "Items" (dropMember · "name")] }
    ["RK_ELEMENT_NAME_MISSING", "RK_NAME_EMPTY"],
  row "a rule with no name, naming no field"
    { elements := edits [ghostRule, onNamed "Broken" (dropMember · "name")] }
    ["RK_ELEMENT_NAME_MISSING", "RK_NAME_EMPTY"],
  row "a field typed by a type reference with no id" { elements := typedBy "Code" none }
    ["RK_TYPE_DEFINITION_NOT_FOUND", "RK_TYPE_REFERENCE_EMPTY"],
  row "a group named with a space, holding a rule naming no field"
    { elements := edits [inItems (withRule "Inner" noSuchField "../Label"), renamed "Items" " "] }
    ["RK_ELEMENT_NAME_MISSING"],
  row "a rule named with a space, naming no field"
    { elements := edits [ghostRule, renamed "Broken" " "] } ["RK_ELEMENT_NAME_MISSING"],
  row "a root group named with a space, holding a rule naming no field"
    { elements := ghostRule, root := rootNamed (.str " ") } ["RK_ROOT_GROUP_NAME_MISSING"],
  row "a root group with an empty name, beside its rule" { root := rootNamed (.str "") } ["UNBUILT"],
  row "a root group with an empty name, alone" emptyRoot ["RK_ROOT_GROUP_NAME_MISSING", "RK_NAME_EMPTY"],
  row "a root group with no name, beside its rule" { root := (dropMember · "name") }
    ["RK_ROOT_GROUP_NAME_MISSING", "RK_NAME_EMPTY"],
  row "a root group whose name is null, beside its rule" { root := rootNamed .null }
    ["RK_ROOT_GROUP_NAME_MISSING", "RK_NAME_EMPTY"],
  row "a root group with an empty name, its rule in a nested group"
    { emptyRoot with elements := edits [withoutRule, inItems (withRule "LabelCheck" "FieldFilled(Label)" "../Label")] }
    ["UNBUILT"],
  row "a root group with an empty name, holding a computation"
    { emptyRoot with elements := edits [withoutRule, withComputation "../Total" "1"] } ["UNBUILT"],
  row "a root group with an empty name, its rule with an empty error path"
    { emptyRoot with elements := edits [withoutRule, withRule "Pathless" "FieldFilled(Code)" ""] }
    ["RK_ROOT_GROUP_NAME_MISSING", "RK_NAME_EMPTY", "RK_ERROR_ENTITY_EMPTY"],
  row "a root group with an empty name, its group indexed by a field"
    { emptyRoot with elements := edits [withoutRule, withGroupMember "indexFieldName" "Label"] } ["UNBUILT"],
  row "a root group with an empty name, its group sorted by a field"
    { emptyRoot with elements := edits [withoutRule,
      withGroupMember "sortFields" (Json.arr #[Json.mkObj [("name", "Label")]])] }
    ["UNBUILT"],
  row "a root group with an empty name, beside a named root holding a rule"
    { emptyRoot with extraRoots := [secondRoot "Claim"] } ["RK_ROOT_GROUP_NAME_MISSING", "RK_NAME_EMPTY"],
  row "a field named with a space, its fraction count above the scale limit"
    { elements := edits [numberMembers "Fee" [("maxFractionalDigits", toJson (20 : Nat))], renamed "Fee" " "] }
    ["RK_ELEMENT_NAME_MISSING"],
  row "a field named with a space, its minimum above its maximum"
    { elements := edits [numberMembers "Fee" [("minValue", toJson (9 : Nat)), ("maxValue", toJson (1 : Nat))],
      renamed "Fee" " "] }
    ["RK_ELEMENT_NAME_MISSING"],
  row "a field named with a space, beside a computation cycle"
    { elements := edits [renamed "Code" " ", withComputation "../Total" "[Fee]" "TotalCalc",
      withComputation "../Fee" "[Total]" "FeeCalc"] }
    ["RK_ELEMENT_NAME_MISSING", "MVK_ERROR_CALC_CYCLE"],
  row "a computation with an empty target" { elements := withComputation "" "1" }
    ["RK_COMPUTED_FIELD_NOT_SPECIFIED", "RK_COMPUTED_FIELD_EMPTY"],
  row "a computation with an unresolvable target, naming no field"
    { elements := withComputation "../NoSuchTotal" "[NoSuchFieldAnywhere]" } ["RK_COMPUTED_FIELD_NOT_FOUND"],
  row "a computation with an unresolvable target, beside a rule naming no field"
    { elements := edits [withComputation "../NoSuchTotal" "1", ghostRule] }
    ["RK_COMPUTED_FIELD_NOT_FOUND", "MVK_INVALID_ENTITY"],
  row "a computation whose target is named with a space"
    { elements := edits [renamed "Total" " ", withComputation "../ " "1"] } ["UNBUILT"],
  row "a computation whose target lies in a group named with a space"
    { elements := edits [renamed "Items" " ", withComputation "../ /Label" "1"] } ["UNBUILT"],
  row "a computation whose target is the later of two fields of one name"
    { elements := edits [duplicated "Total", withComputation "../Total" "1"] } ["RK_CHILD_NAME_DUPLICATE"],
  row "a rule whose error field is named with a space"
    { elements := edits [renamed "Code" " ", withRule "BlankErrorField" "FieldFilled(Ref)" "../ "] }
    ["RK_ELEMENT_NAME_MISSING", "MVK_ERROR_FIELD_MISSING", "MVK_MISSING_ERROR_FIELD"],
  row "a field typed by an undeclared type definition" { elements := typedBy "Code" (some "Ghost") }
    ["RK_TYPE_DEFINITION_NOT_FOUND"],
  row "a field typed by an undeclared type definition, named by a rule"
    { elements := edits [typedBy "Code" (some "Ghost"), withRule "CodeCheck" "FieldFilled(Code)" "../Code"] }
    ["RK_TYPE_DEFINITION_NOT_FOUND"],
  row "two fields of one name" { elements := duplicated "Code" } ["RK_CHILD_NAME_DUPLICATE"],
  row "two fields of one name, the first's fraction count above the scale limit"
    { elements := edits [numberMembers "Fee" [("maxFractionalDigits", toJson (20 : Nat))], duplicated "Fee",
      lastNumberMembers [("maxFractionalDigits", toJson (0 : Nat))]] }
    ["RK_CHILD_NAME_DUPLICATE", "RK_MEMBER_ABOVE_SCALE_LIMIT"],
  row "two fields of one name, the second's fraction count above the scale limit"
    { elements := edits [duplicated "Fee", lastNumberMembers [("maxFractionalDigits", toJson (20 : Nat))]] }
    ["RK_CHILD_NAME_DUPLICATE"],
  row "two rules of one name, the first naming no field"
    { elements := edits [withRule "Twin" noSuchField "../Ref", withRule "Twin" "FieldFilled(Ref)" "../Ref"] }
    ["RK_CHILD_NAME_DUPLICATE", "MVK_INVALID_ENTITY"],
  row "two rules of one name, the second naming no field"
    { elements := edits [withRule "Twin" "FieldFilled(Ref)" "../Ref", withRule "Twin" noSuchField "../Ref"] }
    ["RK_CHILD_NAME_DUPLICATE"]]

/-- The labels of the rows whose class set differs from the oracle's, or whose two readers state different
converter sentences. -/
private def disagreeing : List String :=
  rows.filterMap fun (label, json, expected) =>
    if classes json == expected && (sentences json).1 == (sentences json).2 then none else some label

/-- Every row of the oracle agrees, the rule reporting at a field the converter dropped included: its error
target names nothing, so the declaration gate draws the pair and withholds the condition. -/
example : disagreeing = [] := by native_decide

/- The basic check reports the converter's unbuilt model as its one build failure, ahead of every element's. -/
example : (rows.filter (·.1 == "a root group with an empty name, beside its rule")).map
    (fun (_, json, _) => (checkModelConsistency json).toOption) =
    [some (.notBuilt [] .validationModelUnbuilt)] := by native_decide

/-! ## How often each sentence is stated

The converter states each sentence once per text and source: a blank name once per holding group whatever
the kinds, and a shared name once per kind of later child. By text alone the two-groups row would be one
sentence, and by path alone the field-group-rule row would be. -/

private def twin (elements : List Json) : List Json := withRule "Twin" "FieldFilled(Ref)" "../Ref" elements

private def countRows : List (String × Json × List String) :=
  let duplicate := "codeless:child-name-duplicate"
  let missing := "codeless:element-name-missing"
  [("three rules of one name", ({ elements := edits [twin, twin, twin] } : Witness).json, [duplicate]),
   ("a field and two rules of its name",
    ({ elements := edits [withRule "Code" "FieldFilled(Ref)" "../Ref", withRule "Code" "FieldFilled(Ref)" "../Ref"] } :
      Witness).json, [duplicate]),
   ("a field, a group and a rule of one name",
    ({ elements := edits [renamed "Items" "Code", withRule "Code" "FieldFilled(Ref)" "../Ref"] } : Witness).json,
    [duplicate, duplicate]),
   ("two fields named with a space",
    ({ elements := edits [renamed "Code" " ", renamed "Ref" " "] } : Witness).json, [missing]),
   ("a field and a rule named with a space",
    ({ elements := edits [renamed "Code" " ", withRule " " "FieldFilled(Ref)" "../Ref"] } : Witness).json, [missing]),
   ("a field named with a space in each of two groups",
    ({ elements := edits [renamed "Code" " ", inItems (renamed "Label" " ")] } : Witness).json, [missing, missing])]

/-- The rows whose sentences differ from the oracle's count in either reader. -/
private def miscounted : List String :=
  countRows.filterMap fun (label, json, expected) =>
    if sentences json == (expected, expected) then none else some label

example : miscounted = [] := by native_decide

end A12Kernel.Dm.ConverterSentenceLocks
