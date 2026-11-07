import Lean.Data.Json
import A12Kernel.Elaboration.DeclarationAdmission
import A12Kernel.Reference.Dm.ElementBinding
import A12Kernel.Reference.Dm.ModelFrame

/-! # The validation-model converter of kernel 31.1.1

The Kernel's code-generation rule first converts a model into its validation model. Kernel 30.8.1 threw
on a declaration it could not convert, so the model was not built. Kernel 31.1.1 states a codeless
sentence and goes on without the declaration and its subtree (a12-dmkits
`CheckerConverterSentenceAgreementTest` at `1124b523f`, kernel 31.1.1; peer KF652). The rule's other
checks, the rule and computation static checks included, then walk the converted model, while the basic
check and the other consistency checks still walk the authored one. `convertModel` is that conversion,
over a model whose members are already bound (`bindModelMembers`); the three DM readers each take what
they read from it.

Visited in document order, a name is *blank* by `ExecutableDeclaration.blank`, and an absent or `null`
name reads as the empty name:

* a root group named blank draws `rootGroupNameMissing` at its own path and is dropped with its subtree;
* a child named blank draws `elementNameMissing` at the holding group's path and is dropped with its
  subtree;
* a field typed by a `TypeDefType` whose id is absent, empty or names no type definition draws
  `typeDefinitionNotFound` and stays as a plain String;
* a computation whose `computedFieldRelPath` is empty draws `computedFieldNotSpecified`, and one whose
  path resolves on the authored model to no field draws `computedFieldNotFound`, each at the computation,
  which is dropped;
* a child naming what an earlier kept child of its group already names draws `childNameDuplicate` at its
  own path and is dropped, after its own subtree has been converted, so a dropped group still states its
  sentences. A computation dropped above never meets this check.

Identical sentences collapse on one source, as the Kernel keeps one per text and source: a blank name is
stated once per holding group whatever the kinds, and a shared name once per kind of later child.

A model that builds no validation model at all is `unbuilt`, measured for two compositions and not
modelled by any mechanism: a root group whose `name` is present as exactly the empty text and holds, at
any depth, a rule, a computation, a group with an index field or a group with sort fields, an empty
reference in any of them included on kernel 31.3.1 (31.3.1 Letter J §8), where 31.1.1 built a rule with an
empty error path; a kept computation whose target is a field the conversion dropped; and, on kernel 31.3.1, a
computation whose target's leading `..` run climbs past the technical model root (a12-dmkits KF679,
`../../../Customer/Name` from a computation in a root group; the same climb in an error target is
unmeasured). That a blank, absent or `null` root name, only fields, or a rule in a sibling named root
builds is measured too. That a target lying in a duplicate or blank-root group is unbuilt is derived, not measured.

Sentence paths are derived from the element each sentence is stated for, and no measurement observes
them: the oracle compares sets of classes. A computed-field path is read lexically from the computation,
`..` climbing from it to its group, as `lexicalErrorPath` reads an error path, plus the absolute spelling;
a path spelled otherwise is left to the target resolution that refuses it. A path landing on a group or a
rule counts as naming no field, measured for a fixed and a repeatable group on kernel 31.3.1 (31.3.1 Letter J
§8) and for a rule, and a name resolves to the first element of that name. The lexical reading and the first
element are derived, not measured. Peer names for the sentences, for comments only: `RK_ROOT_GROUP_NAME_MISSING`,
`RK_ELEMENT_NAME_MISSING`, `RK_CHILD_NAME_DUPLICATE`, `RK_COMPUTED_FIELD_NOT_SPECIFIED`,
`RK_COMPUTED_FIELD_NOT_FOUND`, `RK_TYPE_DEFINITION_NOT_FOUND`.
-/

namespace A12Kernel.Dm

open Lean A12Kernel

/-- A sentence the converter states for a declaration it drops or repairs. -/
inductive ConverterSentence where
  | rootGroupNameMissing
  | elementNameMissing
  | childNameDuplicate
  | computedFieldNotSpecified
  | computedFieldNotFound
  | typeDefinitionNotFound
  deriving Repr, DecidableEq

/-- The label the declaration walk and the model reader's refusals give the sentence. The sentences have no
Kernel code, so each is a codeless class named by itself. -/
def ConverterSentence.label : ConverterSentence → String
  | rootGroupNameMissing => "codeless:root-group-name-missing"
  | elementNameMissing => "codeless:element-name-missing"
  | childNameDuplicate => "codeless:child-name-duplicate"
  | computedFieldNotSpecified => "codeless:computed-field-not-specified"
  | computedFieldNotFound => "codeless:computed-field-not-found"
  | typeDefinitionNotFound => "codeless:type-definition-not-found"

/-- A model as the Kernel's validation model holds it. -/
structure ConvertedModel where
  /-- The root groups that remain, converted. -/
  roots : Array Json
  /-- Each sentence with the path of the element it is stated for, collapsed, in document order. -/
  sentences : List (ConverterSentence × List String)
  /-- Whether the conversion builds no model at all. -/
  unbuilt : Bool

/-- A sentence with the discriminator under which identical sentences collapse. -/
private structure Drawn where
  sentences : Array (ConverterSentence × List String × String) := #[]
  /-- The resolved names of each kept computation's target. -/
  targets : Array (List String) := #[]
  /-- Whether a computation's target climbs past the technical model root. -/
  pastModelRoot : Bool := false

private def draw (sentence : ConverterSentence) (path : List String) (discriminator : String := "") :
    StateM Drawn Unit :=
  modify fun drawn =>
    if drawn.sentences.contains (sentence, path, discriminator) then drawn
    else { drawn with sentences := drawn.sentences.push (sentence, path, discriminator) }

private def kindOf (element : Json) : Option String := (element.getObjValAs? String "type").toOption

private def groupChildren (element : Json) : List Json :=
  match elementBody element "Group" with
  | .ok body => (groupElements body).toOption.getD []
  | .error _ => []

/-- The element a path of names reaches, taking the first element of each name below the one before. -/
private def descend : Option Json → List String → Option Json
  | found, [] => found
  | none, _ => none
  | some element, name :: rest =>
      if kindOf element == some "Group" then
        descend ((groupChildren element).find? (elementName · == name)) rest
      else none

private def resolveField (roots : List Json) : List String → Option Json
  | [] => none
  | name :: rest =>
      (descend (roots.find? (elementName · == name)) rest).filter (kindOf · == some "Field")

/-- The names a computed-field path spells, or `none` for a spelling this reading does not know. The first
`..` climbs from the computation to its group, and a path that climbs above the document or holds an empty
segment is unread. -/
private def spelledNames? (holder : List String) (text : String) : Option (List String) :=
  let segments := text.splitOn "/"
  if segments.head? == some ".." then
    (segments.foldlM (init := holder ++ [""]) fun path segment =>
      if segment == ".." then (if path.isEmpty then none else some path.dropLast)
      else if segment.isEmpty then none else some (path ++ [segment])).filter (!·.isEmpty)
  else if text.startsWith "/" then
    let names := segments.drop 1
    if names.isEmpty || names.any (·.isEmpty) then none else some names
  else none

/-- Whether a computed-field path's leading `..` run climbs past the technical model root, the first step
climbing from the computation to its group. -/
private def climbsPastModelRoot (holder : List String) (text : String) : Bool :=
  holder.length + 1 < leadingUpSteps text

/-- What the converter makes of a computation: dropped, or kept with the names its target resolved to when
that spelling is read. -/
private inductive ComputationOutcome where
  | dropped
  | kept (target : Option (List String))

private def convertComputation (authored : List Json) (holder path : List String) (body : Json) :
    StateM Drawn ComputationOutcome := do
  let text := (body.getObjValAs? String "computedFieldRelPath").toOption.getD ""
  if text.isEmpty then
    draw .computedFieldNotSpecified path
    return .dropped
  match spelledNames? holder text with
  | none =>
      if climbsPastModelRoot holder text then modify fun drawn => { drawn with pastModelRoot := true }
      return .kept none
  | some names =>
      if (resolveField authored names).isNone then
        draw .computedFieldNotFound path
        return .dropped
      return .kept (some names)

private def plainStringType : Json :=
  Json.mkObj [("type", "StringType"), ("StringType", Json.mkObj [])]

/-- A field whose type definition is missing is kept as a plain String. -/
private def convertField (definitions : List String) (path : List String) (element body : Json) :
    StateM Drawn Json := do
  let some fieldType := (body.getObjVal? "fieldType").toOption | return element
  if (fieldType.getObjValAs? String "type").toOption != some "TypeDefType" then return element
  let reference := (fieldType.getObjVal? "TypeDefType").toOption.getD (Json.mkObj [])
  let id := (reference.getObjValAs? String "typeDefinitionId").toOption.getD ""
  if id.isEmpty || !definitions.contains id then
    draw .typeDefinitionNotFound path
    return element.setObjVal! "Field" (body.setObjVal! "fieldType" plainStringType)
  return element

private def withChildren (group body : Json) (children : Array Json) : Json :=
  group.setObjVal! "Group" (body.setObjVal! "elements" (Json.arr children))

/-- The converted children of a group, in order. `fuel` bounds the nesting depth, which never exceeds the
characters of the text that holds the model. -/
private def convertChildren (definitions : List String) (authored : List Json) :
    Nat → List String → List Json → StateM Drawn (Array Json)
  | 0, _, _ => pure #[]
  | fuel + 1, holder, children => do
      let mut kept : Array Json := #[]
      let mut names : List String := []
      for child in children do
        let name := elementName child
        let some kind := (kindOf child).filter elementKinds.contains | do kept := kept.push child; continue
        if ExecutableDeclaration.blank name then
          draw .elementNameMissing holder
          continue
        let path := holder ++ [name]
        let body := (elementBody child kind).toOption.getD (Json.mkObj [])
        let mut outcome : Option Json := some child
        let mut target : Option (List String) := none
        match kind with
        | "Group" =>
            outcome := some (withChildren child body
              (← convertChildren definitions authored fuel path (groupChildren child)))
        | "Field" => outcome := some (← convertField definitions path child body)
        | "Computation" =>
            match ← convertComputation authored holder path body with
            | .dropped => outcome := none
            | .kept resolved => target := resolved
        | _ => pure ()
        let some converted := outcome | continue
        if names.contains name then
          draw .childNameDuplicate path kind
          continue
        kept := kept.push converted
        names := names ++ [name]
        if let some resolved := target then
          modify fun drawn => { drawn with targets := drawn.targets.push resolved }
      pure kept

private def convertRoots (definitions : List String) (authored : List Json) (fuel : Nat) :
    StateM Drawn (Array Json) := do
  let mut kept : Array Json := #[]
  for root in authored do
    let name := elementName root
    if ExecutableDeclaration.blank name then
      draw .rootGroupNameMissing [name]
      continue
    if kindOf root != some "Group" then kept := kept.push root; continue
    let body := (elementBody root "Group").toOption.getD (Json.mkObj [])
    kept := kept.push (withChildren root body (← convertChildren definitions authored fuel [name] (groupChildren root)))
  pure kept

/-- Whether a root group's authored subtree holds a rule, a computation, or a group ordering its rows. A
group's index field counts when present and not `null`, the empty name included. -/
private def holdsOrderedMember : Nat → Json → Bool
  | 0, _ => false
  | fuel + 1, element =>
      match kindOf element with
      | some "Rule" | some "Computation" => true
      | some "Group" =>
          let body := (elementBody element "Group").toOption.getD (Json.mkObj [])
          let indexed := match body.getObjVal? "indexFieldName" with
            | .ok .null | .error _ => false
            | .ok _ => true
          let sorted := match body.getObjVal? "sortFields" with
            | .ok (.arr sorts) => !sorts.isEmpty
            | _ => false
          indexed || sorted || (groupChildren element).any (holdsOrderedMember fuel)
      | _ => false

/-- Convert a model whose members are bound. -/
def convertModel (frame : ModelFrame) : ConvertedModel :=
  let fuel := frame.nestingFuel
  let authored := frame.rootGroups.toList
  let definitions := frame.typeDefinitions.toList.filterMap fun definition =>
    (definition.getObjValAs? String "id").toOption
  let (roots, drawn) := (convertRoots definitions authored fuel).run {}
  let emptyNamedRoot := authored.any fun root =>
    (match root.getObjVal? "name" with | .ok (.str "") => true | _ => false) && holdsOrderedMember fuel root
  let strandedTarget := drawn.targets.any fun path => (resolveField roots.toList path).isNone
  { roots, sentences := drawn.sentences.toList.map fun (sentence, path, _) => (sentence, path)
    unbuilt := emptyNamedRoot || strandedTarget || drawn.pastModelRoot }

end A12Kernel.Dm
