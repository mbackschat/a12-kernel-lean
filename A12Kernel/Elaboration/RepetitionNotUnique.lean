import A12Kernel.Elaboration.StarNumber
import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.SemanticIndex
import A12Kernel.Semantics.EnumerationRepetitionNotUnique
import A12Kernel.Semantics.RepetitionNotUnique

/-! # Checked nested heterogeneous `RepetitionNotUnique` construction

This boundary resolves one nonempty typed composite key along a single group branch, chooses the default or explicit reference group, expands the deepest key path through the existing star topology, retains each ancestor component's own checked path prefix, removes partially irrelevant composite-key rows before classification, and delegates the resulting ordered rows to the resolved RNU relation. Number, ordinary String, and direct stored-Enumeration components are its legal key domain. Temporal, Boolean/Confirm raw-spelling identity, and prepared custom-String keys are rejected. A surrounding rule supplies one complete environment per deepest row; the topology's existing bound prefix partitions nested default and explicit `@From` scopes without another address model.
-/

namespace A12Kernel

inductive SurfaceRepetitionNotUniqueScope where
  | default
  | from (group : SurfaceGroupReference)
  deriving Repr, DecidableEq

/- Whether the selected reference group was inferred from the key path or named by an authored `@From` clause. The resolved group can be identical in both cases, but only the authored form contributes its subtree to rule reference detection. -/
inductive RepetitionNotUniqueReferenceOrigin where
  | inferredDefault
  | authoredFrom
  deriving Repr, DecidableEq

namespace SurfaceRepetitionNotUniqueScope

def referenceOrigin : SurfaceRepetitionNotUniqueScope →
    RepetitionNotUniqueReferenceOrigin
  | .default => .inferredDefault
  | .from _ => .authoredFrom

end SurfaceRepetitionNotUniqueScope

structure SurfaceRepetitionNotUniqueSource where
  firstKey : SurfaceFieldPath
  restKeys : List SurfaceFieldPath
  scope : SurfaceRepetitionNotUniqueScope := .default
  deriving Repr, DecidableEq

/-- The exact reviewed sole RNU key with a literal text semantic-index suffix. Composite keys,
field-valued keys, other literal domains, and runtime duplicate evaluation have no representation
here ([checkpoint](../../docs/SOURCES.md#src-pr2-semantic-index-carrier-matrix)). -/
structure SurfaceRepetitionNotUniqueSemanticIndexUse where
  target : SurfaceFieldPath
  token : String
  deriving Repr, DecidableEq

inductive RepetitionNotUniqueElabError where
  /-- The model itself failed validation, kept apart from `resolve` so a model defect never reaches
  the key's resolver projection. -/
  | model (error : ResolveError)
  | resolve (error : ResolveError)
  | scope (error : SingleGroupElabError)
  /-- A key the reading-scope walk refuses. -/
  | keyReadRefused (path : List String) (unbound : UnboundOperandLevel)
  /-- The first key named twice: a field by its declaration, a group by its path. -/
  | duplicateKey (path : List String)
  /-- A group key holding another key of the list, the root beside any key included. -/
  | nestedGroupKey (group : GroupPath)
  | groupKey (group : GroupPath)
  | keyPathMismatch (expected actual : GroupPath)
  /-- Without a scope, two keys whose lowest repeatable groups lie on no one hierarchy path. -/
  | keysOffOnePath (left right : GroupPath)
  /-- Without a scope, a key whose group lies outside the rule group. -/
  | keyOutsideRuleGroup (keyPath : List String)
  /-- Keys whose own groups leave one hierarchy path although their repeatable groups do not, or
  keys inside a scope that leave it. The Kernel asks no shared-path gate of either shape; this theory
  needs one path to build the row topology. -/
  | keyGroupsDiverge (left right : GroupPath)
  | unsupportedKeyKind (path : List String) (actual : SurfaceScalarKind)
  | rawStringValue (path : List String)
  | customStringRequiresPreparedChecking (path : List String)
  | missingReferenceGroup (keyPath : List String)
  /-- A rule at a repeatable root whose keys all sit directly in a root group. The Kernel skips its
  repeatable-group gate for this shape, read from its source and measured by no row, and this theory
  has no reference group to evaluate it against. -/
  | repeatableRootKeys (keyPath : List String)
  /-- Without a scope, a key above the default reference group the deepest key selects. -/
  | keyOutsideDefaultReferenceGroup (referenceGroup keyGroup : GroupPath)
  | scopeIsField (path : List String)
  /-- A scope naming a group with no field anywhere in its subtree. -/
  | scopeIsEmpty (path : GroupPath)
  /-- A scope the reading-scope walk refuses. -/
  | scopeReadRefused (path : GroupPath) (unbound : UnboundOperandLevel)
  | referenceGroupNotRepeatable (path : GroupPath)
  | referenceGroupDoesNotContainKey (referenceGroup keyGroup : GroupPath)
  | path (error : StarPathElabError)
  | incoherentCore
  deriving Repr, DecidableEq

namespace RepetitionNotUniqueElabError

/-- Project the measured `RepetitionNotUnique` key-admission classes. Every key is read first, a key that does not resolve drawing the shared resolver's class ([checkpoint](../../docs/sources/path-resolution-class-probes.md#src-pattern-and-key-resolver-classes)) and one the reading-scope walk refuses drawing the walk's; the list's duplicate gate comes next, a key named twice before a group holding another key ([`kf388`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf388)), then its own gates, each over the whole list, then exactly one branch: with `@From` the scope is read and must be a group that repeats and holds every key, without it the shared-path, rule-group and repeatable-group gates run ([inbound](../../docs/SOURCES.md#inbound-2026-09-26f-gate-order)).

Three shapes draw `MVK_REPEATABLE_GROUP_MISSING`: a second key in a nonrepeatable group, a sole key whose group is not repeatable, and a rule already placed at the repeated group, unless that group is a repeatable root holding every key directly. The walk's missing-star class is measured on a key and on a scope; its index and containment classes on either are the shared read's, and a group named twice or the root beside a key takes the duplicate class measured on the other list carriers, assumptions [SG9](../../docs/gaps/paths-and-groups.md#gap-sg9) records. An empty scope claims no class: the measured one is a fixed group ([inbound](../../docs/SOURCES.md#inbound-2026-09-26h-empty-scope)), which this model cannot hold, while the empty repeatable group it can hold meets the walk as well, and no row fixes which of the two answers first.

Every remaining form is named rather than caught by a wildcard, so a new refusal cannot be absorbed into this project's boundary without a decision. A custom String key needing prepared checking and an unsupported key kind are this theory's value-reading limits, diverging key groups its topology limit, and a repeatable root's direct keys its reference-group limit, not Kernel gates. `model` is routing rather than a key refusal, and `incoherentCore` is the unreachable-by-construction arm. The rest are Kernel refusals whose class this carrier has no evidence for. -/
def diagnostic? : RepetitionNotUniqueElabError → Option KernelStaticDiagnostic
  | .resolve error => error.diagnostic?
  | .keyReadRefused _ unbound | .scopeReadRefused _ unbound => unbound.diagnostic?
  | .duplicateKey _ => some .duplicateParam1
  | .nestedGroupKey _ => some .duplicateParam2
  | .groupKey _ => some .noGroupsAllowed
  | .rawStringValue _ => some .rawTypeOperandInvalid
  | .scopeIsField _ => some .noFieldsAllowed
  | .referenceGroupNotRepeatable _ => some .groupNotRepeatable
  | .referenceGroupDoesNotContainKey _ _ => some .entityNotInGroup
  | .keysOffOnePath _ _ => some .notInSamePath
  | .keyOutsideRuleGroup _ => some .notInRuleGroup
  | .keyPathMismatch _ _ | .missingReferenceGroup _ =>
      some .repeatableGroupMissing
  | .model _ | .scope _ | .scopeIsEmpty _ | .keyGroupsDiverge _ _ | .repeatableRootKeys _
  | .keyOutsideDefaultReferenceGroup _ _
  | .unsupportedKeyKind _ _ | .customStringRequiresPreparedChecking _
  | .path _ | .incoherentCore => none

end RepetitionNotUniqueElabError

/-- One ordinary String key certified against the same star plan used by every component. Prepared custom Strings require SG1's checked-document overlay and are not admitted by this raw-cell route. -/
structure CheckedRepetitionStringKey (model : FlatModel) where
  source : CheckedStarFieldPath model
  field : FlatStringField
  fieldOwned : source.declaration.toStringValueField? = some field

/-- One direct stored-Enumeration key attached to the exact declaration-owned checked token domain. Category access is not part of RNU syntax. -/
structure CheckedRepetitionEnumerationKey (model : FlatModel) where
  source : CheckedStarFieldPath model
  declaration : CheckedEnumerationDeclaration
  fieldOwned : source.declaration.policy.kind = .enumeration
  enumerationOwned :
    source.declaration.enumeration = some declaration.declaration

namespace CheckedRepetitionEnumerationKey

/-- RNU always reads the stored token; its plain-field syntax cannot select a category projection. -/
def projection (key : CheckedRepetitionEnumerationKey model) :
    CheckedEnumerationProjection :=
  { declaration := key.declaration
    projectionRef := .stored
    projection := .stored
    projectionChecked := by rfl }

end CheckedRepetitionEnumerationKey

/-- One typed key component. This sum is the extension point for source-verified remaining RNU kinds; it prevents a second homogeneous-key construction path. -/
inductive CheckedRepetitionKey (model : FlatModel) where
  | number (key : CheckedStarNumberSource model)
  | string (key : CheckedRepetitionStringKey model)
  | enumeration (key : CheckedRepetitionEnumerationKey model)

namespace CheckedRepetitionKey

def source : CheckedRepetitionKey model → CheckedStarFieldPath model
  | .number key => key.source
  | .string key => key.source
  | .enumeration key => key.source

def fieldId (key : CheckedRepetitionKey model) : FieldId :=
  key.source.declaration.id

/-- Project one deepest-row environment to the exact repeatable ancestry owned by this key declaration. -/
def environmentPrefix (key : CheckedRepetitionKey model) (environment : Env) : Env :=
  environment.take key.source.path.axes.length

/-- Classify one already-addressed checked cell through the exact typed key owner, applying the key path's structural over-repetition overlay once. -/
def classifyCheckedCell (key : CheckedRepetitionKey model)
    (cell : CheckedCell) (environment : Env) : RepetitionKeyComponent :=
  let keyEnvironment := key.environmentPrefix environment
  match key with
  | .number key =>
      RepetitionKeyComponent.ofNumberValueListCell
        (key.checkedValueListCell .validation cell keyEnvironment)
  | .string key =>
      RepetitionKeyComponent.ofTokenValueListCell
        ((FlatTextFieldOperand.string key.field).checkedValueListCellAt .validation
          (key.source.contextualizeCell keyEnvironment cell))
  | .enumeration key =>
      key.projection.classifyCheckedKeyAt .validation
        (key.source.contextualizeCell keyEnvironment cell)

/-- Classify one caller-checked component through its existing typed star reader after projecting the deepest environment to that component's own ancestry. -/
def classify (key : CheckedRepetitionKey model)
    (read : Env → FieldId → CheckedCell)
    (environment : Env) : RepetitionKeyComponent :=
  let keyEnvironment := key.environmentPrefix environment
  key.classifyCheckedCell
    (read keyEnvironment key.source.declaration.id) environment

end CheckedRepetitionKey

/-- A checked RNU source retains one typed star-classifiable owner per key field. Every owner shares the exact topology plan stored by `firstKey`. -/
structure CheckedRepetitionNotUniqueSource (model : FlatModel) where
  ruleGroup : GroupPath
  referenceGroup : RepeatableGroupDecl
  referenceOrigin : RepetitionNotUniqueReferenceOrigin
  terminalGroup : GroupPath
  topology : CheckedStarPlan
  firstKey : CheckedRepetitionKey model
  restKeys : List (CheckedRepetitionKey model)
  modelWellFormed : model.validate.isOk = true
  referenceGroupOwned : model.repeatableGroups.contains referenceGroup = true
  uniqueKeyFields :
    FieldId.firstDuplicate? ((firstKey :: restKeys).map (·.fieldId)) = none
  terminalGroupOwned :
    (firstKey :: restKeys).any (fun key =>
      key.source.declaration.groupPath == terminalGroup) = true
  keyGroupsOnBranch :
    (firstKey :: restKeys).all (fun key =>
      key.source.declaration.groupPath.isPrefixOf terminalGroup) = true
  keyPathsWithinTopology :
    (firstKey :: restKeys).all (fun key =>
      key.source.path.axes == topology.path.axes.take key.source.path.axes.length) = true
  topologyLevelsOwned :
    topology.path.axes.map (·.level) = model.repeatableScopeForGroupPath terminalGroup
  referenceLevelOwned :
    ((topology.path.axes.drop topology.path.firstStar).head?.map
      (·.level)) = some referenceGroup.level

/-- One otherwise-valid sole RNU key and one valid exact-text semantic-index selection certified as
the same target and reference group before the carrier-specific refusal is projected. It asks no
more of the error field than the key's read does: the refusal is measured with the key itself as
the error field ([checkpoint](../../docs/SOURCES.md#src-pr2-semantic-index-carrier-matrix)) and with
a sibling of it in the key's repeatable group
([inbound](../../docs/SOURCES.md#inbound-2026-09-26f-gate-order)). It supplies no indexed RNU
evaluator. -/
structure CheckedRepetitionNotUniqueSemanticIndexRefusal (model : FlatModel) where
  declaringGroup : GroupPath
  token : String
  source : CheckedRepetitionNotUniqueSource model
  selection : CheckedSemanticIndexSource model
  ruleGroupRetained : (source.ruleGroup == declaringGroup) = true
  referenceGroupSelected : (source.referenceGroup == selection.group) = true
  targetSelected :
    (source.firstKey.source.declaration == selection.targetDeclaration) = true
  keyRetained : (selection.key == .literal (.text token)) = true

inductive RepetitionNotUniqueSemanticIndexRefusalError where
  | repetitionNotUnique (error : RepetitionNotUniqueElabError)
  | semanticIndex (error : SemanticIndexElabError)
  | selectionGroupMismatch (repetition semanticIndex : GroupPath)
  | incoherentCore
  deriving Repr, DecidableEq

/-- One authored key once read: a field, or a path naming a declared group, which the list's own
gate refuses only after every key is read. -/
private inductive RepetitionKeyRead where
  | field (declaration : FlatFieldDecl)
  | group (path : GroupPath)

namespace RepetitionKeyRead

private def groupPath : RepetitionKeyRead → GroupPath
  | .field declaration => declaration.groupPath
  | .group path => path

private def field? : RepetitionKeyRead → Option FlatFieldDecl
  | .field declaration => some declaration
  | .group _ => none

private def group? : RepetitionKeyRead → Option GroupPath
  | .field _ => none
  | .group path => some path

end RepetitionKeyRead

/-- Read one key as any reference is read: resolve it, classing a path that names a group as a group
key rather than as the field miss, then walk it against the rule's reading scope with the error field's
group placing each level it leaves unbound. The walk's missing-star class is measured on a key
([inbound](../../docs/SOURCES.md#inbound-2026-09-26f-gate-order)); its other classes here are the
shared read's by assumption. -/
private def readRepetitionKey (model : FlatModel) (declaringGroup writtenGroup : GroupPath)
    (reference : SurfaceFieldPath) : Except RepetitionNotUniqueElabError RepetitionKeyRead := do
  let (read, path, scope) ←
    match model.resolveFieldDeclarationUnchecked declaringGroup reference with
    | .ok declaration =>
        pure (RepetitionKeyRead.field declaration, declaration.path, declaration.repeatableScope)
    | .error error =>
        let group? := if error.isGroupDisplaceableMiss then
          model.groupNamedBy? declaringGroup reference else none
        match group? with
        | some group => pure (.group group, group, model.repeatableScopeForGroupPath group)
        | none => throw (.resolve error)
  match model.refusedReadLevel? declaringGroup writtenGroup scope with
  | some unbound => throw (.keyReadRefused path unbound)
  | none => pure read

private def readRepetitionKeys (model : FlatModel) (declaringGroup writtenGroup : GroupPath) :
    List SurfaceFieldPath → Except RepetitionNotUniqueElabError (List RepetitionKeyRead)
  | [] => pure []
  | reference :: remaining => do
      pure ((← readRepetitionKey model declaringGroup writtenGroup reference) ::
        (← readRepetitionKeys model declaringGroup writtenGroup remaining))

private def RepetitionKeyRead.path : RepetitionKeyRead → List String
  | .field declaration => declaration.path
  | .group path => path

/-- The first key named twice, in authored order. -/
private def firstDuplicateKey? : List RepetitionKeyRead → Option (List String)
  | [] => none
  | read :: remaining =>
      if remaining.any (·.path == read.path) then some read.path else firstDuplicateKey? remaining

/-- A group key holding another key of the list, whichever of the two is written first. -/
private def firstNestedGroupKey? (reads : List RepetitionKeyRead) : Option GroupPath :=
  reads.findSome? fun read => read.group?.bind fun group =>
    if reads.any (fun other => other.path != group && group.isPrefixOf other.groupPath) then
      some group
    else none

private def FlatModel.terminalRepeatableGroupFor?
    (model : FlatModel) (declaration : FlatFieldDecl) :
    Option RepeatableGroupDecl :=
  declaration.repeatableScope.getLast?.bind model.repeatableGroupAtLevel?

/-- The first pair of keys whose lowest repeatable groups leave one hierarchy path. It keeps the
deepest such group so far, skipping a key under no repeatable group, and reports the first key whose
group neither extends nor lies on it. The Kernel's shared-path check compares these groups, read off
its source; the rows measure it on keys directly in two parallel repeatable groups only. -/
private def firstKeyOffSharedPath? (model : FlatModel) (declarations : List FlatFieldDecl) :
    Option (GroupPath × GroupPath) :=
  let rec walk (deepest : Option GroupPath) : List FlatFieldDecl → Option (GroupPath × GroupPath)
    | [] => none
    | declaration :: remaining =>
        match model.terminalRepeatableGroupFor? declaration with
        | none => walk deepest remaining
        | some group =>
            match deepest with
            | none => walk (some group.path) remaining
            | some path =>
                if path.isPrefixOf group.path then walk (some group.path) remaining
                else if group.path.isPrefixOf path then walk deepest remaining
                else some (path, group.path)
  walk none declarations

private def deepestKeyDeclaration (model : FlatModel) (current : FlatFieldDecl) :
    List FlatFieldDecl → Except RepetitionNotUniqueElabError FlatFieldDecl
  | [] => pure current
  | declaration :: remaining =>
      if current.groupPath.isPrefixOf declaration.groupPath then
        deepestKeyDeclaration model declaration remaining
      else if declaration.groupPath.isPrefixOf current.groupPath then
        deepestKeyDeclaration model current remaining
      else match model.terminalRepeatableGroupFor? current,
          model.terminalRepeatableGroupFor? declaration with
        | some _, some _ =>
            throw (.keyGroupsDiverge current.groupPath declaration.groupPath)
        | _, _ =>
            throw (.keyPathMismatch current.groupPath declaration.groupPath)

private def FlatModel.defaultRepetitionReferenceGroup?
    (model : FlatModel) (declaringGroup keyGroup : GroupPath) :
    Option RepeatableGroupDecl :=
  if declaringGroup.isPrefixOf keyGroup then
    let declaringScope := model.repeatableScopeForGroupPath declaringGroup
    let keyScope := model.repeatableScopeForGroupPath keyGroup
    match (keyScope.drop declaringScope.length).head? with
    | none => none
    | some level => model.repeatableGroups.find? fun group => group.level == level
  else
    none

private def firstKeyGroupOutside? (referenceGroup : GroupPath) :
    List FlatFieldDecl → Option GroupPath
  | [] => none
  | declaration :: remaining =>
      if referenceGroup.isPrefixOf declaration.groupPath then
        firstKeyGroupOutside? referenceGroup remaining
      else
        some declaration.groupPath

/-- The `@From` branch. The scope is read first, as a key is: an empty group is refused and the walk
may refuse the read, so an unpaired repetition is the walk's rather than containment's
([inbound](../../docs/SOURCES.md#inbound-2026-09-26f-gate-order),
[inbound](../../docs/SOURCES.md#inbound-2026-09-26h-empty-scope)). Asking the empty group before
the walk, and the whole read after the key list's gates, is this theory's order, which no row
fixes. Then the scope must be a group,
it must repeat, and it must hold every key. The Kernel asks no shared-path gate here, so keys that
leave one path inside the scope reach only this theory's topology limit. -/
private def resolveScopedReferenceGroup (model : FlatModel) (declaringGroup writtenGroup : GroupPath)
    (surface : SurfaceGroupReference) (declarations : List FlatFieldDecl) :
    Except RepetitionNotUniqueElabError (FlatFieldDecl × RepeatableGroupDecl) := do
  let resolved ← surface.resolveAgainst declaringGroup |>.mapError .scope
  let path := resolved.path
  let field? := model.fields.find? (·.path == path)
  let scope ← match field? with
    | some field => pure field.repeatableScope
    | none =>
        if !model.hasGroupPath path then throw (.resolve (.unknownRepeatableGroup path))
        else if !model.groupContributesField path then throw (.scopeIsEmpty path)
        else pure (model.repeatableScopeForGroupPath path)
  if let some unbound := model.refusedReadLevel? declaringGroup writtenGroup scope then
    throw (.scopeReadRefused path unbound)
  if field?.isSome then throw (.scopeIsField path)
  let group ← match model.lookupUniqueRepeatablePath path with
    | .ok group => pure group
    | .error (.unknownRepeatableGroup _) => throw (.referenceGroupNotRepeatable path)
    | .error error => throw (.resolve error)
  if let some keyGroup := firstKeyGroupOutside? group.path declarations then
    throw (.referenceGroupDoesNotContainKey group.path keyGroup)
  match declarations with
  | [] => throw .incoherentCore
  | first :: rest =>
      let terminal ← deepestKeyDeclaration model first rest |>.mapError fun
        | .keyPathMismatch left right => .keyGroupsDiverge left right
        | error => error
      pure (terminal, group)

/-- The branch without `@From`: the keys' lowest repeatable groups must lie on one path, every key
inside the rule group, and a repeatable group between the rule group and the deepest key, which is
the default reference group. -/
private def resolveDefaultReferenceGroup (model : FlatModel) (declaringGroup : GroupPath)
    (declarations : List FlatFieldDecl) :
    Except RepetitionNotUniqueElabError (FlatFieldDecl × RepeatableGroupDecl) := do
  if let some (left, right) := firstKeyOffSharedPath? model declarations then
    throw (.keysOffOnePath left right)
  if let some outside := declarations.find? (!declaringGroup.isPrefixOf ·.groupPath) then
    throw (.keyOutsideRuleGroup outside.path)
  match declarations with
  | [] => throw .incoherentCore
  | first :: rest =>
      let terminal ← deepestKeyDeclaration model first rest
      match model.defaultRepetitionReferenceGroup? declaringGroup terminal.groupPath with
      | none =>
          if declaringGroup.length == 1 &&
              model.repeatableGroups.any (·.path == declaringGroup) &&
              declarations.all (·.groupPath.length == 1) then
            throw (.repeatableRootKeys terminal.path)
          else throw (.missingReferenceGroup terminal.path)
      | some group =>
          match firstKeyGroupOutside? group.path declarations with
          | none => pure (terminal, group)
          | some keyGroup => throw (.keyOutsideDefaultReferenceGroup group.path keyGroup)

private def repetitionStarSegments (model : FlatModel)
    (referenceGroup : GroupPath) : GroupPath → GroupPath →
      List SurfaceStarGroupSegment
  | _, [] => []
  | pathPrefix, name :: remaining =>
      let path := pathPrefix ++ [name]
      let repeatable := model.repeatableGroups.any fun group => group.path == path
      { name, starred := repeatable && referenceGroup.isPrefixOf path } ::
        repetitionStarSegments model referenceGroup path remaining

private def elaborateRepetitionKeyPlan (model : FlatModel)
    (referenceGroup : GroupPath) (declaration : FlatFieldDecl) :
    Except RepetitionNotUniqueElabError CheckedStarPlan :=
  elaborateStarPathPlan model []
    (repetitionStarSegments model referenceGroup [] declaration.groupPath)
    declaration.path |>.mapError .path

/-- Certify one legal RNU key kind without bypassing its declaration-owned checking. -/
private def certifyRepetitionKey (model : FlatModel)
    (modelWellFormed : model.validate.isOk = true)
    (plan : CheckedStarPlan) (declaration : FlatFieldDecl) :
    Except RepetitionNotUniqueElabError (CheckedRepetitionKey model) :=
  if hDeclaration : model.fields.contains declaration = true then
    if hAncestry : plan.path.axes.map (·.level) = declaration.repeatableScope then
      let source : CheckedStarFieldPath model := {
        declaration
        path := plan.path
        modelWellFormed
        declarationOwned := hDeclaration
        ancestryOwned := hAncestry
        firstStarWithin := plan.firstStarWithin
        pathValid := plan.pathValid }
      match hKind : declaration.policy.kind with
      | .number _ =>
          match hField : declaration.toNumberField? with
          | some field => pure (.number { source, field, fieldOwned := hField })
          | none => throw .incoherentCore
      | .string =>
          if declaration.isRawString then
            throw (.rawStringValue declaration.path)
          else match declaration.customType with
            | some _ => throw (.customStringRequiresPreparedChecking declaration.path)
            | none =>
                match hField : declaration.toStringValueField? with
                | some field =>
                    pure (.string { source, field, fieldOwned := hField })
                | none => throw .incoherentCore
      | .enumeration =>
          match hEnumeration : declaration.enumeration with
          | none => throw .incoherentCore
          | some enumeration =>
              match hChecked : elaborateEnumeration enumeration with
              | .error _ => throw .incoherentCore
              | .ok checked =>
                  pure (.enumeration {
                    source
                    declaration := checked
                    fieldOwned := hKind
                    enumerationOwned := by
                      rw [elaborateEnumeration_declaration_eq enumeration checked hChecked]
                      exact hEnumeration })
      | actual => throw (.unsupportedKeyKind declaration.path actual.surfaceKind)
    else
      throw .incoherentCore
  else
    throw .incoherentCore

private def certifyRepetitionKeys (model : FlatModel)
    (modelWellFormed : model.validate.isOk = true)
    (referenceGroup : GroupPath) : List FlatFieldDecl →
      Except RepetitionNotUniqueElabError
        (List (CheckedRepetitionKey model))
  | [] => pure []
  | declaration :: remaining => do
      let plan ← elaborateRepetitionKeyPlan model referenceGroup declaration
      pure ((← certifyRepetitionKey model modelWellFormed plan declaration) ::
        (← certifyRepetitionKeys model modelWellFormed referenceGroup remaining))

/-- Resolve one typed-key branch, select its kernel-defined reference group, and derive the deepest-row topology whose bound prefix is supplied by the caller's selected outer scope. The Kernel's gates answer in their order: every key read, the duplicate gate, the key list's gates each over the whole list, then one branch ([inbound](../../docs/SOURCES.md#inbound-2026-09-26f-gate-order)). `writtenGroup` is the rule's error field's group, which places every level a read leaves unbound; the rule group cannot stand in for it, since a rule at the root iterates the error field's repetition. -/
def elaborateRepetitionNotUniqueSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceRepetitionNotUniqueSource)
    (writtenGroup : GroupPath) :
    Except RepetitionNotUniqueElabError
      (CheckedRepetitionNotUniqueSource model) :=
  match hModel : model.validate with
  | .error error => .error (.model error)
  | .ok () => do
      let modelWellFormed : model.validate.isOk = true := by rw [hModel]; rfl
      let reads ← readRepetitionKeys model declaringGroup writtenGroup
        (authored.firstKey :: authored.restKeys)
      if let some path := firstDuplicateKey? reads then throw (.duplicateKey path)
      if let some group := firstNestedGroupKey? reads then throw (.nestedGroupKey group)
      if let some group := reads.findSome? (·.group?) then throw (.groupKey group)
      let declarations := reads.filterMap (·.field?)
      if let some raw := declarations.find? (·.isRawString) then throw (.rawStringValue raw.path)
      match declarations with
      | [] => throw .incoherentCore
      | firstDeclaration :: restDeclarations => do
          let (terminalDeclaration, referenceGroup) ← match authored.scope with
            | .from surface =>
                resolveScopedReferenceGroup model declaringGroup writtenGroup surface declarations
            | .default => resolveDefaultReferenceGroup model declaringGroup declarations
          let topology ← elaborateRepetitionKeyPlan model referenceGroup.path terminalDeclaration
          let firstPlan ← elaborateRepetitionKeyPlan model referenceGroup.path firstDeclaration
          let firstKey ← certifyRepetitionKey model modelWellFormed firstPlan firstDeclaration
          let restKeys ← certifyRepetitionKeys model modelWellFormed referenceGroup.path
            restDeclarations
          let keys := firstKey :: restKeys
          if hReference :
              ((topology.path.axes.drop topology.path.firstStar).head?.map
                (·.level)) = some referenceGroup.level then
            match hUnique : FieldId.firstDuplicate? (keys.map (·.fieldId)) with
            | some _ => throw .incoherentCore
            | none =>
                if hTerminal : keys.any (fun key =>
                    key.source.declaration.groupPath ==
                      terminalDeclaration.groupPath) = true then
                  if hBranch : keys.all (fun key =>
                      key.source.declaration.groupPath.isPrefixOf
                        terminalDeclaration.groupPath) = true then
                    if hWithin : keys.all (fun key =>
                        key.source.path.axes ==
                          topology.path.axes.take key.source.path.axes.length) = true then
                      if hTopologyLevels : topology.path.axes.map (·.level) =
                          model.repeatableScopeForGroupPath terminalDeclaration.groupPath then
                        if hReferenceOwned :
                            model.repeatableGroups.contains referenceGroup = true then
                          pure {
                            ruleGroup := declaringGroup
                            referenceGroup
                            referenceOrigin := authored.scope.referenceOrigin
                            terminalGroup := terminalDeclaration.groupPath
                            topology
                            firstKey
                            restKeys
                            modelWellFormed
                            referenceGroupOwned := hReferenceOwned
                            uniqueKeyFields := hUnique
                            terminalGroupOwned := hTerminal
                            keyGroupsOnBranch := hBranch
                            keyPathsWithinTopology := hWithin
                            topologyLevelsOwned := hTopologyLevels
                            referenceLevelOwned := hReference }
                        else throw .incoherentCore
                      else throw .incoherentCore
                    else throw .incoherentCore
                  else throw .incoherentCore
                else throw .incoherentCore
          else
            throw .incoherentCore

/-- Certify the exact sole indexed RNU key as an otherwise-valid RNU source and semantic-index
selection before returning the measured carrier refusal. The executable RNU source remains
index-free. -/
def elaborateRepetitionNotUniqueSemanticIndexRefusal (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceRepetitionNotUniqueSemanticIndexUse)
    (writtenGroup : GroupPath) :
    Except RepetitionNotUniqueSemanticIndexRefusalError
      (CheckedRepetitionNotUniqueSemanticIndexRefusal model) := do
  let source ← elaborateRepetitionNotUniqueSource model declaringGroup {
      firstKey := authored.target
      restKeys := [] } writtenGroup
    |>.mapError .repetitionNotUnique
  let selection ← elaborateSemanticIndexSource model declaringGroup {
      target := authored.target
      key := .literal (.text authored.token) }
    |>.mapError .semanticIndex
  if hRuleGroup : source.ruleGroup == declaringGroup then
    if hReference : source.referenceGroup == selection.group then
      if hTarget : source.firstKey.source.declaration ==
          selection.targetDeclaration then
        if hKey : selection.key == .literal (.text authored.token) then
          pure {
            declaringGroup
            token := authored.token
            source
            selection
            ruleGroupRetained := hRuleGroup
            referenceGroupSelected := hReference
            targetSelected := hTarget
            keyRetained := hKey }
        else
          throw .incoherentCore
      else
        throw .incoherentCore
    else
      throw (.selectionGroupMismatch source.referenceGroup.path selection.group.path)
  else
    throw .incoherentCore

namespace CheckedRepetitionNotUniqueSemanticIndexRefusal

/-- The exact carrier diagnostic measured after both component certificates succeed. -/
def diagnostic (_ : CheckedRepetitionNotUniqueSemanticIndexRefusal model) :
    KernelStaticDiagnostic :=
  .semanticIndexNotAllowed

end CheckedRepetitionNotUniqueSemanticIndexRefusal

/-- Project the exact refusal without assigning its code to an invalid selection, an unsupported
RNU key, or a wider repetition topology. -/
def projectRepetitionNotUniqueSemanticIndexDiagnostic? (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceRepetitionNotUniqueSemanticIndexUse)
    (writtenGroup : GroupPath) :
    Option KernelStaticDiagnostic :=
  match elaborateRepetitionNotUniqueSemanticIndexRefusal model declaringGroup authored
      writtenGroup with
  | .ok checked => some checked.diagnostic
  | .error _ => none

namespace CheckedRepetitionNotUniqueSource

def keys (checked : CheckedRepetitionNotUniqueSource model) :
    List (CheckedRepetitionKey model) :=
  checked.firstKey :: checked.restKeys

/-- A checked RNU condition directly references its key fields. An authored `@From` additionally contributes the already resolved reference-group subtree; an inferred default group does not. -/
def referencesField (checked : CheckedRepetitionNotUniqueSource model)
    (field : FieldId) : Bool :=
  checked.keys.any (fun key => key.fieldId == field) ||
    match checked.referenceOrigin with
    | .inferredDefault => false
    | .authoredFrom =>
        ({ path := checked.referenceGroup.path
           origin := .path } : ResolvedGroupReference).referencesField model field

/-- Recheck the source certificate at the mixed-condition boundary so a checked RNU source cannot be transplanted to another rule group. -/
def wellFormedBool (checked : CheckedRepetitionNotUniqueSource model)
    (rowGroup : GroupPath) : Bool :=
  checked.ruleGroup == rowGroup &&
    model.validate.isOk &&
    model.repeatableGroups.contains checked.referenceGroup &&
    FieldId.firstDuplicate? (checked.keys.map (·.fieldId)) == none &&
    checked.keys.any (fun key =>
      key.source.declaration.groupPath == checked.terminalGroup) &&
    checked.keys.all (fun key =>
      key.source.declaration.groupPath.isPrefixOf checked.terminalGroup) &&
    checked.keys.all (fun key =>
      key.source.path.axes ==
        checked.topology.path.axes.take key.source.path.axes.length) &&
    checked.topology.path.axes.map (·.level) ==
      model.repeatableScopeForGroupPath checked.terminalGroup &&
    ((checked.topology.path.axes.drop
      checked.topology.path.firstStar).head?.map (·.level)) ==
        some checked.referenceGroup.level

/-- Partial relevance admits a row only when every component of its composite key is relevant. -/
def rowRelevant (checked : CheckedRepetitionNotUniqueSource model)
    (scope : ValidationRelevanceScope) (environment : Env) : Bool :=
  checked.keys.all fun key => key.source.cellRelevant scope environment

/-- Construct one ordered heterogeneous key from the existing declaration-owned typed star classifiers. -/
def resolvedRow (checked : CheckedRepetitionNotUniqueSource model)
    (read : Env → FieldId → CheckedCell) (environment : Env) :
    ResolvedRepetitionKeyRow :=
  { row := environment
    key := checked.keys.map fun key => key.classify read environment }

/-- Construct one key row from the immutable checked document in a validation-produced environment, preserving any model, environment, or document addressing failure outside key UNKNOWN. -/
def resolvedRowChecked
    (checked : CheckedRepetitionNotUniqueSource model)
    (document : CheckedDocument model) (environment : Env) :
    Except CheckedAddressingError ResolvedRepetitionKeyRow := do
  let key ← checked.keys.mapM fun key => do
    let keyEnvironment := key.environmentPrefix environment
    let addressed ←
      document.validationAddressedCell keyEnvironment key.fieldId
    pure (key.classifyCheckedCell addressed.cell environment)
  pure { row := environment, key }

/-- Resolve one selected default or explicit `@From` scope, then exclude composite-key rows whose components are not all relevant before reading any key cell. -/
def resolvedRows (checked : CheckedRepetitionNotUniqueSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → CheckedCell) :
    Except StarAddressingError (List ResolvedRepetitionKeyRow) := do
  let topology ← checked.topology.path.resolve document outer
  pure ((topology.environments.filter (checked.rowRelevant scope)).map
    (checked.resolvedRow read))

/-- Resolve the selected scope against the immutable checked input. Concrete topology keeps its established canonical relation order; implicit validation descendants are appended from the validation-only domain. Complete-key relevance is filtered before reads, and every reached address failure remains structural. -/
def resolvedRowsChecked
    (checked : CheckedRepetitionNotUniqueSource model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :
    Except CheckedAddressingError (List ResolvedRepetitionKeyRow) := do
  let topology ←
    (checked.topology.path.resolve document.source.toDocument outer)
      |>.mapError .addressing
  let levels := checked.topology.path.axes.map (·.level)
  let validationRows ←
    (document.validationRowEnvironments levels)
      |>.mapError .rowEnvironment
  let bound ←
    checked.topology.path.boundEnvironment outer
      |>.mapError .addressing
  let implicitRows := validationRows.filter fun environment =>
    environment.take bound.length == bound &&
      !topology.environments.contains environment
  let environments := topology.environments ++ implicitRows
  (environments.filter (checked.rowRelevant scope)).mapM
    (checked.resolvedRowChecked document)

/-- Evaluate one selected checked scope through the established branch-independent RNU relation. -/
def evaluate (checked : CheckedRepetitionNotUniqueSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → CheckedCell) :
    Except StarAddressingError (List RepetitionNotUniqueResult) := do
  pure (evalRepetitionNotUnique (← checked.resolvedRows document outer scope read))

/-- Evaluate one checked scope through the same branch-independent relation while deriving every key observation from the immutable checked document. -/
def evaluateChecked
    (checked : CheckedRepetitionNotUniqueSource model)
    (document : CheckedDocument model) (outer : Env)
    (scope : ValidationRelevanceScope) :
    Except CheckedAddressingError (List RepetitionNotUniqueResult) := do
  pure (evalRepetitionNotUnique
    (← checked.resolvedRowsChecked document outer scope))

end CheckedRepetitionNotUniqueSource

end A12Kernel
