import A12Kernel.Elaboration.StarNumber
import A12Kernel.Semantics.EnumerationRepetitionNotUnique
import A12Kernel.Semantics.RepetitionNotUnique

/-! # Checked nested heterogeneous `RepetitionNotUnique` construction

This capsule resolves one nonempty typed composite key along a single group branch, chooses the default or explicit reference group, expands the deepest key path through the existing star topology, retains each ancestor component's own checked path prefix, removes partially irrelevant composite-key rows before classification, and delegates the resulting ordered rows to the resolved RNU relation. Number, ordinary String, and direct stored-Enumeration components are admitted here; temporal, Boolean/Confirm raw-spelling identity, and prepared custom-String keys remain separate. Whole-rule composition and message-pointer projection also remain separate.
-/

namespace A12Kernel

inductive SurfaceRepetitionNotUniqueScope where
  | default
  | from (group : SurfaceGroupPath)
  deriving Repr, DecidableEq

structure SurfaceRepetitionNotUniqueSource where
  firstKey : SurfaceFieldPath
  restKeys : List SurfaceFieldPath
  scope : SurfaceRepetitionNotUniqueScope := .default
  deriving Repr, DecidableEq

inductive RepetitionNotUniqueElabError where
  | resolve (error : ResolveError)
  | scope (error : SingleGroupElabError)
  | duplicateKeyField (field : FieldId)
  | keyPathMismatch (expected actual : GroupPath)
  | unsupportedKeyKind (path : List String) (actual : SurfaceScalarKind)
  | customStringRequiresPreparedChecking (path : List String)
  | missingReferenceGroup (keyPath : List String)
  | referenceGroupDoesNotContainKey (referenceGroup keyGroup : GroupPath)
  | path (error : StarPathElabError)
  | incoherentCore
  deriving Repr, DecidableEq

/-- One ordinary String key certified against the same star plan used by every component. Prepared custom Strings require SG1's checked-document overlay and are not admitted by this raw-cell route. -/
structure CheckedRepetitionStringKey (model : FlatModel) where
  source : CheckedStarFieldPath model
  fieldOwned : source.declaration.policy.kind = .string

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

/-- Classify one component through its existing typed star reader. -/
def classify (key : CheckedRepetitionKey model)
    (read : Env → FieldId → RawCell) (environment : Env) : RepetitionKeyComponent :=
  let keyEnvironment := key.environmentPrefix environment
  match key with
  | .number key =>
      RepetitionKeyComponent.ofNumberValueListCell (key.valueListCell read keyEnvironment)
  | .string key =>
      RepetitionKeyComponent.ofTokenValueListCell
        (key.source.stringValueListCell key.fieldOwned read keyEnvironment)
  | .enumeration key =>
      key.projection.classifyRawKey
        (read keyEnvironment key.source.declaration.id)

end CheckedRepetitionKey

/-- A checked RNU source retains one typed star-classifiable owner per key field. Every owner shares the exact topology plan stored by `firstKey`. -/
structure CheckedRepetitionNotUniqueSource (model : FlatModel) where
  referenceGroup : RepeatableGroupDecl
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

private def resolveRepetitionKeyDeclarations (model : FlatModel)
    (declaringGroup : GroupPath) : List SurfaceFieldPath →
      Except RepetitionNotUniqueElabError (List FlatFieldDecl)
  | [] => pure []
  | path :: remaining => do
      let declaration ← model.resolveFieldDeclarationUnchecked declaringGroup path
        |>.mapError .resolve
      pure (declaration ::
        (← resolveRepetitionKeyDeclarations model declaringGroup remaining))

private def deepestKeyDeclaration (current : FlatFieldDecl) :
    List FlatFieldDecl → Except RepetitionNotUniqueElabError FlatFieldDecl
  | [] => pure current
  | declaration :: remaining =>
      if current.groupPath.isPrefixOf declaration.groupPath then
        deepestKeyDeclaration declaration remaining
      else if declaration.groupPath.isPrefixOf current.groupPath then
        deepestKeyDeclaration current remaining
      else
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

private def resolveRepetitionReferenceGroup (model : FlatModel)
    (declaringGroup terminalGroup keyPath : GroupPath)
    (declarations : List FlatFieldDecl) :
    SurfaceRepetitionNotUniqueScope →
      Except RepetitionNotUniqueElabError RepeatableGroupDecl
  | .default =>
      match model.defaultRepetitionReferenceGroup? declaringGroup terminalGroup with
      | none => throw (.missingReferenceGroup keyPath)
      | some group =>
          match firstKeyGroupOutside? group.path declarations with
          | none => pure group
          | some keyGroup =>
              throw (.referenceGroupDoesNotContainKey group.path keyGroup)
  | .from surface => do
      let path ← surface.resolveAgainst declaringGroup |>.mapError .scope
      let group ← model.lookupUniqueRepeatablePath path |>.mapError .resolve
      match firstKeyGroupOutside? group.path declarations with
      | none => pure group
      | some keyGroup =>
          throw (.referenceGroupDoesNotContainKey group.path keyGroup)

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

/-- Certify one currently supported RNU key kind without changing its declaration-owned checking. -/
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
          match declaration.customType with
          | some _ => throw (.customStringRequiresPreparedChecking declaration.path)
          | none =>
              pure (.string {
                source
                fieldOwned := hKind })
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

/-- Resolve one typed-key branch, select its kernel-defined reference group, and derive the deepest-row topology whose bound prefix is supplied by the caller's selected outer scope. -/
def elaborateRepetitionNotUniqueSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceRepetitionNotUniqueSource) :
    Except RepetitionNotUniqueElabError
      (CheckedRepetitionNotUniqueSource model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let modelWellFormed : model.validate.isOk = true := by rw [hModel]; rfl
      let firstDeclaration ← model.resolveFieldDeclarationUnchecked declaringGroup
        authored.firstKey |>.mapError .resolve
      let restDeclarations ← resolveRepetitionKeyDeclarations model declaringGroup
        authored.restKeys
      match FieldId.firstDuplicate?
          ((firstDeclaration :: restDeclarations).map (·.id)) with
      | some field => throw (.duplicateKeyField field)
      | none => do
          let declarations := firstDeclaration :: restDeclarations
          let terminalDeclaration ← deepestKeyDeclaration firstDeclaration restDeclarations
          let referenceGroup ← resolveRepetitionReferenceGroup model declaringGroup
            terminalDeclaration.groupPath terminalDeclaration.path declarations authored.scope
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
                            referenceGroup
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

namespace CheckedRepetitionNotUniqueSource

def keys (checked : CheckedRepetitionNotUniqueSource model) :
    List (CheckedRepetitionKey model) :=
  checked.firstKey :: checked.restKeys

/-- Partial relevance admits a row only when every component of its composite key is relevant. -/
def rowRelevant (checked : CheckedRepetitionNotUniqueSource model)
    (scope : ValidationRelevanceScope) (environment : Env) : Bool :=
  checked.keys.all fun key => key.source.cellRelevant scope environment

/-- Construct one ordered heterogeneous key from the existing declaration-owned typed star classifiers. -/
def resolvedRow (checked : CheckedRepetitionNotUniqueSource model)
    (read : Env → FieldId → RawCell) (environment : Env) :
    ResolvedRepetitionKeyRow :=
  { row := environment
    key := checked.keys.map fun key => key.classify read environment }

/-- Resolve one selected default or explicit `@From` scope, then exclude composite-key rows whose components are not all relevant before reading any key cell. -/
def resolvedRows (checked : CheckedRepetitionNotUniqueSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) :
    Except StarAddressingError (List ResolvedRepetitionKeyRow) := do
  let topology ← checked.topology.path.resolve document outer
  pure ((topology.environments.filter (checked.rowRelevant scope)).map
    (checked.resolvedRow read))

/-- Evaluate one selected checked scope through the established branch-independent RNU relation. -/
def evaluate (checked : CheckedRepetitionNotUniqueSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) :
    Except StarAddressingError (List RepetitionNotUniqueResult) := do
  pure (evalRepetitionNotUnique (← checked.resolvedRows document outer scope read))

end CheckedRepetitionNotUniqueSource

end A12Kernel
