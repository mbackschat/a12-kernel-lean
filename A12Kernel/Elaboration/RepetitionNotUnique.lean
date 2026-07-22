import A12Kernel.Elaboration.StarNumber
import A12Kernel.Semantics.RepetitionNotUnique

/-! # Checked nested heterogeneous `RepetitionNotUnique` construction

This capsule resolves one nonempty typed composite key on a common repeatable field path, chooses the default or explicit reference group, constructs one canonical selected scope through the existing star topology, removes partially irrelevant composite-key rows before classification, and delegates the resulting ordered rows to the resolved RNU relation. Number and ordinary String components are admitted here; ancestor-path, temporal, Enumeration, and prepared custom-String keys remain separate. Whole-rule composition and message-pointer projection also remain separate.
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

/-- One typed key component. This sum is the extension point for source-verified temporal and Enumeration RNU keys; it prevents a second homogeneous-key construction path. -/
inductive CheckedRepetitionKey (model : FlatModel) where
  | number (key : CheckedStarNumberSource model)
  | string (key : CheckedRepetitionStringKey model)

namespace CheckedRepetitionKey

def source : CheckedRepetitionKey model → CheckedStarFieldPath model
  | .number key => key.source
  | .string key => key.source

def fieldId (key : CheckedRepetitionKey model) : FieldId :=
  key.source.declaration.id

/-- Classify one component through its existing typed star reader. -/
def classify (key : CheckedRepetitionKey model)
    (read : Env → FieldId → RawCell) (environment : Env) : RepetitionKeyComponent :=
  match key with
  | .number key =>
      RepetitionKeyComponent.ofNumberValueListCell (key.valueListCell read environment)
  | .string key =>
      RepetitionKeyComponent.ofTokenValueListCell
        (key.source.stringValueListCell key.fieldOwned read environment)

end CheckedRepetitionKey

/-- A checked RNU source retains one typed star-classifiable owner per key field. Every owner shares the exact topology plan stored by `firstKey`. -/
structure CheckedRepetitionNotUniqueSource (model : FlatModel) where
  referenceGroup : RepeatableGroupDecl
  firstKey : CheckedRepetitionKey model
  restKeys : List (CheckedRepetitionKey model)
  modelWellFormed : model.validate.isOk = true
  referenceGroupOwned : model.repeatableGroups.contains referenceGroup = true
  uniqueKeyFields :
    FieldId.firstDuplicate? ((firstKey :: restKeys).map (·.fieldId)) = none
  commonKeyPath :
    restKeys.all (fun key =>
      key.source.declaration.groupPath == firstKey.source.declaration.groupPath) = true
  commonStarPath :
    restKeys.all (fun key => key.source.path == firstKey.source.path) = true
  referenceLevelOwned :
    ((firstKey.source.path.axes.drop firstKey.source.path.firstStar).head?.map
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

private def firstMismatchingKeyPath? (expected : GroupPath) :
    List FlatFieldDecl → Option GroupPath
  | [] => none
  | declaration :: remaining =>
      if declaration.groupPath == expected then
        firstMismatchingKeyPath? expected remaining
      else
        some declaration.groupPath

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

private def resolveRepetitionReferenceGroup (model : FlatModel)
    (declaringGroup keyGroup keyPath : GroupPath) :
    SurfaceRepetitionNotUniqueScope →
      Except RepetitionNotUniqueElabError RepeatableGroupDecl
  | .default =>
      match model.defaultRepetitionReferenceGroup? declaringGroup keyGroup with
      | none => throw (.missingReferenceGroup keyPath)
      | some group => pure group
  | .from surface => do
      let path ← surface.resolveAgainst declaringGroup |>.mapError .scope
      let group ← model.lookupUniqueRepeatablePath path |>.mapError .resolve
      if group.path.isPrefixOf keyGroup then
        pure group
      else
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
      | actual => throw (.unsupportedKeyKind declaration.path actual.surfaceKind)
    else
      throw .incoherentCore
  else
    throw .incoherentCore

private def certifyRepetitionKeys (model : FlatModel)
    (modelWellFormed : model.validate.isOk = true)
    (plan : CheckedStarPlan) : List FlatFieldDecl →
      Except RepetitionNotUniqueElabError
        (List (CheckedRepetitionKey model))
  | [] => pure []
  | declaration :: remaining => do
      pure ((← certifyRepetitionKey model modelWellFormed plan declaration) ::
        (← certifyRepetitionKeys model modelWellFormed plan remaining))

/-- Resolve a common typed-key path, select its kernel-defined reference group, and derive one shared star plan whose bound prefix is supplied by the caller's selected outer scope. -/
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
          match firstMismatchingKeyPath? firstDeclaration.groupPath restDeclarations with
          | some path => throw (.keyPathMismatch firstDeclaration.groupPath path)
          | none => do
              let referenceGroup ← resolveRepetitionReferenceGroup model declaringGroup
                firstDeclaration.groupPath firstDeclaration.path authored.scope
              let segments := repetitionStarSegments model referenceGroup.path []
                firstDeclaration.groupPath
              let plan ← elaborateStarPathPlan model [] segments firstDeclaration.path
                |>.mapError .path
              let firstKey ← certifyRepetitionKey model modelWellFormed plan firstDeclaration
              let restKeys ← certifyRepetitionKeys model modelWellFormed plan restDeclarations
              if hReference :
                  ((firstKey.source.path.axes.drop firstKey.source.path.firstStar).head?.map
                    (·.level)) = some referenceGroup.level then
                match hUnique :
                    FieldId.firstDuplicate? ((firstKey :: restKeys).map (·.fieldId)) with
                | some _ => throw .incoherentCore
                | none =>
                    if hPath : restKeys.all (fun key =>
                        key.source.declaration.groupPath ==
                          firstKey.source.declaration.groupPath) = true then
                      if hStar : restKeys.all (fun key =>
                          key.source.path == firstKey.source.path) = true then
                        if hReferenceOwned :
                            model.repeatableGroups.contains referenceGroup = true then
                          pure {
                            referenceGroup
                            firstKey
                            restKeys
                            modelWellFormed
                            referenceGroupOwned := hReferenceOwned
                            uniqueKeyFields := hUnique
                            commonKeyPath := hPath
                            commonStarPath := hStar
                            referenceLevelOwned := hReference }
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
  let topology ← checked.firstKey.source.path.resolve document outer
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
