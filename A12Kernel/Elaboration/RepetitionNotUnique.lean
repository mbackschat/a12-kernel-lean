import A12Kernel.Elaboration.StarNumber
import A12Kernel.Semantics.RepetitionNotUnique

/-! # Checked nested Number `RepetitionNotUnique` construction

This capsule resolves one nonempty composite Number key on a common repeatable field path, chooses the default or explicit reference group, constructs one canonical selected scope through the existing star topology, removes partially irrelevant composite-key rows before classification, and delegates the resulting ordered rows to the resolved RNU relation. Whole-rule composition and message-pointer projection remain separate.
-/

namespace A12Kernel

inductive SurfaceNumberRepetitionNotUniqueScope where
  | default
  | from (group : SurfaceGroupPath)
  deriving Repr, DecidableEq

structure SurfaceNumberRepetitionNotUniqueSource where
  firstKey : SurfaceFieldPath
  restKeys : List SurfaceFieldPath
  scope : SurfaceNumberRepetitionNotUniqueScope := .default
  deriving Repr, DecidableEq

inductive NumberRepetitionNotUniqueElabError where
  | resolve (error : ResolveError)
  | scope (error : SingleGroupElabError)
  | duplicateKeyField (field : FieldId)
  | keyPathMismatch (expected actual : GroupPath)
  | keyNotNumber (path : List String) (actual : SurfaceScalarKind)
  | missingReferenceGroup (keyPath : List String)
  | referenceGroupDoesNotContainKey (referenceGroup keyGroup : GroupPath)
  | path (error : StarPathElabError)
  | incoherentCore
  deriving Repr, DecidableEq

/-- A checked RNU source retains one star-classifiable owner per Number key field. Every owner shares the exact topology plan stored by `firstKey`. -/
structure CheckedNumberRepetitionNotUniqueSource (model : FlatModel) where
  referenceGroup : RepeatableGroupDecl
  firstKey : CheckedStarNumberSource model
  restKeys : List (CheckedStarNumberSource model)
  modelWellFormed : model.validate.isOk = true
  referenceGroupOwned : model.repeatableGroups.contains referenceGroup = true
  uniqueKeyFields :
    FieldId.firstDuplicate? ((firstKey :: restKeys).map (·.field.id)) = none
  commonKeyPath :
    restKeys.all (fun key =>
      key.source.declaration.groupPath == firstKey.source.declaration.groupPath) = true
  commonStarPath :
    restKeys.all (fun key => key.source.path == firstKey.source.path) = true
  referenceLevelOwned :
    ((firstKey.source.path.axes.drop firstKey.source.path.firstStar).head?.map
      (·.level)) = some referenceGroup.level

private def resolveNumberRepetitionKeyDeclarations (model : FlatModel)
    (declaringGroup : GroupPath) : List SurfaceFieldPath →
      Except NumberRepetitionNotUniqueElabError (List FlatFieldDecl)
  | [] => pure []
  | path :: remaining => do
      let declaration ← model.resolveFieldDeclarationUnchecked declaringGroup path
        |>.mapError .resolve
      pure (declaration ::
        (← resolveNumberRepetitionKeyDeclarations model declaringGroup remaining))

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

private def resolveNumberRepetitionReferenceGroup (model : FlatModel)
    (declaringGroup keyGroup keyPath : GroupPath) :
    SurfaceNumberRepetitionNotUniqueScope →
      Except NumberRepetitionNotUniqueElabError RepeatableGroupDecl
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

private def numberRepetitionStarSegments (model : FlatModel)
    (referenceGroup : GroupPath) : GroupPath → GroupPath →
      List SurfaceStarGroupSegment
  | _, [] => []
  | pathPrefix, name :: remaining =>
      let path := pathPrefix ++ [name]
      let repeatable := model.repeatableGroups.any fun group => group.path == path
      { name, starred := repeatable && referenceGroup.isPrefixOf path } ::
        numberRepetitionStarSegments model referenceGroup path remaining

private def certifyNumberRepetitionKey (model : FlatModel)
    (modelWellFormed : model.validate.isOk = true)
    (plan : CheckedStarPlan) (declaration : FlatFieldDecl) :
    Except NumberRepetitionNotUniqueElabError (CheckedStarNumberSource model) :=
  match hField : declaration.toNumberField? with
  | none => throw (.keyNotNumber declaration.path declaration.policy.kind.surfaceKind)
  | some field =>
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
          pure { source, field, fieldOwned := hField }
        else
          throw .incoherentCore
      else
        throw .incoherentCore

private def certifyNumberRepetitionKeys (model : FlatModel)
    (modelWellFormed : model.validate.isOk = true)
    (plan : CheckedStarPlan) : List FlatFieldDecl →
      Except NumberRepetitionNotUniqueElabError
        (List (CheckedStarNumberSource model))
  | [] => pure []
  | declaration :: remaining => do
      pure ((← certifyNumberRepetitionKey model modelWellFormed plan declaration) ::
        (← certifyNumberRepetitionKeys model modelWellFormed plan remaining))

/-- Resolve a common Number-key path, select its kernel-defined reference group, and derive one shared star plan whose bound prefix is supplied by the caller's selected outer scope. -/
def elaborateNumberRepetitionNotUniqueSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceNumberRepetitionNotUniqueSource) :
    Except NumberRepetitionNotUniqueElabError
      (CheckedNumberRepetitionNotUniqueSource model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let modelWellFormed : model.validate.isOk = true := by rw [hModel]; rfl
      let firstDeclaration ← model.resolveFieldDeclarationUnchecked declaringGroup
        authored.firstKey |>.mapError .resolve
      let restDeclarations ← resolveNumberRepetitionKeyDeclarations model declaringGroup
        authored.restKeys
      match FieldId.firstDuplicate?
          ((firstDeclaration :: restDeclarations).map (·.id)) with
      | some field => throw (.duplicateKeyField field)
      | none => do
          match firstMismatchingKeyPath? firstDeclaration.groupPath restDeclarations with
          | some path => throw (.keyPathMismatch firstDeclaration.groupPath path)
          | none => do
              let referenceGroup ← resolveNumberRepetitionReferenceGroup model declaringGroup
                firstDeclaration.groupPath firstDeclaration.path authored.scope
              let segments := numberRepetitionStarSegments model referenceGroup.path []
                firstDeclaration.groupPath
              let plan ← elaborateStarPathPlan model [] segments firstDeclaration.path
                |>.mapError .path
              let firstKey ← certifyNumberRepetitionKey model modelWellFormed plan firstDeclaration
              let restKeys ← certifyNumberRepetitionKeys model modelWellFormed plan restDeclarations
              if hReference :
                  ((firstKey.source.path.axes.drop firstKey.source.path.firstStar).head?.map
                    (·.level)) = some referenceGroup.level then
                match hUnique :
                    FieldId.firstDuplicate? ((firstKey :: restKeys).map (·.field.id)) with
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

namespace CheckedNumberRepetitionNotUniqueSource

def keys (checked : CheckedNumberRepetitionNotUniqueSource model) :
    List (CheckedStarNumberSource model) :=
  checked.firstKey :: checked.restKeys

/-- Partial relevance admits a row only when every component of its composite key is relevant. -/
def rowRelevant (checked : CheckedNumberRepetitionNotUniqueSource model)
    (scope : ValidationRelevanceScope) (environment : Env) : Bool :=
  checked.keys.all fun key => key.source.cellRelevant scope environment

/-- Construct one ordered typed key from the existing declaration-owned Number-star cell classifier. -/
def resolvedRow (checked : CheckedNumberRepetitionNotUniqueSource model)
    (read : Env → FieldId → RawCell) (environment : Env) :
    ResolvedRepetitionKeyRow :=
  { row := environment
    key := checked.keys.map fun key =>
      RepetitionKeyComponent.ofNumberValueListCell
        (key.valueListCell read environment) }

/-- Resolve one selected default or explicit `@From` scope, then exclude composite-key rows whose components are not all relevant before reading any key cell. -/
def resolvedRows (checked : CheckedNumberRepetitionNotUniqueSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) :
    Except StarAddressingError (List ResolvedRepetitionKeyRow) := do
  let topology ← checked.firstKey.source.path.resolve document outer
  pure ((topology.environments.filter (checked.rowRelevant scope)).map
    (checked.resolvedRow read))

/-- Evaluate one selected checked scope through the established branch-independent RNU relation. -/
def evaluate (checked : CheckedNumberRepetitionNotUniqueSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (read : Env → FieldId → RawCell) :
    Except StarAddressingError (List RepetitionNotUniqueResult) := do
  pure (evalRepetitionNotUnique (← checked.resolvedRows document outer scope read))

end CheckedNumberRepetitionNotUniqueSource

end A12Kernel
