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
  | resolve (error : ResolveError)
  | scope (error : SingleGroupElabError)
  | duplicateKeyField (field : FieldId)
  | keyPathMismatch (expected actual : GroupPath)
  | unsupportedParallelRepeatableKeyPaths (left right : GroupPath)
  | unsupportedKeyKind (path : List String) (actual : SurfaceScalarKind)
  | rawStringValue (path : List String)
  | customStringRequiresPreparedChecking (path : List String)
  | missingReferenceGroup (keyPath : List String)
  | referenceGroupNotRepeatable (path : GroupPath)
  | referenceGroupDoesNotContainKey (referenceGroup keyGroup : GroupPath)
  | path (error : StarPathElabError)
  | incoherentCore
  deriving Repr, DecidableEq

namespace RepetitionNotUniqueElabError

/-- Project the measured `RepetitionNotUnique` key-admission classes. Three shapes draw one Kernel class: a second key in a nonrepeatable group, a sole key whose group is not repeatable, and a rule already placed at the repeated group. The first two have distinct local errors; the third reaches the missing-reference-group arm in either absolute or relative spelling. Parallel repeatable paths remain unmapped because the two observed fixtures differ without an established discriminator. Every other unmeasured refusal returns `none`. -/
def diagnostic? : RepetitionNotUniqueElabError → Option KernelStaticDiagnostic
  | .duplicateKeyField _ => some .duplicateParam1
  | .keyPathMismatch _ _ | .missingReferenceGroup _ =>
      some .repeatableGroupMissing
  | .resolve (.invalidEntity _) => some .invalidEntity
  | _ => none

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
the same target, reference group, and error field before the carrier-specific refusal is projected.
It supplies no indexed RNU evaluator. -/
structure CheckedRepetitionNotUniqueSemanticIndexRefusal (model : FlatModel) where
  declaringGroup : GroupPath
  errorField : FieldId
  token : String
  source : CheckedRepetitionNotUniqueSource model
  selection : CheckedSemanticIndexSource model
  ruleGroupRetained : (source.ruleGroup == declaringGroup) = true
  referenceGroupSelected : (source.referenceGroup == selection.group) = true
  targetSelected :
    (source.firstKey.source.declaration == selection.targetDeclaration) = true
  errorFieldSelected : (selection.targetDeclaration.id == errorField) = true
  keyRetained : (selection.key == .literal (.text token)) = true

inductive RepetitionNotUniqueSemanticIndexRefusalError where
  | repetitionNotUnique (error : RepetitionNotUniqueElabError)
  | semanticIndex (error : SemanticIndexElabError)
  | selectionGroupMismatch (repetition semanticIndex : GroupPath)
  | errorFieldMismatch (expected actual : FieldId)
  | incoherentCore
  deriving Repr, DecidableEq

private def resolveRepetitionKeyDeclarations (model : FlatModel)
    (declaringGroup : GroupPath) : List SurfaceFieldPath →
      Except RepetitionNotUniqueElabError (List FlatFieldDecl)
  | [] => pure []
  | path :: remaining => do
      let declaration ← model.resolveFieldDeclarationUnchecked declaringGroup path
        |>.mapError .resolve
      pure (declaration ::
        (← resolveRepetitionKeyDeclarations model declaringGroup remaining))

private def FlatModel.terminalRepeatableGroupFor?
    (model : FlatModel) (declaration : FlatFieldDecl) :
    Option RepeatableGroupDecl :=
  declaration.repeatableScope.getLast?.bind model.repeatableGroupAtLevel?

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
            throw (.unsupportedParallelRepeatableKeyPaths
              current.groupPath declaration.groupPath)
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
      let resolved ← surface.resolveAgainst declaringGroup |>.mapError .scope
      let group ← match model.lookupUniqueRepeatablePath resolved.path with
        | .ok group => pure group
        | .error (.unknownRepeatableGroup _) =>
            if model.hasGroupPath resolved.path then
              throw (.referenceGroupNotRepeatable resolved.path)
            else
              throw (.resolve (.unknownRepeatableGroup resolved.path))
        | .error error => throw (.resolve error)
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
          let terminalDeclaration ←
            deepestKeyDeclaration model firstDeclaration restDeclarations
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
    (declaringGroup : GroupPath) (errorField : FieldId)
    (authored : SurfaceRepetitionNotUniqueSemanticIndexUse) :
    Except RepetitionNotUniqueSemanticIndexRefusalError
      (CheckedRepetitionNotUniqueSemanticIndexRefusal model) := do
  let source ← elaborateRepetitionNotUniqueSource model declaringGroup {
      firstKey := authored.target
      restKeys := [] }
    |>.mapError .repetitionNotUnique
  let selection ← elaborateSemanticIndexSource model declaringGroup {
      target := authored.target
      key := .literal (.text authored.token) }
    |>.mapError .semanticIndex
  if hRuleGroup : source.ruleGroup == declaringGroup then
    if hReference : source.referenceGroup == selection.group then
      if hTarget : source.firstKey.source.declaration ==
          selection.targetDeclaration then
        if hErrorField : selection.targetDeclaration.id == errorField then
          if hKey : selection.key == .literal (.text authored.token) then
            pure {
              declaringGroup
              errorField
              token := authored.token
              source
              selection
              ruleGroupRetained := hRuleGroup
              referenceGroupSelected := hReference
              targetSelected := hTarget
              errorFieldSelected := hErrorField
              keyRetained := hKey }
          else
            throw .incoherentCore
        else
          throw (.errorFieldMismatch selection.targetDeclaration.id errorField)
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
RNU key, a different error field, or a wider repetition topology. -/
def projectRepetitionNotUniqueSemanticIndexDiagnostic? (model : FlatModel)
    (declaringGroup : GroupPath) (errorField : FieldId)
    (authored : SurfaceRepetitionNotUniqueSemanticIndexUse) :
    Option KernelStaticDiagnostic :=
  match elaborateRepetitionNotUniqueSemanticIndexRefusal model declaringGroup errorField authored with
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
