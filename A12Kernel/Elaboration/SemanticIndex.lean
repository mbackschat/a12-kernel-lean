import A12Kernel.Elaboration.CheckedIndexColumn
import A12Kernel.Elaboration.SemanticIndexAdmission
import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Elaboration.StarPath
import A12Kernel.Semantics.RepetitionNotUnique
import A12Kernel.Semantics.SemanticIndex
import A12Kernel.Semantics.NumericInput

/-! # Checked one-group semantic-index construction

A semantic index selects one row of a group by its declared index field's value. This capsule
certifies that selection and hands it to the resolved evaluator, which owns the phase policy.

The **index field's kind is not narrowed**: a Number index compares by numeric value and every other
kind by normalized cache text (spec/02 §3), and the shared checked column owner already decides that identity, so this
certificate carries the declaration rather than a Number field. The measured Kernel rule is that the
index kind and the selected target's kind are independent. The **reduced raw-context route** below
stays a Number-index, Number-target instance, because it rebuilds the column from a one-group scan
rather than projecting the shared one; the **immutable generated-preliminary route** serves the
general case and only needs the target's id.

This checked surface starts after literal decoding. The entity-list reader consumes
[`IndexKeyShape`](IndexKeyShape.lean) before supplying the decoded identity and original spelling.
Direct callers own the same declaration-format precondition. Repeatable field-valued keys and
nested indices remain outside this one-group certificate.
-/

namespace A12Kernel

inductive SurfaceSemanticIndexKey where
  /-- A declaration-admitted literal, already decoded into the identity its declared index field
  uses. `spelling` retains the unescaped, line-normalized token for authored operand identity:
  numeric equality does not make differently spelled entity-list parameters duplicates
  (`CheckEntityListenUtils` and `SemanticIndexRef`, kernel 30.8.1). The declaration-format check
  remains the caller's responsibility. -/
  | literal (token : SemanticIndexKey) (spelling : Option String := none)
  /-- A field whose checked current value supplies the lookup key. -/
  | field (reference : SurfaceFieldPath)
  deriving Repr, DecidableEq

structure SurfaceSemanticIndex where
  target : SurfaceFieldPath
  key : SurfaceSemanticIndexKey
  deriving Repr, DecidableEq

/-- The measured exact-text literal semantic-index suffix on the reserved `RuleGroup` entity.
Keeping this surface distinct excludes unmeasured numeric literals, field-valued keys, and
wildcard-plus-index combinations ([checkpoint](../../docs/sources/inbound-group-operand-batches.md#src-pr2-rulegroup-semantic-index)). -/
structure SurfaceRuleGroupSemanticIndex where
  token : String
  deriving Repr, DecidableEq

/-- The exact reviewed two-field `NumberOfFilledFields` carrier: two authored target paths, one
exact-text semantic-index key, and no runtime count claim. Other arities and key forms have distinct
surface types or no representation ([checkpoint](../../docs/sources/inbound-group-operand-batches.md#src-pr2-semantic-index-carrier-matrix)). -/
structure SurfaceFilledFieldCountSemanticIndexPair where
  firstTarget : SurfaceFieldPath
  secondTarget : SurfaceFieldPath
  token : String
  deriving Repr, DecidableEq

/-- The exact reviewed one-level starred Number target with a literal text semantic-index suffix.
Other target kinds, repetition topologies, and key forms have no representation in this certificate
([checkpoint](../../docs/sources/inbound-group-operand-batches.md#src-pr2-semantic-index-carrier-matrix)). -/
structure SurfaceStarredNumberSemanticIndexUse where
  target : SurfaceStarFieldPath
  token : String
  deriving Repr, DecidableEq

/-- The Number surface retained for the reduced raw-context route, whose literal is a numeric value. -/
abbrev SurfaceNumberSemanticIndexKey := SurfaceSemanticIndexKey
abbrev SurfaceNumberSemanticIndex := SurfaceSemanticIndex

inductive SemanticIndexElabError where
  | keyAdmission (diagnostic : KernelStaticDiagnostic)
  | resolve (error : ResolveError)
  | group (error : SingleGroupElabError)
  | missingIndexField (groupPath : GroupPath)
  /-- The literal key's identity domain disagrees with the declared index field's: a numeric literal
  against a text-identity index, or a text literal against a Number one. -/
  | indexKeyDomainMismatch (path : List String) (key : SemanticIndexKey)
  | targetNotNumber (path : List String)
  /-- The reduced raw-context route needs a Number index and a Number target; the general
  preliminary route does not. -/
  | reducedRouteNeedsNumber (path : List String)
  | reducedRouteNeedsSingleGroup
  | multipleIndexGroups
  /-- The field-valued key is read from inside the indexed group itself. -/
  | keyContainedInIndexedGroup (path : List String) (groupPath : GroupPath)
  | incoherentCore

  deriving Repr, DecidableEq

namespace SemanticIndexElabError

/-- Project the source-derived key-admission and containment diagnostics.

Every other form is named rather than caught by a wildcard, so that a new arm cannot be absorbed
into this project's boundary without a decision. `reducedRouteNeedsNumber` and `incoherentCore` are
that boundary — the reduced raw-context route is narrower than the Kernel by construction. The
remaining unmapped forms are unmeasured Kernel refusals: `missingIndexField` carries a measured class on the
`RuleGroup` suffix alone, through `ruleGroupDiagnostic?` below, and the other carriers need their
own evidence before inheriting it. -/
def diagnostic? : SemanticIndexElabError → Option KernelStaticDiagnostic
  | .keyAdmission diagnostic => some diagnostic
  | .multipleIndexGroups => some .multipleIndexFields
  | .keyContainedInIndexedGroup _ _ => some .semanticIndexContainedInIndex
  | .resolve error => error.diagnostic?
  | .group _ | .missingIndexField _ | .indexKeyDomainMismatch _ _
  | .targetNotNumber _ | .reducedRouteNeedsNumber _ | .reducedRouteNeedsSingleGroup | .incoherentCore => none

/-- Exact diagnostic projection measured for the `RuleGroup` literal suffix. A missing index on
other carriers requires its own evidence before it can inherit this code
([checkpoint](../../docs/sources/inbound-group-operand-batches.md#src-pr2-rulegroup-semantic-index)). -/
def ruleGroupDiagnostic? : SemanticIndexElabError → Option KernelStaticDiagnostic
  | .missingIndexField _ => some .noIndexField
  | error => error.diagnostic?

end SemanticIndexElabError

inductive FilledFieldCountSemanticIndexPairElabError where
  | first (error : SemanticIndexElabError)
  | second (error : SemanticIndexElabError)
  | differentGroup (first second : GroupPath)
  | duplicateTarget (path : List String)
  | incoherentCore
  deriving Repr, DecidableEq

inductive StarredNumberSemanticIndexRefusalError where
  | starPath (error : StarPathElabError)
  | semanticIndex (error : SemanticIndexElabError)
  | targetNotNumber (path : List String)
  | unsupportedTopology (levels : List RepeatableLevel)
      (firstStar selectedLevel : Nat)
  | incoherentCore
  deriving Repr, DecidableEq

inductive CheckedSemanticIndexKey where
  | literal (token : SemanticIndexKey) (spelling : Option String := none)
  | field (source : FlatFieldDecl)
  deriving Repr, DecidableEq

namespace CheckedSemanticIndexKey

/-- The key retains its exact model declaration; its reading scope is checked separately (spec/08 §4). -/
def admittedBy (key : CheckedSemanticIndexKey) (model : FlatModel) : Bool :=
  match key with
  | .literal _ _ => true
  | .field source =>
      match model.lookupUniqueId source.id with
      | .ok admitted => admitted == source
      | .error _ => false

def bindingScope : CheckedSemanticIndexKey → List RepeatableLevel
  | .literal .. => []
  | .field source => source.repeatableScope

/-- Key identity must match the index declaration even when a checked source is constructed
without the surface elaborator (`SemanticIndexAdmission.keyAgreementRefusal`). -/
def agreesWith (key : CheckedSemanticIndexKey) (index : FlatFieldDecl) : Bool :=
  match key with
  | .literal token _ => match token, index.policy.kind with
    | .number _, .number _ => true
    | .text _, .number _ => false
    | .number _, _ => false
    | .text _, _ => true
  | .field source => source.policy.kind.surfaceKind.sharesValueListBaseType index.policy.kind.surfaceKind

/-- Retain the certified key declaration when reading a current computation or validation view.
Literal identity is independent of the reader; a dynamic key must retain its phase and formal cause
for the shared column lookup (`ResolvedSemanticIndexColumn.lookupObservationForIndex`). -/
def observeWith (key : CheckedSemanticIndexKey)
    (read : FlatFieldDecl → CellObservation) : CellObservation :=
  match key with
  | .literal (.number value) _ => .value (.num value)
  | .literal (.text token) _ => .value (.str token)
  | .field source => read source

/-- Apply declaration-owned checking to a dynamic key and retain the requested phase. -/
def observe (key : CheckedSemanticIndexKey) (model : FlatModel)
    (raw : RawFlatContext) (phase : Phase) : CellObservation :=
  key.observeWith fun source => observeCell phase ((model.checkContext raw).read source.id)

end CheckedSemanticIndexKey

/-- Index declaration ownership follows the complete group scope. Parent rows stay bound while
selection replaces the final coordinate (spec/08 §4 and the parent-scoped index checkpoint). -/
def FlatModel.admitsSemanticIndexDeclaration (model : FlatModel)
    (group : RepeatableGroupDecl) (declaration : FlatFieldDecl) : Bool :=
  match model.lookupUniqueId declaration.id with
  | .error _ => false
  | .ok admitted => admitted == declaration && declaration.groupPath == group.path &&
      declaration.repeatableScope == model.repeatableScopeForGroupPath group.path &&
      declaration.repeatableScope.getLast? == some group.level

/-- The shared checked selection core before a carrier chooses whether it reads one field or retains
the selected group itself. -/
structure CheckedSemanticIndexSelection (model : FlatModel) where
  group : RepeatableGroupDecl
  indexDeclaration : FlatFieldDecl
  key : CheckedSemanticIndexKey
  modelWellFormed : model.validate.isOk = true
  groupOwned : model.repeatableGroups.contains group = true
  indexDeclared : (group.indexField == some indexDeclaration.id) = true
  indexOwned : model.admitsSemanticIndexDeclaration group indexDeclaration = true
  keyOwned : key.admittedBy model = true
  keyAgrees : key.agreesWith indexDeclaration = true

/-- Retain the selector's identity when the selected payload is the index field itself. This
projection lets selected extents reuse the field reader's normalization and current-key handling. -/
def CheckedSemanticIndexSelection.numericIndex (selection : CheckedSemanticIndexSelection model) : Bool :=
  match selection.indexDeclaration.policy.kind with | .number _ => true | _ => false

/-- A literal semantic index statically selecting the exact group that contains the authored rule.
Runtime row presence remains outside this certificate. -/
structure CheckedRuleGroupSemanticIndexSource (model : FlatModel) where
  ruleGroup : GroupPath
  selection : CheckedSemanticIndexSelection model
  groupSelected : (selection.group.path == ruleGroup) = true

/-- The index binds the nearest indexed ancestor (spec/08 §4); fixed descendants retain the
same row address, and a repeatable level below it is read at the rule's own row
([below-key selection](../../docs/sources/model-structure-and-declaration-probes.md#src-below-key-selection)). Only a
repeatable group is ever selected: an index nominated on the root or a fixed group is not read for a
selection, and `nominatesNonrepeatableIndexOnChain` reports it for the admission walk alone. -/
def FlatModel.semanticIndexGroupForPath? (model : FlatModel) (path : GroupPath) : Option RepeatableGroupDecl :=
  ((model.repeatableScopeForGroupPath path).filterMap fun level =>
    (model.repeatableGroupAtLevel? level).filter (·.indexField.isSome)).getLast?

/-- Whether the root or a fixed group on `path`'s chain nominates an index field. A key whose chain has
no repeatable index group but one such nomination is no missing-index case where the chain crosses a
repetition: the operand's unbound repeatable level answers, with the missing-wildcard class when the
operand binds no level of its own, in the rule check `SemanticIndexPinnedLevelLawsTest` at
a12-dmkits `fecf8552`
([inbound](../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-27)). A chain that crosses no
repetition, a starred operand and a rule bound to the repetition are admitted by the Kernel
(unknown-scale-and-root-index-2026-10-28, `ug2`–`ug13`); no selection here reads such an index. -/
def FlatModel.nominatesNonrepeatableIndexOnChain (model : FlatModel) (path : GroupPath) : Bool :=
  model.nonrepeatableIndexFields.any fun (group, _) => group.isPrefixOf path

/-- The identity a literal key spelling has in `index`'s column. A Number index reads it as a decimal,
taking a comma for the separator; any other index keeps the text. `none` is a spelling the Number
column cannot read. -/
def FlatFieldDecl.semanticIndexLiteral? (index : FlatFieldDecl) (spelling : String) :
    Option SemanticIndexKey :=
  match index.policy.kind with
  | .number _ => (parseNumericFormalRead? (spelling.replace "," ".")).map (.number ·.value)
  | _ => some (.text spelling)

/-- A target lies inside the selected group, at its level or at a repeatable level below it. The
selection replaces only the group's own coordinate; every level below it is the rule's to bind, and an
unbound one draws the walk's `MVK_NO_WILDCARD` before this certificate is asked (spec/08 §4.3,
[below-key selection](../../docs/sources/model-structure-and-declaration-probes.md#src-below-key-selection)). -/
def FlatModel.admitsSemanticIndexTarget (model : FlatModel)
    (group : RepeatableGroupDecl) (declaration : FlatFieldDecl) : Bool :=
  match model.lookupUniqueId declaration.id with
  | .error _ => false
  | .ok admitted => admitted == declaration && group.path.isPrefixOf declaration.groupPath &&
      (model.repeatableScopeForGroupPath group.path).isPrefixOf declaration.repeatableScope

/-- A semantic-index source certified against one indexed ancestor, its declared index field, one
selected target declaration at that group's repeatable scope or below it, and a literal or dynamic key. The index and target kinds
are unconstrained here: the shared column owner decides the index identity, and the selected target's
kind belongs to whichever consumer reads it. -/
structure CheckedSemanticIndexSource (model : FlatModel) where
  group : RepeatableGroupDecl
  indexDeclaration : FlatFieldDecl
  targetDeclaration : FlatFieldDecl
  key : CheckedSemanticIndexKey
  modelWellFormed : model.validate.isOk = true
  groupOwned : model.repeatableGroups.contains group = true
  indexDeclared : (group.indexField == some indexDeclaration.id) = true
  indexOwned :
    model.admitsSemanticIndexDeclaration group indexDeclaration = true
  targetOwned :
    model.admitsSemanticIndexTarget group targetDeclaration = true
  keyOwned : key.admittedBy model = true
  keyAgrees : key.agreesWith indexDeclaration = true

def CheckedSemanticIndexSelection.indexSource (selection : CheckedSemanticIndexSelection model) :
    CheckedSemanticIndexSource model := {
  group := selection.group, indexDeclaration := selection.indexDeclaration,
  targetDeclaration := selection.indexDeclaration, key := selection.key,
  modelWellFormed := selection.modelWellFormed, groupOwned := selection.groupOwned,
  indexDeclared := selection.indexDeclared, indexOwned := selection.indexOwned,
  targetOwned := by
    have pathSelf (path : GroupPath) : path.isPrefixOf path = true := by
      induction path <;> simp_all [GroupPath.isPrefixOf]
    have owned := selection.indexOwned
    cases resolved : model.lookupUniqueId selection.indexDeclaration.id <;>
      simp_all [FlatModel.admitsSemanticIndexDeclaration, FlatModel.admitsSemanticIndexTarget],
  keyOwned := selection.keyOwned, keyAgrees := selection.keyAgrees }

/-- Selection binds its own level, while the caller supplies the parent and key scopes and, for a
target below the selected group, the target's own scope. That scope repeats the selected level as
the prefix of the lower levels, so the iteration guard drops it again: the selection references only
the rule's rows below it. -/
def CheckedSemanticIndexSource.bindingScopes (source : CheckedSemanticIndexSource model) :
    List (List RepeatableLevel) :=
  [source.indexDeclaration.repeatableScope.dropLast, source.key.bindingScope] ++
    if source.indexDeclaration.repeatableScope.length < source.targetDeclaration.repeatableScope.length then
      [source.targetDeclaration.repeatableScope]
    else []

/-- A Number selected field keeps its own scale and empty-fillability metadata independently
of the index field's identity domain (`spec/08` §4). -/
structure CheckedNumericSemanticIndexSource (model : FlatModel) extends CheckedSemanticIndexSource model where
  field : FlatNumberField
  targetNumber : targetDeclaration.toNumberField? = some field

namespace CheckedSemanticIndexSource

/-- Selection reads both the index and any dynamic key, even when its target is a different field. -/
def referencesField (source : CheckedSemanticIndexSource model) (field : FieldId) : Bool :=
  source.targetDeclaration.id == field || source.indexDeclaration.id == field ||
    match source.key with
    | .field declaration => declaration.id == field
    | .literal _ _ => false

/-- Whether the declared index field compares by numeric value. This is the sole place the two key
identity domains are chosen between. -/
def numericIndex (checked : CheckedSemanticIndexSource model) : Bool :=
  match checked.indexDeclaration.policy.kind with
  | .number _ => true
  | _ => false

end CheckedSemanticIndexSource

/-- The checked ordered pair admitted on the measured `NumberOfFilledFields` carrier. Each member is
an ordinary checked semantic-index source; the extra witnesses retain the pair's shared selection
identity and distinct target declarations without evaluating a count. -/
structure CheckedFilledFieldCountSemanticIndexPair (model : FlatModel) where
  token : String
  first : CheckedSemanticIndexSource model
  second : CheckedSemanticIndexSource model
  sharedGroup : (first.group == second.group) = true
  sharedIndex : (first.indexDeclaration == second.indexDeclaration) = true
  firstKeyRetained : (first.key == .literal (.text token)) = true
  secondKeyRetained : (second.key == .literal (.text token)) = true
  distinctTargets : (first.targetDeclaration.id != second.targetDeclaration.id) = true

/-- One valid starred Number field and one valid exact-text semantic-index selection certified as
the same one-level target before the path-specific refusal is projected. It supplies no indexed
star evaluator. -/
structure CheckedStarredNumberSemanticIndexRefusal (model : FlatModel) where
  token : String
  starred : CheckedStarFieldPath model
  selection : CheckedSemanticIndexSource model
  field : FlatNumberField
  targetSelected : (starred.declaration == selection.targetDeclaration) = true
  targetNumber : starred.declaration.toNumberField? = some field
  groupSelected : (selection.group.path == starred.declaration.groupPath) = true
  oneLevel :
    (starred.path.axes.map (·.level) == [selection.group.level]) = true
  firstStarAtSelectedLevel : (starred.path.firstStar == 0) = true
  keyRetained : (selection.key == .literal (.text token)) = true

/-- The reduced raw-context instance: that route rebuilds the column from a one-group scan rather
than projecting the shared one, so it needs a Number index and a Number target. -/
structure CheckedNumberSemanticIndexSource (model : FlatModel)
    extends CheckedSemanticIndexSource model where
  singleGroup : toCheckedSemanticIndexSource.indexDeclaration.repeatableScope = [toCheckedSemanticIndexSource.group.level]
  scalarKey : toCheckedSemanticIndexSource.key.bindingScope = []
  indexNumber :
    toCheckedSemanticIndexSource.indexDeclaration.toNumberField?.isSome = true
  targetNumber :
    toCheckedSemanticIndexSource.targetDeclaration.toNumberField?.isSome = true

namespace CheckedNumberSemanticIndexSource

/-- The Number index field the reduced route scans, recovered from its own kind witness. -/
def indexField (checked : CheckedNumberSemanticIndexSource model) :
    FlatNumberField :=
  checked.indexDeclaration.toNumberField?.get checked.indexNumber

/-- The Number target the reduced route reads, recovered from its own kind witness. -/
def targetField (checked : CheckedNumberSemanticIndexSource model) :
    FlatNumberField :=
  checked.targetDeclaration.toNumberField?.get checked.targetNumber

end CheckedNumberSemanticIndexSource

private def elaborateSemanticIndexSelectionWithValidatedModel
    (model : FlatModel) (declaringGroup : GroupPath)
    (group : RepeatableGroupDecl) (authored : SurfaceSemanticIndexKey)
    (hModel : model.validate = .ok ()) (boundScope? : Option (List RepeatableLevel) := none) :
    Except SemanticIndexElabError (CheckedSemanticIndexSelection model) := do
  let scope := boundScope?.getD (model.repeatableScopeForGroupPath declaringGroup)
  let groupScope := model.repeatableScopeForGroupPath group.path
  if (groupScope.filterMap fun level =>
      (model.repeatableGroupAtLevel? level).filter (·.indexField.isSome)).length > 1 then
    throw .multipleIndexGroups
  let indexId ← match group.indexField with
    | some indexId => pure indexId
    | none => throw (.missingIndexField group.path)
  let indexDeclaration ← model.lookupUniqueId indexId |>.mapError .resolve
  let numericIndex := match indexDeclaration.policy.kind with
    | .number _ => true
    | _ => false
  let key ← match authored with
    | .literal token spelling =>
        -- The literal identity domain is owned by the declared index column, not by its carrier.
        match token, numericIndex with
        | .number _, true | .text _, false => pure (.literal token spelling)
        | _, _ =>
            throw (.indexKeyDomainMismatch indexDeclaration.path token)
    | .field reference =>
        let declaration ← model.resolveFieldDeclarationUnchecked
          declaringGroup reference |>.mapError .resolve
        let keyShape : SemanticIndexAdmissionKey := .reference {
          baseTypeMatchesIndexField :=
            declaration.policy.kind.surfaceKind.sharesValueListBaseType indexDeclaration.policy.kind.surfaceKind }
        if let some diagnostic := keyAgreementRefusal keyShape then
          throw (.keyAdmission diagnostic)
        if group.path.isPrefixOf declaration.groupPath then
          throw (.keyContainedInIndexedGroup declaration.path group.path)
        else
          if !declaration.repeatableScope.isPrefixOf scope then
            throw (.keyAdmission .semanticIndexKeyInvalidIteration)
          pure (.field declaration)
  if !groupScope.dropLast.isPrefixOf scope then
    throw (.resolve (.repeatableReference group.path))
  if hGroup : model.repeatableGroups.contains group = true then
    if hDeclared : group.indexField == some indexDeclaration.id then
      if hIndexOwned :
          model.admitsSemanticIndexDeclaration group indexDeclaration = true then
        if hKeyOwned : key.admittedBy model = true then
          if hKeyAgrees : key.agreesWith indexDeclaration = true then
            pure {
              group
              indexDeclaration
              key
              modelWellFormed := by rw [hModel]; rfl
              groupOwned := hGroup
              indexDeclared := hDeclared
              indexOwned := hIndexOwned
              keyOwned := hKeyOwned
              keyAgrees := hKeyAgrees
            }
          else
            throw .incoherentCore
        else
          throw .incoherentCore
      else
        throw .incoherentCore
    else
      throw .incoherentCore
  else
    throw .incoherentCore

/-- Certify the shared selection before an extent consumer binds the chosen row. -/
def elaborateSemanticIndexSelection (model : FlatModel) (declaringGroup : GroupPath)
    (group : RepeatableGroupDecl) (key : SurfaceSemanticIndexKey)
    (boundScope? : Option (List RepeatableLevel) := none) :
    Except SemanticIndexElabError (CheckedSemanticIndexSelection model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => elaborateSemanticIndexSelectionWithValidatedModel model declaringGroup group key hModel boundScope?

/-- One exact group selected by a literal text key, retaining the resolved group, index declaration,
and authored token for carrier-specific static checks. -/
structure CheckedTextSemanticIndexGroupSelection (model : FlatModel) where
  groupPath : GroupPath
  token : String
  selection : CheckedSemanticIndexSelection model
  groupSelected : (selection.group.path == groupPath) = true
  keyRetained : (selection.key == .literal (.text token)) = true

/-- Select an exact group by a literal text key after model validation. Rule groups, indexed
group-field fill checks, and indexed filled-group counts share this core while retaining their
carrier-specific operator and diagnostic boundaries. -/
private def elaborateTextSemanticIndexGroupSelectionWithValidatedModel
    (model : FlatModel) (declaringGroup groupPath : GroupPath) (token : String)
    (hModel : model.validate = .ok ()) :
    Except SemanticIndexElabError (CheckedTextSemanticIndexGroupSelection model) := do
  if !model.hasGroupPath groupPath then
    throw (.resolve (.unknownRepeatableGroup groupPath))
  let group ← match model.repeatableGroups.find?
      (fun candidate => candidate.path == groupPath) with
    | some group => pure group
    | none => throw (.missingIndexField groupPath)
  let selection ← elaborateSemanticIndexSelectionWithValidatedModel model declaringGroup
    group (.literal (.text token)) hModel
  if hSelected : selection.group.path == groupPath then
    if hKey : selection.key == .literal (.text token) then
      pure { groupPath, token, selection, groupSelected := hSelected, keyRetained := hKey }
    else
      throw .incoherentCore
  else
    throw .incoherentCore

/-- Resolve and certify one literal text-indexed group. Carrier-specific acceptance, refusal, and
runtime behavior remain with the caller. -/
def elaborateTextSemanticIndexGroupSelection (model : FlatModel)
    (declaringGroup : GroupPath) (authoredGroup : SurfaceGroupPath) (token : String) :
    Except SemanticIndexElabError (CheckedTextSemanticIndexGroupSelection model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let groupPath ← authoredGroup.resolveAgainst declaringGroup |>.mapError .group
      elaborateTextSemanticIndexGroupSelectionWithValidatedModel model declaringGroup
        groupPath token hModel

/-- Certify the reviewed literal semantic-index suffix on `RuleGroup`. A known nonrepeatable group
has no index declaration and therefore reaches the same missing-index class as an unindexed
repeatable group; an unknown group still fails as a resolution error
([checkpoint](../../docs/sources/inbound-group-operand-batches.md#src-pr2-rulegroup-semantic-index)). -/
def elaborateRuleGroupSemanticIndexSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceRuleGroupSemanticIndex) :
    Except SemanticIndexElabError (CheckedRuleGroupSemanticIndexSource model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let checked ← elaborateTextSemanticIndexGroupSelectionWithValidatedModel model
        declaringGroup declaringGroup authored.token hModel
      pure {
        ruleGroup := checked.groupPath
        selection := checked.selection
        groupSelected := checked.groupSelected }

/-- Resolve the target before its nearest indexed ancestor. The caller binds the ancestor's
parent scope and any key field; selection supplies only the indexed coordinate (spec/08 §4). -/
def elaborateSemanticIndexSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceSemanticIndex)
    (boundScope? : Option (List RepeatableLevel) := none) :
    Except SemanticIndexElabError (CheckedSemanticIndexSource model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let targetDeclaration ← model.resolveFieldDeclarationUnchecked
        declaringGroup authored.target |>.mapError .resolve
      let some group := model.semanticIndexGroupForPath? targetDeclaration.groupPath
        | throw (.missingIndexField targetDeclaration.groupPath)
      let selection ← elaborateSemanticIndexSelectionWithValidatedModel model declaringGroup
        group authored.key hModel boundScope?
      if hTargetOwned :
          model.admitsSemanticIndexTarget selection.group targetDeclaration = true then
        pure {
          group := selection.group
          indexDeclaration := selection.indexDeclaration
          targetDeclaration
          key := selection.key
          modelWellFormed := selection.modelWellFormed
          groupOwned := selection.groupOwned
          indexDeclared := selection.indexDeclared
          indexOwned := selection.indexOwned
          targetOwned := hTargetOwned
          keyOwned := selection.keyOwned
          keyAgrees := selection.keyAgrees
        }
      else
        throw .incoherentCore

theorem elaborateSemanticIndexSource_declaringGroupValid
    {model : FlatModel} {declaringGroup : GroupPath} {authored : SurfaceSemanticIndex}
    {checked : CheckedSemanticIndexSource model} {boundScope? : Option (List RepeatableLevel)}
    (ok : elaborateSemanticIndexSource model declaringGroup authored boundScope? = .ok checked) :
    GroupPath.isValid declaringGroup = true := by
  unfold elaborateSemanticIndexSource at ok
  split at ok
  · cases ok
  · cases hTarget : model.resolveFieldDeclarationUnchecked declaringGroup authored.target with
    | error error => simp [hTarget, Except.mapError, bind, Except.bind] at ok
    | ok declaration => exact FlatModel.resolveFieldDeclarationUnchecked_declaringGroupValid hTarget

/-- Certify the exact reviewed pair of index-selected fields for `NumberOfFilledFields`. The two
ordinary sources are checked independently, then narrowed to one group/index/token identity and two
distinct targets; the wrapper supplies no runtime field-count evaluator. -/
def elaborateFilledFieldCountSemanticIndexPair (model : FlatModel)
    (declaringGroup : GroupPath)
    (authored : SurfaceFilledFieldCountSemanticIndexPair) :
    Except FilledFieldCountSemanticIndexPairElabError
      (CheckedFilledFieldCountSemanticIndexPair model) := do
  let first ← elaborateSemanticIndexSource model declaringGroup {
      target := authored.firstTarget
      key := .literal (.text authored.token) }
    |>.mapError .first
  let second ← elaborateSemanticIndexSource model declaringGroup {
      target := authored.secondTarget
      key := .literal (.text authored.token) }
    |>.mapError .second
  if hGroup : first.group == second.group then
    if hIndex : first.indexDeclaration == second.indexDeclaration then
      if hFirstKey : first.key == .literal (.text authored.token) then
        if hSecondKey : second.key == .literal (.text authored.token) then
          if hDistinct : first.targetDeclaration.id != second.targetDeclaration.id then
            pure {
              token := authored.token
              first
              second
              sharedGroup := hGroup
              sharedIndex := hIndex
              firstKeyRetained := hFirstKey
              secondKeyRetained := hSecondKey
              distinctTargets := hDistinct }
          else
            throw (.duplicateTarget first.targetDeclaration.path)
        else
          throw .incoherentCore
      else
        throw .incoherentCore
    else
      throw .incoherentCore
  else
    throw (.differentGroup first.group.path second.group.path)

/-- Certify the exact one-level starred Number target and its otherwise-valid literal text
semantic-index selection before returning the measured wildcard/index refusal. -/
def elaborateStarredNumberSemanticIndexRefusal (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceStarredNumberSemanticIndexUse) :
    Except StarredNumberSemanticIndexRefusalError
      (CheckedStarredNumberSemanticIndexRefusal model) := do
  let starred ← elaborateStarFieldPath model declaringGroup authored.target
    |>.mapError .starPath
  let selection ← elaborateSemanticIndexSource model declaringGroup {
      target := authored.target.toFieldPath
      key := .literal (.text authored.token) }
    |>.mapError .semanticIndex
  if hTarget : starred.declaration == selection.targetDeclaration then
    match hNumber : starred.declaration.toNumberField? with
    | none => throw (.targetNotNumber starred.declaration.path)
    | some field =>
        if hGroup : selection.group.path == starred.declaration.groupPath then
          if hLevel : starred.path.axes.map (·.level) == [selection.group.level] then
            if hFirstStar : starred.path.firstStar == 0 then
              if hKey : selection.key == .literal (.text authored.token) then
                pure {
                  token := authored.token
                  starred
                  selection
                  field
                  targetSelected := hTarget
                  targetNumber := hNumber
                  groupSelected := hGroup
                  oneLevel := hLevel
                  firstStarAtSelectedLevel := hFirstStar
                  keyRetained := hKey }
              else
                throw .incoherentCore
            else
              throw (.unsupportedTopology
                (starred.path.axes.map (·.level)) starred.path.firstStar
                selection.group.level)
          else
            throw (.unsupportedTopology
              (starred.path.axes.map (·.level)) starred.path.firstStar
              selection.group.level)
        else
          throw .incoherentCore
  else
    throw .incoherentCore

namespace CheckedStarredNumberSemanticIndexRefusal

/-- The exact path diagnostic measured after both component certificates succeed. -/
def diagnostic (_ : CheckedStarredNumberSemanticIndexRefusal model) :
    KernelStaticDiagnostic :=
  .semanticIndexAndWildcard

end CheckedStarredNumberSemanticIndexRefusal

/-- Project the exact refusal without assigning its code to an invalid index selection, an
unstarred path, a non-Number target, or a wider repetition topology. -/
def projectStarredNumberSemanticIndexDiagnostic? (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceStarredNumberSemanticIndexUse) :
    Option KernelStaticDiagnostic :=
  match elaborateStarredNumberSemanticIndexRefusal model declaringGroup authored with
  | .ok checked => some checked.diagnostic
  | .error _ => none

/-- Refine the general source to the reduced raw-context route's Number index and Number target. -/
def elaborateNumberSemanticIndexSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceNumberSemanticIndex) :
    Except SemanticIndexElabError (CheckedNumberSemanticIndexSource model) := do
  let checked ← elaborateSemanticIndexSource model declaringGroup authored
  -- The reduced route reads its target at the selected row alone, so a target below it stays out.
  if checked.targetDeclaration.repeatableScope != [checked.group.level] then
    throw .reducedRouteNeedsSingleGroup
  if hSingle : checked.indexDeclaration.repeatableScope = [checked.group.level] then
    if hKey : checked.key.bindingScope = [] then
      if hIndex : checked.indexDeclaration.toNumberField?.isSome = true then
        if hTarget : checked.targetDeclaration.toNumberField?.isSome = true then
          pure { toCheckedSemanticIndexSource := checked
                 singleGroup := hSingle, scalarKey := hKey
                 indexNumber := hIndex, targetNumber := hTarget }
        else throw (.reducedRouteNeedsNumber checked.targetDeclaration.path)
      else throw (.reducedRouteNeedsNumber checked.indexDeclaration.path)
    else throw .reducedRouteNeedsSingleGroup
  else throw .reducedRouteNeedsSingleGroup

inductive SemanticIndexContextError where
  | topology (error : SingleGroupContextError)
  | checkedColumn (error : CheckedIndexColumnError)
  deriving Repr, DecidableEq

private structure NumberIndexCandidate where
  row : RowIndex
  key : RepetitionKeyComponent
  deriving Repr, DecidableEq

private def scanNumberIndexKeys (context : SingleGroupValidationContext)
    (indexField : FlatNumberField) : List RowIndex → List NumberIndexCandidate
  | [] => []
  | row :: remaining =>
      let key := match observeCell .validation (context.read row indexField.id) with
        | .value (.num value) => .present (.number value)
        | .empty => .empty
        | .unknown cause | .poison cause => .unknown cause
        | .value _ => .unknown .malformed
      { row, key } :: scanNumberIndexKeys context indexField remaining

private def NumberIndexCandidate.resolved
    (level : RepeatableLevel) (candidate : NumberIndexCandidate) :
    ResolvedRepetitionKeyRow :=
  { row := [(level, candidate.row)], key := [candidate.key] }

private def NumberIndexCandidate.directUnavailable? :
    NumberIndexCandidate → Option FormalCause
  | { key := .empty, .. } => some .indexRequired
  | { key := .unknown cause, .. } => some cause
  | _ => none

private def NumberIndexCandidates.toColumn
    (candidates : List NumberIndexCandidate) (level : RepeatableLevel)
    (readTarget : RowIndex → CheckedCell) :
    ResolvedSemanticIndexColumn :=
  let results := evalRepetitionNotUnique (candidates.map (·.resolved level))
  let unavailableKey := match
      (candidates.filterMap NumberIndexCandidate.directUnavailable?).head? with
    | some cause => some cause
    | none =>
        if results.any fun result => match result.verdict with
          | .fired _ => true
          | _ => false then
          some .duplicateIndex
        else
          none
  let entries := (candidates.zip results).filterMap fun pair =>
    match pair.1.key, pair.2.verdict with
    | .present (.number key), .notFired =>
        some {
          token := SemanticIndexKey.number key
          target := readTarget pair.1.row
        }
    | _, _ => none
  { entries, unavailableKey }

namespace CheckedSemanticIndexSource

/-- Dynamic non-Number keys compare by normalized cache text (spec/06, stored-value checking and normalization), as the column does; a checked Boolean,
Enumeration or temporal payload cannot recover that identity. String observations already carry
the one-pass evaluated value, including changed-cell readers; normalizing their spelling again
would consume newly exposed CRLF pairs (spec/02 §3). Preserve empty and formal failure
before consulting spelling, so failed producers retain their computation poison. -/
def observeCurrentKey (checked : CheckedSemanticIndexSource model) (phase : Phase)
    (read : FieldId → CheckedCell) (stored : FieldId → Option String) :
    Except SemanticIndexContextError CellObservation := do
  let observation := checked.key.observeWith fun declaration => observeCell phase (read declaration.id)
  if checked.numericIndex then return observation
  match checked.key, observation with
  | .field _, .value (.str _) => pure observation
  | .field declaration, .value _ =>
      match stored declaration.id with
      | some token => pure (.value (.str (normalizeEvaluatedString token)))
      | none => throw (.checkedColumn (.missingStoredValue { field := declaration.id, path := [] }))
  | _, _ => pure observation

/-- Project the shared generated-preliminary index column into semantic-index's clean unique-entry
policy without rebuilding topology, defaults, or generated findings. This route needs only the
selected target's id, so it serves every target kind. -/
def resolvePreliminaryColumn
    (checked : CheckedSemanticIndexSource model)
    (preliminary : CheckedIndexPreliminary model) (outer : Env := [])
    (read : CellAddr → Except CheckedDocumentError CheckedCell := preliminary.readAuthoredValidation) :
    Except SemanticIndexContextError ResolvedSemanticIndexColumn := do
  let column ← preliminary.resolveIndexColumn checked.group outer
    |>.mapError .checkedColumn
  column.toSemanticIndexColumnWith read checked.targetDeclaration.id outer
    |>.mapError .checkedColumn

/-- Keep the prepared index column fixed while reading the selected target and dynamic key from
current views. Computation targets cannot be index fields (`spec/09`), but their values may supply
lookup keys or selected payloads; selection must therefore retain addresses rather than stored values. -/
def lookupPreliminaryValueWith
    (checked : CheckedSemanticIndexSource model)
    (preliminary : CheckedIndexPreliminary model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (keyRead : FlatFieldDecl → CellObservation) (phase : Phase) (outer : Env := []) :
    Except SemanticIndexContextError CellObservation := do
  let column ← checked.resolvePreliminaryColumn preliminary outer read
  pure (column.lookupObservationForIndex phase checked.numericIndex
    (checked.key.observeWith keyRead))

/-- Evaluate a literal or dynamic key over the immutable checked preliminary document through the
common resolved-column evaluator, under the identity the declared index field uses. -/
def lookupPreliminaryValue
    (checked : CheckedSemanticIndexSource model)
    (preliminary : CheckedIndexPreliminary model)
    (keyRaw : RawFlatContext) (phase : Phase) (outer : Env := []) :
    Except SemanticIndexContextError CellObservation :=
  checked.lookupPreliminaryValueWith preliminary preliminary.readAuthoredValidation
    (fun source => observeCell phase ((model.checkContext keyRaw).read source.id)) phase outer

end CheckedSemanticIndexSource

namespace CheckedNumberSemanticIndexSource

/-- Validate row topology, apply declaration-owned key and target checks, remove every duplicate-key participant, and retain one unavailable-column cause. -/
def resolveColumn (checked : CheckedNumberSemanticIndexSource model)
    (raw : RawSingleGroupContext) :
    Except SemanticIndexContextError ResolvedSemanticIndexColumn := do
  raw.validate |>.mapError .topology
  let context := model.checkSingleGroupContext checked.group raw
  pure (NumberIndexCandidates.toColumn
    (scanNumberIndexKeys context checked.indexField raw.candidates)
    checked.group.level (fun row => checked.targetDeclaration.checkRaw (raw.read row checked.targetDeclaration.id)))

/-- Evaluate the checked literal or dynamic Number lookup through the sole resolved phase-policy owner. -/
def lookupValue (checked : CheckedNumberSemanticIndexSource model)
    (raw : RawSingleGroupContext) (keyRaw : RawFlatContext) (phase : Phase) :
    Except SemanticIndexContextError CellObservation := do
  let column ← checked.resolveColumn raw
  let key := checked.key.observe model keyRaw phase
  pure (column.lookupNumberObservation phase key)

/-- Project a checked validation read into the established target-declaration-owned Number comparison operand. -/
def validationNumberOperand (checked : CheckedNumberSemanticIndexSource model)
    (raw : RawSingleGroupContext) (keyRaw : RawFlatContext) :
    Except SemanticIndexContextError NumericOperand := do
  let column ← checked.resolveColumn raw
  let key := checked.key.observe model keyRaw .validation
  pure (column.validationNumberObservedKeyOperand checked.targetField.info key)

end CheckedNumberSemanticIndexSource

/-- Refine an already checked selection by the target's Number kind, without narrowing the index kind. -/
def elaborateNumericSemanticIndexSource (model : FlatModel) (declaringGroup : GroupPath)
    (surface : SurfaceSemanticIndex) (boundScope? : Option (List RepeatableLevel) := none) :
    Except SemanticIndexElabError (CheckedNumericSemanticIndexSource model) := do
  let source ← elaborateSemanticIndexSource model declaringGroup surface boundScope?
  match h : source.targetDeclaration.toNumberField? with
  | none => throw (.targetNotNumber source.targetDeclaration.path)
  | some field => pure { toCheckedSemanticIndexSource := source, field, targetNumber := h }

end A12Kernel
