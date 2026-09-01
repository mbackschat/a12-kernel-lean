import A12Kernel.Elaboration.CheckedIndexColumn
import A12Kernel.Elaboration.FieldEntityList
import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Semantics.RepetitionNotUnique
import A12Kernel.Semantics.SemanticIndex

/-! # Checked one-group semantic-index construction

A semantic index selects one row of a group by its declared index field's value. This capsule
certifies that selection and hands it to the resolved evaluator, which owns the phase policy.

The **index field's kind is not narrowed**: a Number index compares by numeric value and every other
kind by exact stored text, and the shared checked column owner already decides that identity, so this
certificate carries the declaration rather than a Number field. The measured Kernel rule is that the
index kind and the selected target's kind are independent. The **reduced raw-context route** below
stays a Number-index, Number-target instance, because it rebuilds the column from a one-group scan
rather than projecting the shared one; the **immutable generated-preliminary route** serves the
general case and only needs the target's id.

Two boundaries stay outside deliberately. This project performs no lexing, so an authored literal key
reaches the surface already decoded into the identity its index field uses, and the Kernel's
declaration-format check on that token — `MVK_INDEX_VALUE_INVALID`, which rejects `For "250"` against
a `minFractionalDigits = 2` field — therefore has no representation here. Repeatable field-valued
keys, nested indices, and concrete syntax also remain outside.
-/

namespace A12Kernel

inductive SurfaceSemanticIndexKey where
  /-- A declaration-admitted literal, already decoded into the identity its declared index field
  uses. The Kernel's format check on the authored token sits outside this project's boundary. -/
  | literal (token : SemanticIndexKey)
  /-- A field whose checked current value supplies the lookup key. -/
  | field (reference : SurfaceFieldPath)
  deriving Repr, DecidableEq

structure SurfaceSemanticIndex where
  target : SurfaceFieldPath
  key : SurfaceSemanticIndexKey
  deriving Repr, DecidableEq

/-- The measured exact-text literal semantic-index suffix on the reserved `RuleGroup` entity.
Keeping this surface distinct excludes unmeasured numeric literals, field-valued keys, and
wildcard-plus-index combinations ([checkpoint](../../docs/SOURCES.md#src-pr2-rulegroup-semantic-index)). -/
structure SurfaceRuleGroupSemanticIndex where
  token : String
  deriving Repr, DecidableEq

/-- The exact reviewed two-field `NumberOfFilledFields` carrier: two authored target paths, one
exact-text semantic-index key, and no runtime count claim. Other arities and key forms have distinct
surface types or no representation ([checkpoint](../../docs/SOURCES.md#src-pr2-semantic-index-carrier-matrix)). -/
structure SurfaceFilledFieldCountSemanticIndexPair where
  firstTarget : SurfaceFieldPath
  secondTarget : SurfaceFieldPath
  token : String
  deriving Repr, DecidableEq

/-- The two reviewed field-fill carriers that accept one index-selected group followed by one direct
field. Keeping the operator closed here prevents the static admission from transferring to another
quantifier ([checkpoint](../../docs/SOURCES.md#src-pr2-semantic-index-carrier-matrix)). -/
inductive IndexedGroupFieldFillOperator where
  | allFieldsFilled
  | noFieldFilled
  deriving Repr, DecidableEq

/-- The exact reviewed indexed-group/direct-field authoring shape. Stars, filters, selected fields,
additional operands, and reversed order have no representation in this certificate
([checkpoint](../../docs/SOURCES.md#src-pr2-semantic-index-carrier-matrix)). -/
structure SurfaceIndexedGroupFieldFillPair where
  operator : IndexedGroupFieldFillOperator
  group : SurfaceGroupPath
  token : String
  field : SurfaceFieldPath
  deriving Repr, DecidableEq

/-- The Number surface retained for the reduced raw-context route, whose literal is a numeric value. -/
abbrev SurfaceNumberSemanticIndexKey := SurfaceSemanticIndexKey
abbrev SurfaceNumberSemanticIndex := SurfaceSemanticIndex

inductive SemanticIndexElabError where
  | resolve (error : ResolveError)
  | group (error : SingleGroupElabError)
  | missingIndexField (groupPath : GroupPath)
  /-- The literal key's identity domain disagrees with the declared index field's: a numeric literal
  against a text-identity index, or a text literal against a Number one. -/
  | indexKeyDomainMismatch (path : List String) (key : SemanticIndexKey)
  | keyFieldNotNumber (path : List String)
  /-- The reduced raw-context route needs a Number index and a Number target; the general
  preliminary route does not. -/
  | reducedRouteNeedsNumber (path : List String)
  /-- The field-valued key is read from inside the indexed group itself. -/
  | keyContainedInIndexedGroup (path : List String) (groupPath : GroupPath)
  | incoherentCore

  deriving Repr, DecidableEq

namespace SemanticIndexElabError

/-- Project the two refusals with measured Kernel diagnostics. The reduced-route and coherence
classes stay unmapped, because they are this project's own boundary rather than the Kernel's. -/
def diagnostic? : SemanticIndexElabError → Option KernelStaticDiagnostic
  | .keyContainedInIndexedGroup _ _ => some .semanticIndexContainedInIndex
  | .resolve error => error.diagnostic?
  | _ => none

/-- Exact diagnostic projection measured for the `RuleGroup` literal suffix. A missing index on
other carriers requires its own evidence before it can inherit this code
([checkpoint](../../docs/SOURCES.md#src-pr2-rulegroup-semantic-index)). -/
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

inductive IndexedGroupFieldFillPairElabError where
  | groupReference (error : SingleGroupElabError)
  | semanticIndex (error : SemanticIndexElabError)
  | fieldEntity (error : FieldEntityShapeElabError)
  | incoherentCore
  deriving Repr, DecidableEq

inductive CheckedSemanticIndexKey where
  | literal (token : SemanticIndexKey)
  | field (source : FlatFieldDecl)
  deriving Repr, DecidableEq

namespace CheckedSemanticIndexKey

/-- The dynamic key field must be the exact nonrepeatable declaration retained by the checked model. A literal has no additional model owner. -/
def admittedBy (key : CheckedSemanticIndexKey) (model : FlatModel) : Bool :=
  match key with
  | .literal _ => true
  | .field source =>
      match model.lookupUniqueId source.id with
      | .ok admitted => admitted == source && source.repeatableScope.isEmpty
      | .error _ => false

/-- Apply declaration-owned checking to a dynamic key and retain the requested phase. A literal
bypasses the raw context, rendered into the value domain the shared lookup dispatch consumes. -/
def observe (key : CheckedSemanticIndexKey) (model : FlatModel)
    (raw : RawFlatContext) (phase : Phase) : CellObservation :=
  match key with
  | .literal (.number value) => .value (.num value)
  | .literal (.text token) => .value (.str token)
  | .field source => observeCell phase ((model.checkContext raw).read source.id)

end CheckedSemanticIndexKey

/-- The shared checked selection core before a carrier chooses whether it reads one field or retains
the selected group itself. -/
structure CheckedSemanticIndexSelection (model : FlatModel) where
  group : RepeatableGroupDecl
  indexDeclaration : FlatFieldDecl
  key : CheckedSemanticIndexKey
  modelWellFormed : model.validate.isOk = true
  groupOwned : model.repeatableGroups.contains group = true
  indexDeclared : (group.indexField == some indexDeclaration.id) = true
  indexOwned : model.admitsSingleGroupDeclaration group indexDeclaration = true
  keyOwned : key.admittedBy model = true

/-- A literal semantic index statically selecting the exact group that contains the authored rule.
Runtime row presence remains outside this certificate. -/
structure CheckedRuleGroupSemanticIndexSource (model : FlatModel) where
  ruleGroup : GroupPath
  selection : CheckedSemanticIndexSelection model
  groupSelected : (selection.group.path == ruleGroup) = true

/-- A semantic-index source certified against one exact target group, its declared index field, one
selected target declaration in that group, and a literal or dynamic key. The index and target kinds
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
    model.admitsSingleGroupDeclaration group indexDeclaration = true
  targetOwned :
    model.admitsSingleGroupDeclaration group targetDeclaration = true
  keyOwned : key.admittedBy model = true

namespace CheckedSemanticIndexSource

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

/-- Static authoring certificate for the reviewed indexed-group/direct-field pair. It retains the
operator and authored order together with the selected group, index declaration, exact-text key, and
direct nonrepeatable field; it supplies no field-fill evaluator. -/
structure CheckedIndexedGroupFieldFillPair (model : FlatModel) where
  operator : IndexedGroupFieldFillOperator
  groupPath : GroupPath
  token : String
  selection : CheckedSemanticIndexSelection model
  field : FlatFieldDecl
  groupSelected : (selection.group.path == groupPath) = true
  keyRetained : (selection.key == .literal (.text token)) = true
  fieldOwned : model.fields.contains field = true
  fieldNonrepeatable : field.repeatableScope.isEmpty = true
  fieldOutsideSelection : (!selection.group.path.isPrefixOf field.groupPath) = true

/-- The reduced raw-context instance: that route rebuilds the column from a one-group scan rather
than projecting the shared one, so it needs a Number index and a Number target. -/
structure CheckedNumberSemanticIndexSource (model : FlatModel)
    extends CheckedSemanticIndexSource model where
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
    (hModel : model.validate = .ok ()) :
    Except SemanticIndexElabError (CheckedSemanticIndexSelection model) := do
  let indexId ← match group.indexField with
    | some indexId => pure indexId
    | none => throw (.missingIndexField group.path)
  let indexDeclaration ← model.lookupUniqueId indexId |>.mapError .resolve
  let numericIndex := match indexDeclaration.policy.kind with
    | .number _ => true
    | _ => false
  let key ← match authored with
    | .literal token =>
        -- The literal identity domain is owned by the declared index column, not by its carrier.
        match token, numericIndex with
        | .number _, true | .text _, false => pure (.literal token)
        | _, _ =>
            throw (.indexKeyDomainMismatch indexDeclaration.path token)
    | .field reference =>
        let declaration ← model.resolveFieldDeclarationUnchecked
          declaringGroup reference |>.mapError .resolve
        if group.path.isPrefixOf declaration.groupPath then
          throw (.keyContainedInIndexedGroup declaration.path group.path)
        else
          let checkedDeclaration ← declaration.requireNonrepeatable
            |>.mapError .resolve
          pure (.field checkedDeclaration)
  if hGroup : model.repeatableGroups.contains group = true then
    if hDeclared : group.indexField == some indexDeclaration.id then
      if hIndexOwned :
          model.admitsSingleGroupDeclaration group indexDeclaration = true then
        if hKeyOwned : key.admittedBy model = true then
          pure {
            group
            indexDeclaration
            key
            modelWellFormed := by rw [hModel]; rfl
            groupOwned := hGroup
            indexDeclared := hDeclared
            indexOwned := hIndexOwned
            keyOwned := hKeyOwned
          }
        else
          throw .incoherentCore
      else
        throw .incoherentCore
    else
      throw .incoherentCore
  else
    throw .incoherentCore

private structure CheckedTextSemanticIndexGroupSelection (model : FlatModel) where
  groupPath : GroupPath
  token : String
  selection : CheckedSemanticIndexSelection model
  groupSelected : (selection.group.path == groupPath) = true
  keyRetained : (selection.key == .literal (.text token)) = true

/-- Select an exact group by a literal text key after model validation. Both reviewed group-valued
carriers use this core; their operator and diagnostic boundaries remain carrier-specific. -/
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

/-- Certify the reviewed literal semantic-index suffix on `RuleGroup`. A known nonrepeatable group
has no index declaration and therefore reaches the same missing-index class as an unindexed
repeatable group; an unknown group still fails as a resolution error
([checkpoint](../../docs/SOURCES.md#src-pr2-rulegroup-semantic-index)). -/
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

/-- Resolve the target first, then require its exact one-level repeatable group, its declared index
field of any kind, and a literal whose identity domain matches that index or a nonrepeatable field
key. -/
def elaborateSemanticIndexSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceSemanticIndex) :
    Except SemanticIndexElabError (CheckedSemanticIndexSource model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let targetDeclaration ← model.resolveFieldDeclarationUnchecked
        declaringGroup authored.target |>.mapError .resolve
      let group ← model.lookupUniqueRepeatablePath targetDeclaration.groupPath
        |>.mapError .resolve
      let selection ← elaborateSemanticIndexSelectionWithValidatedModel model declaringGroup
        group authored.key hModel
      if hTargetOwned :
          model.admitsSingleGroupDeclaration selection.group targetDeclaration = true then
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
        }
      else
        throw .incoherentCore

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

/-- Certify the reviewed `AllFieldsFilled`/`NoFieldFilled` indexed-group pair. Group selection and
direct-field resolution reuse their existing checked owners, while this carrier retains order and
prevents the direct operand from collapsing into the selected group's expansion. Runtime truth and
polarity remain outside the certificate. -/
def elaborateIndexedGroupFieldFillPair (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceIndexedGroupFieldFillPair) :
    Except IndexedGroupFieldFillPairElabError
      (CheckedIndexedGroupFieldFillPair model) :=
  match hModel : model.validate with
  | .error error => .error (.semanticIndex (.resolve error))
  | .ok () => do
      let groupPath ← authored.group.resolveAgainst declaringGroup
        |>.mapError .groupReference
      let checkedGroup ← elaborateTextSemanticIndexGroupSelectionWithValidatedModel model
        declaringGroup groupPath authored.token hModel
        |>.mapError .semanticIndex
      let resolvedField ← resolveFieldEntityOperandIn model declaringGroup []
        (.field authored.field .stored) |>.mapError .fieldEntity
      let field ← match resolvedField with
        | .field declaration .stored => pure declaration
        | _ => throw .incoherentCore
      if hOwned : model.fields.contains field = true then
        if hNonrepeatable : field.repeatableScope.isEmpty = true then
          if hOutside :
              (!checkedGroup.selection.group.path.isPrefixOf field.groupPath) = true then
            pure {
              operator := authored.operator
              groupPath := checkedGroup.groupPath
              token := checkedGroup.token
              selection := checkedGroup.selection
              field
              groupSelected := checkedGroup.groupSelected
              keyRetained := checkedGroup.keyRetained
              fieldOwned := hOwned
              fieldNonrepeatable := hNonrepeatable
              fieldOutsideSelection := hOutside }
          else
            throw .incoherentCore
        else
          throw .incoherentCore
      else
        throw .incoherentCore

/-- Refine the general source to the reduced raw-context route's Number index and Number target. -/
def elaborateNumberSemanticIndexSource (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceNumberSemanticIndex) :
    Except SemanticIndexElabError (CheckedNumberSemanticIndexSource model) := do
  let checked ← elaborateSemanticIndexSource model declaringGroup authored
  if hIndex : checked.indexDeclaration.toNumberField?.isSome = true then
    if hTarget : checked.targetDeclaration.toNumberField?.isSome = true then
      match checked.key with
      | .field source =>
          if source.toNumberField?.isSome then
            pure {
              toCheckedSemanticIndexSource := checked
              indexNumber := hIndex
              targetNumber := hTarget }
          else
            throw (.keyFieldNotNumber source.path)
      | .literal _ =>
          pure {
            toCheckedSemanticIndexSource := checked
            indexNumber := hIndex
            targetNumber := hTarget }
    else
      throw (.reducedRouteNeedsNumber checked.targetDeclaration.path)
  else
    throw (.reducedRouteNeedsNumber checked.indexDeclaration.path)

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
  | { key := .empty, .. } => some .required
  | { key := .unknown cause, .. } => some cause
  | _ => none

private def NumberIndexCandidates.toColumn
    (candidates : List NumberIndexCandidate) (level : RepeatableLevel)
    (context : SingleGroupValidationContext) (targetField : FlatNumberField) :
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
          target := context.read pair.1.row targetField.id
        }
    | _, _ => none
  { entries, unavailableKey }

namespace CheckedSemanticIndexSource

/-- Project the shared generated-preliminary index column into semantic-index's clean unique-entry
policy without rebuilding topology, defaults, or generated findings. This route needs only the
selected target's id, so it serves every target kind. -/
def resolvePreliminaryColumn
    (checked : CheckedSemanticIndexSource model)
    (preliminary : CheckedIndexPreliminary model) (outer : Env := []) :
    Except SemanticIndexContextError ResolvedSemanticIndexColumn := do
  let column ← preliminary.resolveIndexColumn checked.group outer
    |>.mapError .checkedColumn
  column.toSemanticIndexColumn preliminary checked.targetDeclaration.id
    |>.mapError .checkedColumn

/-- Evaluate a literal or dynamic key over the immutable checked preliminary document through the
common resolved-column evaluator, under the identity the declared index field uses. -/
def lookupPreliminaryValue
    (checked : CheckedSemanticIndexSource model)
    (preliminary : CheckedIndexPreliminary model)
    (keyRaw : RawFlatContext) (phase : Phase) (outer : Env := []) :
    Except SemanticIndexContextError CellObservation := do
  let column ← checked.resolvePreliminaryColumn preliminary outer
  pure (column.lookupObservationForIndex phase checked.numericIndex
    (checked.key.observe model keyRaw phase))

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
    checked.group.level context checked.targetField)

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

end A12Kernel
