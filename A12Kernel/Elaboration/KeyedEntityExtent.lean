import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.StarGroup

/-! # Entity extents below a selected index row

Selection preserves the checked row environment; ordinary group/star expansion owns every lower
row and declared omission. `spec/08` §4 and the keyed-group and keyed-parent-star handbacks settle
this boundary. Consumer-specific kind, duplicate and result rules remain with entity-list owners.
-/

namespace A12Kernel

inductive SurfaceKeyedEntityTarget where
  | group (path : SurfaceGroupPath)
  | star (path : SurfaceStarFieldPath)
  | starredGroup (path : SurfaceStarGroupPath)
  deriving Repr, DecidableEq

structure SurfaceKeyedEntityExtent where
  target : SurfaceKeyedEntityTarget
  key : SurfaceSemanticIndexKey
  deriving Repr, DecidableEq

inductive KeyedEntityExtentError where
  | index (error : SemanticIndexElabError)
  | group (error : SingleGroupElabError)
  | star (error : StarPathElabError)
  | starredGroup (error : StarredGroupElabError)
  | unsupportedExtent
  deriving Repr, DecidableEq

inductive CheckedKeyedEntityTarget (model : FlatModel) where
  | group (path : GroupPath)
  | starredGroup (path : GroupPath)
  | star (source : CheckedStarFieldPath model)

structure CheckedKeyedEntityExtent (model : FlatModel) where
  private mk ::
  selection : CheckedSemanticIndexSelection model
  target : CheckedKeyedEntityTarget model

namespace CheckedKeyedEntityExtent

def declarations (source : CheckedKeyedEntityExtent model) : List FlatFieldDecl :=
  match source.target with
  | .group path | .starredGroup path => model.groupSubtreeFields path
  | .star path => [path.declaration]

def entityPath (source : CheckedKeyedEntityExtent model) : List String :=
  match source.target with | .group path | .starredGroup path => path | .star path => path.declaration.path

def groupPath (source : CheckedKeyedEntityExtent model) : GroupPath :=
  match source.target with | .group path | .starredGroup path => path | .star path => path.declaration.groupPath

/-- The levels the extent reads at fixed rows: the selected group's scope, then, for a star or an
unstarred group below rule-bound levels, those levels too. Every level from the first star down is
reopened. -/
def boundLevelCount (source : CheckedKeyedEntityExtent model) : Nat :=
  match source.target with
  | .star path => path.path.firstStar
  | .group path => max source.selection.indexDeclaration.repeatableScope.length
      (model.repeatableScopeForGroupPath path).length
  | .starredGroup _ => source.selection.indexDeclaration.repeatableScope.length

/-- The parent and key scopes of the selection, plus the rule-bound levels between the selected
group and the extent's star. -/
def bindingScopes (source : CheckedKeyedEntityExtent model) : List (List RepeatableLevel) :=
  source.selection.indexSource.bindingScopes ++
    if source.selection.indexDeclaration.repeatableScope.length < source.boundLevelCount then
      [(model.repeatableScopeForGroupPath source.groupPath).take source.boundLevelCount]
    else []

def capacity? (source : CheckedKeyedEntityExtent model) : Option Nat :=
  model.declarationsSlotCapacity? source.boundLevelCount source.declarations

def referencesField (source : CheckedKeyedEntityExtent model) (field : FieldId) : Bool :=
  source.declarations.any (·.id == field) || source.selection.indexSource.referencesField field

/-- A selected row whose group lacks a rule-bound lower row selects as empty, as a clean no-match
does ([below-key routes](../../docs/sources/model-structure-and-declaration-probes.md#src-below-key-routes)).
The index column cannot see that row, because the selection reads it at the index field. -/
def boundRowsPresent (source : CheckedKeyedEntityExtent model) (document : Document) (selected : Env) :
    Except CheckedAddressingError Bool := do
  let scope := (model.repeatableScopeForGroupPath source.groupPath).take source.boundLevelCount
  let path ← selected.pathForScope scope |>.mapError .environment
  pure ((repeatableAncestorRowsFor scope path).all document.instantiatedRows.contains)

def presentSelection (source : CheckedKeyedEntityExtent model) (document : Document) :
    CellObservation Env → Except CheckedAddressingError (CellObservation Env)
  | .value selected => do
      pure (if ← source.boundRowsPresent document selected then .value selected else .empty)
  | selection => pure selection

/-- A selected entry without an environment is a scalar-only column, never an absent row. -/
def selectWith (source : CheckedKeyedEntityExtent model) (document : Document) (phase : Phase)
    (readColumn : SemanticIndexColumnReader) (outer : Env)
    (read : FieldId → CheckedCell) (stored : FieldId → Option String) :
    Except CheckedAddressingError (CellObservation Env) := do
  source.presentSelection document (← source.selection.indexSource.selectEnvironmentWith phase readColumn outer read stored)

/-- Physical rows and omitted declared tails stay separate for each declaration, preserving
field-fill order when a group contains several independently repeatable descendants. -/
def rows (source : CheckedKeyedEntityExtent model) (document : Document) (selected : Env) :
    Except StarAddressingError (List (FlatFieldDecl × List Env × Bool)) :=
  source.declarations.mapM fun declaration => do
    let some axes := model.repeatableAxesForScope? declaration.repeatableScope
      | throw (.unsupportedGroupOperand declaration.groupPath)
    let (environments, omitted) ← StarAxes.resolveOperandExtent axes document selected source.boundLevelCount
    pure (declaration, environments, omitted)

/-- Read selected cells through the supplied current view; absence and formal failure remain
separate from an existing selected row whose descendant extent is empty. -/
def observationsWith (source : CheckedKeyedEntityExtent model) (phase : Phase)
    (document : Document) (selection : CellObservation Env) (read : Env → FieldId → CheckedCell) :
    Except CheckedAddressingError (List CellObservation) := do
  match selection with
  | .empty => pure []
  | .unknown cause => pure [.unknown cause]
  | .poison cause => pure [.poison cause]
  | .value selected =>
      let rows ← source.rows document selected |>.mapError .addressing
      pure (rows.flatMap fun (declaration, environments, _) =>
        environments.map fun environment => observeCell phase (read environment declaration.id))

/-- A missing row contributes an empty declared extent. Each reached declaration's omitted tail
stays before the next declaration, using the ordinary field-fill slot policy. -/
def computationSlotsWith (source : CheckedKeyedEntityExtent model)
    (document : Document) (selection : CellObservation Env) (read : Env → FieldId → CheckedCell) :
    Except CheckedAddressingError (List ComputationFillSlot) := do
  match selection with
  | .empty => pure [.uninstantiated]
  | .unknown cause | .poison cause => pure [(.poison cause : CellObservation).asComputationFillSlot]
  | .value selected =>
      let rows ← source.rows document selected |>.mapError .addressing
      pure (rows.flatMap fun (declaration, environments, omitted) =>
        (environments.map fun environment =>
          (observeCell .computation (read environment declaration.id)).asComputationFillSlot) ++
          if omitted then [.uninstantiated] else [])

/-- Reuse the current computation overlay for selected keys and every descendant field. -/
def computationSlotsIn (source : CheckedKeyedEntityExtent model) (context : ScalarComputationContext)
    (readColumn : SemanticIndexColumnReader) : Except CheckedAddressingError (List ComputationFillSlot) := do
  let some addressed := context.addressed | throw (.checkedDocumentRequired source.groupPath)
  let selected ← source.selectWith addressed.document .computation readColumn context.row context.read context.storedText
  source.computationSlotsWith addressed.document selected addressed.read

end CheckedKeyedEntityExtent

/-- A selected side with the declaration behind each cell and each omitted tail, for consumers
whose result depends on the declaration a missing value belongs to, such as `Sum`'s signedness
(spec/10 §4). `declarations` is aligned with `side.cells`. -/
structure SelectedValueListCells (kind : ValueListKind) where
  side : ResolvedValueListSide kind
  declarations : List FlatFieldDecl
  omitted : List FlatFieldDecl

/-- Selection owns phase policy, row identity and omitted extents (spec/08 §4.1); each value-list
consumer supplies its declaration-aware cell projection and absent-star policy. Products and list
quantifiers retain omission on an absent selected star (spec/07 §3.8 and spec/08 §4.1). -/
def selectedValueListCellsWith {kind : ValueListKind}
    (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model))
    (phase : Phase) (document : Document) (outer : Env) (direct : FieldId → CheckedCell)
    (stored : FieldId → Option String) (read : Env → FieldId → CheckedCell)
    (column : SemanticIndexColumnReader)
    (classify : FlatFieldDecl → CellObservation → Except CheckedAddressingError (ValueListCell kind))
    (missingStarIsOmitted : Bool := false) :
    Except CheckedAddressingError (SelectedValueListCells kind) := do
  match source with
  | .inl selected =>
      let value ← selected.observeColumnWith phase column outer direct stored
      pure { side := { cells := [← classify selected.targetDeclaration value], hasUninstantiatedTail := false, hasHaving := false }
             declarations := [selected.targetDeclaration], omitted := [] }
  | .inr selected =>
      match ← selected.selectWith document phase column outer direct stored with
      | .empty =>
          let omitted := match selected.target with
            | .group _ => true | .star _ | .starredGroup _ => missingStarIsOmitted
          pure { side := { cells := [], hasUninstantiatedTail := omitted, hasHaving := false }
                 declarations := [], omitted := if omitted then selected.declarations else [] }
      | .unknown cause | .poison cause =>
          pure { side := { cells := [.unknown cause], hasUninstantiatedTail := false, hasHaving := false }
                 declarations := selected.declarations.take 1, omitted := [] }
      | .value environment =>
          let rows ← selected.rows document environment |>.mapError .addressing
          let cells ← rows.flatMapM fun (declaration, environments, _) =>
            environments.mapM fun row => do
              pure (declaration, ← classify declaration (observeCell phase (read row declaration.id)))
          let hasEmptyPrefix ← model.groupOperandEmptyPrefix document environment
            selected.boundLevelCount (selected.declarations.map (·.repeatableScope)) |>.mapError .addressing
          pure { side := { cells := cells.map (·.2), hasUninstantiatedTail := rows.any (·.2.2), hasHaving := false, hasEmptyPrefix }
                 declarations := cells.map (·.1), omitted := (rows.filter (·.2.2)).map (·.1) }

def selectedValueListSideWith {kind : ValueListKind}
    (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model))
    (phase : Phase) (document : Document) (outer : Env) (direct : FieldId → CheckedCell)
    (stored : FieldId → Option String) (read : Env → FieldId → CheckedCell)
    (column : SemanticIndexColumnReader)
    (classify : FlatFieldDecl → CellObservation → Except CheckedAddressingError (ValueListCell kind))
    (missingStarIsOmitted : Bool := false) :
    Except CheckedAddressingError (ResolvedValueListSide kind) :=
  (·.side) <$> selectedValueListCellsWith source phase document outer direct stored read column classify missingStarIsOmitted

/-- Bind the innermost declared index before checking the remaining unbound extent. A group
without its own star may retain only nonrepeatable steps below the selected level (`spec/08` §4). A
star field or an unstarred group may sit below repeatable levels the rule binds, which keep the
rule's row, as `Sum(Cells*/Q For "b")` and `GroupFilled(/Depot/Bins/Slots For "b")` from a rule in
`Slots` below the indexed `Bins` do
([below-key selection](../../docs/sources/model-structure-and-declaration-probes.md#src-below-key-selection),
[below-key routes](../../docs/sources/model-structure-and-declaration-probes.md#src-below-key-routes)).
An unbound lower level draws the walk's `MVK_NO_WILDCARD` before this elaborator runs, in rules and
computations alike (`q1`, `q3`, `s1`–`s3` of the routes capture). -/
def elaborateKeyedEntityExtent (model : FlatModel) (declaringGroup : GroupPath)
    (authored : SurfaceKeyedEntityExtent) (boundScope? : Option (List RepeatableLevel) := none) : Except KeyedEntityExtentError (CheckedKeyedEntityExtent model) := do
  if !GroupPath.isValid declaringGroup then
    throw (.group (.resolve (.invalidRuleGroup declaringGroup)))
  let (target, targetGroup, firstStar?) ← match authored.target with
    | .group path => do
        let group ← path.resolveAgainst declaringGroup |>.mapError .group
        if !model.hasGroupPath group then throw .unsupportedExtent
        pure (CheckedKeyedEntityTarget.group group, group, none)
    | .starredGroup path => do
        let source ← elaborateStarredGroupOperandSource model declaringGroup path |>.mapError .starredGroup
        let (group, firstStar) := match source with
          | .terminalRepeatable source => (source.group.path, source.path.firstStar)
          | .terminalPresence source => (source.groupPath, source.path.firstStar)
        pure (CheckedKeyedEntityTarget.starredGroup group, group, some firstStar)
    | .star path => do
        let source ← elaborateStarFieldPath model declaringGroup path |>.mapError .star
        pure (CheckedKeyedEntityTarget.star source, source.declaration.groupPath, some source.path.firstStar)
  let some group := model.semanticIndexGroupForPath? targetGroup | throw (.index (.missingIndexField targetGroup))
  let selection ← elaborateSemanticIndexSelection model declaringGroup group authored.key boundScope? |>.mapError .index
  let depth := selection.indexDeclaration.repeatableScope.length
  if let some firstStar := firstStar? then
    -- A star at the index group's own level draws the index's wildcard class (rule check
    -- `CheckerEntitySpecModifierAgreementTest` at a12-dmkits `fecf8552`,
    -- [inbound](../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-27)); a star above it has the
    -- `MVK_SEMANTIC_INDEX_BELOW_WILDCARD` class (spec/08 §4), which no constructor of this error
    -- carries, so every other mismatch stays unsupported.
    let belowRuleBoundLevels := match target with
      | .star _ => depth < firstStar
      | .group _ | .starredGroup _ => false
    if firstStar != depth && !belowRuleBoundLevels then
      throw (if firstStar + 1 == depth then .index (.keyAdmission .semanticIndexAndWildcard)
        else .unsupportedExtent)
  else if (model.repeatableScopeForGroupPath targetGroup).length < depth then
    throw .unsupportedExtent
  pure { selection, target }

end A12Kernel
