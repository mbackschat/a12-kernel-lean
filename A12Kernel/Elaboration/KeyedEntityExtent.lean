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

def bindingScopes (source : CheckedKeyedEntityExtent model) : List (List RepeatableLevel) :=
  source.selection.indexSource.bindingScopes

def boundLevelCount (source : CheckedKeyedEntityExtent model) : Nat :=
  source.selection.indexDeclaration.repeatableScope.length

def capacity? (source : CheckedKeyedEntityExtent model) : Option Nat :=
  model.declarationsSlotCapacity? source.boundLevelCount source.declarations

def referencesField (source : CheckedKeyedEntityExtent model) (field : FieldId) : Bool :=
  source.declarations.any (·.id == field) || source.selection.indexSource.referencesField field

/-- A selected entry without an environment is a scalar-only column, never an absent row. -/
def selectWith (source : CheckedKeyedEntityExtent model) (phase : Phase)
    (readColumn : SemanticIndexColumnReader) (outer : Env)
    (read : FieldId → CheckedCell) (stored : FieldId → Option String) :
    Except CheckedAddressingError (CellObservation Env) := do
  source.selection.indexSource.selectEnvironmentWith phase readColumn outer read stored

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
  let selected ← source.selectWith .computation readColumn context.row context.read context.storedText
  source.computationSlotsWith addressed.document selected addressed.read

end CheckedKeyedEntityExtent

/-- Selection owns phase policy, row identity and omitted extents (spec/08 §4.1); each value-list
consumer supplies its declaration-aware cell projection and absent-star policy. Products and list
quantifiers retain omission on an absent selected star (spec/07 §4 and spec/08 §4.1). -/
def selectedValueListSideWith {kind : ValueListKind}
    (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model))
    (phase : Phase) (document : Document) (outer : Env) (direct : FieldId → CheckedCell)
    (stored : FieldId → Option String) (read : Env → FieldId → CheckedCell)
    (column : SemanticIndexColumnReader)
    (classify : FlatFieldDecl → CellObservation → Except CheckedAddressingError (ValueListCell kind))
    (missingStarIsOmitted : Bool := false) :
    Except CheckedAddressingError (ResolvedValueListSide kind) := do
  match source with
  | .inl selected =>
      let value ← selected.observeColumnWith phase column outer direct stored
      pure { cells := [← classify selected.targetDeclaration value], hasUninstantiatedTail := false, hasHaving := false }
  | .inr selected =>
      match ← selected.selectWith phase column outer direct stored with
      | .empty =>
          pure { cells := [], hasUninstantiatedTail := match selected.target with
                   | .group _ => true | .star _ | .starredGroup _ => missingStarIsOmitted
                 hasHaving := false }
      | .unknown cause | .poison cause =>
          pure { cells := [.unknown cause], hasUninstantiatedTail := false, hasHaving := false }
      | .value environment =>
          let rows ← selected.rows document environment |>.mapError .addressing
          let cells ← rows.flatMapM fun (declaration, environments, _) =>
            environments.mapM fun row => classify declaration (observeCell phase (read row declaration.id))
          let hasEmptyPrefix ← model.groupOperandEmptyPrefix document environment
            selected.boundLevelCount (selected.declarations.map (·.repeatableScope)) |>.mapError .addressing
          pure { cells, hasUninstantiatedTail := rows.any (·.2.2), hasHaving := false, hasEmptyPrefix }

/-- Bind the innermost declared index before checking the remaining unbound extent. A group
without its own star may retain only nonrepeatable steps below the selected level (`spec/08` §4). -/
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
    if firstStar != depth then throw .unsupportedExtent
  else if (model.repeatableScopeForGroupPath targetGroup).length != depth then
    throw .unsupportedExtent
  pure { selection, target }

end A12Kernel
