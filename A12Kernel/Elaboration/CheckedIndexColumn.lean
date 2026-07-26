import A12Kernel.Elaboration.CheckedIndexPreliminary
import A12Kernel.Semantics.SemanticIndex

/-! # Checked index columns and bounded parallel joins

This family-owned boundary resolves one generated-preliminary index column without inventing another document or address model. It retains every ordered key occurrence, duplicate identity for semantic-index exclusion, and one column-unavailability cause. The parallel projection makes its deterministic reference selection separately. The first parallel profile joins direct sibling groups with exact non-Number stored keys; Number rendering order remains outside until its declaration/locale owner exists.
-/

namespace A12Kernel

inductive CheckedIndexColumnError where
  | model (error : ResolveError)
  | document (error : CheckedDocumentError)
  | environment (error : EnvBindingError)
  | groupNotOwned (path : GroupPath)
  | missingIndexField (path : GroupPath)
  | incoherentScope (path : GroupPath)
  | incoherentIndexDeclaration (path : GroupPath) (expected actual : FieldId)
  | incoherentRow (row : RowAddr) (expected : Nat)
  | incoherentIndexValue (address : CellAddr)
  | missingStoredValue (address : CellAddr)
  | fieldOutsideGroup (field : FieldId) (group : GroupPath)
  | incompatibleGroups (left right : GroupPath)
  | incompatibleIndexFields (left right : List String)
  | unsupportedParallelNumberIndex (path : List String)
  deriving Repr, DecidableEq

structure ResolvedCheckedIndexEntry where
  key : SemanticIndexKey
  environment : Env
  deriving Repr, DecidableEq

structure ResolvedCheckedIndexColumn (model : FlatModel) where
  private mk ::
  group : RepeatableGroupDecl
  indexDeclaration : FlatFieldDecl
  entries : List ResolvedCheckedIndexEntry
  duplicateKeys : List SemanticIndexKey
  unavailableKey : Option FormalCause
  modelWellFormed : model.validate.isOk = true
  groupOwned : model.repeatableGroups.contains group = true
  indexDeclared : group.indexField = some indexDeclaration.id

structure ResolvedParallelIndexSide where
  group : RepeatableGroupDecl
  environment : Option Env
  unavailableKey : Option FormalCause
  deriving Repr, DecidableEq

structure ResolvedParallelIndexRow where
  key : SemanticIndexKey
  left : ResolvedParallelIndexSide
  right : ResolvedParallelIndexSide
  deriving Repr, DecidableEq

structure ResolvedParallelIndexJoin where
  leftGroup : RepeatableGroupDecl
  rightGroup : RepeatableGroupDecl
  rows : List ResolvedParallelIndexRow
  deriving Repr, DecidableEq

namespace ResolvedCheckedIndexColumn

/-- The public certificate boundary: the column belongs to one validated model and its declaration is the group's exact index field. -/
def WellFormed (column : ResolvedCheckedIndexColumn model) : Prop :=
  model.validate.isOk = true ∧
    model.repeatableGroups.contains column.group = true ∧
    column.group.indexField = some column.indexDeclaration.id

/-- Semantic index admits exactly the keys that generated uniqueness did not classify as duplicates. Parallel iteration deliberately does not use this projection. -/
def admitsSemanticKey (column : ResolvedCheckedIndexColumn model)
    (key : SemanticIndexKey) : Bool :=
  !column.duplicateKeys.contains key

end ResolvedCheckedIndexColumn

private structure IndexColumnState where
  entries : List ResolvedCheckedIndexEntry := []
  duplicateKeys : List SemanticIndexKey := []
  unavailableKey : Option FormalCause := none

private def CheckedIndexPreliminary.storedAt?
    (preliminary : CheckedIndexPreliminary model) (address : CellAddr) :
    Option String :=
  match preliminary.defaultStoredAt? address with
  | some stored => some stored
  | none =>
      (preliminary.base.source.cells.find? fun input =>
        input.address == address).map (·.stored)

private def CheckedIndexPreliminary.indexKey?
    (preliminary : CheckedIndexPreliminary model)
    (declaration : FlatFieldDecl) (address : CellAddr)
    (cell : CheckedCell) :
    Except CheckedIndexColumnError (Option SemanticIndexKey) :=
  match declaration.policy.kind, cell.parsed with
  | .number _, some (.num value) => pure (some (.number value))
  | .number _, some _ => throw (.incoherentIndexValue address)
  | .number _, none => pure none
  | _, some _ =>
      match preliminary.storedAt? address with
      | some stored => pure (some (.text stored))
      | none => throw (.missingStoredValue address)
  | _, none => pure none

private def IndexColumnState.add
    (state : IndexColumnState) (entry : Option ResolvedCheckedIndexEntry)
    (duplicate : Bool) (cause : Option FormalCause) : IndexColumnState :=
  let entries := match entry with
    | none => state.entries
    | some current => state.entries ++ [current]
  let duplicateKeys := match entry with
    | some current =>
        if duplicate && !state.duplicateKeys.contains current.key then
          state.duplicateKeys ++ [current.key]
        else
          state.duplicateKeys
    | none => state.duplicateKeys
  {
    entries
    duplicateKeys
    unavailableKey := state.unavailableKey.orElse fun _ => cause
  }

private def CheckedIndexPreliminary.scanIndexRows
    (preliminary : CheckedIndexPreliminary model)
    (group : RepeatableGroupDecl) (declaration : FlatFieldDecl)
    (scope : List RepeatableLevel) :
    List RowAddr → IndexColumnState →
      Except CheckedIndexColumnError IndexColumnState
  | [], state => pure state
  | row :: rows, state => do
      if row.path.length != scope.length then
        throw (.incoherentRow row scope.length)
      let overLimit ← match model.addressOverLimit? scope row.path with
        | some result => pure result
        | none => throw (.incoherentScope group.path)
      if overLimit then
        preliminary.scanIndexRows group declaration scope rows state
      else
        let address : CellAddr := { field := declaration.id, path := row.path }
        let cell ← preliminary.readAuthoredValidation address |>.mapError .document
        let key ← preliminary.indexKey? declaration address cell
        let entry := key.map fun resolved =>
          { key := resolved, environment := scope.zip row.path }
        let duplicate :=
          preliminary.findingKindAt? address == some .unique
        preliminary.scanIndexRows group declaration scope rows
          (state.add entry duplicate cell.findings.head?)

namespace CheckedIndexPreliminary

def resolveIndexColumn (preliminary : CheckedIndexPreliminary model)
    (group : RepeatableGroupDecl) (outer : Env := []) :
    Except CheckedIndexColumnError (ResolvedCheckedIndexColumn model) := do
  if hGroup : model.repeatableGroups.contains group = true then
    let indexId ← match group.indexField with
      | some indexId => pure indexId
      | none => throw (.missingIndexField group.path)
    let declaration ← model.lookupUniqueId indexId |>.mapError .model
    if hDeclared : group.indexField = some declaration.id then
      let scope := model.repeatableScopeForGroupPath group.path
      if scope.getLast? != some group.level then
        throw (.incoherentScope group.path)
      let parentPath ←
        outer.pathForScope scope.dropLast |>.mapError .environment
      let rows := preliminary.base.source.instantiatedRows.filter fun row =>
        row.group == group.level && row.path.dropLast == parentPath
      let state ← preliminary.scanIndexRows group declaration scope rows {}
      pure {
        group
        indexDeclaration := declaration
        entries := state.entries
        duplicateKeys := state.duplicateKeys
        unavailableKey := state.unavailableKey
        modelWellFormed := preliminary.base.modelWellFormed
        groupOwned := hGroup
        indexDeclared := hDeclared
      }
    else
      throw (.incoherentIndexDeclaration group.path indexId declaration.id)
  else
    throw (.groupNotOwned group.path)

private def entryFor?
    (column : ResolvedCheckedIndexColumn model) (key : SemanticIndexKey) :
    Option ResolvedCheckedIndexEntry :=
  column.entries.foldl (fun selected entry =>
    if entry.key == key then some entry else selected) none

private def textKeys
    (column : ResolvedCheckedIndexColumn model) : List String :=
  column.entries.filterMap fun entry => match entry.key with
    | .text token => some token
    | .number _ => none

private def parallelSide (column : ResolvedCheckedIndexColumn model)
    (key : SemanticIndexKey) : ResolvedParallelIndexSide := {
  group := column.group
  environment := (entryFor? column key).map (·.environment)
  unavailableKey := column.unavailableKey
}

def resolveParallelIndexJoin (preliminary : CheckedIndexPreliminary model)
    (left right : RepeatableGroupDecl) (outer : Env := []) :
    Except CheckedIndexColumnError ResolvedParallelIndexJoin := do
  if left.path == right.path ||
      left.path.dropLast != right.path.dropLast then
    throw (.incompatibleGroups left.path right.path)
  let leftColumn ← preliminary.resolveIndexColumn left outer
  let rightColumn ← preliminary.resolveIndexColumn right outer
  if leftColumn.indexDeclaration.name !=
      rightColumn.indexDeclaration.name ||
      leftColumn.indexDeclaration.policy.kind !=
        rightColumn.indexDeclaration.policy.kind then
    throw (.incompatibleIndexFields
      leftColumn.indexDeclaration.path rightColumn.indexDeclaration.path)
  match leftColumn.indexDeclaration.policy.kind with
  | .number _ =>
      throw (.unsupportedParallelNumberIndex
        leftColumn.indexDeclaration.path)
  | _ =>
      let unsorted := (textKeys leftColumn ++ textKeys rightColumn).eraseDups
      let sorted := unsorted.mergeSort fun first second =>
        compare first second != .gt
      let keys := sorted.map SemanticIndexKey.text
      pure {
        leftGroup := left
        rightGroup := right
        rows := keys.map fun key => {
          key
          left := parallelSide leftColumn key
          right := parallelSide rightColumn key
        }
      }

end CheckedIndexPreliminary

namespace ResolvedParallelIndexSide

/-- An unmatched clean side is semantically empty; an unmatched invalid column is validation-unknown. No sentinel coordinate enters the physical address domain. -/
def missingObservation (side : ResolvedParallelIndexSide) : CellObservation :=
  match side.unavailableKey with
  | none => .empty
  | some cause => .unknown cause

/-- Read a field from the matched physical row through the generated-preliminary view, or apply the exact unmatched-side policy. A field outside this side remains structural failure. -/
def readValidation (side : ResolvedParallelIndexSide)
    (preliminary : CheckedIndexPreliminary model) (field : FieldId) :
    Except CheckedIndexColumnError CellObservation := do
  let declaration ← model.lookupUniqueId field |>.mapError .model
  if !side.group.path.isPrefixOf declaration.groupPath then
    throw (.fieldOutsideGroup field side.group.path)
  match side.environment with
  | none => pure side.missingObservation
  | some environment =>
      let path ← environment.pathForScope declaration.repeatableScope
        |>.mapError .environment
      let cell ← preliminary.readAuthoredValidation { field, path }
        |>.mapError .document
      pure (observeCell .validation cell)

end ResolvedParallelIndexSide

namespace ResolvedCheckedIndexColumn

/-- Project the shared checked column to semantic-index's clean-entry contract. Every duplicate participant is removed, while the column cause remains available to the phase-specific evaluator. -/
def toSemanticIndexColumn (column : ResolvedCheckedIndexColumn model)
    (preliminary : CheckedIndexPreliminary model) (target : FieldId) :
    Except CheckedIndexColumnError ResolvedSemanticIndexColumn := do
  let declaration ← model.lookupUniqueId target |>.mapError .model
  if !column.group.path.isPrefixOf declaration.groupPath then
    throw (.fieldOutsideGroup target column.group.path)
  let entries ← (column.entries.filter fun entry =>
    column.admitsSemanticKey entry.key).mapM fun entry => do
      let path ← entry.environment.pathForScope declaration.repeatableScope
        |>.mapError .environment
      let target ← preliminary.readAuthoredValidation { field := target, path }
        |>.mapError .document
      pure { token := entry.key, target }
  pure { entries, unavailableKey := column.unavailableKey }

end ResolvedCheckedIndexColumn

end A12Kernel
