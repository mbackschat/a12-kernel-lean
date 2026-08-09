import A12Kernel.Elaboration.CheckedIndexPreliminary
import A12Kernel.Semantics.SemanticIndex

/-! # Checked index columns and bounded parallel joins

This family-owned boundary resolves one generated-preliminary index column without inventing another document or address model. It retains every ordered key occurrence, duplicate identity for selection exclusion, and one column-unavailability cause. Semantic-index and parallel projections share only that admission relation while retaining their separate selection and missing-side policies. The checked parallel profile admits either one common outer repeatable scope or one non-indexed frame on exactly one side, across transparent nonrepeatable wrappers and exact non-Number stored keys; Number rendering order remains outside until its declaration/locale owner exists.
-/

namespace A12Kernel

inductive CheckedIndexColumnError where
  | model (error : ResolveError)
  | document (error : CheckedDocumentError)
  | environment (error : EnvBindingError)
  | groupNotOwned (path : GroupPath)
  | missingIndexField (path : GroupPath)
  | incoherentScope (path : GroupPath)
  | incoherentFrameScope (scope : List RepeatableLevel)
  | incoherentIndexDeclaration (path : GroupPath) (expected actual : FieldId)
  | incoherentRow (row : RowAddr) (expected : Nat)
  | incoherentIndexValue (address : CellAddr)
  | missingStoredValue (address : CellAddr)
  | fieldOutsideGroup (field : FieldId) (group : GroupPath)
  | fieldOutsideParallelGroups (field : FieldId)
      (left right : GroupPath)
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

namespace FieldKind

/-- Parallel iteration orders every non-Number index by its exact stored token. Number needs declaration/locale-owned rendering and therefore fails this bounded profile closed. -/
def supportsExactTextParallelKey : FieldKind → Bool
  | .number _ => false
  | .boolean | .confirm | .string | .enumeration | .temporal _ _ => true

end FieldKind

/-- The exact group-path ancestor shared by two parallel sides. Nonrepeatable segments below this path are transparent to repetition environments. -/
def parallelCommonParent : GroupPath → GroupPath → GroupPath
  | left :: leftRest, right :: rightRest =>
      if left == right then
        left :: parallelCommonParent leftRest rightRest
      else
        []
  | _, _ => []

inductive ParallelFrameSide where
  | left
  | right
  deriving Repr, DecidableEq

/-- The complete outer-scope relation between two keyed groups. A frame suffix is nonempty when produced by `classify`; divergent scopes have no plan. -/
inductive ParallelOuterScopePlan where
  | common (scope : List RepeatableLevel)
  | framed (side : ParallelFrameSide)
      (commonScope frameScope : List RepeatableLevel)
  deriving Repr, DecidableEq

namespace ParallelOuterScopePlan

/-- Classify equal scopes or a strict one-sided extension. This is the checked static boundary between a common join, one ordinary outer frame, and incompatible frames on both sides. -/
def classify :
    List RepeatableLevel → List RepeatableLevel →
      Option ParallelOuterScopePlan
  | [], [] => some (.common [])
  | left@(_ :: _), [] => some (.framed .left [] left)
  | [], right@(_ :: _) => some (.framed .right [] right)
  | left :: leftRest, right :: rightRest =>
      if left == right then
        match classify leftRest rightRest with
        | some (ParallelOuterScopePlan.common shared) =>
            some (.common (left :: shared))
        | some (ParallelOuterScopePlan.framed side shared frame) =>
            some (.framed side (left :: shared) frame)
        | none => none
      else
        none

/-- Whether a selected error operand lies on the side that carries every required frame coordinate. Common-scope joins allow either operand. -/
def admitsErrorOnLeft : ParallelOuterScopePlan → Bool → Bool
  | .common _, _ => true
  | .framed .left _ _, errorOnLeft => errorOnLeft
  | .framed .right _ _, errorOnLeft => !errorOnLeft

end ParallelOuterScopePlan

/-- A model-certified pair of index groups with either one common outer repeatable scope or one non-indexed frame on exactly one side. -/
structure CheckedParallelIndexGroups (model : FlatModel) where
  private mk ::
  leftGroup : RepeatableGroupDecl
  rightGroup : RepeatableGroupDecl
  leftIndexDeclaration : FlatFieldDecl
  rightIndexDeclaration : FlatFieldDecl
  modelWellFormed : model.validate.isOk = true
  leftGroupOwned : model.repeatableGroups.contains leftGroup = true
  rightGroupOwned : model.repeatableGroups.contains rightGroup = true
  leftIndexDeclared :
    leftGroup.indexField = some leftIndexDeclaration.id
  rightIndexDeclared :
    rightGroup.indexField = some rightIndexDeclaration.id
  groupsDistinct : (leftGroup.path == rightGroup.path) = false
  commonParent : GroupPath
  commonParentOwned :
    commonParent = parallelCommonParent leftGroup.path rightGroup.path
  commonParentNonempty : commonParent.isEmpty = false
  outerScopePlan : ParallelOuterScopePlan
  outerScopePlanOwned :
    ParallelOuterScopePlan.classify
      (model.repeatableScopeForGroupPath leftGroup.path).dropLast
      (model.repeatableScopeForGroupPath rightGroup.path).dropLast =
        some outerScopePlan
  commonIndexName :
    (leftIndexDeclaration.name == rightIndexDeclaration.name) = true
  commonIndexKind :
    (leftIndexDeclaration.policy.kind ==
      rightIndexDeclaration.policy.kind) = true
  exactTextIndex :
    leftIndexDeclaration.policy.kind.supportsExactTextParallelKey = true

namespace ResolvedCheckedIndexColumn

/-- The public certificate boundary: the column belongs to one validated model and its declaration is the group's exact index field. -/
def WellFormed (column : ResolvedCheckedIndexColumn model) : Prop :=
  model.validate.isOk = true ∧
    model.repeatableGroups.contains column.group = true ∧
    column.group.indexField = some column.indexDeclaration.id

/-- A key is selectable exactly when generated uniqueness did not classify it as duplicated. Every consumer keeps its own lookup and missing-side policy after this common admission relation. -/
def admitsSelectableKey (column : ResolvedCheckedIndexColumn model)
    (key : SemanticIndexKey) : Bool :=
  !column.duplicateKeys.contains key

/-- Semantic-index selection specializes the shared duplicate exclusion. -/
def admitsSemanticKey (column : ResolvedCheckedIndexColumn model)
    (key : SemanticIndexKey) : Bool :=
  column.admitsSelectableKey key

/-- Parallel selection specializes the same duplicate exclusion. -/
def admitsParallelKey (column : ResolvedCheckedIndexColumn model)
    (key : SemanticIndexKey) : Bool :=
  column.admitsSelectableKey key

end ResolvedCheckedIndexColumn

namespace CheckedParallelIndexGroups

/-- The public certificate boundary for the bounded exact-text transparent-wrapper profile. -/
def WellFormed (groups : CheckedParallelIndexGroups model) : Prop :=
  model.validate.isOk = true ∧
    model.repeatableGroups.contains groups.leftGroup = true ∧
    model.repeatableGroups.contains groups.rightGroup = true ∧
    groups.leftGroup.indexField =
      some groups.leftIndexDeclaration.id ∧
    groups.rightGroup.indexField =
      some groups.rightIndexDeclaration.id ∧
    (groups.leftGroup.path == groups.rightGroup.path) = false ∧
    groups.commonParent =
      parallelCommonParent groups.leftGroup.path groups.rightGroup.path ∧
    groups.commonParent.isEmpty = false ∧
    ParallelOuterScopePlan.classify
      (model.repeatableScopeForGroupPath groups.leftGroup.path).dropLast
      (model.repeatableScopeForGroupPath groups.rightGroup.path).dropLast =
        some groups.outerScopePlan ∧
    (groups.leftIndexDeclaration.name ==
      groups.rightIndexDeclaration.name) = true ∧
    (groups.leftIndexDeclaration.policy.kind ==
      groups.rightIndexDeclaration.policy.kind) = true ∧
    groups.leftIndexDeclaration.policy.kind.supportsExactTextParallelKey =
      true

end CheckedParallelIndexGroups

/-- Every indexed repeatable ancestor of one model declaration, in model order. Cardinality and consumer-specific scope rules stay with the checked consumer. -/
def FlatModel.indexedAncestorGroups (model : FlatModel)
    (declaration : FlatFieldDecl) : List RepeatableGroupDecl :=
  model.repeatableGroups.filter fun group =>
    group.path.isPrefixOf declaration.groupPath && group.indexField.isSome

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

/-- Check the document-independent parallel group profile once. The indexed groups may share their complete outer repeatable scope or one may add a non-indexed frame suffix; divergent frames are incompatible. Differing nonrepeatable path segments remain transparent. -/
def checkParallelIndexGroups (model : FlatModel)
    (left right : RepeatableGroupDecl) :
    Except CheckedIndexColumnError
      (CheckedParallelIndexGroups model) :=
  match hModel : model.validate with
  | .error error => .error (.model error)
  | .ok () =>
      if hLeft : model.repeatableGroups.contains left = true then
        if hRight : model.repeatableGroups.contains right = true then
          if hDistinct : (left.path == right.path) = false then
            let commonParent :=
              parallelCommonParent left.path right.path
            if hCommon : commonParent.isEmpty = false then
              let leftOuterScope :=
                (model.repeatableScopeForGroupPath left.path).dropLast
              let rightOuterScope :=
                (model.repeatableScopeForGroupPath right.path).dropLast
              match hOuterScope :
                  ParallelOuterScopePlan.classify
                    leftOuterScope rightOuterScope with
              | some outerScopePlan => do
                let leftIndexId ← match left.indexField with
                  | some field => pure field
                  | none => throw (.missingIndexField left.path)
                let rightIndexId ← match right.indexField with
                  | some field => pure field
                  | none => throw (.missingIndexField right.path)
                let leftIndex ←
                  model.lookupUniqueId leftIndexId |>.mapError .model
                let rightIndex ←
                  model.lookupUniqueId rightIndexId |>.mapError .model
                if hLeftDeclared :
                    left.indexField = some leftIndex.id then
                  if hRightDeclared :
                      right.indexField = some rightIndex.id then
                    if hName :
                        (leftIndex.name == rightIndex.name) = true then
                      if hKind :
                          (leftIndex.policy.kind ==
                            rightIndex.policy.kind) = true then
                        if hText :
                            FieldKind.supportsExactTextParallelKey
                              leftIndex.policy.kind = true then
                          pure {
                            leftGroup := left
                            rightGroup := right
                            leftIndexDeclaration := leftIndex
                            rightIndexDeclaration := rightIndex
                            modelWellFormed := by rw [hModel]; rfl
                            leftGroupOwned := hLeft
                            rightGroupOwned := hRight
                            leftIndexDeclared := hLeftDeclared
                            rightIndexDeclared := hRightDeclared
                            groupsDistinct := hDistinct
                            commonParent
                            commonParentOwned := rfl
                            commonParentNonempty := hCommon
                            outerScopePlan
                            outerScopePlanOwned := by
                              simpa [leftOuterScope, rightOuterScope]
                                using hOuterScope
                            commonIndexName := hName
                            commonIndexKind := hKind
                            exactTextIndex := hText
                          }
                        else
                          throw (.unsupportedParallelNumberIndex
                            leftIndex.path)
                      else
                        throw (.incompatibleIndexFields
                          leftIndex.path rightIndex.path)
                    else
                      throw (.incompatibleIndexFields
                        leftIndex.path rightIndex.path)
                  else
                    throw (.incoherentIndexDeclaration
                      right.path rightIndexId rightIndex.id)
                else
                  throw (.incoherentIndexDeclaration
                    left.path leftIndexId leftIndex.id)
              | none =>
                .error (.incompatibleGroups left.path right.path)
            else
              .error (.incompatibleGroups left.path right.path)
          else
            .error (.incompatibleGroups left.path right.path)
        else
          .error (.groupNotOwned right.path)
      else
        .error (.groupNotOwned left.path)

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

private def collectParallelFrameEnvironments
    (preliminary : CheckedIndexPreliminary model)
    (scope : List RepeatableLevel) (commonPath : List Nat) :
    List RowAddr → List Env →
      Except CheckedIndexColumnError (List Env)
  | [], reversed => pure reversed.reverse
  | row :: rows, reversed => do
      if row.path.length != scope.length then
        throw (.incoherentRow row scope.length)
      let overLimit ← match model.addressOverLimit? scope row.path with
        | some result => pure result
        | none => throw (.incoherentFrameScope scope)
      let belongsToOuter :=
        row.path.take commonPath.length == commonPath
      let next :=
        if overLimit || !belongsToOuter then reversed
        else scope.zip row.path :: reversed
      preliminary.collectParallelFrameEnvironments
        scope commonPath rows next

/-- Enumerate the actual deepest rows of one certified non-indexed frame in immutable document order. The caller supplies only the common outer bindings; over-limit frame rows are excluded before any keyed join is constructed. -/
def resolveCheckedParallelFrameEnvironments
    (preliminary : CheckedIndexPreliminary model)
    (groups : CheckedParallelIndexGroups model)
    (outer : Env := []) :
    Except CheckedIndexColumnError (List Env) :=
  match groups.outerScopePlan with
  | .common scope => .error (.incoherentFrameScope scope)
  | .framed _ commonScope frameScope => do
      let scope := commonScope ++ frameScope
      let deepest ← match frameScope.getLast? with
        | some level => pure level
        | none => throw (.incoherentFrameScope frameScope)
      let commonPath ←
        outer.pathForScope commonScope |>.mapError .environment
      let rows := preliminary.base.source.instantiatedRows.filter fun row =>
        row.group == deepest
      preliminary.collectParallelFrameEnvironments
        scope commonPath rows []

private def entryFor?
    (column : ResolvedCheckedIndexColumn model) (key : SemanticIndexKey) :
    Option ResolvedCheckedIndexEntry :=
  if column.admitsParallelKey key then
    column.entries.find? fun entry => entry.key == key
  else
    none

private def textKeys
    (column : ResolvedCheckedIndexColumn model) : List String :=
  column.entries.filterMap fun entry =>
    if column.admitsParallelKey entry.key then
      match entry.key with
      | .text token => some token
      | .number _ => none
    else
      none

private def parallelSide (column : ResolvedCheckedIndexColumn model)
    (key : SemanticIndexKey) : ResolvedParallelIndexSide := {
  group := column.group
  environment := (entryFor? column key).map (·.environment)
  unavailableKey := column.unavailableKey
}

private def resolveCheckedParallelIndexJoinAt
    (preliminary : CheckedIndexPreliminary model)
    (groups : CheckedParallelIndexGroups model)
    (leftOuter rightOuter : Env) :
    Except CheckedIndexColumnError ResolvedParallelIndexJoin := do
  let leftColumn ←
    preliminary.resolveIndexColumn groups.leftGroup leftOuter
  let rightColumn ←
    preliminary.resolveIndexColumn groups.rightGroup rightOuter
  let unsorted := (textKeys leftColumn ++ textKeys rightColumn).eraseDups
  let sorted := unsorted.mergeSort fun first second =>
    compare first second != .gt
  let keys := sorted.map SemanticIndexKey.text
  pure {
    leftGroup := groups.leftGroup
    rightGroup := groups.rightGroup
    rows := keys.map fun key => {
      key
      left := parallelSide leftColumn key
      right := parallelSide rightColumn key
    }
  }

/-- Resolve document rows for a common-scope certified pair without repeating its static compatibility decision. -/
def resolveCheckedParallelIndexJoin
    (preliminary : CheckedIndexPreliminary model)
    (groups : CheckedParallelIndexGroups model) (outer : Env := []) :
    Except CheckedIndexColumnError ResolvedParallelIndexJoin :=
  preliminary.resolveCheckedParallelIndexJoinAt groups outer outer

/-- Resolve one certified framed join. The checked plan, not the caller, decides which column receives the complete frame environment. -/
def resolveCheckedParallelIndexJoinInFrame
    (preliminary : CheckedIndexPreliminary model)
    (groups : CheckedParallelIndexGroups model)
    (frameOuter commonOuter : Env) :
    Except CheckedIndexColumnError ResolvedParallelIndexJoin :=
  match groups.outerScopePlan with
  | .common scope => .error (.incoherentFrameScope scope)
  | .framed .left _ _ =>
      preliminary.resolveCheckedParallelIndexJoinAt
        groups frameOuter commonOuter
  | .framed .right _ _ =>
      preliminary.resolveCheckedParallelIndexJoinAt
        groups commonOuter frameOuter

def resolveParallelIndexJoin (preliminary : CheckedIndexPreliminary model)
    (left right : RepeatableGroupDecl) (outer : Env := []) :
    Except CheckedIndexColumnError ResolvedParallelIndexJoin := do
  let groups ← checkParallelIndexGroups model left right
  preliminary.resolveCheckedParallelIndexJoin groups outer

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

namespace ResolvedParallelIndexRow

/-- Route one resolved field to its joined side by model ownership. A reference outside both groups is a structural rule-shape failure, not a synthetic absent observation. -/
def readValidation (row : ResolvedParallelIndexRow)
    (preliminary : CheckedIndexPreliminary model) (field : FieldId) :
    Except CheckedIndexColumnError CellObservation := do
  let declaration ← model.lookupUniqueId field |>.mapError .model
  if row.left.group.path.isPrefixOf declaration.groupPath then
    row.left.readValidation preliminary field
  else if row.right.group.path.isPrefixOf declaration.groupPath then
    row.right.readValidation preliminary field
  else
    throw (.fieldOutsideParallelGroups field
      row.left.group.path row.right.group.path)

end ResolvedParallelIndexRow

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
