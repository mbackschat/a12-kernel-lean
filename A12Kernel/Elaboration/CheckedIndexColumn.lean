import A12Kernel.Semantics.MessageCacheOrder
import A12Kernel.Elaboration.CheckedIndexPreliminary
import A12Kernel.Elaboration.RuleIterationDomain
import A12Kernel.Semantics.SemanticIndex
import A12Kernel.Semantics.MessagePointer

/-! # Checked index columns and bounded parallel joins

This family-owned boundary resolves one generated-preliminary index column without inventing another document or address model. It retains every ordered key occurrence, duplicate identity for selection exclusion, and one column-unavailability cause. Semantic-index and parallel projections share only that admission relation while retaining their separate selection and missing-side policies. The checked parallel profile admits either one common outer repeatable scope or one non-indexed frame on exactly one side, across transparent nonrepeatable wrappers and normalized non-Number cache keys (spec/02 §3) or dot-decimal Number keys. Number iteration tokens retain declaration-specific minimum scale separately from numeric lookup identity (spec/07 §2).
-/

namespace A12Kernel

inductive CheckedIndexColumnError where
  | model (error : ResolveError)
  | document (error : CheckedDocumentError)
  | environment (error : EnvBindingError)
  | rows (error : ActualRowEnvironmentError)
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
  | unresolvedDuplicatePointer (field : FieldId) (group : GroupPath)
  | incompatibleGroups (left right : GroupPath)
  | incompatibleIndexFields (left right : List String)
  deriving Repr, DecidableEq

structure ResolvedCheckedIndexEntry where
  key : SemanticIndexKey
  environment : Env
  deriving Repr, DecidableEq

structure ResolvedCheckedIndexColumn (model : FlatModel) where
  private mk ::
  group : SemanticIndexGroup
  indexDeclaration : FlatFieldDecl
  entries : List ResolvedCheckedIndexEntry
  duplicateKeys : List SemanticIndexKey
  unavailableKey : Option FormalCause
  modelWellFormed : model.validate.isOk = true
  groupOwned : model.declaresSemanticIndexGroup group = true
  indexDeclared : group.indexField = some indexDeclaration.id

structure ResolvedParallelIndexSide where
  group : RepeatableGroupDecl
  environment : Option Env
  unavailableKey : Option FormalCause
  /-- Duplicate value selection is unavailable, but its message address requires the separate cache insertion order (spec/08 §4.3). -/
  duplicatePointer : Bool := false
  /-- An unmatched side's bindings of the nested levels a rule visits below its group, which its
  message pointer names concretely beside the unknown joined coordinate (KF603). -/
  inner : Env := []
  deriving Repr, DecidableEq

structure ResolvedParallelIndexRow where
  iterationToken : String
  key : SemanticIndexKey
  left : ResolvedParallelIndexSide
  right : ResolvedParallelIndexSide
  deriving Repr, DecidableEq

structure ResolvedParallelIndexJoin where
  leftGroup : RepeatableGroupDecl
  rightGroup : RepeatableGroupDecl
  rows : List ResolvedParallelIndexRow
  deriving Repr, DecidableEq

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

/-- Whether two index fields' kinds join: equal kinds, two Numbers whatever their scales, or two
    temporal kinds. The Kernel admits a Number join across maximum scales (k22-static-classes-2026-10-24,
    `s5-j-n0n2`), and its lookup re-normalizes a key under the destination declaration without rounding,
    so equal numbers meet as equal kinds' do
    ([checkpoint](../../docs/sources/key-join-and-parallel-probes.md#src-parallel-number-index-tokens)).
    A temporal pair joins on its keys' cache text, so a Date beside a DateTime, a Time or a date fragment
    binds no partner row whose text differs, as the Kernel's rows do
    ([checkpoint](../../docs/sources/key-join-and-parallel-probes.md#src-cross-kind-join-keys)); which
    temporal pairs a rule may join is `FieldKind.indexTypeGate`'s question, asked before this one. -/
def FieldKind.joinsAsIndex : FieldKind → FieldKind → Bool
  | .number _, .number _ => true
  | .temporal _ _, .temporal _ _ => true
  | left, right => left == right

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
    leftIndexDeclaration.policy.kind.joinsAsIndex rightIndexDeclaration.policy.kind = true

namespace ResolvedCheckedIndexColumn

/-- The public certificate boundary: the column belongs to one validated model and its declaration is the group's exact index field. -/
def WellFormed (column : ResolvedCheckedIndexColumn model) : Prop :=
  model.validate.isOk = true ∧
    model.declaresSemanticIndexGroup column.group = true ∧
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

/-- Recover the unique selectable physical entry without choosing a consumer-specific missing or poison policy. -/
def selectableEntryFor? (column : ResolvedCheckedIndexColumn model)
    (key : SemanticIndexKey) : Option ResolvedCheckedIndexEntry :=
  if column.admitsSelectableKey key then
    column.entries.find? fun entry => entry.key == key
  else
    none

end ResolvedCheckedIndexColumn

namespace CheckedParallelIndexGroups

/-- The public certificate boundary for the bounded transparent-wrapper profile. -/
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
    groups.leftIndexDeclaration.policy.kind.joinsAsIndex groups.rightIndexDeclaration.policy.kind = true

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
  -- As `CheckedIndexPreliminary.storedAt?`: an overlaid base carries its spelling on the placement.
  | none => (preliminary.base.storedTextAt address).orElse fun _ =>
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
      | some stored => pure (some (.text (normalizeEvaluatedString stored)))
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

private def CheckedIndexPreliminary.addIndexCell
    (preliminary : CheckedIndexPreliminary model) (declaration : FlatFieldDecl)
    (scope : List RepeatableLevel) (path : List Nat) (state : IndexColumnState) :
    Except CheckedIndexColumnError IndexColumnState := do
  let address : CellAddr := { field := declaration.id, path }
  let cell ← preliminary.readAuthoredValidation address |>.mapError .document
  let key ← preliminary.indexKey? declaration address cell
  let entry := key.map fun resolved => { key := resolved, environment := scope.zip path }
  let duplicate := preliminary.findingKindAt? address == some .unique
  pure (state.add entry duplicate cell.findings.head?)

private def CheckedIndexPreliminary.scanIndexRows
    (preliminary : CheckedIndexPreliminary model)
    (groupPath : GroupPath) (declaration : FlatFieldDecl)
    (scope : List RepeatableLevel) :
    List RowAddr → IndexColumnState →
      Except CheckedIndexColumnError IndexColumnState
  | [], state => pure state
  | row :: rows, state => do
      if row.path.length != scope.length then
        throw (.incoherentRow row scope.length)
      let overLimit ← match model.addressOverLimit? scope row.path with
        | some result => pure result
        | none => throw (.incoherentScope groupPath)
      if overLimit then
        preliminary.scanIndexRows groupPath declaration scope rows state
      else
        preliminary.scanIndexRows groupPath declaration scope rows
          (← preliminary.addIndexCell declaration scope row.path state)

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
                          leftIndex.policy.kind.joinsAsIndex rightIndex.policy.kind = true then
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
                        }
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

/-- A repeatable group's column holds its rows under the enclosing parent row. A root or fixed group
has one instance, at the enclosing rows, so its column holds at most that instance's index cell
([runtime open cells](../../docs/sources/model-structure-and-declaration-probes.md#src-runtime-open-cells), `ix*`; below a
repeatable row, [single-instance key](../../docs/sources/model-structure-and-declaration-probes.md#src-single-instance-key),
`RW1`). An enclosing row over its capacity contributes no cell, as a repeatable row does; that is
assumed, not measured. -/
def resolveIndexColumn (preliminary : CheckedIndexPreliminary model)
    (group : SemanticIndexGroup) (outer : Env := [])
    (includeAddress : CellAddr → Bool := fun _ => true) :
    Except CheckedIndexColumnError (ResolvedCheckedIndexColumn model) := do
  if hGroup : model.declaresSemanticIndexGroup group = true then
    let indexId ← match group.indexField with
      | some indexId => pure indexId
      | none => throw (.missingIndexField group.path)
    let declaration ← model.lookupUniqueId indexId |>.mapError .model
    if hDeclared : group.indexField = some declaration.id then
      let scope := model.repeatableScopeForGroupPath group.path
      let state ← match group.level? with
        | some level => do
            if scope.getLast? != some level then
              throw (.incoherentScope group.path)
            let parentPath ←
              outer.pathForScope scope.dropLast |>.mapError .environment
            let rows := preliminary.base.source.instantiatedRows.filter fun row =>
              row.group == level && row.path.dropLast == parentPath &&
                includeAddress { field := declaration.id, path := row.path }
            preliminary.scanIndexRows group.path declaration scope rows {}
        | none => do
            let path ← outer.pathForScope scope |>.mapError .environment
            let overLimit ← match model.addressOverLimit? scope path with
              | some result => pure result
              | none => throw (.incoherentScope group.path)
            if !overLimit && includeAddress { field := declaration.id, path } then
              preliminary.addIndexCell declaration scope path {}
            else pure {}
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

/-- One-sided frames use the shared declared-product/occupied-prefix validation domain. The parallel key slot contributes no numeric bound. Empty declared frames can still join keys supplied by the other side (partial-parallel frame controls, 2026-10-10). -/
def resolveCheckedParallelFrameEnvironments
    (preliminary : CheckedIndexPreliminary model)
    (groups : CheckedParallelIndexGroups model)
    (outer : Env := []) :
    Except CheckedIndexColumnError (List Env) :=
  match groups.outerScopePlan with
  | .common scope => .error (.incoherentFrameScope scope)
  | .framed _ commonScope frameScope => do
      let commonPath ← outer.pathForScope commonScope |>.mapError .environment
      let frames ← preliminary.base.fullValidationRowEnvironments (commonScope ++ frameScope)
        |>.mapError .rows
      pure (frames.filter fun frame =>
        (frame.pathForScope commonScope).toOption == some commonPath)

/-- The index cache normalizes Number storage even in the String-valued input regime.
The parsed fractional scale reconstructs the exact decimal without computed-result rounding. -/
private def parallelNumberToken (preliminary : CheckedIndexPreliminary model)
    (column : ResolvedCheckedIndexColumn model) (entry : ResolvedCheckedIndexEntry) :
    Except CheckedIndexColumnError String := do
  let path ← entry.environment.pathForScope column.indexDeclaration.repeatableScope
    |>.mapError .environment
  let address : CellAddr := { field := column.indexDeclaration.id, path }
  let stored ← match preliminary.storedAt? address with
    | some stored => pure stored
    | none => throw (.missingStoredValue address)
  let parsed ← match parseNumericFormalRead? stored with
    | some parsed => pure parsed
    | none => throw (.incoherentIndexValue address)
  let exact := parsed.value * (decimalFactor parsed.fractionalDigits : Nat)
  if exact.den != 1 || entry.key != .number parsed.value then
    throw (.incoherentIndexValue address)
  let decimal : NumericInputDecimal := { unscaled := exact.num, scale := parsed.fractionalDigits }
  pure (decimal.formalReadText column.indexDeclaration.numericTargetConstraints.minFractionalDigits)

private def parallelKeys (preliminary : CheckedIndexPreliminary model)
    (column : ResolvedCheckedIndexColumn model) :
    Except CheckedIndexColumnError (List (String × SemanticIndexKey)) := do
  let entries := column.entries.filter fun entry => column.admitsParallelKey entry.key
  entries.mapM fun entry => do
    let token ← match entry.key with
      | .text token => pure token
      | .number _ => preliminary.parallelNumberToken column entry
    pure (token, entry.key)

private def parallelSide (group : RepeatableGroupDecl) (column : ResolvedCheckedIndexColumn model)
    (key : SemanticIndexKey) : ResolvedParallelIndexSide := {
  group
  environment := (column.selectableEntryFor? key).map (·.environment)
  unavailableKey := column.unavailableKey
  duplicatePointer := column.duplicateKeys.contains key
}

private def resolveCheckedParallelIndexJoinAt
    (preliminary : CheckedIndexPreliminary model)
    (groups : CheckedParallelIndexGroups model)
    (leftOuter rightOuter : Env) (includeAddress : CellAddr → Bool) :
    Except CheckedIndexColumnError ResolvedParallelIndexJoin := do
  let leftColumn ←
    preliminary.resolveIndexColumn groups.leftGroup leftOuter includeAddress
  let rightColumn ←
    preliminary.resolveIndexColumn groups.rightGroup rightOuter includeAddress
  let leftKeys ← preliminary.parallelKeys leftColumn
  let rightKeys ← preliminary.parallelKeys rightColumn
  let keys := (leftKeys ++ rightKeys).eraseDups.mergeSort fun first second =>
    compare first.1 second.1 != .gt
  pure {
    leftGroup := groups.leftGroup
    rightGroup := groups.rightGroup
    rows := keys.map fun (iterationToken, key) => {
      iterationToken
      key
      left := parallelSide groups.leftGroup leftColumn key
      right := parallelSide groups.rightGroup rightColumn key
    }
  }

/-- Resolve document rows for a common-scope certified pair without repeating its static compatibility decision. -/
def resolveCheckedParallelIndexJoin
    (preliminary : CheckedIndexPreliminary model)
    (groups : CheckedParallelIndexGroups model) (outer : Env := [])
    (includeAddress : CellAddr → Bool := fun _ => true) :
    Except CheckedIndexColumnError ResolvedParallelIndexJoin :=
  preliminary.resolveCheckedParallelIndexJoinAt groups outer outer includeAddress

/-- Resolve one certified framed join. The checked plan, not the caller, decides which column receives the complete frame environment. -/
def resolveCheckedParallelIndexJoinInFrame
    (preliminary : CheckedIndexPreliminary model)
    (groups : CheckedParallelIndexGroups model)
    (frameOuter commonOuter : Env) (includeAddress : CellAddr → Bool := fun _ => true) :
    Except CheckedIndexColumnError ResolvedParallelIndexJoin :=
  match groups.outerScopePlan with
  | .common scope => .error (.incoherentFrameScope scope)
  | .framed .left _ _ =>
      preliminary.resolveCheckedParallelIndexJoinAt
        groups frameOuter commonOuter includeAddress
  | .framed .right _ _ =>
      preliminary.resolveCheckedParallelIndexJoinAt
        groups commonOuter frameOuter includeAddress

def resolveParallelIndexJoin (preliminary : CheckedIndexPreliminary model)
    (left right : RepeatableGroupDecl) (outer : Env := []) :
    Except CheckedIndexColumnError ResolvedParallelIndexJoin := do
  let groups ← checkParallelIndexGroups model left right
  preliminary.resolveCheckedParallelIndexJoin groups outer

end CheckedIndexPreliminary

namespace ResolvedParallelIndexSide

/-- A missing joined row contributes an unknown coordinate while its outer frame stays concrete
(`spec/07` §2). Index-column invalidity changes the read, not this address. Missing outer bindings
remain structural errors rather than being widened into more unknown coordinates. A duplicate requires the actual cache association supplied by its caller: document bytes alone need not determine its host-dependent winner (spec/08 §4.3). -/
def messagePointer (side : ResolvedParallelIndexSide) (model : FlatModel)
    (outer : Env) (field : FieldId)
    (cacheQuery : Option (MessageIndexContext × SemanticIndexKey) := none) :
    Except CheckedIndexColumnError MessagePointer := do
  let declaration ← model.lookupUniqueId field |>.mapError .model
  if !side.group.path.isPrefixOf declaration.groupPath then
    throw (.fieldOutsideGroup field side.group.path)
  let selected ← if side.duplicatePointer then do
      let some (cache, key) := cacheQuery
        | throw (.unresolvedDuplicatePointer field side.group.path)
      let parentScope := (model.repeatableScopeForGroupPath side.group.path).dropLast
      let parentPath ← outer.pathForScope parentScope |>.mapError .environment
      match cache.lookup side.group.level parentPath (some key) with
      | .ok (.concrete row) => pure (some row)
      | _ => throw (.unresolvedDuplicatePointer field side.group.path)
    else pure none
  let coordinates ← match selected, side.environment with
    | some row, _ => declaration.repeatableScope.mapM fun level =>
        if level == side.group.level then pure (.concrete row)
        else (outer.bindingAt level).map MessageRepetitionCoordinate.concrete |>.mapError .environment
    | none, some environment => do
        let path ← environment.pathForScope declaration.repeatableScope |>.mapError .environment
        pure (path.map MessageRepetitionCoordinate.concrete)
    | none, none => declaration.repeatableScope.mapM fun level =>
        if level == side.group.level then pure .unknown
        else ((outer ++ side.inner).bindingAt level).map MessageRepetitionCoordinate.concrete |>.mapError .environment
  pure { field, coordinates }

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
      -- A nested row the rule visits inside a matched joined row need not exist; its declared slot
      -- reads empty, as a frame's does (KF603).
      let cell ← preliminary.base.filterReadWith preliminary.readAuthoredValidation { field, path }
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

/-- The selected row's environment as a read below the selected group sees it: the entry's own
bindings replace the selected group's coordinate and its parents, and `outer`, the reading rule's
row, supplies every level below. A target at the group's own level projects the same address either
way ([below-key selection](../../docs/sources/model-structure-and-declaration-probes.md#src-below-key-selection)). -/
private def selectedEnvironment (selected outer : Env) : Env :=
  selected ++ outer.filter fun binding => !selected.any (·.1 == binding.1)

/-- Project the shared checked column to semantic-index's clean-entry contract. Every duplicate participant is removed, while the column cause remains available to the phase-specific evaluator. -/
def toSemanticIndexColumnWith (column : ResolvedCheckedIndexColumn model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) (target : FieldId) (outer : Env) :
    Except CheckedIndexColumnError ResolvedSemanticIndexColumn := do
  let declaration ← model.lookupUniqueId target |>.mapError .model
  if !column.group.path.isPrefixOf declaration.groupPath then
    throw (.fieldOutsideGroup target column.group.path)
  let entries ← (column.entries.filter fun entry =>
    column.admitsSemanticKey entry.key).mapM fun entry => do
      let environment := selectedEnvironment entry.environment outer
      let path ← environment.pathForScope declaration.repeatableScope
        |>.mapError .environment
      -- The selected row exists, so a missing row is one below it: the firing row's coordinate in
      -- a selected group with fewer rows, which reads empty (`bk-short` of the below-key capture).
      let (target, targetRowAbsent) ← match read { field := target, path } with
        | .error (.missingRow row) =>
            if column.indexDeclaration.repeatableScope.length < declaration.repeatableScope.length then
              pure (checkAdmittedRawCell .empty, true)
            else throw (.document (.missingRow row))
        | .error error => throw (.document error)
        | .ok cell => pure (cell, false)
      pure { token := entry.key, target, environment := some environment, targetRowAbsent }
  pure { entries, unavailableKey := column.unavailableKey }

/-- The immutable validation view is the current-reader projection specialized to preliminary cells. -/
def toSemanticIndexColumn (column : ResolvedCheckedIndexColumn model)
    (preliminary : CheckedIndexPreliminary model) (target : FieldId) (outer : Env) :
    Except CheckedIndexColumnError ResolvedSemanticIndexColumn :=
  column.toSemanticIndexColumnWith preliminary.readAuthoredValidation target outer

end ResolvedCheckedIndexColumn

end A12Kernel
