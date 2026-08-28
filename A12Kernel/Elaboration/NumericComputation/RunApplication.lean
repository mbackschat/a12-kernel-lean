import A12Kernel.Elaboration.NumericComputation.RunResult
import A12Kernel.Semantics.NumericApplication

/-! # Number-specific whole-run application

This capsule applies an already-classified Number result to an explicitly supplied compatible destination. It distinguishes source-classified retained clears from direct errors and accepted outcomes and never reclassifies an action against the destination. -/

namespace A12Kernel

/-- The exact caller-supplied target-state projection needed by one Number result target-key domain. -/
abbrev NumericComputationDestination (Target : Type := FieldId) :=
  Target → NumericTargetState

namespace NumericComputationDestination

def update {Target : Type} [DecidableEq Target]
    (destination : NumericComputationDestination Target)
    (target : Target) (state : NumericTargetState) :
    NumericComputationDestination Target :=
  fun candidate =>
    if candidate = target then state else destination candidate

def applyOutcome {Target : Type} [DecidableEq Target]
    (destination : NumericComputationDestination Target)
    (target : Target) (outcome : NumericTargetOutcome) :
    NumericComputationDestination Target :=
  destination.update target (outcome.applyTo (destination target))

/-- Apply one source-classified CLEARED action without reclassifying it against the destination. -/
def applyRetainedClear {Target : Type} [DecidableEq Target]
    (destination : NumericComputationDestination Target)
    (target : Target) : NumericComputationDestination Target :=
  destination.update target (destination target).applyRetainedClear

end NumericComputationDestination

/-- Fail-closed destination-owned target-address errors. The retained result is not model-indexed, so source/destination model compatibility remains an explicit caller precondition. -/
inductive NumericComputationDocumentApplicationError where
  | duplicateActionTarget (target : CellAddr)
  | targetField (address : CellAddr) (cause : ResolveError)
  | nonNumericTarget (address : CellAddr)
  | invalidTargetDepth (address : CellAddr) (expected : Nat)
  | zeroTargetCoordinate (address : CellAddr)
  | unknownRepeatableLevel (level : RepeatableLevel)
  | unboundedRepeatableLevel (level : RepeatableLevel)
  | invalidOneLevelScope (address : CellAddr) (expected : RepeatableLevel)
  | overCapacityTarget (address : CellAddr) (maximum : Nat)
  | unsupportedOneLevelDestination (level : RepeatableLevel)
  | invalidTwoLevelScope (address : CellAddr)
      (outer inner : RepeatableLevel)
  | unsupportedTwoLevelDestination
      (outer inner : RepeatableLevel)
  deriving Repr, DecidableEq

/-- Validate one retained Number action address against the destination model and derive only its directly addressed repeatable ancestry. -/
def numericComputationActionRowsFor
    (model : FlatModel) (address : CellAddr) :
    Except NumericComputationDocumentApplicationError (List RowAddr) := do
  let declaration ←
    (model.lookupUniqueId address.field).mapError (.targetField address)
  match declaration.policy.kind with
  | .number _ => pure ()
  | _ => throw (.nonNumericTarget address)
  if address.path.length != declaration.repeatableScope.length then
    throw (.invalidTargetDepth address declaration.repeatableScope.length)
  if address.path.any (· == 0) then
    throw (.zeroTargetCoordinate address)
  pure (repeatableAncestorRowsFor declaration.repeatableScope address.path)

private def numericAppliedValueCell (value : StoredNumber) : CheckedCell :=
  checkAdmittedRawCell (.parsed (.num value.amount))

private def numericAppliedEmptyCell (present : Bool) : CheckedCell :=
  if present then checkAdmittedRawCell .presentEmpty
  else checkAdmittedRawCell .empty

namespace NumericComputationRunView

/-- Read one validation-phase cell after this view has successfully applied to the supplied destination. Retained Number actions override only their exact target; every other field preserves the destination's checked observation. -/
def validationCellAfterApplication
    (view : NumericComputationRunView Message CellAddr)
    (destination : CheckedDocument model)
    (environment : Env) (field : FieldId) :
    Except CheckedAddressingError CheckedCell := do
  let declaration ←
    (model.lookupUniqueId field).mapError (.field field)
  let path ←
    (environment.pathForScope declaration.repeatableScope)
      |>.mapError .environment
  let address : CellAddr := { field, path }
  match view.withChanges.find? fun computed =>
      computed.targetField == address with
  | some computed => pure (numericAppliedValueCell computed.value)
  | none =>
      if view.cleared.contains address then
        pure (numericAppliedEmptyCell true)
      else if view.withErrors.any fun computed =>
          computed.targetField == address then
        pure (numericAppliedEmptyCell
          (destination.numericTargetPlacementStateAt address).isPresent)
      else
        let physical :=
          (repeatableAncestorRowsFor declaration.repeatableScope path).all
            destination.source.instantiatedRows.contains
        if physical then
          destination.read address |>.mapError .document
        else
          pure (numericAppliedEmptyCell false)

end NumericComputationRunView

/-- Exact Number-cell projection after retained-result application to a separately supplied checked destination. `createdRows` records only directly addressed ancestors proved absent in that destination; it deliberately makes no claim about unobserved predecessor padding or row order. -/
structure NumericComputationApplicationProjection
    (model : FlatModel) where
  private mk ::
  private destination : CheckedDocument model
  private states : CellAddr → NumericTargetState
  private createdRows : List RowAddr

namespace NumericComputationApplicationProjection

/-- Initialize the application projection from one checked destination. -/
def ofChecked (destination : CheckedDocument model) :
    NumericComputationApplicationProjection model := {
  destination
  states := destination.numericTargetPlacementStateAt
  createdRows := []
}

/-- Read one Number target state after the retained actions applied so far. -/
def stateAt (projection : NumericComputationApplicationProjection model)
    (address : CellAddr) : NumericTargetState :=
  projection.states address

/-- Whether retained-result application directly created one addressed ancestor that was absent in the supplied destination. False says only that direct creation was not observed by this projection; predecessor padding is outside its claim. -/
def createdRow (projection : NumericComputationApplicationProjection model)
    (row : RowAddr) : Bool :=
  projection.createdRows.contains row

private def updateState
    (projection : NumericComputationApplicationProjection model)
    (address : CellAddr) (state : NumericTargetState) :
    NumericComputationApplicationProjection model := {
  projection with
  states := fun candidate =>
    if candidate == address then state else projection.states candidate
}

private def withCreatedAncestors
    (projection : NumericComputationApplicationProjection model)
    (rows : List RowAddr) :
    NumericComputationApplicationProjection model :=
  let newlyCreated := rows.filter fun row =>
    !projection.destination.source.instantiatedRows.contains row &&
      !projection.createdRows.contains row
  { projection with
    createdRows := projection.createdRows ++ newlyCreated }

private def place
    (projection : NumericComputationApplicationProjection model)
    (address : CellAddr) (rows : List RowAddr)
    (state : NumericTargetState) :
    NumericComputationApplicationProjection model :=
  (projection.withCreatedAncestors rows).updateState address state

/-- Validate and apply one retained clear at an exact destination address. -/
def applyRetainedClearAt
    (projection : NumericComputationApplicationProjection model)
    (address : CellAddr) :
    Except NumericComputationDocumentApplicationError
      (NumericComputationApplicationProjection model) := do
  let rows ← numericComputationActionRowsFor model address
  let withRows := projection.withCreatedAncestors rows
  pure {
    withRows with
    states := fun candidate =>
      if candidate == address then
        (projection.states address).applyRetainedClear
      else withRows.states candidate
  }

private def applyError
    (projection : NumericComputationApplicationProjection model)
    (address : CellAddr) :
    NumericComputationApplicationProjection model :=
  projection.updateState address (projection.states address).clearValue

private def applyValue
    (projection : NumericComputationApplicationProjection model)
    (address : CellAddr) (rows : List RowAddr) (value : StoredNumber) :
    NumericComputationApplicationProjection model :=
  projection.place address rows (.presentValue (.decimal value))

end NumericComputationApplicationProjection

/-- A bounded applied-document projection for one finite repetition level. It adds the normalized predecessor prefix established for direct one-level Number application while retaining exact destination and applied cell states from the generic checked projection. -/
structure NumericComputationOneLevelApplicationProjection
    (model : FlatModel) where
  private mk ::
  private applied : NumericComputationApplicationProjection model
  private group : RepeatableGroupDecl
  private maximum : Nat
  private rowCount : Nat

namespace NumericComputationOneLevelApplicationProjection

private def rowsThrough (level : RepeatableLevel) (count : Nat) : List RowAddr :=
  (List.range count).map fun offset => { group := level, path := [offset + 1] }

private def ofApplied
    (destination : CheckedDocument model)
    (applied : NumericComputationApplicationProjection model)
    (level : RepeatableLevel) :
    Except NumericComputationDocumentApplicationError
      (NumericComputationOneLevelApplicationProjection model) := do
  let group ← match model.repeatableGroupAtLevel? level with
    | some group => pure group
    | none => throw (.unknownRepeatableLevel level)
  if model.repeatableScopeForGroupPath group.path != [level] then
    throw (.unsupportedOneLevelDestination level)
  let maximum ← match group.repeatability with
    | some maximum => pure maximum
    | none => throw (.unboundedRepeatableLevel level)
  let selectedRows := destination.source.instantiatedRows.filter
    fun row => row.group == level
  if selectedRows.any fun row => row.path.length != 1 then
    throw (.unsupportedOneLevelDestination level)
  if selectedRows.length > maximum then
    throw (.unsupportedOneLevelDestination level)
  pure { applied, group, maximum, rowCount := selectedRows.length }

private def coordinateFor
    (projection : NumericComputationOneLevelApplicationProjection model)
    (address : CellAddr) :
    Except NumericComputationDocumentApplicationError Nat := do
  let declaration ←
    (model.lookupUniqueId address.field).mapError (.targetField address)
  match declaration.policy.kind with
  | .number _ => pure ()
  | _ => throw (.nonNumericTarget address)
  if declaration.repeatableScope != [projection.group.level] then
    throw (.invalidOneLevelScope address projection.group.level)
  let coordinate ← match address.path with
    | [coordinate] => pure coordinate
    | _ => throw (.invalidTargetDepth address 1)
  if coordinate == 0 then
    throw (.zeroTargetCoordinate address)
  if coordinate > projection.maximum then
    throw (.overCapacityTarget address projection.maximum)
  pure coordinate

private def materializeAt
    (projection : NumericComputationOneLevelApplicationProjection model)
    (address : CellAddr) :
    Except NumericComputationDocumentApplicationError
      (NumericComputationOneLevelApplicationProjection model) := do
  let coordinate ← projection.coordinateFor address
  pure { projection with rowCount := max projection.rowCount coordinate }

private def validateAt
    (projection : NumericComputationOneLevelApplicationProjection model)
    (address : CellAddr) :
    Except NumericComputationDocumentApplicationError
      (NumericComputationOneLevelApplicationProjection model) :=
  projection.coordinateFor address |>.map fun _ => projection

/-- The complete normalized predecessor prefix at the selected repetition level. -/
def rows (projection : NumericComputationOneLevelApplicationProjection model) :
    List RowAddr :=
  rowsThrough projection.group.level projection.rowCount

/-- The selected repetition level and materialized prefix length. -/
def prefixExtent (projection : NumericComputationOneLevelApplicationProjection model) :
    RepeatableLevel × Nat :=
  (projection.group.level, projection.rowCount)

/-- Read one exact Number state after application. Cells not targeted by the retained result preserve the caller-supplied destination state. -/
def stateAt
    (projection : NumericComputationOneLevelApplicationProjection model)
    (address : CellAddr) : NumericTargetState :=
  projection.applied.stateAt address

end NumericComputationOneLevelApplicationProjection

/-- A bounded applied-document projection for two finite direct repetition levels. Each inner prefix belongs only to its concrete outer coordinate; padding an outer predecessor never invents an inner row. -/
structure NumericComputationTwoLevelApplicationProjection
    (model : FlatModel) where
  private mk ::
  private applied : NumericComputationApplicationProjection model
  private outerGroup : RepeatableGroupDecl
  private innerGroup : RepeatableGroupDecl
  private maximumOuter : Nat
  private maximumInner : Nat
  private outerRowCount : Nat
  private innerRowCount : Nat → Nat

namespace NumericComputationTwoLevelApplicationProjection

private def selectedRows
    (destination : CheckedDocument model) (level : RepeatableLevel) :
    List RowAddr :=
  destination.source.instantiatedRows.filter fun row => row.group == level

private def countInnerRows (rows : List RowAddr) (outer : Nat) : Nat :=
  rows.countP fun row => match row.path with
    | candidate :: _ => candidate == outer
    | [] => false

private def ofApplied
    (destination : CheckedDocument model)
    (applied : NumericComputationApplicationProjection model)
    (outer inner : RepeatableLevel) :
    Except NumericComputationDocumentApplicationError
      (NumericComputationTwoLevelApplicationProjection model) := do
  let outerGroup ← match model.repeatableGroupAtLevel? outer with
    | some group => pure group
    | none => throw (.unknownRepeatableLevel outer)
  let innerGroup ← match model.repeatableGroupAtLevel? inner with
    | some group => pure group
    | none => throw (.unknownRepeatableLevel inner)
  if model.repeatableScopeForGroupPath outerGroup.path != [outer] then
    throw (.unsupportedTwoLevelDestination outer inner)
  if model.repeatableScopeForGroupPath innerGroup.path != [outer, inner] then
    throw (.unsupportedTwoLevelDestination outer inner)
  let maximumOuter ← match outerGroup.repeatability with
    | some maximum => pure maximum
    | none => throw (.unboundedRepeatableLevel outer)
  let maximumInner ← match innerGroup.repeatability with
    | some maximum => pure maximum
    | none => throw (.unboundedRepeatableLevel inner)
  let outerRows := selectedRows destination outer
  let innerRows := selectedRows destination inner
  if outerRows.any fun row => match row.path with
      | [coordinate] => coordinate > maximumOuter
      | _ => true then
    throw (.unsupportedTwoLevelDestination outer inner)
  if innerRows.any fun row => match row.path with
      | [_, coordinate] => coordinate > maximumInner
      | _ => true then
    throw (.unsupportedTwoLevelDestination outer inner)
  pure {
    applied, outerGroup, innerGroup, maximumOuter, maximumInner
    outerRowCount := outerRows.length
    innerRowCount := countInnerRows innerRows
  }

private def coordinatesFor
    (projection : NumericComputationTwoLevelApplicationProjection model)
    (address : CellAddr) :
    Except NumericComputationDocumentApplicationError (Nat × Nat) := do
  let declaration ←
    (model.lookupUniqueId address.field).mapError (.targetField address)
  match declaration.policy.kind with
  | .number _ => pure ()
  | _ => throw (.nonNumericTarget address)
  if declaration.repeatableScope !=
      [projection.outerGroup.level, projection.innerGroup.level] then
    throw (.invalidTwoLevelScope address
      projection.outerGroup.level projection.innerGroup.level)
  let (outer, inner) ← match address.path with
    | [outer, inner] => pure (outer, inner)
    | _ => throw (.invalidTargetDepth address 2)
  if outer == 0 || inner == 0 then
    throw (.zeroTargetCoordinate address)
  if outer > projection.maximumOuter then
    throw (.overCapacityTarget address projection.maximumOuter)
  if inner > projection.maximumInner then
    throw (.overCapacityTarget address projection.maximumInner)
  pure (outer, inner)

private def materializeAt
    (projection : NumericComputationTwoLevelApplicationProjection model)
    (address : CellAddr) :
    Except NumericComputationDocumentApplicationError
      (NumericComputationTwoLevelApplicationProjection model) := do
  let (outer, inner) ← projection.coordinatesFor address
  pure {
    projection with
    outerRowCount := max projection.outerRowCount outer
    innerRowCount := fun candidate =>
      if candidate == outer then max (projection.innerRowCount candidate) inner
      else projection.innerRowCount candidate
  }

private def validateAt
    (projection : NumericComputationTwoLevelApplicationProjection model)
    (address : CellAddr) :
    Except NumericComputationDocumentApplicationError
      (NumericComputationTwoLevelApplicationProjection model) :=
  projection.coordinatesFor address |>.map fun _ => projection

/-- The selected outer and inner repetition levels. -/
def levels
    (projection : NumericComputationTwoLevelApplicationProjection model) :
    RepeatableLevel × RepeatableLevel :=
  (projection.outerGroup.level, projection.innerGroup.level)

/-- The normalized outer prefix length. -/
def outerExtent
    (projection : NumericComputationTwoLevelApplicationProjection model) : Nat :=
  projection.outerRowCount

/-- The normalized inner prefix length below one concrete outer coordinate. -/
def innerExtentAt
    (projection : NumericComputationTwoLevelApplicationProjection model)
    (outer : Nat) : Nat :=
  projection.innerRowCount outer

/-- The complete normalized outer predecessor prefix. -/
def outerRows
    (projection : NumericComputationTwoLevelApplicationProjection model) :
    List RowAddr :=
  (List.range projection.outerExtent).map fun offset =>
    { group := projection.outerGroup.level, path := [offset + 1] }

/-- The complete inner predecessor prefix scoped to one concrete outer coordinate. -/
def innerRowsAt
    (projection : NumericComputationTwoLevelApplicationProjection model)
    (outer : Nat) : List RowAddr :=
  (List.range (projection.innerExtentAt outer)).map fun offset =>
    { group := projection.innerGroup.level, path := [outer, offset + 1] }

/-- Every concrete inner row in outer-coordinate order. Synthetic outer predecessors with no addressed inner row contribute nothing. -/
def leafRows
    (projection : NumericComputationTwoLevelApplicationProjection model) :
    List RowAddr :=
  projection.outerRows.flatMap fun row => match row.path with
    | [outer] => projection.innerRowsAt outer
    | _ => []

/-- Read one exact Number state after application. -/
def stateAt
    (projection : NumericComputationTwoLevelApplicationProjection model)
    (address : CellAddr) : NumericTargetState :=
  projection.applied.stateAt address

end NumericComputationTwoLevelApplicationProjection

namespace NumericComputationRunView

inductive NumericComputationRunApplicationError
    (Target : Type := FieldId) where
  | duplicateActionTarget (target : Target)
  deriving Repr, DecidableEq

/-- Targets consumed by application. Unchanged successes and residual messages are deliberately absent. -/
def actionTargets {Target : Type}
    (view : NumericComputationRunView ResidualMessage Target) :
    List Target :=
  view.cleared ++ view.withErrors.map (·.targetField) ++
    view.withChanges.map (·.targetField)

def firstDuplicateActionTarget? {Target : Type} [DecidableEq Target]
    (view : NumericComputationRunView ResidualMessage Target) :
    Option Target :=
  firstDuplicate? view.actionTargets
where
  firstDuplicate? : List Target → Option Target
    | [] => none
    | target :: remaining =>
        if target ∈ remaining then some target
        else firstDuplicate? remaining

/-- Apply clears, errors, then source-relative changes. Repeated action targets are structural rather than list-order conflicts. -/
def applyTo {Target : Type} [DecidableEq Target]
    (view : NumericComputationRunView ResidualMessage Target)
    (destination : NumericComputationDestination Target) :
    Except (NumericComputationRunApplicationError Target)
      (NumericComputationDestination Target) :=
  match view.firstDuplicateActionTarget? with
  | some duplicate => .error (.duplicateActionTarget duplicate)
  | none =>
      let afterCleared := view.cleared.foldl
        (fun current target => current.applyRetainedClear target) destination
      let afterErrors := view.withErrors.foldl
        (fun current computed => current.applyOutcome computed.targetField
          (.rejected computed.attempted computed.cause)) afterCleared
      .ok (view.withChanges.foldl
        (fun current computed => current.applyOutcome computed.targetField
          (.accepted computed.value)) afterErrors)

/-- Apply source-relative CLEARED, ERRORED, and changed-VALUE actions to a separately supplied checked destination. Every action address is validated against the destination model. The unindexed retained view cannot certify source/destination model identity, so model compatibility remains a caller precondition. CLEARED and VALUE place their target and directly addressed ancestors; ERRORED clears only an already-present destination target. -/
def applyToChecked
    (view : NumericComputationRunView ResidualMessage CellAddr)
    (destination : CheckedDocument model) :
    Except NumericComputationDocumentApplicationError
      (NumericComputationApplicationProjection model) :=
  match view.firstDuplicateActionTarget? with
  | some duplicate => .error (.duplicateActionTarget duplicate)
  | none => do
      let initial :=
        NumericComputationApplicationProjection.ofChecked destination
      let afterCleared ← view.cleared.foldlM
        (fun current address =>
          current.applyRetainedClearAt address) initial
      let afterErrors ← view.withErrors.foldlM
        (fun current computed => do
          let _ ← numericComputationActionRowsFor
            model computed.targetField
          pure (current.applyError computed.targetField)) afterCleared
      view.withChanges.foldlM
        (fun current computed => do
          let rows ← numericComputationActionRowsFor
            model computed.targetField
          pure (current.applyValue computed.targetField rows computed.value))
        afterErrors

private def applyCheckedTopologyActions
    (view : NumericComputationRunView ResidualMessage CellAddr)
    (initial : Projection)
    (materialize validate : Projection → CellAddr →
      Except NumericComputationDocumentApplicationError Projection) :
    Except NumericComputationDocumentApplicationError Projection := do
  let afterCleared ← view.cleared.foldlM materialize initial
  let afterErrors ← view.withErrors.foldlM
    (fun current computed => validate current computed.targetField)
    afterCleared
  view.withChanges.foldlM
    (fun current computed => materialize current computed.targetField)
    afterErrors

/-- Apply one retained Number run to a checked destination and expose the externally calibrated complete row prefix for one finite, direct repetition level. CLEARED and changed VALUE materialize their exact coordinate and every predecessor; ERRORED validates its address but does not create an absent row. Nested repetition and non-Number targets remain outside this bounded projection. -/
def applyToCheckedOneLevel
    (view : NumericComputationRunView ResidualMessage CellAddr)
    (destination : CheckedDocument model)
    (level : RepeatableLevel) :
    Except NumericComputationDocumentApplicationError
      (NumericComputationOneLevelApplicationProjection model) := do
  let applied ← view.applyToChecked destination
  let initial ←
    NumericComputationOneLevelApplicationProjection.ofApplied
      destination applied level
  applyCheckedTopologyActions view initial
    NumericComputationOneLevelApplicationProjection.materializeAt
    NumericComputationOneLevelApplicationProjection.validateAt

/-- Apply one retained Number run to a checked destination and expose the externally calibrated scoped predecessor topology for exactly two finite, direct repetition levels. CLEARED and changed VALUE materialize both exact coordinates and their local predecessors; ERRORED validates without creating absent rows. -/
def applyToCheckedTwoLevel
    (view : NumericComputationRunView ResidualMessage CellAddr)
    (destination : CheckedDocument model)
    (outer inner : RepeatableLevel) :
    Except NumericComputationDocumentApplicationError
      (NumericComputationTwoLevelApplicationProjection model) := do
  let applied ← view.applyToChecked destination
  let initial ←
    NumericComputationTwoLevelApplicationProjection.ofApplied
      destination applied outer inner
  applyCheckedTopologyActions view initial
    NumericComputationTwoLevelApplicationProjection.materializeAt
    NumericComputationTwoLevelApplicationProjection.validateAt

end NumericComputationRunView

end A12Kernel
