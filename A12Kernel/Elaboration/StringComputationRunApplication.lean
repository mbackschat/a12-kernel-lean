import A12Kernel.Elaboration.StringComputationRunResult
import A12Kernel.Semantics.StringApplication

/-! # String-specific whole-run application

This capsule applies an already-classified String result to an explicitly supplied compatible destination. The generic route accepts an exact target-state projection; the original checked route validates nonrepeatable String actions against a caller-supplied checked document. Bounded addressed routes additionally expose the measured complete predecessor topology for one or two finite direct repetition levels. Neither route reconstructs a document. Application distinguishes source-classified retained clears from direct errored and accepted outcomes and never reclassifies an action against the destination.
-/

namespace A12Kernel

/-- The exact caller-supplied target-state projection needed by one String result target-key domain. -/
abbrev StringComputationDestination (Target : Type := FieldId) :=
  Target → StringTargetState

namespace StringComputationDestination

/-- Replace one target state while preserving every other field projection. -/
def update {Target : Type} [DecidableEq Target]
    (destination : StringComputationDestination Target)
    (target : Target) (state : StringTargetState) :
    StringComputationDestination Target :=
  fun candidate => if candidate = target then state else destination candidate

/-- Specialize the existing one-target transition at one field. -/
def applyOutcome {Target : Type} [DecidableEq Target]
    (destination : StringComputationDestination Target)
    (target : Target) (outcome : StringTargetOutcome) :
    StringComputationDestination Target :=
  destination.update target (outcome.applyTo (destination target))

/-- Apply one source-classified CLEARED action without reclassifying it against the destination. -/
def applyRetainedClear {Target : Type} [DecidableEq Target]
    (destination : StringComputationDestination Target)
    (target : Target) : StringComputationDestination Target :=
  destination.update target (destination target).applyRetainedClear

end StringComputationDestination

/-- Fail-closed errors while applying nonrepeatable String actions to a checked caller destination. The retained result is not model-indexed, so source/destination model compatibility remains an explicit caller precondition. -/
inductive StringComputationDocumentApplicationError where
  | duplicateActionTarget (target : FieldId)
  | targetField (target : FieldId) (cause : ResolveError)
  | nonStringTarget (target : FieldId)
  | repeatableTarget (target : FieldId)
  deriving Repr, DecidableEq

/-- Fail-closed errors for the calibrated finite repeatable String application boundary. -/
inductive StringComputationRepeatableApplicationError where
  | duplicateActionTarget (target : CellAddr)
  | targetField (address : CellAddr) (cause : ResolveError)
  | nonStringTarget (address : CellAddr)
  | invalidTargetDepth (address : CellAddr) (expected : Nat)
  | zeroTargetCoordinate (address : CellAddr)
  | unknownRepeatableLevel (level : RepeatableLevel)
  | unboundedRepeatableLevel (level : RepeatableLevel)
  | invalidOneLevelScope (address : CellAddr) (expected : RepeatableLevel)
  | invalidTwoLevelScope (address : CellAddr)
      (outer inner : RepeatableLevel)
  | overCapacityTarget (address : CellAddr) (maximum : Nat)
  | unsupportedOneLevelDestination (level : RepeatableLevel)
  | unsupportedTwoLevelDestination
      (outer inner : RepeatableLevel)
  deriving Repr, DecidableEq

/-- Validate one retained action against the exact root String boundary represented by the existing nonrepeatable run. -/
def validateStringComputationActionTarget
    (model : FlatModel) (target : FieldId) :
    Except StringComputationDocumentApplicationError Unit := do
  let declaration ←
    (model.lookupUniqueId target).mapError (.targetField target)
  match declaration.policy.kind with
  | .string => pure ()
  | _ => throw (.nonStringTarget target)
  if !declaration.repeatableScope.isEmpty then
    throw (.repeatableTarget target)

/-- Validate every unique action target before destination state participates. -/
def validateStringComputationActionTargets
    (model : FlatModel) : List FieldId →
      Except StringComputationDocumentApplicationError Unit
  | [] => pure ()
  | target :: remaining => do
      validateStringComputationActionTarget model target
      validateStringComputationActionTargets model remaining

/-- A bounded separate-destination projection for direct String targets at one finite repetition level. It retains exact String cell states and the complete normalized predecessor prefix established by the external differential. -/
structure StringComputationOneLevelApplicationProjection
    (model : FlatModel) where
  private mk ::
  private states : CellAddr → StringTargetState
  private group : RepeatableGroupDecl
  private maximum : Nat
  private rowCount : Nat

namespace StringComputationOneLevelApplicationProjection

private def ofChecked
    (destination : CheckedDocument model)
    (level : RepeatableLevel) :
    Except StringComputationRepeatableApplicationError
      (StringComputationOneLevelApplicationProjection model) := do
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
  pure {
    states := destination.sourceStringTargetStateAt
    group
    maximum
    rowCount := selectedRows.length
  }

private def coordinateFor
    (projection : StringComputationOneLevelApplicationProjection model)
    (address : CellAddr) :
    Except StringComputationRepeatableApplicationError Nat := do
  let declaration ←
    (model.lookupUniqueId address.field).mapError (.targetField address)
  match declaration.policy.kind with
  | .string => pure ()
  | _ => throw (.nonStringTarget address)
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

private def updateState
    (projection : StringComputationOneLevelApplicationProjection model)
    (address : CellAddr) (state : StringTargetState) :
    StringComputationOneLevelApplicationProjection model := {
  projection with
  states := fun candidate =>
    if candidate == address then state else projection.states candidate
}

private def materializeAt
    (projection : StringComputationOneLevelApplicationProjection model)
    (address : CellAddr) :
    Except StringComputationRepeatableApplicationError
      (StringComputationOneLevelApplicationProjection model) := do
  let coordinate ← projection.coordinateFor address
  pure { projection with rowCount := max projection.rowCount coordinate }

private def applyRetainedClearAt
    (projection : StringComputationOneLevelApplicationProjection model)
    (address : CellAddr) :
    Except StringComputationRepeatableApplicationError
      (StringComputationOneLevelApplicationProjection model) := do
  let materialized ← projection.materializeAt address
  pure (materialized.updateState address
    (materialized.states address).applyRetainedClear)

private def applyErrorAt
    (projection : StringComputationOneLevelApplicationProjection model)
    (address : CellAddr) :
    Except StringComputationRepeatableApplicationError
      (StringComputationOneLevelApplicationProjection model) := do
  let _ ← projection.coordinateFor address
  pure (projection.updateState address (projection.states address).clearValue)

private def applyValueAt
    (projection : StringComputationOneLevelApplicationProjection model)
    (address : CellAddr) (value : StoredString) :
    Except StringComputationRepeatableApplicationError
      (StringComputationOneLevelApplicationProjection model) := do
  let materialized ← projection.materializeAt address
  pure (materialized.updateState address (.presentValue value))

/-- The complete normalized predecessor prefix at the selected repetition level. -/
def rows (projection : StringComputationOneLevelApplicationProjection model) :
    List RowAddr :=
  (List.range projection.rowCount).map fun offset =>
    { group := projection.group.level, path := [offset + 1] }

/-- The selected repetition level and materialized prefix length. -/
def prefixExtent
    (projection : StringComputationOneLevelApplicationProjection model) :
    RepeatableLevel × Nat :=
  (projection.group.level, projection.rowCount)

/-- Read one exact String state after application. Untargeted cells preserve the caller-supplied destination state. -/
def stateAt
    (projection : StringComputationOneLevelApplicationProjection model)
    (address : CellAddr) : StringTargetState :=
  projection.states address

end StringComputationOneLevelApplicationProjection

/-- A bounded separate-destination projection for direct String targets at exactly two finite repetition levels. Inner prefixes remain scoped to their concrete outer coordinate. -/
structure StringComputationTwoLevelApplicationProjection
    (model : FlatModel) where
  private mk ::
  private states : CellAddr → StringTargetState
  private outerGroup : RepeatableGroupDecl
  private innerGroup : RepeatableGroupDecl
  private maximumOuter : Nat
  private maximumInner : Nat
  private outerRowCount : Nat
  private innerRowCount : Nat → Nat

namespace StringComputationTwoLevelApplicationProjection

private def selectedRows
    (destination : CheckedDocument model) (level : RepeatableLevel) :
    List RowAddr :=
  destination.source.instantiatedRows.filter fun row => row.group == level

private def countInnerRows (rows : List RowAddr) (outer : Nat) : Nat :=
  rows.countP fun row => match row.path with
    | candidate :: _ => candidate == outer
    | [] => false

private def ofChecked
    (destination : CheckedDocument model)
    (outer inner : RepeatableLevel) :
    Except StringComputationRepeatableApplicationError
      (StringComputationTwoLevelApplicationProjection model) := do
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
    states := destination.sourceStringTargetStateAt
    outerGroup, innerGroup, maximumOuter, maximumInner
    outerRowCount := outerRows.length
    innerRowCount := countInnerRows innerRows
  }

private def coordinatesFor
    (projection : StringComputationTwoLevelApplicationProjection model)
    (address : CellAddr) :
    Except StringComputationRepeatableApplicationError (Nat × Nat) := do
  let declaration ←
    (model.lookupUniqueId address.field).mapError (.targetField address)
  match declaration.policy.kind with
  | .string => pure ()
  | _ => throw (.nonStringTarget address)
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

private def updateState
    (projection : StringComputationTwoLevelApplicationProjection model)
    (address : CellAddr) (state : StringTargetState) :
    StringComputationTwoLevelApplicationProjection model := {
  projection with
  states := fun candidate =>
    if candidate == address then state else projection.states candidate
}

private def materializeAt
    (projection : StringComputationTwoLevelApplicationProjection model)
    (address : CellAddr) :
    Except StringComputationRepeatableApplicationError
      (StringComputationTwoLevelApplicationProjection model) := do
  let (outer, inner) ← projection.coordinatesFor address
  pure {
    projection with
    outerRowCount := max projection.outerRowCount outer
    innerRowCount := fun candidate =>
      if candidate == outer then max (projection.innerRowCount candidate) inner
      else projection.innerRowCount candidate
  }

private def applyRetainedClearAt
    (projection : StringComputationTwoLevelApplicationProjection model)
    (address : CellAddr) :
    Except StringComputationRepeatableApplicationError
      (StringComputationTwoLevelApplicationProjection model) := do
  let materialized ← projection.materializeAt address
  pure (materialized.updateState address
    (materialized.states address).applyRetainedClear)

private def applyErrorAt
    (projection : StringComputationTwoLevelApplicationProjection model)
    (address : CellAddr) :
    Except StringComputationRepeatableApplicationError
      (StringComputationTwoLevelApplicationProjection model) := do
  let _ ← projection.coordinatesFor address
  pure (projection.updateState address (projection.states address).clearValue)

private def applyValueAt
    (projection : StringComputationTwoLevelApplicationProjection model)
    (address : CellAddr) (value : StoredString) :
    Except StringComputationRepeatableApplicationError
      (StringComputationTwoLevelApplicationProjection model) := do
  let materialized ← projection.materializeAt address
  pure (materialized.updateState address (.presentValue value))

/-- The selected outer and inner repetition levels. -/
def levels
    (projection : StringComputationTwoLevelApplicationProjection model) :
    RepeatableLevel × RepeatableLevel :=
  (projection.outerGroup.level, projection.innerGroup.level)

/-- The normalized outer prefix length. -/
def outerExtent
    (projection : StringComputationTwoLevelApplicationProjection model) : Nat :=
  projection.outerRowCount

/-- The normalized inner prefix length below one concrete outer coordinate. -/
def innerExtentAt
    (projection : StringComputationTwoLevelApplicationProjection model)
    (outer : Nat) : Nat :=
  projection.innerRowCount outer

/-- The complete normalized outer predecessor prefix. -/
def outerRows
    (projection : StringComputationTwoLevelApplicationProjection model) :
    List RowAddr :=
  (List.range projection.outerExtent).map fun offset =>
    { group := projection.outerGroup.level, path := [offset + 1] }

/-- The complete inner predecessor prefix scoped to one concrete outer coordinate. -/
def innerRowsAt
    (projection : StringComputationTwoLevelApplicationProjection model)
    (outer : Nat) : List RowAddr :=
  (List.range (projection.innerExtentAt outer)).map fun offset =>
    { group := projection.innerGroup.level, path := [outer, offset + 1] }

/-- Every concrete inner row in outer-coordinate order. Synthetic outer predecessors with no addressed inner row contribute nothing. -/
def leafRows
    (projection : StringComputationTwoLevelApplicationProjection model) :
    List RowAddr :=
  projection.outerRows.flatMap fun row => match row.path with
    | [outer] => projection.innerRowsAt outer
    | _ => []

/-- Read one exact String state after application. Untargeted cells preserve the caller-supplied destination state. -/
def stateAt
    (projection : StringComputationTwoLevelApplicationProjection model)
    (address : CellAddr) : StringTargetState :=
  projection.states address

end StringComputationTwoLevelApplicationProjection

namespace StringComputationRunView

inductive StringComputationRunApplicationError
    (Target : Type := FieldId) where
  | duplicateActionTarget (target : Target)
  deriving Repr, DecidableEq

/-- The targets consumed by application. Successful unchanged instances and residual messages are deliberately absent. -/
def actionTargets {Target : Type}
    (view : StringComputationRunView ResidualMessage Target) :
    List Target :=
  view.cleared ++ view.withErrors.map (·.targetField) ++
    view.withChanges.map (·.targetField)

/-- Locate the first repeated exact target key in encounter order. -/
def firstDuplicateStringTarget? {Target : Type} [DecidableEq Target] :
    List Target → Option Target
  | [] => none
  | target :: remaining =>
      if target ∈ remaining then some target
      else firstDuplicateStringTarget? remaining

/-- Locate the first malformed repeated action target before destination application begins. -/
def firstDuplicateActionTarget? {Target : Type} [DecidableEq Target]
    (view : StringComputationRunView ResidualMessage Target) :
    Option Target :=
  firstDuplicateStringTarget? view.actionTargets

/-- Apply retained clears, target errors, then source-relative changes. Repeated action targets fail structurally before application. -/
def applyTo {Target : Type} [DecidableEq Target]
    (view : StringComputationRunView ResidualMessage Target)
    (destination : StringComputationDestination Target) :
    Except (StringComputationRunApplicationError Target)
      (StringComputationDestination Target) :=
  match view.firstDuplicateActionTarget? with
  | some duplicate => .error (.duplicateActionTarget duplicate)
  | none =>
      let afterCleared := view.cleared.foldl
        (fun current target => current.applyRetainedClear target) destination
      let afterErrors := view.withErrors.foldl
        (fun current computed => current.applyOutcome computed.targetField
          (.errored computed.attempted computed.cause)) afterCleared
      .ok (view.withChanges.foldl
        (fun current computed => current.applyOutcome computed.targetField
          (.accepted computed.value)) afterErrors)

/-- Apply one retained nonrepeatable String result to a separately supplied checked destination. Duplicate actions fail before target validation; admitted actions delegate exactly to the existing source-classified String fold. The returned function is the exact root String-state projection, not a reconstructed document. -/
def applyToChecked
    (view : StringComputationRunView ResidualMessage FieldId)
    (destination : CheckedDocument model) :
    Except StringComputationDocumentApplicationError
      (StringComputationDestination FieldId) :=
  match view.firstDuplicateActionTarget? with
  | some duplicate => .error (.duplicateActionTarget duplicate)
  | none => do
      validateStringComputationActionTargets model view.actionTargets
      match view.applyTo destination.sourceStringTargetState with
      | .error (.duplicateActionTarget duplicate) =>
          .error (.duplicateActionTarget duplicate)
      | .ok applied => .ok applied

/-- Apply one retained String run to a checked destination and expose the externally calibrated complete row prefix for one finite, direct repetition level. CLEARED and changed VALUE materialize their exact coordinate and every predecessor; ERRORED validates and clears an existing target without creating an absent row. -/
def applyToCheckedOneLevel
    (view : StringComputationRunView ResidualMessage CellAddr)
    (destination : CheckedDocument model)
    (level : RepeatableLevel) :
    Except StringComputationRepeatableApplicationError
      (StringComputationOneLevelApplicationProjection model) :=
  match view.firstDuplicateActionTarget? with
  | some duplicate => .error (.duplicateActionTarget duplicate)
  | none => do
      let initial ←
        StringComputationOneLevelApplicationProjection.ofChecked
          destination level
      let afterCleared ← view.cleared.foldlM
        (fun current address => current.applyRetainedClearAt address)
        initial
      let afterErrors ← view.withErrors.foldlM
        (fun current computed => current.applyErrorAt computed.targetField)
        afterCleared
      view.withChanges.foldlM
        (fun current computed =>
          current.applyValueAt computed.targetField computed.value)
        afterErrors

/-- Apply one retained String run to a checked destination and expose the externally calibrated scoped predecessor topology for exactly two finite, direct repetition levels. CLEARED and changed VALUE materialize their exact coordinates and local predecessors; ERRORED validates and clears an existing target without creating absent rows. -/
def applyToCheckedTwoLevel
    (view : StringComputationRunView ResidualMessage CellAddr)
    (destination : CheckedDocument model)
    (outer inner : RepeatableLevel) :
    Except StringComputationRepeatableApplicationError
      (StringComputationTwoLevelApplicationProjection model) :=
  match view.firstDuplicateActionTarget? with
  | some duplicate => .error (.duplicateActionTarget duplicate)
  | none => do
      let initial ←
        StringComputationTwoLevelApplicationProjection.ofChecked
          destination outer inner
      let afterCleared ← view.cleared.foldlM
        (fun current address => current.applyRetainedClearAt address)
        initial
      let afterErrors ← view.withErrors.foldlM
        (fun current computed => current.applyErrorAt computed.targetField)
        afterCleared
      view.withChanges.foldlM
        (fun current computed =>
          current.applyValueAt computed.targetField computed.value)
        afterErrors

end StringComputationRunView

end A12Kernel
