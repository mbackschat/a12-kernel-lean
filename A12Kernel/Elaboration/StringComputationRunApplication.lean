import A12Kernel.Elaboration.StringComputationRunResult
import A12Kernel.Semantics.StringApplication

/-! # String-specific whole-run application

This capsule applies an already-classified String result to an explicitly supplied compatible destination. The generic route accepts an exact target-state projection; the original checked route validates nonrepeatable String actions against a caller-supplied checked document. A bounded addressed route additionally exposes the measured complete predecessor prefix for one finite direct repetition level. Neither route reconstructs a document. Application distinguishes source-classified retained clears from direct errored and accepted outcomes and never reclassifies an action against the destination.
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

/-- Fail-closed errors for the calibrated one-level repeatable String application boundary. -/
inductive StringComputationRepeatableApplicationError where
  | duplicateActionTarget (target : CellAddr)
  | targetField (address : CellAddr) (cause : ResolveError)
  | nonStringTarget (address : CellAddr)
  | invalidTargetDepth (address : CellAddr) (expected : Nat)
  | zeroTargetCoordinate (address : CellAddr)
  | unknownRepeatableLevel (level : RepeatableLevel)
  | unboundedRepeatableLevel (level : RepeatableLevel)
  | invalidOneLevelScope (address : CellAddr) (expected : RepeatableLevel)
  | overCapacityTarget (address : CellAddr) (maximum : Nat)
  | unsupportedOneLevelDestination (level : RepeatableLevel)
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

end StringComputationRunView

end A12Kernel
