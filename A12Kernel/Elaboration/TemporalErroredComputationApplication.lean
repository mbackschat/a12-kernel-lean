import A12Kernel.Elaboration.TemporalComputationResult

/-! # Error-bearing temporal whole-result application

This capsule shares the immutable clear/error/change fold used by temporal targets with target-local rejection. FullDate and DateRange retain their own payloads, destination aliases, outcome transitions, and application-error types.
-/

namespace A12Kernel

namespace TemporalErroredComputationRunView

/-- Targets consumed by error-bearing application; unchanged successes and residual messages are absent. -/
def actionTargets
    (view : TemporalComputationRunView ComputedInstance ComputedError ResidualMessage)
    (errorTarget : ComputedError → FieldId)
    (changedTarget : ComputedInstance → FieldId) : List FieldId :=
  view.cleared ++ view.withErrors.map errorTarget ++
    view.withChanges.map changedTarget

/-- Apply retained clears, rejected attempts, then source-relative changed successes. Duplicate targets fail before destination lookup. -/
def applyTo
    (view : TemporalComputationRunView ComputedInstance ComputedError ResidualMessage)
    (destination : Destination)
    (errorTarget : ComputedError → FieldId)
    (changedTarget : ComputedInstance → FieldId)
    (duplicateError : FieldId → ApplicationError)
    (applyRetainedClear : Destination → FieldId → Destination)
    (applyError : Destination → ComputedError → Destination)
    (applyChanged : Destination → ComputedInstance → Destination) :
    Except ApplicationError Destination :=
  match FieldId.firstDuplicate?
      (actionTargets view errorTarget changedTarget) with
  | some duplicate => .error (duplicateError duplicate)
  | none =>
      let afterCleared := view.cleared.foldl applyRetainedClear destination
      let afterErrors := view.withErrors.foldl applyError afterCleared
      .ok (view.withChanges.foldl applyChanged afterErrors)

/-- Validate one exact action target against a family predicate and the shared nonrepeatable application boundary. -/
def validateNonrepeatableActionTarget
    (model : FlatModel) (target : FieldId)
    (acceptsKind : FieldKind → Bool)
    (targetFieldError : FieldId → ResolveError → ApplicationError)
    (wrongKindError repeatableError : FieldId → ApplicationError) :
    Except ApplicationError Unit := do
  let declaration ←
    (model.lookupUniqueId target).mapError (targetFieldError target)
  if !acceptsKind declaration.policy.kind then
    throw (wrongKindError target)
  if !declaration.repeatableScope.isEmpty then
    throw (repeatableError target)

/-- Validate every exact action target before the destination projection participates. -/
def validateNonrepeatableActionTargets
    (model : FlatModel) (acceptsKind : FieldKind → Bool)
    (targetFieldError : FieldId → ResolveError → ApplicationError)
    (wrongKindError repeatableError : FieldId → ApplicationError) :
    List FieldId → Except ApplicationError Unit
  | [] => pure ()
  | target :: remaining => do
      validateNonrepeatableActionTarget model target acceptsKind
        targetFieldError wrongKindError repeatableError
      validateNonrepeatableActionTargets model acceptsKind
        targetFieldError wrongKindError repeatableError remaining

end TemporalErroredComputationRunView

/-- Exact caller-supplied target-state projection needed by the nonrepeatable FullDate fragment. -/
abbrev FullDateComputationDestination :=
  TemporalComputationDestination StoredDate

namespace FullDateComputationDestination

def update (destination : FullDateComputationDestination)
    (target : FieldId) (state : FullDateTargetState) :
    FullDateComputationDestination :=
  TemporalComputationDestination.update destination target state

def applyOutcome (destination : FullDateComputationDestination)
    (target : FieldId) (outcome : FullDateTargetOutcome) :
    FullDateComputationDestination :=
  destination.update target (outcome.applyTo (destination target))

def applyRetainedClear (destination : FullDateComputationDestination)
    (target : FieldId) : FullDateComputationDestination :=
  TemporalComputationDestination.applyRetainedClear destination target

end FullDateComputationDestination

namespace FullDateComputationRunView

inductive FullDateComputationRunApplicationError where
  | duplicateActionTarget (field : FieldId)
  | targetField (field : FieldId) (cause : ResolveError)
  | nonFullDateTarget (field : FieldId)
  | repeatableTarget (field : FieldId)
  deriving Repr, DecidableEq

def actionTargets (view : FullDateComputationRunView ResidualMessage) :
    List FieldId :=
  TemporalErroredComputationRunView.actionTargets view
    (fun computed => computed.targetField)
    (fun computed => computed.targetField)

def applyTo (view : FullDateComputationRunView ResidualMessage)
    (destination : FullDateComputationDestination) :
    Except FullDateComputationRunApplicationError
      FullDateComputationDestination :=
  TemporalErroredComputationRunView.applyTo view destination
    (fun computed => computed.targetField)
    (fun computed => computed.targetField)
    FullDateComputationRunApplicationError.duplicateActionTarget
    FullDateComputationDestination.applyRetainedClear
    (fun current computed => current.applyOutcome computed.targetField
      (.errored computed.attempted computed.cause))
    (fun current computed => current.applyOutcome computed.targetField
      (.accepted computed.value))

private def acceptsActionKind : FieldKind → Bool
  | .temporal .date components => components == TemporalComponents.fullDate
  | _ => false

def validateActionTargets (model : FlatModel) (targets : List FieldId) :
    Except FullDateComputationRunApplicationError Unit :=
  TemporalErroredComputationRunView.validateNonrepeatableActionTargets
    model acceptsActionKind FullDateComputationRunApplicationError.targetField
    FullDateComputationRunApplicationError.nonFullDateTarget
    FullDateComputationRunApplicationError.repeatableTarget targets

/-- Apply one retained nonrepeatable FullDate result to the exact root Date-state projection of a separately supplied checked destination. The retained result is not model-indexed, so source/destination model compatibility remains a caller precondition. -/
def applyToChecked (view : FullDateComputationRunView ResidualMessage)
    (destination : CheckedDocument model) :
    Except FullDateComputationRunApplicationError
      FullDateComputationDestination :=
  match FieldId.firstDuplicate? view.actionTargets with
  | some duplicate => .error (.duplicateActionTarget duplicate)
  | none => do
      validateActionTargets model view.actionTargets
      view.applyTo destination.sourceFullDateTargetState

end FullDateComputationRunView

/-- Exact caller-supplied target-state projection needed by the nonrepeatable DateRange fragment. -/
abbrev DateRangeComputationDestination :=
  TemporalComputationDestination StoredDateRange

namespace DateRangeComputationDestination

def update (destination : DateRangeComputationDestination)
    (target : FieldId) (state : TemporalTargetState StoredDateRange) :
    DateRangeComputationDestination :=
  TemporalComputationDestination.update destination target state

def applyOutcome (destination : DateRangeComputationDestination)
    (target : FieldId) (outcome : DateRangeTargetOutcome) :
    DateRangeComputationDestination :=
  destination.update target (outcome.applyTo (destination target))

def applyRetainedClear (destination : DateRangeComputationDestination)
    (target : FieldId) : DateRangeComputationDestination :=
  TemporalComputationDestination.applyRetainedClear destination target

end DateRangeComputationDestination

namespace DateRangeComputationRunView

inductive DateRangeComputationRunApplicationError where
  | duplicateActionTarget (field : FieldId)
  | targetField (field : FieldId) (cause : ResolveError)
  | nonDateRangeTarget (field : FieldId)
  | repeatableTarget (field : FieldId)
  deriving Repr, DecidableEq

def actionTargets (view : DateRangeComputationRunView ResidualMessage) :
    List FieldId :=
  TemporalErroredComputationRunView.actionTargets view
    (fun computed => computed.targetField)
    (fun computed => computed.targetField)

def applyTo (view : DateRangeComputationRunView ResidualMessage)
    (destination : DateRangeComputationDestination) :
    Except DateRangeComputationRunApplicationError
      DateRangeComputationDestination :=
  TemporalErroredComputationRunView.applyTo view destination
    (fun computed => computed.targetField)
    (fun computed => computed.targetField)
    DateRangeComputationRunApplicationError.duplicateActionTarget
    DateRangeComputationDestination.applyRetainedClear
    (fun current computed => current.applyOutcome computed.targetField
      (.errored computed.attempted computed.cause))
    (fun current computed => current.applyOutcome computed.targetField
      (.accepted computed.value))

/-- Validate one retained action against the nonrepeatable DateRange target boundary represented by this result. -/
def validateActionTarget (model : FlatModel) (target : FieldId) :
    Except DateRangeComputationRunApplicationError Unit :=
  TemporalErroredComputationRunView.validateNonrepeatableActionTarget
    model target (· == .dateRange)
    DateRangeComputationRunApplicationError.targetField
    DateRangeComputationRunApplicationError.nonDateRangeTarget
    DateRangeComputationRunApplicationError.repeatableTarget

/-- Validate every unique DateRange action target before reading the destination projection. -/
def validateActionTargets (model : FlatModel) : List FieldId →
    Except DateRangeComputationRunApplicationError Unit :=
  TemporalErroredComputationRunView.validateNonrepeatableActionTargets
    model (· == .dateRange)
    DateRangeComputationRunApplicationError.targetField
    DateRangeComputationRunApplicationError.nonDateRangeTarget
    DateRangeComputationRunApplicationError.repeatableTarget

/-- Apply one retained nonrepeatable DateRange result to a separately supplied checked destination. The returned function is the exact root DateRange-state projection, not a reconstructed document. The retained result is not model-indexed, so source/destination model compatibility remains a caller precondition. -/
def applyToChecked (view : DateRangeComputationRunView ResidualMessage)
    (destination : CheckedDocument model) :
    Except DateRangeComputationRunApplicationError
      DateRangeComputationDestination :=
  match FieldId.firstDuplicate? view.actionTargets with
  | some duplicate => .error (.duplicateActionTarget duplicate)
  | none => do
      validateActionTargets model view.actionTargets
      view.applyTo destination.sourceDateRangeTargetState

end DateRangeComputationRunView

end A12Kernel
