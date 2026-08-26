import A12Kernel.Elaboration.TemporalValueComputationApplication

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
  TemporalComputationApplicationTarget.validateAllNonrepeatable
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
  TemporalComputationApplicationTarget.validateNonrepeatable
    model target (· == .dateRange)
    DateRangeComputationRunApplicationError.targetField
    DateRangeComputationRunApplicationError.nonDateRangeTarget
    DateRangeComputationRunApplicationError.repeatableTarget

/-- Validate every unique DateRange action target before reading the destination projection. -/
def validateActionTargets (model : FlatModel) : List FieldId →
    Except DateRangeComputationRunApplicationError Unit :=
  TemporalComputationApplicationTarget.validateAllNonrepeatable
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
