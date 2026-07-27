import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Semantics.TemporalApplication

/-! # Temporal V2 computation result projection

This capsule shares the five extensional result collections used by full Date and DateTime while retaining family-specific outcome and computed-error domains. Each projection consumes supplied rich outcomes, exact immutable source placement, and an independently supplied residual-message channel. Execution, message construction, whole-result application, other temporal kinds, and repeatable pointers remain separate.
-/

namespace A12Kernel

/-- One successful non-clearing temporal instance indexed by its stored scalar kind. -/
structure TemporalComputedInstance (kind : TemporalKind) where
  targetField : FieldId
  value : StoredTemporalText kind
  deriving Repr, DecidableEq

/-- Successful full-Date instance. -/
abbrev FullDateComputedInstance := TemporalComputedInstance .date

/-- Successful DateTime instance. -/
abbrev DateTimeComputedInstance := TemporalComputedInstance .dateTime

/-- One computed full-Date instance whose exact attempted text failed target checking. -/
structure FullDateComputedError where
  targetField : FieldId
  attempted : StoredDate
  cause : FullDateTargetError
  deriving Repr, DecidableEq

/-- The bounded DateTime target has no target-local rejection outcome, so its computed-error collection is uninhabited. -/
inductive DateTimeComputedError
  deriving Repr, DecidableEq

namespace FullDateTargetOutcome

/-- Whether the outcome produced a nonempty computed-data instance. A rejected attempt counts; quiet no-value and poison do not. -/
def hasComputedInstance : FullDateTargetOutcome → Bool
  | .accepted _ | .errored _ _ => true
  | .noValue | .poison _ => false

end FullDateTargetOutcome

namespace DateTimeTargetOutcome

/-- Whether the DateTime outcome produced a nonempty computed-data instance. -/
def hasComputedInstance : DateTimeTargetOutcome → Bool
  | .accepted _ => true
  | .noValue | .poison _ => false

end DateTimeTargetOutcome

namespace CheckedDocument

private def sourceTemporalTargetState (input : CheckedDocument model)
    (field : FieldId) : TemporalTargetState (StoredTemporalText kind) :=
  match input.source.cells.find? fun cell =>
      cell.address == ({ field, path := [] } : CellAddr) with
  | none => .absent
  | some cell =>
      if empty : cell.stored = "" then
        .presentEmpty
      else
        .presentValue { text := cell.stored, nonempty := empty }

/-- Recover exact nonrepeatable source placement and stored Date text without reparsing it. -/
def sourceFullDateTargetState (input : CheckedDocument model)
    (field : FieldId) : FullDateTargetState :=
  sourceTemporalTargetState input field

/-- Recover exact nonrepeatable source placement and stored DateTime text without reparsing it. -/
def sourceDateTimeTargetState (input : CheckedDocument model)
    (field : FieldId) : DateTimeTargetState :=
  sourceTemporalTargetState input field

end CheckedDocument

/-- Five extensional V2 result collections parameterized by the family-specific success and error payloads. List order is not public. -/
structure TemporalComputationRunView
    (ComputedInstance ComputedError ResidualMessage : Type) where
  private mk ::
  withoutErrors : List ComputedInstance
  withChanges : List ComputedInstance
  withErrors : List ComputedError
  cleared : List FieldId
  formalErrorsInOperands : List ResidualMessage
  deriving Repr, DecidableEq

/-- Full-Date specialization of the shared temporal result collections. -/
abbrev FullDateComputationRunView (ResidualMessage : Type) :=
  TemporalComputationRunView
    FullDateComputedInstance FullDateComputedError ResidualMessage

/-- DateTime specialization of the shared temporal result collections. -/
abbrev DateTimeComputationRunView (ResidualMessage : Type) :=
  TemporalComputationRunView
    DateTimeComputedInstance DateTimeComputedError ResidualMessage

namespace TemporalComputationRunView

/-- The public error predicate observes exactly computed-instance errors and residual messages. -/
def noErrorOccurred
    (view : TemporalComputationRunView Instance Error ResidualMessage) :
    Bool :=
  view.withErrors.isEmpty && view.formalErrorsInOperands.isEmpty

/-- Order-independent equality of the five public collections. -/
def ExtensionalEq
    (left right :
      TemporalComputationRunView Instance Error ResidualMessage) : Prop :=
  left.withoutErrors.Perm right.withoutErrors ∧
    left.withChanges.Perm right.withChanges ∧
    left.withErrors.Perm right.withErrors ∧
    left.cleared.Perm right.cleared ∧
    left.formalErrorsInOperands.Perm right.formalErrorsInOperands

end TemporalComputationRunView

namespace FullDateComputationRunView

def successfulInstance? :
    FieldId × FullDateTargetOutcome → Option FullDateComputedInstance
  | (targetField, .accepted value) => some { targetField, value }
  | _ => none

def computedError? :
    FieldId × FullDateTargetOutcome → Option FullDateComputedError
  | (targetField, .errored attempted cause) =>
      some { targetField, attempted, cause }
  | _ => none

def sourceValueChanged (input : CheckedDocument model)
    (computed : FullDateComputedInstance) : Bool :=
  (input.sourceFullDateTargetState computed.targetField).storedValue !=
    some computed.value

/-- A source-filled target is publicly cleared exactly when no computed-data instance was produced. -/
def shouldClear (input : CheckedDocument model)
    (entry : FieldId × FullDateTargetOutcome) : Bool :=
  !entry.2.hasComputedInstance &&
    (input.sourceFullDateTargetState entry.1).storedValue.isSome

/-- Build all five public projections from rich outcomes and an already-classified residual channel. -/
def fromOutcomes (input : CheckedDocument model)
    (residualMessages : List ResidualMessage)
    (outcomes : List (FieldId × FullDateTargetOutcome)) :
    FullDateComputationRunView ResidualMessage :=
  let withoutErrors := outcomes.filterMap successfulInstance?
  {
    withoutErrors
    withChanges := withoutErrors.filter (sourceValueChanged input)
    withErrors := outcomes.filterMap computedError?
    cleared := (outcomes.filter (shouldClear input)).map Prod.fst
    formalErrorsInOperands := residualMessages
  }

/-- The public error predicate observes exactly computed-instance errors and residual messages. -/
def noErrorOccurred (view : FullDateComputationRunView ResidualMessage) : Bool :=
  TemporalComputationRunView.noErrorOccurred view

/-- Order-independent equality of the five public collections. -/
def ExtensionalEq (left right : FullDateComputationRunView ResidualMessage) : Prop :=
  TemporalComputationRunView.ExtensionalEq left right

end FullDateComputationRunView

namespace DateTimeComputationRunView

def successfulInstance? :
    FieldId × DateTimeTargetOutcome → Option DateTimeComputedInstance
  | (targetField, .accepted value) => some { targetField, value }
  | _ => none

def sourceValueChanged (input : CheckedDocument model)
    (computed : DateTimeComputedInstance) : Bool :=
  (input.sourceDateTimeTargetState computed.targetField).storedValue !=
    some computed.value

/-- A source-filled DateTime target is publicly cleared exactly when no computed-data instance was produced. -/
def shouldClear (input : CheckedDocument model)
    (entry : FieldId × DateTimeTargetOutcome) : Bool :=
  !entry.2.hasComputedInstance &&
    (input.sourceDateTimeTargetState entry.1).storedValue.isSome

/-- Build the five public DateTime projections from rich outcomes and an already-classified residual channel. The target-local error collection is empty by construction. -/
def fromOutcomes (input : CheckedDocument model)
    (residualMessages : List ResidualMessage)
    (outcomes : List (FieldId × DateTimeTargetOutcome)) :
    DateTimeComputationRunView ResidualMessage :=
  let withoutErrors := outcomes.filterMap successfulInstance?
  {
    withoutErrors
    withChanges := withoutErrors.filter (sourceValueChanged input)
    withErrors := []
    cleared := (outcomes.filter (shouldClear input)).map Prod.fst
    formalErrorsInOperands := residualMessages
  }

/-- The bounded DateTime result reports an error exactly when the supplied residual channel is nonempty. -/
def noErrorOccurred
    (view : DateTimeComputationRunView ResidualMessage) : Bool :=
  TemporalComputationRunView.noErrorOccurred view

/-- Order-independent equality of the five DateTime collections. -/
def ExtensionalEq
    (left right : DateTimeComputationRunView ResidualMessage) : Prop :=
  TemporalComputationRunView.ExtensionalEq left right

end DateTimeComputationRunView

end A12Kernel
