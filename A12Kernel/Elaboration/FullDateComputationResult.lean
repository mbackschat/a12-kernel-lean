import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Semantics.TemporalApplication

/-! # Full-Date V2 computation result projection

This capsule projects supplied full-Date target outcomes against one immutable computation source. It preserves successful unchanged values, the source-relative changed subset, payloadful target errors, source-filled clearing, and an independently supplied residual-message channel. Date execution, message construction, application, other temporal kinds, and repeatable pointers remain separate.
-/

namespace A12Kernel

/-- One successful non-clearing computed full-Date instance. -/
structure FullDateComputedInstance where
  targetField : FieldId
  value : StoredDate
  deriving Repr, DecidableEq

/-- One computed full-Date instance whose exact attempted text failed target checking. -/
structure FullDateComputedError where
  targetField : FieldId
  attempted : StoredDate
  cause : FullDateTargetError
  deriving Repr, DecidableEq

namespace FullDateTargetOutcome

/-- Whether the outcome produced a nonempty computed-data instance. A rejected attempt counts; quiet no-value and poison do not. -/
def hasComputedInstance : FullDateTargetOutcome → Bool
  | .accepted _ | .errored _ _ => true
  | .noValue | .poison _ => false

end FullDateTargetOutcome

namespace CheckedDocument

/-- Recover exact nonrepeatable source placement and stored Date text without reparsing it. -/
def sourceFullDateTargetState (input : CheckedDocument model)
    (field : FieldId) : FullDateTargetState :=
  match input.source.cells.find? fun cell =>
      cell.address == ({ field, path := [] } : CellAddr) with
  | none => .absent
  | some cell =>
      if empty : cell.stored = "" then
        .presentEmpty
      else
        .presentValue { text := cell.stored, nonempty := empty }

end CheckedDocument

/-- The full-Date fragment of the immutable V2 result. Collections are extensional; list order is not public. -/
structure FullDateComputationRunView (ResidualMessage : Type) where
  private mk ::
  withoutErrors : List FullDateComputedInstance
  withChanges : List FullDateComputedInstance
  withErrors : List FullDateComputedError
  cleared : List FieldId
  formalErrorsInOperands : List ResidualMessage
  deriving Repr, DecidableEq

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
  view.withErrors.isEmpty && view.formalErrorsInOperands.isEmpty

/-- Order-independent equality of the five public collections. -/
def ExtensionalEq (left right : FullDateComputationRunView ResidualMessage) : Prop :=
  left.withoutErrors.Perm right.withoutErrors ∧
    left.withChanges.Perm right.withChanges ∧
    left.withErrors.Perm right.withErrors ∧
    left.cleared.Perm right.cleared ∧
    left.formalErrorsInOperands.Perm right.formalErrorsInOperands

end FullDateComputationRunView

end A12Kernel
