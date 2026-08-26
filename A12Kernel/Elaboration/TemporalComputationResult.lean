import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Semantics.TemporalApplication

/-! # Temporal V2 computation result projection

This capsule shares the five extensional result collections used by scalar temporal targets while retaining family-specific outcome and computed-error domains. Each projection consumes supplied rich outcomes, exact immutable source placement, and an independently supplied residual-message channel. Execution, message construction, whole-result application, and repeatable pointers remain separate.
-/

namespace A12Kernel

/-- One successful non-clearing temporal instance indexed by its stored scalar kind and exact target-key domain. -/
structure TemporalComputedInstance (kind : TemporalKind)
    (Target : Type := FieldId) where
  targetField : Target
  value : StoredTemporalText kind
  deriving Repr, DecidableEq

/-- Successful Time instance over an exact caller-selected target-key domain. -/
abbrev TimeComputedInstance (Target : Type := FieldId) :=
  TemporalComputedInstance .time Target

/-- Successful full-Date instance. -/
abbrev FullDateComputedInstance (Target : Type := FieldId) :=
  TemporalComputedInstance .date Target

/-- Successful DateTime instance. -/
abbrev DateTimeComputedInstance :=
  TemporalComputedInstance .dateTime FieldId

/-- One computed full-Date instance whose exact attempted text failed target checking. -/
structure FullDateComputedError (Target : Type := FieldId) where
  targetField : Target
  attempted : StoredDate
  cause : FullDateTargetError
  deriving Repr, DecidableEq

/-- One successful DateRange instance retaining its exact target-owned spelling. -/
structure DateRangeComputedInstance where
  targetField : FieldId
  value : StoredDateRange
  deriving Repr, DecidableEq

/-- One DateRange instance whose exact rendered attempt failed target checking. -/
structure DateRangeComputedError where
  targetField : FieldId
  attempted : StoredDateRange
  cause : DateRangeTargetError
  deriving Repr, DecidableEq

/-- The bounded DateTime target has no target-local rejection outcome, so its computed-error collection is uninhabited. -/
inductive DateTimeComputedError
  deriving Repr, DecidableEq

/-- The admitted Time target has no target-local rejection outcome. -/
inductive TimeComputedError
  deriving Repr, DecidableEq

namespace TimeTargetOutcome

/-- Whether the Time outcome produced a nonempty computed-data instance. -/
def hasComputedInstance : TimeTargetOutcome → Bool
  | .accepted _ => true
  | .noValue | .poison _ => false

end TimeTargetOutcome

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

namespace DateRangeTargetOutcome

/-- Whether the DateRange outcome produced a computed-data instance. A rejected attempt counts; quiet no-value and poison do not. -/
def hasComputedInstance : DateRangeTargetOutcome → Bool
  | .accepted _ | .errored _ _ => true
  | .noValue | .poison _ => false

end DateRangeTargetOutcome

namespace CheckedDocument

/-- Recover exact addressed source placement and construct a family-owned stored identity only for nonempty text. -/
def sourceNonemptyStoredTargetStateAt (input : CheckedDocument model)
    (address : CellAddr)
    (makeStored : (text : String) → text ≠ "" → Stored) :
    TemporalTargetState Stored :=
  match input.source.cells.find? fun cell =>
      cell.address == address with
  | none => .absent
  | some cell =>
      if empty : cell.stored = "" then
        .presentEmpty
      else
        .presentValue (makeStored cell.stored empty)

/-- Nonrepeatable compatibility projection through the exact addressed owner. -/
def sourceNonemptyStoredTargetState (input : CheckedDocument model)
    (field : FieldId) (makeStored : (text : String) → text ≠ "" → Stored) :
    TemporalTargetState Stored :=
  sourceNonemptyStoredTargetStateAt input { field, path := [] } makeStored

/-- Recover exact addressed source placement and opaque stored temporal text at one kind-indexed target. -/
def sourceTemporalTargetStateAt (input : CheckedDocument model)
    (address : CellAddr) : TemporalTargetState (StoredTemporalText kind) :=
  sourceNonemptyStoredTargetStateAt input address fun text nonempty =>
    { text, nonempty }

/-- Recover exact nonrepeatable source placement and opaque stored temporal text at one kind-indexed target. -/
def sourceTemporalTargetState (input : CheckedDocument model)
    (field : FieldId) : TemporalTargetState (StoredTemporalText kind) :=
  sourceTemporalTargetStateAt input { field, path := [] }

/-- Recover exact addressed source placement and stored Date text without reparsing it. -/
def sourceFullDateTargetStateAt (input : CheckedDocument model)
    (address : CellAddr) : FullDateTargetState :=
  sourceTemporalTargetStateAt input address

/-- Recover exact nonrepeatable source placement and stored Date text without reparsing it. -/
def sourceFullDateTargetState (input : CheckedDocument model)
    (field : FieldId) : FullDateTargetState :=
  sourceFullDateTargetStateAt input { field, path := [] }

/-- Recover exact addressed source placement and opaque stored Time text. -/
def sourceTimeTargetStateAt (input : CheckedDocument model)
    (address : CellAddr) : TimeTargetState :=
  sourceTemporalTargetStateAt input address

/-- Recover exact nonrepeatable source placement and opaque stored Time text. -/
def sourceTimeTargetState (input : CheckedDocument model)
    (field : FieldId) : TimeTargetState :=
  sourceTimeTargetStateAt input { field, path := [] }

/-- Recover exact nonrepeatable source placement and stored DateTime text without reparsing it. -/
def sourceDateTimeTargetState (input : CheckedDocument model)
    (field : FieldId) : DateTimeTargetState :=
  sourceTemporalTargetState input field

/-- Recover exact nonrepeatable source placement and stored DateRange text without reparsing it. -/
def sourceDateRangeTargetState (input : CheckedDocument model)
    (field : FieldId) : TemporalTargetState StoredDateRange :=
  sourceNonemptyStoredTargetState input field fun text nonempty =>
    { text, nonempty }

end CheckedDocument

/-- Five extensional V2 result collections parameterized by the family-specific success and error payloads. List order is not public. -/
structure TemporalComputationRunView
    (ComputedInstance ComputedError ResidualMessage : Type)
    (Target : Type := FieldId) where
  private mk ::
  withoutErrors : List ComputedInstance
  withChanges : List ComputedInstance
  withErrors : List ComputedError
  cleared : List Target
  formalErrorsInOperands : List ResidualMessage
  deriving Repr, DecidableEq

/-- Time specialization of the shared temporal result collections over an exact caller-selected target-key domain. -/
abbrev TimeComputationRunView (ResidualMessage : Type)
    (Target : Type := FieldId) :=
  TemporalComputationRunView
    (TimeComputedInstance Target) TimeComputedError ResidualMessage Target

/-- Full-Date specialization of the shared temporal result collections. -/
abbrev FullDateComputationRunView (ResidualMessage : Type)
    (Target : Type := FieldId) :=
  TemporalComputationRunView
    (FullDateComputedInstance Target) (FullDateComputedError Target)
    ResidualMessage Target

/-- DateTime specialization of the shared temporal result collections. -/
abbrev DateTimeComputationRunView (ResidualMessage : Type) :=
  TemporalComputationRunView
    DateTimeComputedInstance DateTimeComputedError ResidualMessage FieldId

/-- DateRange specialization of the shared five result collections. -/
abbrev DateRangeComputationRunView (ResidualMessage : Type) :=
  TemporalComputationRunView
    DateRangeComputedInstance DateRangeComputedError ResidualMessage FieldId

namespace TemporalComputationRunView

/-- The public error predicate observes exactly computed-instance errors and residual messages. -/
def noErrorOccurred
    (view : TemporalComputationRunView Instance Error ResidualMessage Target) :
    Bool :=
  view.withErrors.isEmpty && view.formalErrorsInOperands.isEmpty

/-- Order-independent equality of the five public collections. -/
def ExtensionalEq
    (left right :
      TemporalComputationRunView Instance Error ResidualMessage Target) : Prop :=
  left.withoutErrors.Perm right.withoutErrors ∧
    left.withChanges.Perm right.withChanges ∧
    left.withErrors.Perm right.withErrors ∧
    left.cleared.Perm right.cleared ∧
    left.formalErrorsInOperands.Perm right.formalErrorsInOperands

/-- Shared value/clear projection for target families with no target-local error branch. -/
def fromValueOutcomes {Target : Type}
    (successfulInstance? :
      Target × Outcome → Option (TemporalComputedInstance kind Target))
    (sourceValueChanged : TemporalComputedInstance kind Target → Bool)
    (shouldClear : Target × Outcome → Bool)
    (residualMessages : List ResidualMessage)
    (outcomes : List (Target × Outcome)) :
    TemporalComputationRunView
      (TemporalComputedInstance kind Target) Error ResidualMessage Target :=
  let withoutErrors := outcomes.filterMap successfulInstance?
  {
    withoutErrors
    withChanges := withoutErrors.filter sourceValueChanged
    withErrors := []
    cleared := (outcomes.filter shouldClear).map Prod.fst
    formalErrorsInOperands := residualMessages
  }

/-- Shared five-channel projection for temporal families whose rich outcome distinguishes accepted values from target-rejected attempts. -/
def fromErrorOutcomes {Target : Type}
    (successfulInstance? : Target × Outcome → Option ComputedInstance)
    (computedError? : Target × Outcome → Option ComputedError)
    (sourceValueChanged : ComputedInstance → Bool)
    (shouldClear : Target × Outcome → Bool)
    (residualMessages : List ResidualMessage)
    (outcomes : List (Target × Outcome)) :
    TemporalComputationRunView ComputedInstance ComputedError ResidualMessage
      Target :=
  let withoutErrors := outcomes.filterMap successfulInstance?
  {
    withoutErrors
    withChanges := withoutErrors.filter sourceValueChanged
    withErrors := outcomes.filterMap computedError?
    cleared := (outcomes.filter shouldClear).map Prod.fst
    formalErrorsInOperands := residualMessages
  }

end TemporalComputationRunView

namespace TimeComputationRunView

/-- Project one accepted Time outcome into a computed instance. -/
def successfulInstance? {Target : Type} :
    Target × TimeTargetOutcome → Option (TimeComputedInstance Target)
  | (targetField, .accepted value) => some { targetField, value }
  | _ => none

/-- Kernel 30.8.1 reports every clean computed Time in the changed subset, including a clock text equal to the source. The causal implementation detail is deliberately not modeled. -/
def reportsChanged (_computed : TimeComputedInstance Target) : Bool :=
  true

/-- A source-filled Time target is cleared exactly when no computed-data instance was produced. -/
def shouldClearAt (sourceState : Target → TimeTargetState)
    (entry : Target × TimeTargetOutcome) : Bool :=
  !entry.2.hasComputedInstance &&
    (sourceState entry.1).storedValue.isSome

/-- Nonrepeatable compatibility specialization of exact-key clearing classification. -/
def shouldClear (input : CheckedDocument model)
    (entry : FieldId × TimeTargetOutcome) : Bool :=
  shouldClearAt input.sourceTimeTargetState entry

/-- Build the five public Time projections over an exact caller-selected target-key domain and immutable source-state projection. -/
def fromOutcomesAt (sourceState : Target → TimeTargetState)
    (residualMessages : List ResidualMessage)
    (outcomes : List (Target × TimeTargetOutcome)) :
    TimeComputationRunView ResidualMessage Target :=
  TemporalComputationRunView.fromValueOutcomes
    successfulInstance? reportsChanged (shouldClearAt sourceState)
    residualMessages outcomes

/-- Build the five public scalar Time projections from rich outcomes and an already-classified residual channel. -/
def fromOutcomes (input : CheckedDocument model)
    (residualMessages : List ResidualMessage)
    (outcomes : List (FieldId × TimeTargetOutcome)) :
    TimeComputationRunView ResidualMessage :=
  fromOutcomesAt input.sourceTimeTargetState residualMessages outcomes

/-- Time reports an error exactly when the supplied residual channel is nonempty. -/
def noErrorOccurred
    (view : TimeComputationRunView ResidualMessage Target) : Bool :=
  TemporalComputationRunView.noErrorOccurred view

end TimeComputationRunView

namespace FullDateComputationRunView

def successfulInstance? {Target : Type} :
    Target × FullDateTargetOutcome → Option (FullDateComputedInstance Target)
  | (targetField, .accepted value) => some { targetField, value }
  | _ => none

def computedError? {Target : Type} :
    Target × FullDateTargetOutcome → Option (FullDateComputedError Target)
  | (targetField, .errored attempted cause) =>
      some { targetField, attempted, cause }
  | _ => none

def sourceValueChangedAt (sourceState : Target → FullDateTargetState)
    (computed : FullDateComputedInstance Target) : Bool :=
  (sourceState computed.targetField).storedValue !=
    some computed.value

/-- Nonrepeatable compatibility specialization of exact-key source-relative change classification. -/
def sourceValueChanged (input : CheckedDocument model)
    (computed : FullDateComputedInstance) : Bool :=
  sourceValueChangedAt input.sourceFullDateTargetState computed

/-- A source-filled target is publicly cleared exactly when no computed-data instance was produced. -/
def shouldClearAt (sourceState : Target → FullDateTargetState)
    (entry : Target × FullDateTargetOutcome) : Bool :=
  !entry.2.hasComputedInstance &&
    (sourceState entry.1).storedValue.isSome

/-- Nonrepeatable compatibility specialization of exact-key clearing classification. -/
def shouldClear (input : CheckedDocument model)
    (entry : FieldId × FullDateTargetOutcome) : Bool :=
  shouldClearAt input.sourceFullDateTargetState entry

/-- Build all five FullDate projections over an exact caller-selected target-key domain and immutable source-state projection. -/
def fromOutcomesAt (sourceState : Target → FullDateTargetState)
    (residualMessages : List ResidualMessage)
    (outcomes : List (Target × FullDateTargetOutcome)) :
    FullDateComputationRunView ResidualMessage Target :=
  TemporalComputationRunView.fromErrorOutcomes successfulInstance?
    computedError? (sourceValueChangedAt sourceState) (shouldClearAt sourceState)
    residualMessages outcomes

/-- Build all five public projections from rich outcomes and an already-classified residual channel. -/
def fromOutcomes (input : CheckedDocument model)
    (residualMessages : List ResidualMessage)
    (outcomes : List (FieldId × FullDateTargetOutcome)) :
    FullDateComputationRunView ResidualMessage :=
  fromOutcomesAt input.sourceFullDateTargetState residualMessages outcomes

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
  TemporalComputationRunView.fromValueOutcomes
    successfulInstance? (sourceValueChanged input) (shouldClear input)
    residualMessages outcomes

/-- The bounded DateTime result reports an error exactly when the supplied residual channel is nonempty. -/
def noErrorOccurred
    (view : DateTimeComputationRunView ResidualMessage) : Bool :=
  TemporalComputationRunView.noErrorOccurred view

/-- Order-independent equality of the five DateTime collections. -/
def ExtensionalEq
    (left right : DateTimeComputationRunView ResidualMessage) : Prop :=
  TemporalComputationRunView.ExtensionalEq left right

end DateTimeComputationRunView

namespace DateRangeComputationRunView

def successfulInstance? :
    FieldId × DateRangeTargetOutcome → Option DateRangeComputedInstance
  | (targetField, .accepted value) => some { targetField, value }
  | _ => none

def computedError? :
    FieldId × DateRangeTargetOutcome → Option DateRangeComputedError
  | (targetField, .errored attempted cause) =>
      some { targetField, attempted, cause }
  | _ => none

def sourceValueChanged (input : CheckedDocument model)
    (computed : DateRangeComputedInstance) : Bool :=
  (input.sourceDateRangeTargetState computed.targetField).storedValue !=
    some computed.value

def shouldClear (input : CheckedDocument model)
    (entry : FieldId × DateRangeTargetOutcome) : Bool :=
  !entry.2.hasComputedInstance &&
    (input.sourceDateRangeTargetState entry.1).storedValue.isSome

/-- Build all five public DateRange projections from rich outcomes and an independently classified residual channel. -/
def fromOutcomes (input : CheckedDocument model)
    (residualMessages : List ResidualMessage)
    (outcomes : List (FieldId × DateRangeTargetOutcome)) :
    DateRangeComputationRunView ResidualMessage :=
  TemporalComputationRunView.fromErrorOutcomes successfulInstance?
    computedError? (sourceValueChanged input) (shouldClear input)
    residualMessages outcomes

def noErrorOccurred
    (view : DateRangeComputationRunView ResidualMessage) : Bool :=
  TemporalComputationRunView.noErrorOccurred view

def ExtensionalEq
    (left right : DateRangeComputationRunView ResidualMessage) : Prop :=
  TemporalComputationRunView.ExtensionalEq left right

end DateRangeComputationRunView

end A12Kernel
