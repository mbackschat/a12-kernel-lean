import A12Kernel.Semantics.TemporalTarget

/-! # Temporal delta and exact one-target application

This capsule shares only the source-placement mechanism whose meaning agrees for Time, Date, and DateTime. Stored text remains kind-indexed, and each target family retains its own outcome and delta domain. Application preserves exact text and absent versus present-empty placement without reparsing. Document traversal, missing-ancestor creation, repeatable addressing, scheduling, and multi-target application remain separate.
-/

namespace A12Kernel

/-- Prior temporal value used by source-relative delta classification. Empty placement is intentionally not represented here. -/
inductive PriorTemporalTarget (Stored : Type) where
  | empty
  | filled (value : Stored)
  deriving Repr, DecidableEq

/-- Shared source-relative value/clear action for temporal families without a target-error branch. -/
inductive TemporalValueDelta (Stored : Type) where
  | value (stored : Stored)
  | cleared
  deriving Repr, DecidableEq

namespace TemporalValueDelta

/-- Classify one accepted stored temporal value relative to the source. -/
def projectValue [DecidableEq Stored] (value : Stored) :
    PriorTemporalTarget Stored → Option (TemporalValueDelta Stored)
  | .empty => some (.value value)
  | .filled previous =>
      if value = previous then none else some (.value value)

/-- Classify an outcome that stores no value relative to the source. -/
def projectNoValue :
    PriorTemporalTarget Stored → Option (TemporalValueDelta Stored)
  | .empty => none
  | .filled _ => some .cleared

end TemporalValueDelta

/-- Exact state of one scalar temporal target cell. The stored type keeps Date and DateTime values distinct. -/
inductive TemporalTargetState (Stored : Type) where
  | absent
  | presentEmpty
  | presentValue (value : Stored)
  deriving Repr, DecidableEq

namespace TemporalTargetState

/-- Empty a present target in place without creating an absent target. -/
def clearValue :
    TemporalTargetState Stored → TemporalTargetState Stored
  | .absent => .absent
  | .presentEmpty | .presentValue _ => .presentEmpty

/-- Return the exact stored temporal value when this state contains one. -/
def storedValue : TemporalTargetState Stored → Option Stored
  | .presentValue value => some value
  | .absent | .presentEmpty => none

/-- Report whether the target cell exists independently of its stored value. -/
def isPresent : TemporalTargetState Stored → Bool
  | .absent => false
  | .presentEmpty | .presentValue _ => true

/-- Forget placement while retaining the source value needed for delta classification. -/
def toDeltaPrior :
    TemporalTargetState Stored → PriorTemporalTarget Stored
  | .presentValue value => .filled value
  | .absent | .presentEmpty => .empty

end TemporalTargetState

/-- Exact caller-supplied field projection used by scalar temporal whole-result application. -/
abbrev TemporalComputationDestination (Stored : Type) :=
  FieldId → TemporalTargetState Stored

namespace TemporalComputationDestination

/-- Replace one temporal target projection while preserving every other field. -/
def update (destination : TemporalComputationDestination Stored)
    (target : FieldId) (state : TemporalTargetState Stored) :
    TemporalComputationDestination Stored :=
  fun field => if field == target then state else destination field

end TemporalComputationDestination

/-- Time-specific prior target value. -/
abbrev PriorTimeTarget := PriorTemporalTarget StoredTime

/-- Time has the shared value/clear delta domain. -/
abbrev TimeDelta := TemporalValueDelta StoredTime

/-- Exact state of one Time target cell. -/
abbrev TimeTargetState := TemporalTargetState StoredTime

namespace TimeTargetState

/-- Recover the stored Time exactly when the target currently has a nonempty value. -/
def storedValue : TimeTargetState → Option StoredTime :=
  TemporalTargetState.storedValue

end TimeTargetState

namespace TimeTargetOutcome

/-- Project one rich Time outcome relative to exact prior source placement. -/
def projectDelta (outcome : TimeTargetOutcome)
    (prior : PriorTimeTarget) : Option TimeDelta :=
  match outcome with
  | .accepted value => TemporalValueDelta.projectValue value prior
  | .noValue | .poison _ => TemporalValueDelta.projectNoValue prior

/-- Apply one Time outcome without reparsing its stored text. -/
def applyTo : TimeTargetOutcome → TimeTargetState → TimeTargetState
  | .accepted value, _ => .presentValue value
  | .noValue, prior => prior.clearValue
  | .poison _, prior => prior.clearValue

end TimeTargetOutcome

/-- Date-specific prior target value. -/
abbrev PriorFullDateTarget := PriorTemporalTarget StoredDate

/-- Source-relative action for one checked full-Date outcome. Target rejection retains the exact rendered attempt. -/
inductive FullDateDelta where
  | value (stored : StoredDate)
  | cleared
  | errored (attempted : StoredDate) (cause : FullDateTargetError)
  deriving Repr, DecidableEq

namespace FullDateDelta

/-- Classify an accepted stored Date relative to the source value. -/
def projectValue (value : StoredDate) : PriorFullDateTarget → Option FullDateDelta
  | prior =>
      match TemporalValueDelta.projectValue value prior with
      | none => none
      | some (.value stored) => some (.value stored)
      | some .cleared => some .cleared

/-- Classify an outcome that stores no value relative to the source value. -/
def projectNoValue : PriorFullDateTarget → Option FullDateDelta
  | prior =>
      match TemporalValueDelta.projectNoValue prior with
      | none => none
      | some (.value stored) => some (.value stored)
      | some .cleared => some .cleared

end FullDateDelta

namespace FullDateTargetOutcome

/-- Classify one rich target outcome relative to the computation source. Accepted values are change-sensitive; target errors are unconditional; quiet no-value and poison clear only a source-filled target. -/
def projectDelta (outcome : FullDateTargetOutcome)
    (prior : PriorFullDateTarget) : Option FullDateDelta :=
  match outcome with
  | .accepted value => FullDateDelta.projectValue value prior
  | .errored attempted cause => some (.errored attempted cause)
  | .noValue | .poison _ => FullDateDelta.projectNoValue prior

/-- Exact stored value supplied by an accepted outcome, independently of placement. -/
def appliedValue : FullDateTargetOutcome → Option StoredDate
  | .accepted value => some value
  | .noValue | .errored _ _ | .poison _ => none

end FullDateTargetOutcome

/-- Exact state of one full-Date target cell. -/
abbrev FullDateTargetState := TemporalTargetState StoredDate

namespace FullDateTargetState

/-- Date specialization of placement-preserving clearing. -/
def clearValue : FullDateTargetState → FullDateTargetState :=
  TemporalTargetState.clearValue

/-- Date specialization of stored-value projection. -/
def storedValue : FullDateTargetState → Option StoredDate :=
  TemporalTargetState.storedValue

/-- Date specialization of placement presence. -/
def isPresent : FullDateTargetState → Bool :=
  TemporalTargetState.isPresent

/-- Date specialization of source-relative prior projection. -/
def toDeltaPrior :
    FullDateTargetState → PriorFullDateTarget :=
  TemporalTargetState.toDeltaPrior

end FullDateTargetState

namespace FullDateTargetOutcome

/-- Apply one checked full-Date outcome to an exact target cell. Accepted text creates or overwrites the value; every other outcome clears an existing target in place and leaves absence unchanged. -/
def applyTo : FullDateTargetOutcome → FullDateTargetState → FullDateTargetState
  | .accepted value, _ => .presentValue value
  | .noValue, prior => prior.clearValue
  | .errored _ _, prior => prior.clearValue
  | .poison _, prior => prior.clearValue

end FullDateTargetOutcome

/-- DateTime-specific prior target value. -/
abbrev PriorDateTimeTarget := PriorTemporalTarget StoredDateTime

/-- DateTime has exactly the shared value/clear delta domain in this bounded target fragment. -/
abbrev DateTimeDelta := TemporalValueDelta StoredDateTime

/-- Exact state of one DateTime target cell. -/
abbrev DateTimeTargetState := TemporalTargetState StoredDateTime

namespace DateTimeTargetState

/-- DateTime specialization of placement-preserving clearing. -/
def clearValue : DateTimeTargetState → DateTimeTargetState :=
  TemporalTargetState.clearValue

/-- DateTime specialization of stored-value projection. -/
def storedValue : DateTimeTargetState → Option StoredDateTime :=
  TemporalTargetState.storedValue

/-- DateTime specialization of placement presence. -/
def isPresent : DateTimeTargetState → Bool :=
  TemporalTargetState.isPresent

/-- DateTime specialization of source-relative prior projection. -/
def toDeltaPrior :
    DateTimeTargetState → PriorDateTimeTarget :=
  TemporalTargetState.toDeltaPrior

end DateTimeTargetState

namespace DateTimeTargetOutcome

/-- Classify one rich DateTime target outcome relative to the computation source. Accepted text is change-sensitive; quiet no-value and poison clear only a source-filled target. -/
def projectDelta (outcome : DateTimeTargetOutcome)
    (prior : PriorDateTimeTarget) : Option DateTimeDelta :=
  match outcome with
  | .accepted value => TemporalValueDelta.projectValue value prior
  | .noValue | .poison _ => TemporalValueDelta.projectNoValue prior

/-- Exact stored value supplied by an accepted DateTime outcome, independently of placement. -/
def appliedValue : DateTimeTargetOutcome → Option StoredDateTime
  | .accepted value => some value
  | .noValue | .poison _ => none

/-- Apply one checked DateTime outcome to an exact target cell. Accepted text creates or overwrites the value; no-value and poison clear an existing target in place and leave absence unchanged. -/
def applyTo :
    DateTimeTargetOutcome → DateTimeTargetState → DateTimeTargetState
  | .accepted value, _ => .presentValue value
  | .noValue, prior => prior.clearValue
  | .poison _, prior => prior.clearValue

end DateTimeTargetOutcome

end A12Kernel
