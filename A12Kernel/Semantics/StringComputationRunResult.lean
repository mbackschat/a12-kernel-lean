import A12Kernel.Document
import A12Kernel.Semantics.StringApplication

/-! # String result classification from supplied outcomes and source state -/

namespace A12Kernel

/-- One successful non-clearing computed String instance at an exact target key. -/
structure StringComputedInstance (Target : Type := FieldId) where
  targetField : Target
  value : StoredString
  deriving Repr, DecidableEq

/-- One computed String instance whose attempted stored value failed target checking. -/
structure StringComputedError (Target : Type := FieldId) where
  targetField : Target
  attempted : StoredString
  cause : StringTargetError
  deriving Repr, DecidableEq

/-- One rich String outcome paired with the exact immutable source-target state needed for public source-relative classification. -/
structure SourcedStringTargetOutcome (Target : Type := FieldId) where
  targetField : Target
  outcome : StringTargetOutcome
  source : StringTargetState
  deriving Repr, DecidableEq

namespace StringTargetOutcome

/-- Whether the runtime produced a nonempty computed-data instance. Target-rejected attempts count; clean no-value and inherited poison do not. -/
def hasComputedInstance : StringTargetOutcome → Bool
  | .accepted _ | .errored _ _ => true
  | .noValue | .invalidNoValue | .poison _ => false

end StringTargetOutcome

/-- The String fragment of the immutable V2 result. The residual payload remains opaque so its later partition/message owner can be threaded without a second message representation. Lists represent extensional collections; their order is not public. -/
structure StringComputationRunView (ResidualMessage : Type)
    (Target : Type := FieldId) where
  private mk ::
  withoutErrors : List (StringComputedInstance Target)
  withChanges : List (StringComputedInstance Target)
  withErrors : List (StringComputedError Target)
  cleared : List Target
  formalErrorsInOperands : List ResidualMessage
  deriving Repr, DecidableEq

namespace StringComputationRunView

/-- Project the successful computed instance, retaining unchanged values. -/
def successfulInstance? {Target : Type} :
    SourcedStringTargetOutcome Target → Option (StringComputedInstance Target)
  | ⟨targetField, .accepted value, _⟩ => some { targetField, value }
  | _ => none

/-- Project only payloadful target rejection. Inherited poison carries no computed-instance message. -/
def computedError? {Target : Type} :
    SourcedStringTargetOutcome Target → Option (StringComputedError Target)
  | ⟨targetField, .errored attempted cause, _⟩ =>
      some { targetField, attempted, cause }
  | _ => none

/-- Compare a successful String value with the immutable computation source, not a later application destination. -/
def changedInstance? {Target : Type}
    (entry : SourcedStringTargetOutcome Target) :
    Option (StringComputedInstance Target) := do
  let computed ← successfulInstance? entry
  if entry.source.computedValue = some computed.value then
    none
  else
    some computed

/-- A source-filled target is publicly cleared exactly when execution produced no computed-data instance. A target-rejected attempt therefore belongs only to `withErrors`, even though later application clears it. -/
def shouldClear {Target : Type}
    (entry : SourcedStringTargetOutcome Target) : Bool :=
  !entry.outcome.hasComputedInstance && entry.source.storedValue.isSome

/-- Build the extensional String result after the caller has attached exact immutable source state to every outcome. -/
def fromSourcedOutcomes {Target : Type}
    (residualMessages : List ResidualMessage)
    (entries : List (SourcedStringTargetOutcome Target)) :
    StringComputationRunView ResidualMessage Target :=
  {
    withoutErrors := entries.filterMap successfulInstance?
    withChanges := entries.filterMap changedInstance?
    withErrors := entries.filterMap computedError?
    cleared := (entries.filter shouldClear).map (·.targetField)
    formalErrorsInOperands := residualMessages
  }

/-- The V2 error predicate observes exactly the computed-instance and residual message channels. Changes and clearing are not errors. -/
def noErrorOccurred {Target : Type}
    (view : StringComputationRunView ResidualMessage Target) : Bool :=
  view.withErrors.isEmpty && view.formalErrorsInOperands.isEmpty

/-- Order-independent equality of the five V2 collections. The private plan order remains an execution fact, not a public result-order guarantee. -/
def ExtensionalEq {Target : Type}
    (left right : StringComputationRunView ResidualMessage Target) : Prop :=
  left.withoutErrors.Perm right.withoutErrors ∧
    left.withChanges.Perm right.withChanges ∧
    left.withErrors.Perm right.withErrors ∧
    left.cleared.Perm right.cleared ∧
    left.formalErrorsInOperands.Perm right.formalErrorsInOperands

end StringComputationRunView

end A12Kernel
