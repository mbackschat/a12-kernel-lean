import A12Kernel.Elaboration.NumericComputation.Run
import A12Kernel.Elaboration.NumericComputation.SourceTarget

/-! # Number-specific V2 computation result projection

This capsule classifies rich Number outcomes paired with their immutable source state. The classification is shared by scalar field IDs and exact repeatable addresses; attaching scalar outcomes to source state remains a checked-document operation below. It preserves successful unchanged values, the typed source-relative changed subset, payloadful target errors, source-filled clearing, and an independently supplied residual-message channel. Missing typed Number source identity is structural. Residual-message construction, application, and validation remain separate. -/

namespace A12Kernel

/-- One successful non-clearing computed Number instance at an exact target key. -/
structure NumericComputedInstance (Target : Type := FieldId) where
  targetField : Target
  value : StoredNumber
  deriving Repr, DecidableEq

/-- One computed Number instance whose attempted stored value failed target checking. -/
structure NumericComputedError (Target : Type := FieldId) where
  targetField : Target
  attempted : StoredNumber
  cause : NumericTargetError
  deriving Repr, DecidableEq

/-- One rich run outcome paired with its exact immutable source-target state. This is the minimal input needed for source-relative public classification. -/
structure SourcedNumericTargetOutcome (Target : Type := FieldId) where
  targetField : Target
  outcome : NumericTargetOutcome
  source : NumericTargetState
  deriving Repr, DecidableEq

namespace NumericTargetOutcome

/-- Whether the runtime produced a computed-data instance. A target-rejected attempt counts; clean no-value, local invalidity, and inherited poison do not. -/
def hasComputedInstance : NumericTargetOutcome → Bool
  | .accepted _ | .rejected _ _ => true
  | .noValue | .invalidNoValue _ | .inheritedPoison _ => false

end NumericTargetOutcome

/-- The Number fragment of the immutable V2 result. Lists represent extensional collections; their order is not public. -/
structure NumericComputationRunView (ResidualMessage : Type)
    (Target : Type := FieldId) where
  private mk ::
  withoutErrors : List (NumericComputedInstance Target)
  withChanges : List (NumericComputedInstance Target)
  withErrors : List (NumericComputedError Target)
  cleared : List Target
  formalErrorsInOperands : List ResidualMessage
  deriving Repr, DecidableEq

namespace NumericComputationRunView

def successfulInstance? {Target : Type} :
    SourcedNumericTargetOutcome Target → Option (NumericComputedInstance Target)
  | ⟨targetField, .accepted value, _⟩ => some ⟨targetField, value⟩
  | _ => none

def changedInstance? {Target : Type}
    (entry : SourcedNumericTargetOutcome Target) :
    Option (NumericComputedInstance Target) := do
  let computed ← successfulInstance? entry
  if entry.source.sourceIdentity == some (.decimal computed.value) then
    none
  else some computed

def computedError? {Target : Type} :
    SourcedNumericTargetOutcome Target → Option (NumericComputedError Target)
  | ⟨targetField, .rejected attempted cause, _⟩ =>
      some ⟨targetField, attempted, cause⟩
  | _ => none

/-- A source-filled target is publicly cleared exactly when execution produced no computed-data instance. -/
def shouldClear {Target : Type}
    (entry : SourcedNumericTargetOutcome Target) : Bool :=
  !entry.outcome.hasComputedInstance && entry.source.sourceIdentity.isSome

def fromSourceOutcomes {Target : Type}
    (residualMessages : List ResidualMessage)
    (entries : List (SourcedNumericTargetOutcome Target)) :
    NumericComputationRunView ResidualMessage Target :=
  {
    withoutErrors := entries.filterMap successfulInstance?
    withChanges := entries.filterMap changedInstance?
    withErrors := entries.filterMap computedError?
    cleared := (entries.filter shouldClear).map (·.targetField)
    formalErrorsInOperands := residualMessages
  }

/-- Attach immutable source state to each rich run outcome, then build the public projection. -/
def fromOutcomes (input : CheckedDocument model)
    (residualMessages : List ResidualMessage)
    (outcomes : List (FieldId × NumericTargetOutcome)) :
    Except NumericSourceTargetError (NumericComputationRunView ResidualMessage) := do
  let entries ← outcomes.mapM fun (targetField, outcome) => do
    let source ← input.numericTargetState targetField
    pure { targetField, outcome, source }
  pure (fromSourceOutcomes residualMessages entries)

/-- The V2 error predicate observes exactly the computed-instance and residual-message channels. -/
def noErrorOccurred {Target : Type}
    (view : NumericComputationRunView ResidualMessage Target) : Bool :=
  view.withErrors.isEmpty && view.formalErrorsInOperands.isEmpty

def ExtensionalEq {Target : Type}
    (left right : NumericComputationRunView ResidualMessage Target) : Prop :=
  left.withoutErrors.Perm right.withoutErrors ∧
    left.withChanges.Perm right.withChanges ∧
    left.withErrors.Perm right.withErrors ∧
    left.cleared.Perm right.cleared ∧
    left.formalErrorsInOperands.Perm right.formalErrorsInOperands

end NumericComputationRunView

inductive NumericComputationRunResultFault where
  | execution (cause : NumericComputationRunFault)
  | sourceTarget (cause : NumericSourceTargetError)
  deriving Repr, DecidableEq

namespace CheckedNumericComputationRun

/-- Execute the checked run and classify its outcomes relative to that same immutable source document. -/
def executeResult (run : CheckedNumericComputationRun model)
    (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except NumericComputationRunResultFault
      (NumericComputationRunView ResidualMessage) := do
  let outcomes ← (run.execute input).mapError .execution
  (NumericComputationRunView.fromOutcomes input residualMessages outcomes).mapError
    .sourceTarget

end CheckedNumericComputationRun

end A12Kernel
