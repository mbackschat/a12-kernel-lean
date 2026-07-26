import A12Kernel.Elaboration.NumericComputation.Run
import A12Kernel.Elaboration.NumericComputation.SourceTarget

/-! # Number-specific V2 computation result projection

This capsule projects a successful checked scalar Number run against its immutable source document. It preserves successful unchanged values, the typed source-relative changed subset, payloadful target errors, source-filled clearing, and an independently supplied residual-message channel. Missing typed Number source identity is structural. Residual-message construction, application, heterogeneous runs, repeatable pointers, and validation remain separate. -/

namespace A12Kernel

/-- One successful non-clearing computed Number instance. -/
structure NumericComputedInstance where
  targetField : FieldId
  value : StoredNumber
  deriving Repr, DecidableEq

/-- One computed Number instance whose attempted stored value failed target checking. -/
structure NumericComputedError where
  targetField : FieldId
  attempted : StoredNumber
  cause : NumericTargetError
  deriving Repr, DecidableEq

/-- One rich run outcome paired with its exact immutable source-target state. This is the minimal input needed for source-relative public classification. -/
structure SourcedNumericTargetOutcome where
  targetField : FieldId
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
structure NumericComputationRunView (ResidualMessage : Type) where
  private mk ::
  withoutErrors : List NumericComputedInstance
  withChanges : List NumericComputedInstance
  withErrors : List NumericComputedError
  cleared : List FieldId
  formalErrorsInOperands : List ResidualMessage
  deriving Repr, DecidableEq

namespace NumericComputationRunView

def successfulInstance? :
    SourcedNumericTargetOutcome → Option NumericComputedInstance
  | ⟨targetField, .accepted value, _⟩ => some ⟨targetField, value⟩
  | _ => none

def changedInstance? (entry : SourcedNumericTargetOutcome) :
    Option NumericComputedInstance := do
  let computed ← successfulInstance? entry
  if entry.source.sourceIdentity == some (.decimal computed.value) then
    none
  else some computed

def computedError? :
    SourcedNumericTargetOutcome → Option NumericComputedError
  | ⟨targetField, .rejected attempted cause, _⟩ =>
      some ⟨targetField, attempted, cause⟩
  | _ => none

/-- A source-filled target is publicly cleared exactly when execution produced no computed-data instance. -/
def shouldClear (entry : SourcedNumericTargetOutcome) : Bool :=
  !entry.outcome.hasComputedInstance && entry.source.sourceIdentity.isSome

def fromSourceOutcomes (residualMessages : List ResidualMessage)
    (entries : List SourcedNumericTargetOutcome) :
    NumericComputationRunView ResidualMessage :=
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
def noErrorOccurred (view : NumericComputationRunView ResidualMessage) : Bool :=
  view.withErrors.isEmpty && view.formalErrorsInOperands.isEmpty

def ExtensionalEq (left right : NumericComputationRunView ResidualMessage) : Prop :=
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
