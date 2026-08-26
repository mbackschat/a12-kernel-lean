import A12Kernel.Elaboration.TemporalComputationResult

/-! # Shared scalar temporal value/clear application -/

namespace A12Kernel

/-- Structural failure shared by temporal target families whose public actions are only clears and changed values. -/
inductive TemporalValueComputationApplicationError where
  | duplicateActionTarget (field : FieldId)
  deriving Repr, DecidableEq

namespace TemporalComputationApplicationTarget

/-- Validate one exact action target against a family predicate and the shared nonrepeatable application boundary. -/
def validateNonrepeatable
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
def validateAllNonrepeatable
    (model : FlatModel) (acceptsKind : FieldKind → Bool)
    (targetFieldError : FieldId → ResolveError → ApplicationError)
    (wrongKindError repeatableError : FieldId → ApplicationError) :
    List FieldId → Except ApplicationError Unit
  | [] => pure ()
  | target :: remaining => do
      validateNonrepeatable model target acceptsKind
        targetFieldError wrongKindError repeatableError
      validateAllNonrepeatable model acceptsKind
        targetFieldError wrongKindError repeatableError remaining

end TemporalComputationApplicationTarget

namespace TemporalValueComputationRunView

/-- Targets consumed by value/clear application; unchanged successes and residual messages are absent. -/
def actionTargets
    (view : TemporalComputationRunView
      (TemporalComputedInstance kind) Error ResidualMessage) :
    List FieldId :=
  view.cleared ++ view.withChanges.map (·.targetField)

/-- Apply source-classified retained clears before changed values. The two callbacks are deliberately distinct: a retained clear is an action, not a direct no-value outcome re-evaluated against the destination. -/
def applyTo
    (view : TemporalComputationRunView
      (TemporalComputedInstance kind) Error ResidualMessage)
    (destination : Destination)
    (applyRetainedClear : Destination → FieldId → Destination)
    (applyAccepted :
      Destination → FieldId → StoredTemporalText kind → Destination) :
    Except TemporalValueComputationApplicationError Destination :=
  match FieldId.firstDuplicate? (actionTargets view) with
  | some duplicate => .error (.duplicateActionTarget duplicate)
  | none =>
      let afterCleared := view.cleared.foldl
        applyRetainedClear destination
      .ok (view.withChanges.foldl
        (fun current computed =>
          applyAccepted current computed.targetField computed.value) afterCleared)

end TemporalValueComputationRunView

end A12Kernel
