import A12Kernel.Elaboration.StringComputationRunResult
import A12Kernel.Semantics.StringApplication

/-! # String-specific whole-run application

This capsule applies an already-classified String result to an explicitly supplied compatible destination. The generic route accepts an exact target-state projection; the checked route validates nonrepeatable String actions against a caller-supplied checked document and returns the same projection rather than reconstructing a document. Application distinguishes source-classified retained clears from direct errored and accepted outcomes and never reclassifies an action against the destination.
-/

namespace A12Kernel

/-- The exact caller-supplied target-state projection needed by one String result target-key domain. -/
abbrev StringComputationDestination (Target : Type := FieldId) :=
  Target → StringTargetState

namespace StringComputationDestination

/-- Replace one target state while preserving every other field projection. -/
def update {Target : Type} [DecidableEq Target]
    (destination : StringComputationDestination Target)
    (target : Target) (state : StringTargetState) :
    StringComputationDestination Target :=
  fun candidate => if candidate = target then state else destination candidate

/-- Specialize the existing one-target transition at one field. -/
def applyOutcome {Target : Type} [DecidableEq Target]
    (destination : StringComputationDestination Target)
    (target : Target) (outcome : StringTargetOutcome) :
    StringComputationDestination Target :=
  destination.update target (outcome.applyTo (destination target))

/-- Apply one source-classified CLEARED action without reclassifying it against the destination. -/
def applyRetainedClear {Target : Type} [DecidableEq Target]
    (destination : StringComputationDestination Target)
    (target : Target) : StringComputationDestination Target :=
  destination.update target (destination target).applyRetainedClear

end StringComputationDestination

/-- Fail-closed errors while applying nonrepeatable String actions to a checked caller destination. The retained result is not model-indexed, so source/destination model compatibility remains an explicit caller precondition. -/
inductive StringComputationDocumentApplicationError where
  | duplicateActionTarget (target : FieldId)
  | targetField (target : FieldId) (cause : ResolveError)
  | nonStringTarget (target : FieldId)
  | repeatableTarget (target : FieldId)
  deriving Repr, DecidableEq

/-- Validate one retained action against the exact root String boundary represented by the existing nonrepeatable run. -/
def validateStringComputationActionTarget
    (model : FlatModel) (target : FieldId) :
    Except StringComputationDocumentApplicationError Unit := do
  let declaration ←
    (model.lookupUniqueId target).mapError (.targetField target)
  match declaration.policy.kind with
  | .string => pure ()
  | _ => throw (.nonStringTarget target)
  if !declaration.repeatableScope.isEmpty then
    throw (.repeatableTarget target)

/-- Validate every unique action target before destination state participates. -/
def validateStringComputationActionTargets
    (model : FlatModel) : List FieldId →
      Except StringComputationDocumentApplicationError Unit
  | [] => pure ()
  | target :: remaining => do
      validateStringComputationActionTarget model target
      validateStringComputationActionTargets model remaining

namespace StringComputationRunView

inductive StringComputationRunApplicationError
    (Target : Type := FieldId) where
  | duplicateActionTarget (target : Target)
  deriving Repr, DecidableEq

/-- The targets consumed by application. Successful unchanged instances and residual messages are deliberately absent. -/
def actionTargets {Target : Type}
    (view : StringComputationRunView ResidualMessage Target) :
    List Target :=
  view.cleared ++ view.withErrors.map (·.targetField) ++
    view.withChanges.map (·.targetField)

/-- Locate the first repeated exact target key in encounter order. -/
def firstDuplicateStringTarget? {Target : Type} [DecidableEq Target] :
    List Target → Option Target
  | [] => none
  | target :: remaining =>
      if target ∈ remaining then some target
      else firstDuplicateStringTarget? remaining

/-- Locate the first malformed repeated action target before destination application begins. -/
def firstDuplicateActionTarget? {Target : Type} [DecidableEq Target]
    (view : StringComputationRunView ResidualMessage Target) :
    Option Target :=
  firstDuplicateStringTarget? view.actionTargets

/-- Apply retained clears, target errors, then source-relative changes. Repeated action targets fail structurally before application. -/
def applyTo {Target : Type} [DecidableEq Target]
    (view : StringComputationRunView ResidualMessage Target)
    (destination : StringComputationDestination Target) :
    Except (StringComputationRunApplicationError Target)
      (StringComputationDestination Target) :=
  match view.firstDuplicateActionTarget? with
  | some duplicate => .error (.duplicateActionTarget duplicate)
  | none =>
      let afterCleared := view.cleared.foldl
        (fun current target => current.applyRetainedClear target) destination
      let afterErrors := view.withErrors.foldl
        (fun current computed => current.applyOutcome computed.targetField
          (.errored computed.attempted computed.cause)) afterCleared
      .ok (view.withChanges.foldl
        (fun current computed => current.applyOutcome computed.targetField
          (.accepted computed.value)) afterErrors)

/-- Apply one retained nonrepeatable String result to a separately supplied checked destination. Duplicate actions fail before target validation; admitted actions delegate exactly to the existing source-classified String fold. The returned function is the exact root String-state projection, not a reconstructed document. -/
def applyToChecked
    (view : StringComputationRunView ResidualMessage FieldId)
    (destination : CheckedDocument model) :
    Except StringComputationDocumentApplicationError
      (StringComputationDestination FieldId) :=
  match view.firstDuplicateActionTarget? with
  | some duplicate => .error (.duplicateActionTarget duplicate)
  | none => do
      validateStringComputationActionTargets model view.actionTargets
      match view.applyTo destination.sourceStringTargetState with
      | .error (.duplicateActionTarget duplicate) =>
          .error (.duplicateActionTarget duplicate)
      | .ok applied => .ok applied

end StringComputationRunView

end A12Kernel
