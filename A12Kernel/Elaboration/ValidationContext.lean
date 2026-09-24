import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Semantics.GroupPresence

/-! # Shared resolved validation context

Checked validation consumers read scalar fields and already-resolved group product states through one phase-specific context. Group-state construction and general document traversal remain outside this boundary.
-/

namespace A12Kernel

/-- Runtime group states are supplied by the checked-document boundary and keyed by resolved group path. Missing state is explicit unavailability. -/
abbrev GroupPresenceContext := GroupPath → Option GroupPresenceState

namespace GroupPresenceContext

/-- Explicitly provide no resolved group slices to a condition known to use only field-backed leaf families. -/
def unavailable : GroupPresenceContext := fun _ => none

/-- Resolve every fixed group operand in declaration order, failing when the checked-document boundary omitted any required state. -/
def resolveAll (context : GroupPresenceContext) :
    List ResolvedGroupReference → Option (List GroupPresenceState)
  | [] => some []
  | reference :: remaining => do
      let state ← context reference.path
      pure (state :: (← context.resolveAll remaining))

end GroupPresenceContext

/-- The Kernel pass an evaluation answers for, `validateFull` or `validatePart`. Group states alone
    cannot tell them apart, because a partial call covering every field reads the same states as a
    full one, yet the filled-group count's error rule differs between them
    (`GroupPresenceState.decidesPartialCount`). -/
inductive ValidationPass where
  | full
  | part
  deriving Repr, DecidableEq

/-- The fixed-only filled-group count this pass answers. -/
def ValidationPass.countFilledGroups : ValidationPass → List GroupPresenceState → FilledGroupCount
  | .full, states => numberOfFilledGroups states
  | .part, states => numberOfFilledGroupsPartial states

/-- The shared checked-validation evaluator keeps field observations and already-resolved group states separate. -/
structure ValidationEvaluationContext where
  fields : FlatContext
  groups : GroupPresenceContext
  pass : ValidationPass := .full

end A12Kernel
