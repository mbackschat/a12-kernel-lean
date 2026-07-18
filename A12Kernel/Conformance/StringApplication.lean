import A12Kernel.Semantics.StringApplication

/-! # A12Kernel.Conformance.StringApplication — exact one-target String application locks

These examples lock the complete internal transition table. The owning evidence documents state which rows are externally calibrated and which remain pending.
-/

namespace A12Kernel.Conformance.StringApplication

open A12Kernel

private def storedOld : StoredString := ⟨"OLD", by decide⟩
private def storedAbcd : StoredString := ⟨"ABCD", by decide⟩

/- Accepted writes create or replace the target, including the unchanged-value control. -/
example : (StringTargetOutcome.accepted storedAbcd).applyTo .absent =
    .presentValue storedAbcd := by
  rfl

example : (StringTargetOutcome.accepted storedAbcd).applyTo .presentEmpty =
    .presentValue storedAbcd := by
  rfl

example : (StringTargetOutcome.accepted storedAbcd).applyTo (.presentValue storedOld) =
    .presentValue storedAbcd := by
  rfl

example : (StringTargetOutcome.accepted storedAbcd).applyTo (.presentValue storedAbcd) =
    .presentValue storedAbcd := by
  rfl

/- Quiet no-value preserves absence and present-empty placement, and empties a filled target in place. -/
example : StringTargetOutcome.noValue.applyTo .absent = .absent := by
  rfl

example : StringTargetOutcome.noValue.applyTo .presentEmpty = .presentEmpty := by
  rfl

example : StringTargetOutcome.noValue.applyTo (.presentValue storedOld) = .presentEmpty := by
  rfl

/- Target rejection has the same placement effect while retaining a distinct outcome and delta. -/
example : (StringTargetOutcome.errored storedAbcd .tooLong).applyTo .absent = .absent := by
  rfl

example : (StringTargetOutcome.errored storedAbcd .tooLong).applyTo .presentEmpty =
    .presentEmpty := by
  rfl

example : (StringTargetOutcome.errored storedAbcd .tooLong).applyTo
    (.presentValue storedOld) = .presentEmpty := by
  rfl

/- Internal poison clears only an existing target while remaining a distinct outcome. -/
example : (StringTargetOutcome.poison .malformed).applyTo .absent = .absent := by
  rfl

example : (StringTargetOutcome.poison .malformed).applyTo .presentEmpty =
    .presentEmpty := by
  rfl

example : (StringTargetOutcome.poison .malformed).applyTo
    (.presentValue storedOld) = .presentEmpty := by
  rfl

/- Equal delta priors do not determine the exact post-application state. -/
example : StringTargetState.absent.toDeltaPrior =
      StringTargetState.presentEmpty.toDeltaPrior ∧
    StringTargetOutcome.noValue.applyTo .absent ≠
      StringTargetOutcome.noValue.applyTo .presentEmpty := by
  decide

end A12Kernel.Conformance.StringApplication
