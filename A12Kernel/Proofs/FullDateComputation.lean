import A12Kernel.Elaboration.FullDateComputation

/-! # Checked full-Date field-copy laws -/

namespace A12Kernel

/-- A computation-phase empty source remains clean no-value through target execution. -/
theorem fullDateFieldCopy_empty
    (operation : CheckedFullDateFieldCopy model)
    (input : CheckedDocument model)
    (read :
      input.read { field := operation.source.id, path := [] } = .ok cell)
    (empty :
      observeCell .computation cell = .empty) :
    operation.evaluateOutcome input = .ok .noValue := by
  have sourceRead :
      operation.readSource input = .ok .noValue := by
    simp [CheckedFullDateFieldCopy.readSource, read, empty] <;> rfl
  unfold CheckedFullDateFieldCopy.evaluateOutcome
  rw [sourceRead]
  rfl

/-- A reached formal source failure preserves its exact cause and never becomes a target error. -/
theorem fullDateFieldCopy_poison
    (operation : CheckedFullDateFieldCopy model)
    (input : CheckedDocument model)
    (read :
      input.read { field := operation.source.id, path := [] } = .ok cell)
    (poison :
      observeCell .computation cell = .poison cause) :
    operation.evaluateOutcome input = .ok (.poison cause) := by
  have sourceRead :
      operation.readSource input = .ok (.poison cause) := by
    simp [CheckedFullDateFieldCopy.readSource, read, poison] <;> rfl
  unfold CheckedFullDateFieldCopy.evaluateOutcome
  rw [sourceRead]
  rfl

/-- A checked Date source transports its exact instant to the declaration-owned target; source text, decoded parts, and calendar basis cannot replace target policy. -/
theorem fullDateFieldCopy_value
    (operation : CheckedFullDateFieldCopy model)
    (input : CheckedDocument model)
    (read :
      input.read { field := operation.source.id, path := [] } = .ok cell)
    (value :
      observeCell .computation cell =
        .value (.temporal (.date instant parts basis))) :
    operation.evaluateOutcome input =
      (operation.target.evaluate (.value instant)).mapError .target := by
  have sourceRead :
      operation.readSource input = .ok (.value instant) := by
    simp [CheckedFullDateFieldCopy.readSource, read, value] <;> rfl
  unfold CheckedFullDateFieldCopy.evaluateOutcome
  rw [sourceRead]

end A12Kernel
