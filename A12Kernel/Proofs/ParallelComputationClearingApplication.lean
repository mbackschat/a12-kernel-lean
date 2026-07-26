import A12Kernel.Elaboration.ParallelComputationClearingApplication
import A12Kernel.Proofs.NumericApplication

/-! # Repeatable Number clearing-application laws -/

namespace A12Kernel

@[simp] theorem addressedNumericDestination_update_same
    (destination : AddressedNumericDestination)
    (target : CellAddr) (state : NumericTargetState) :
    destination.update target state target = state := by
  simp [AddressedNumericDestination.update]

/-- One exact clear delegates to the existing one-target state transition. -/
@[simp] theorem addressedNumericDestination_clearAt_same
    (destination : AddressedNumericDestination) (target : CellAddr) :
    destination.clearAt target target =
      (destination target).clearValue := by
  simp [AddressedNumericDestination.clearAt]

/-- One exact clear preserves every other destination address. -/
theorem addressedNumericDestination_clearAt_other
    (destination : AddressedNumericDestination)
    (target other : CellAddr) (different : other ≠ target) :
    destination.clearAt target other = destination other := by
  simp [AddressedNumericDestination.clearAt,
    AddressedNumericDestination.update, different]

/-- Clearing cannot create a target cell at any address. -/
theorem addressedNumericDestination_clearAt_preserves_absent
    (destination : AddressedNumericDestination)
    (target address : CellAddr)
    (absent : destination address = .absent) :
    destination.clearAt target address = .absent := by
  by_cases same : address = target
  · subst target
    simp [absent, NumericTargetState.clearValue]
  · rw [addressedNumericDestination_clearAt_other
      destination target address same, absent]

/-- Repeating the same exact clear has no further effect. -/
theorem addressedNumericDestination_clearAt_idempotent
    (destination : AddressedNumericDestination)
    (target : CellAddr) :
    (destination.clearAt target).clearAt target =
      destination.clearAt target := by
  funext address
  by_cases same : address = target
  · subst target
    cases state : destination address <;>
      simp [AddressedNumericDestination.clearAt,
        AddressedNumericDestination.update,
        NumericTargetState.clearValue, state]
  · simp [AddressedNumericDestination.clearAt,
      AddressedNumericDestination.update, same]

/-- Exact clears commute at any two addresses. -/
theorem addressedNumericDestination_clearAt_comm
    (destination : AddressedNumericDestination)
    (first second : CellAddr) :
    (destination.clearAt first).clearAt second =
      (destination.clearAt second).clearAt first := by
  funext address
  by_cases atFirst : address = first
  · subst first
    by_cases same : address = second
    · subst second
      cases destination address <;> rfl
    · simp [addressedNumericDestination_clearAt_other,
        same, NumericTargetState.clearValue]
  · by_cases atSecond : address = second
    · subst second
      simp [addressedNumericDestination_clearAt_other,
        atFirst, NumericTargetState.clearValue]
    · simp [addressedNumericDestination_clearAt_other,
        atFirst, atSecond]

/-- A singleton clearing view is exactly one addressed clear. -/
theorem parallelNumericClearing_applyTo_singleton
    (view : ParallelNumericClearingView)
    (destination : AddressedNumericDestination) (target : CellAddr)
    (only : view.cleared = [target]) :
    view.applyTo destination = destination.clearAt target := by
  simp [ParallelNumericClearingView.applyTo, only]

/-- Whole-view application preserves every address outside the clearing projection. -/
theorem parallelNumericClearing_applyTo_other
    (view : ParallelNumericClearingView)
    (destination : AddressedNumericDestination) (address : CellAddr)
    (notCleared : address ∉ view.cleared) :
    view.applyTo destination address = destination address := by
  have go : ∀ (targets : List CellAddr)
      (current : AddressedNumericDestination),
      address ∉ targets →
      targets.foldl
        (fun state target => state.clearAt target) current address =
        current address := by
    intro targets
    induction targets with
    | nil =>
        simp
    | cons target remaining ih =>
        intro current missing
        have different : address ≠ target := by
          intro same
          apply missing
          simp [same]
        have absentFromRemaining : address ∉ remaining := by
          intro present
          apply missing
          simp [present]
        simp only [List.foldl_cons]
        rw [ih (current.clearAt target) absentFromRemaining]
        exact addressedNumericDestination_clearAt_other
          current target address different
  exact go view.cleared destination notCleared

/-- Whole-view clearing cannot create an absent destination target. -/
theorem parallelNumericClearing_applyTo_preserves_absent
    (view : ParallelNumericClearingView)
    (destination : AddressedNumericDestination) (address : CellAddr)
    (absent : destination address = .absent) :
    view.applyTo destination address = .absent := by
  have go : ∀ (targets : List CellAddr)
      (current : AddressedNumericDestination),
      current address = .absent →
      targets.foldl
        (fun state target => state.clearAt target) current address =
        .absent := by
    intro targets
    induction targets with
    | nil =>
        simp
    | cons target remaining ih =>
        intro current currentAbsent
        simp only [List.foldl_cons]
        apply ih
        exact addressedNumericDestination_clearAt_preserves_absent
          current target address currentAbsent
  exact go view.cleared destination absent

/-- Extensional clearing views have identical application behavior; list order is not observable. -/
theorem parallelNumericClearing_applyTo_extensional
    (left right : ParallelNumericClearingView)
    (destination : AddressedNumericDestination)
    (same : left.ExtensionalEq right) :
    left.applyTo destination = right.applyTo destination := by
  apply same.foldl_eq'
  intro first _ second _ current
  exact addressedNumericDestination_clearAt_comm
    current first second

end A12Kernel
