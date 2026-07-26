import A12Kernel.Elaboration.ParallelComputationClearing

/-! # Repeatable Number clearing application

This capsule applies an already-classified extensional clearing view to an explicitly supplied addressed destination. It clears present cells in place, never creates absent cells or document ancestors, and does not reclassify against the destination. -/

namespace A12Kernel

/-- The exact caller-supplied target-state projection needed by repeatable Number application. -/
abbrev AddressedNumericDestination := CellAddr → NumericTargetState

namespace AddressedNumericDestination

def update (destination : AddressedNumericDestination)
    (target : CellAddr) (state : NumericTargetState) :
    AddressedNumericDestination :=
  fun address => if address == target then state else destination address

/-- Clear one exact address through the existing one-target transition. -/
def clearAt (destination : AddressedNumericDestination)
    (target : CellAddr) : AddressedNumericDestination :=
  destination.update target (destination target).clearValue

end AddressedNumericDestination

namespace ParallelNumericClearingView

/-- Apply every classified clear to the caller-supplied destination. The fold order is internal: exact clears at different addresses commute and repeated identical clears are idempotent. -/
def applyTo (view : ParallelNumericClearingView)
    (destination : AddressedNumericDestination) :
    AddressedNumericDestination :=
  view.cleared.foldl
    (fun current target => current.clearAt target) destination

end ParallelNumericClearingView

end A12Kernel
