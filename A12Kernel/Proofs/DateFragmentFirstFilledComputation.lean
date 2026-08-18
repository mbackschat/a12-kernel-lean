import A12Kernel.Elaboration.DateFragmentFirstFilledComputation

/-! # Direct one-star DateFragment `FirstFilledValue` computation laws -/

namespace A12Kernel

/-- A clean checked DateFragment value retains the token presented to the bounded first-filled adapter. -/
theorem dateFragmentFirstFilledCellAt_value
    (addressed : CheckedAddressedCell) (date : DateValue) (token : String)
    (observed : observeCell .computation addressed.cell =
      .value (.temporal (.date date)))
    (stored : addressed.stored = some token) :
    dateFragmentFirstFilledCellAt addressed = .present token := by
  simp [dateFragmentFirstFilledCellAt, observed, stored]

/-- A reached formal rejection retains its exact cause at the DateFragment computation adapter. -/
theorem dateFragmentFirstFilledCellAt_poison
    (addressed : CheckedAddressedCell) (cause : FormalCause)
    (observed : observeCell .computation addressed.cell = .poison cause) :
    dateFragmentFirstFilledCellAt addressed = .unknown cause := by
  simp [dateFragmentFirstFilledCellAt, observed]

end A12Kernel
