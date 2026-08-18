import A12Kernel.Elaboration.CustomFirstFilledComputation

/-! # Direct one-star Custom `FirstFilledValue` computation laws -/

namespace A12Kernel

/-- A clean prepared Custom String remains the exact token consumed by the shared first-filled scan. -/
theorem customFirstFilledCellAt_value (value : String) :
    customFirstFilledCellAt {
      rawPresent := true, parsed := some (.str value), findings := []
    } = .present value := by
  rfl

/-- A registered Custom rejection retains its exact cause at the computation adapter. -/
theorem customFirstFilledCellAt_registeredRejection
    (value : String) (rejection : RegisteredCustomRejection) :
    customFirstFilledCellAt {
      rawPresent := true
      parsed := some (.str value)
      findings := [.registeredCustomValidation rejection]
    } = .unknown (.registeredCustomValidation rejection) := by
  rfl

end A12Kernel
