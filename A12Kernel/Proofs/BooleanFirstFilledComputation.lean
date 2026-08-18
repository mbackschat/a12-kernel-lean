import A12Kernel.Elaboration.BooleanFirstFilledComputation

/-! # Direct one-star Boolean `FirstFilledValue` computation laws -/

namespace A12Kernel

/-- An exhausted Boolean source clears rather than manufacturing `false`. -/
theorem firstFilledBoolean_exhausted_noValue :
    evalFirstFilledBoolean [] = .noValue := by
  rfl

/-- `false` is a present Boolean value, not the empty-selection identity. -/
theorem firstFilledBoolean_false_is_value
    (tail : List FirstFilledBooleanCell) :
    evalFirstFilledBoolean (.present false :: tail) =
      .value false := by
  rfl

end A12Kernel
