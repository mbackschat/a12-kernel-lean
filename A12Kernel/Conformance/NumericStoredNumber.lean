import A12Kernel.Semantics.NumericStoredNumber

/-! # Stored Number representation locks -/

namespace A12Kernel.Conformance.NumericStoredNumber

open A12Kernel

private def stored (unscaled : Int) (scale : Nat) : StoredNumber :=
  { unscaled, scale }

/- Conversion keeps the target's declared minimum stored scale. -/
example : StoredNumber.fromComputed 10 2 =
    (0, stored 1000 2) := by
  native_decide

example : StoredNumber.fromComputed (11 / 2) 2 =
    (1, stored 550 2) := by
  native_decide

/- Normalized rendering covers whole, leading-fractional-zero, negative, and zero branches. -/
example : (stored 1000 2).render = "10.00" := by
  native_decide

example : (stored 1 2).render = "0.01" := by
  native_decide

example : (stored (-1) 2).render = "-0.01" := by
  native_decide

example : (stored 0 2).render = "0.00" := by
  native_decide

/- Stored equality retains decimal scale although numeric amount equality does not. -/
example : (stored 7 0).amount = (stored 700 2).amount ∧
    stored 7 0 ≠ stored 700 2 := by
  native_decide

end A12Kernel.Conformance.NumericStoredNumber
