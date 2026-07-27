import A12Kernel.Elaboration.TimeLiteral

/-! # Checked Time-literal law -/

namespace A12Kernel

/-- Static checking succeeds with exactly the clock returned by the exact decoder. -/
theorem elaborateTimeLiteral_ok_iff
    (source : String) (time : TimeOfDay) :
    elaborateTimeLiteral source = .ok time ↔
      decodeTimeLiteral? source = some time := by
  unfold elaborateTimeLiteral
  cases decoded : decodeTimeLiteral? source <;> simp_all

end A12Kernel
