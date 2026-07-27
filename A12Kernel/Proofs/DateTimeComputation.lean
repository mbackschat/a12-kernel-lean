import A12Kernel.Elaboration.DateTimeComputation

/-! # Checked `Now` DateTime computation law -/

namespace A12Kernel

/-- Every execution transports that call's exact world instant into the checked target; elaboration retains no earlier sample. -/
theorem dateTimeComputation_transports_now
    (operation : CheckedDateTimeComputation model)
    (world : World) :
    operation.evaluateOutcome world =
      (operation.target.evaluate (.value world.now)).mapError .target := by
  rfl

end A12Kernel
