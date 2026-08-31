import A12Kernel.Elaboration.StringNumberComputationRunView
import A12Kernel.Proofs.NumericComputationRunResult
import A12Kernel.Proofs.StringComputationRunResult

/-! # Family-preserving String and Number result laws -/

namespace A12Kernel

/-- The mixed result's status observes exactly the two error channels in each retained family. -/
theorem stringNumberComputationRun_noErrorOccurred_iff
    (view : StringNumberComputationRunView
      StringResidual NumberPayload Target) :
    view.noErrorOccurred = true ↔
      (view.string.withErrors = [] ∧
        view.string.formalErrorsInOperands = []) ∧
      (view.number.withErrors = [] ∧
        view.number.formalErrorsInOperands = []) := by
  simp [StringNumberComputationRunView.noErrorOccurred,
    StringComputationRunView.noErrorOccurred,
    NumericComputationRunView.noErrorOccurred]

end A12Kernel
