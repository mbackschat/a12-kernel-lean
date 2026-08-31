import A12Kernel.Elaboration.NumericComputation.RunResult
import A12Kernel.Elaboration.StringComputationRunResult

/-! # Family-preserving String and Number computation result

This direction-neutral carrier retains the two established family views over one exact target-key domain. Family-separated application is defined in `A12Kernel.Elaboration.StringNumberComputationRunApplication`; execution order, dependency direction, activation, and mixed-document reconstruction remain owned by the checked run that returns it.
-/

namespace A12Kernel

/-- One family-preserving result for a bounded computation that may emit String and Number outcomes over the same target-key domain. -/
structure StringNumberComputationRunView
    (StringResidual NumberPayload : Type) (Target : Type := FieldId) where
  string : StringComputationRunView StringResidual Target
  number :
    NumericComputationRunView (ComputationFormalMessage NumberPayload) Target
  deriving Repr, DecidableEq

end A12Kernel
