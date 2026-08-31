import A12Kernel.Elaboration.NumericComputation.RunResult
import A12Kernel.Elaboration.StringComputationRunResult

/-! # Family-preserving String and Number computation result

This direction-neutral carrier retains the two established family views over one exact target-key domain and derives its aggregate error status and family-preserving extensional equality from their existing predicates. Family-separated application is defined in `A12Kernel.Elaboration.StringNumberComputationRunApplication`; execution order, dependency direction, activation, and mixed-document reconstruction remain owned by the checked run that returns it.
-/

namespace A12Kernel

/-- One family-preserving result for a bounded computation that may emit String and Number outcomes over the same target-key domain. -/
structure StringNumberComputationRunView
    (StringResidual NumberPayload : Type) (Target : Type := FieldId) where
  string : StringComputationRunView StringResidual Target
  number :
    NumericComputationRunView (ComputationFormalMessage NumberPayload) Target
  deriving Repr, DecidableEq

namespace StringNumberComputationRunView

/-- The combined result is error-free exactly when both retained family results are error-free. Successful changes and clears remain outside the predicate through the family owners. -/
def noErrorOccurred
    (view : StringNumberComputationRunView
      StringResidual NumberPayload Target) : Bool :=
  view.string.noErrorOccurred && view.number.noErrorOccurred

/-- Family-preserving equality of the ten public result collections. Each family remains extensional in its own target and payload domain; no cross-family order or matching is introduced. -/
def ExtensionalEq
    (left right : StringNumberComputationRunView
      StringResidual NumberPayload Target) : Prop :=
  left.string.ExtensionalEq right.string ∧
    left.number.ExtensionalEq right.number

end StringNumberComputationRunView

end A12Kernel
