import A12Kernel.Elaboration.NumericComputation.RunApplication
import A12Kernel.Elaboration.StringComputationRunApplication
import A12Kernel.Elaboration.StringNumberComputationRunView

/-! # Family-separated String and Number application

The shared result carrier already preserves String and Number views over one target-key domain. Application keeps that separation: each family delegates to its existing source-classified fold and retains its own structural result. A malformed action list in one family therefore cannot hide the other family's application result. Checked-document reconstruction, cross-family physical write order, and validation remain separate.
-/

namespace A12Kernel

/-- Independent typed application results for one family-preserving String/Number view. Keeping both `Except` values prevents a failure in one family from inventing cross-family precedence or erasing the other result. -/
structure StringNumberComputationRunApplication
    (Target : Type) where
  string :
    Except (StringComputationRunView.StringComputationRunApplicationError Target)
      (StringComputationDestination Target)
  number :
    Except (NumericComputationRunView.NumericComputationRunApplicationError Target)
      (NumericComputationDestination Target)

namespace StringNumberComputationRunView

/-- Apply both retained family views independently to their exact typed destination projections. -/
def applyTo [DecidableEq Target]
    (view : StringNumberComputationRunView
      StringResidual NumberPayload Target)
    (stringDestination : StringComputationDestination Target)
    (numberDestination : NumericComputationDestination Target) :
    StringNumberComputationRunApplication Target := {
  string := view.string.applyTo stringDestination
  number := view.number.applyTo numberDestination
}

end StringNumberComputationRunView

end A12Kernel
