import A12Kernel.Elaboration.ScalarComputationRun
import A12Kernel.Elaboration.NumericComputation.RunResult
import A12Kernel.Elaboration.StringComputationRunResult

/-! # Family-preserving result for a finite mixed scalar run

This capsule partitions successful mixed outcomes solely by their retained constructor, then delegates source-relative classification to the existing String and Number result owners. It defines no common computed instance, error, message, or collection-order contract.
-/

namespace A12Kernel

/-- The two exact family outcome lists recovered from one mixed execution. Relative order within each family is retained; cross-family supplied order is private execution state. -/
structure ScalarComputationOutcomePartitions where
  string : List (FieldId × StringTargetOutcome)
  number : List (FieldId × NumericTargetOutcome)
  deriving Repr, DecidableEq

namespace ScalarComputationOutcomePartitions

def ofOutcomes : List ScalarComputationOutcome →
    ScalarComputationOutcomePartitions
  | [] => { string := [], number := [] }
  | .string target outcome :: remaining =>
      let partitioned := ofOutcomes remaining
      {
        string := (target, outcome) :: partitioned.string
        number := partitioned.number
      }
  | .number target outcome :: remaining =>
      let partitioned := ofOutcomes remaining
      {
        string := partitioned.string
        number := (target, outcome) :: partitioned.number
      }

end ScalarComputationOutcomePartitions

/-- Public mixed result with both established family views retained separately. -/
structure ScalarComputationRunView
    (StringResidual NumberPayload : Type) where
  string : StringComputationRunView StringResidual
  number :
    NumericComputationRunView (ComputationFormalMessage NumberPayload)
  deriving Repr, DecidableEq

inductive ScalarComputationRunResultFault where
  | execution (cause : ScalarComputationRunFault)
  | numberSource (cause : NumericSourceTargetError)
  deriving Repr, DecidableEq

namespace CheckedScalarComputationRun

/-- Execute once, partition only by retained family, and route each partition through its existing source-relative result owner. -/
def executeResult (run : CheckedScalarComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (numberPayloadAt : FieldId → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (stringResidualMessages : List StringResidual) :
    Except ScalarComputationRunResultFault
      (ScalarComputationRunView StringResidual NumberPayload) := do
  let outcomes ← (run.execute world patterns input).mapError .execution
  let partitioned := ScalarComputationOutcomePartitions.ofOutcomes outcomes
  let string :=
    StringComputationRunView.fromOutcomes input
      stringResidualMessages partitioned.string
  let number ←
    (NumericComputationRunView.fromOutcomes input numberPayloadAt
      numberMessages partitioned.number).mapError .numberSource
  pure { string, number }

end CheckedScalarComputationRun

end A12Kernel
