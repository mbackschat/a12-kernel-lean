import A12Kernel.Elaboration.NumericComputation.RunResult
import A12Kernel.Elaboration.StringComputationRunResult
import A12Kernel.Elaboration.ScalarComputationRun
import A12Kernel.Elaboration.StringNumberComputationRunView

/-! # Family-preserving result for a finite mixed scalar run

This capsule partitions successful mixed outcomes solely by their retained constructor, then delegates source-relative classification to the existing String and Number result owners. This view routes only those two families; a whole-document outcome's family owners are not composed into it, so a run that computed one is refused rather than reported without it. It defines no common computed instance, error, message, or collection-order contract.
-/

namespace A12Kernel

/-- The exact family outcome lists recovered from one mixed execution. Relative order within each family is retained; cross-family supplied order is private execution state. -/
structure ScalarComputationOutcomePartitions where
  string : List (FieldId × StringTargetOutcome)
  number : List (FieldId × NumericTargetOutcome)
  document : List (FieldId × DocumentTargetOutcome)
  deriving Repr, DecidableEq

namespace ScalarComputationOutcomePartitions

def ofOutcomes : List ScalarComputationOutcome →
    ScalarComputationOutcomePartitions
  | [] => { string := [], number := [], document := [] }
  | .string target outcome :: remaining =>
      let partitioned := ofOutcomes remaining
      { partitioned with string := (target, outcome) :: partitioned.string }
  | .number target outcome :: remaining =>
      let partitioned := ofOutcomes remaining
      { partitioned with number := (target, outcome) :: partitioned.number }
  | .document target outcome :: remaining =>
      let partitioned := ofOutcomes remaining
      { partitioned with document := (target, outcome) :: partitioned.document }

end ScalarComputationOutcomePartitions

/-- Scalar-run compatibility name for the shared family-preserving result. -/
abbrev ScalarComputationRunView
    (StringResidual NumberPayload : Type) (Target : Type := FieldId) :=
  StringNumberComputationRunView StringResidual NumberPayload Target

inductive ScalarComputationRunResultFault where
  | execution (cause : ScalarComputationRunFault)
  | numberSource (cause : NumericSourceTargetError)
  | documentTarget (target : FieldId)
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
  if let some (target, _) := partitioned.document.head? then
    throw (.documentTarget target)
  let string :=
    StringComputationRunView.fromOutcomes input
      stringResidualMessages partitioned.string
  let number ←
    (NumericComputationRunView.fromOutcomes input numberPayloadAt
      numberMessages partitioned.number).mapError .numberSource
  pure { string, number }

end CheckedScalarComputationRun

end A12Kernel
