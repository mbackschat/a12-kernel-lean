import A12Kernel.Elaboration.ScalarComputationRunResult

/-! # Family-preserving mixed result laws

The partition laws show that no outcome is lost or routed to the wrong family. The result law then fixes delegation to the two established family owners.
-/

namespace A12Kernel

/-- Every tagged outcome contributes to exactly one family partition. -/
theorem scalarComputationOutcomePartitions_count
    (outcomes : List ScalarComputationOutcome) :
    let partitioned := ScalarComputationOutcomePartitions.ofOutcomes outcomes
    partitioned.string.length + partitioned.number.length =
      outcomes.length := by
  induction outcomes with
  | nil =>
      simp [ScalarComputationOutcomePartitions.ofOutcomes]
  | cons outcome remaining inductionHypothesis =>
      dsimp at inductionHypothesis
      cases outcome <;>
        simp only [ScalarComputationOutcomePartitions.ofOutcomes,
          List.length_cons]
      all_goals omega

/-- String membership is preserved exactly by the String partition. -/
theorem scalarComputationOutcomePartitions_string_mem_iff
    (outcomes : List ScalarComputationOutcome)
    (target : FieldId) (outcome : StringTargetOutcome) :
    (target, outcome) ∈
        (ScalarComputationOutcomePartitions.ofOutcomes outcomes).string ↔
      ScalarComputationOutcome.string target outcome ∈ outcomes := by
  induction outcomes with
  | nil =>
      simp [ScalarComputationOutcomePartitions.ofOutcomes]
  | cons head remaining inductionHypothesis =>
      cases head <;>
        simp [ScalarComputationOutcomePartitions.ofOutcomes,
          inductionHypothesis]

/-- Number membership is preserved exactly by the Number partition. -/
theorem scalarComputationOutcomePartitions_number_mem_iff
    (outcomes : List ScalarComputationOutcome)
    (target : FieldId) (outcome : NumericTargetOutcome) :
    (target, outcome) ∈
        (ScalarComputationOutcomePartitions.ofOutcomes outcomes).number ↔
      ScalarComputationOutcome.number target outcome ∈ outcomes := by
  induction outcomes with
  | nil =>
      simp [ScalarComputationOutcomePartitions.ofOutcomes]
  | cons head remaining inductionHypothesis =>
      cases head <;>
        simp [ScalarComputationOutcomePartitions.ofOutcomes,
          inductionHypothesis]

/-- Successful mixed result projection delegates the exact constructor partitions to the two existing family owners. -/
theorem scalarComputationRun_executeResult_routesFamilies
    (run : CheckedScalarComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (numberPayloadAt : FieldId → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (stringResidualMessages : List StringResidual)
    (outcomes : List ScalarComputationOutcome)
    (number :
      NumericComputationRunView
        (ComputationFormalMessage NumberPayload))
    (executed : run.execute world patterns input = .ok outcomes)
    (numberProjected :
      NumericComputationRunView.fromOutcomes input numberPayloadAt
        numberMessages
        (ScalarComputationOutcomePartitions.ofOutcomes outcomes).number =
          .ok number) :
    run.executeResult world patterns input numberPayloadAt
        numberMessages stringResidualMessages =
      .ok {
        string := StringComputationRunView.fromOutcomes input
          stringResidualMessages
          (ScalarComputationOutcomePartitions.ofOutcomes outcomes).string
        number
      } := by
  unfold CheckedScalarComputationRun.executeResult
  rw [executed]
  change
    (do
      let projected ←
        (NumericComputationRunView.fromOutcomes input numberPayloadAt
          numberMessages
          (ScalarComputationOutcomePartitions.ofOutcomes outcomes).number).mapError
            ScalarComputationRunResultFault.numberSource
      pure ({
        string := StringComputationRunView.fromOutcomes input
          stringResidualMessages
          (ScalarComputationOutcomePartitions.ofOutcomes outcomes).string
        number := projected
      } : ScalarComputationRunView StringResidual NumberPayload)) = _
  rw [numberProjected]
  rfl

end A12Kernel
