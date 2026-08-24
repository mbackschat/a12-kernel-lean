import A12Kernel.Elaboration.RepeatableNumberAggregateMixedRun

/-! # Aggregate-seeded mixed scalar-run laws -/

namespace A12Kernel

/-- Analyze retains every suffix family, target, and computed-target edge in supplied order. -/
@[simp]
theorem checkedRepeatableNumberAggregateMixedRun_analyze
    (plan : CheckedRepeatableNumberAggregateMixedRun model) :
    plan.analyze =
      let candidates :=
        plan.cascade.total.operation.core.target.id :: plan.run.targetFields
      {
        cascade := plan.cascade.analyze
        scalarTargets := plan.run.steps.map fun step =>
          (step.targetKind, step.targetField)
        computedDependencies := plan.run.steps.map fun step =>
          (step.targetField,
            candidates.filter fun field => step.referencesField field)
      } := by
  rfl

/-- Successful result projection preserves the prefix outcomes and delegates the exact scalar suffix partitions to the two existing family owners. -/
theorem checkedRepeatableNumberAggregateMixedRun_executeResult_routesSuffixFamilies
    (plan : CheckedRepeatableNumberAggregateMixedRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (numberPayloadAt : FieldId → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (stringResidualMessages : List StringResidual)
    (outcomes : RepeatableNumberAggregateMixedRunOutcomes)
    (number :
      NumericComputationRunView
        (ComputationFormalMessage NumberPayload))
    (executed : plan.execute world patterns input = .ok outcomes)
    (numberProjected :
      NumericComputationRunView.fromOutcomes input numberPayloadAt
        numberMessages
        (ScalarComputationOutcomePartitions.ofOutcomes
          outcomes.scalars).number = .ok number) :
    plan.executeResult world patterns input numberPayloadAt
        numberMessages stringResidualMessages =
      .ok {
        cascade := outcomes.cascade
        scalars := {
          string := StringComputationRunView.fromOutcomes input
            stringResidualMessages
            (ScalarComputationOutcomePartitions.ofOutcomes
              outcomes.scalars).string
          number
        }
      } := by
  unfold CheckedRepeatableNumberAggregateMixedRun.executeResult
  rw [executed]
  change
    (do
      let projected ←
        (NumericComputationRunView.fromOutcomes input numberPayloadAt
          numberMessages
          (ScalarComputationOutcomePartitions.ofOutcomes
            outcomes.scalars).number).mapError
              RepeatableNumberAggregateMixedRunResultFault.numberSource
      pure ({
        cascade := outcomes.cascade
        scalars := {
          string := StringComputationRunView.fromOutcomes input
            stringResidualMessages
            (ScalarComputationOutcomePartitions.ofOutcomes
              outcomes.scalars).string
          number := projected
        }
      } : RepeatableNumberAggregateMixedRunView
        StringResidual NumberPayload)) = _
  rw [numberProjected]
  rfl

end A12Kernel
