import A12Kernel.Elaboration.CurrentRepetitionAlternatingEnumerationHaving
import A12Kernel.Proofs.AddressedEnumerationComputation

/-! # Four-stage CurrentRepetition Number/String/Number/Enumeration laws -/

namespace A12Kernel

/-- The final filtered consumer statically retains the terminal Number dependency. -/
theorem currentRepetitionAlternatingEnumerationHaving_filterDependency
    (plan : CheckedCurrentRepetitionAlternatingEnumerationHaving model) :
    plan.havingDependencies.contains
      plan.chain.third.placement.targetField = true :=
  plan.filterDependency

/-- Analyze delegates the prefix inventory and appends the final consumer inventory exactly once. -/
@[simp]
theorem currentRepetitionAlternatingEnumerationHaving_analyze
    (plan : CheckedCurrentRepetitionAlternatingEnumerationHaving model) :
    plan.analyze = {
      structuralGroup := plan.chain.numberToString.source.path
      scope := plan.chain.numberToString.source.completeScope
      thirdProjection := plan.chain.third.projectionRef
      consumerTarget := plan.consumer.target.field
      fieldDependencies := plan.chain.analyze.fieldDependencies ++ [
        (plan.consumer.target.field, plan.consumer.source.fieldDependencies)]
    } := by
  rfl

/-- Execution completes the established alternating chain before exposing both Number phases to the final lazy consumer. -/
theorem currentRepetitionAlternatingEnumerationHaving_execute_delegates
    (plan : CheckedCurrentRepetitionAlternatingEnumerationHaving model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    plan.execute patterns input = (do
      let chain ← plan.chain.execute patterns input |>.mapError
        CurrentRepetitionAlternatingEnumerationHavingFault.chain
      let numberOutcomes := chain.rows.flatMap fun row => [row.first, row.third]
      let consumer ← plan.consumer.executeWithRead input
          (readAfterNumericDependencies input numberOutcomes) |>.mapError
        CurrentRepetitionAlternatingEnumerationHavingFault.consumer
      pure { chain, consumer }) := by
  rfl

/-- Result projection classifies all four already-executed phases without recomputation. -/
theorem currentRepetitionAlternatingEnumerationHaving_executeResult_projects
    (plan : CheckedCurrentRepetitionAlternatingEnumerationHaving model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (numberPayloadAt : CellAddr → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (chainStringResidualMessages consumerResidualMessages :
      List StringResidual)
    (outcomes : CurrentRepetitionAlternatingEnumerationHavingOutcomes)
    (executed : plan.execute patterns input = .ok outcomes) :
    (plan.executeResult patterns input numberPayloadAt numberMessages
      chainStringResidualMessages consumerResidualMessages).map
      (fun view => (view.chain, view.consumer)) = .ok (
        {
          string := StringComputationRunView.fromSourcedOutcomes
            chainStringResidualMessages (outcomes.chain.rows.map (·.second))
          number := NumericComputationRunView.fromSourceOutcomesWithMessages
            MessagePointer.ofCellAddr numberPayloadAt numberMessages
            (outcomes.chain.rows.flatMap fun row => [row.first, row.third])
        },
        projectAddressedEnumerationResults input consumerResidualMessages
          outcomes.consumer) := by
  unfold CheckedCurrentRepetitionAlternatingEnumerationHaving.executeResult
  rw [executed]
  rfl

/-- The statically compatible Enumeration consumer cannot invent a target-rejection entry. -/
theorem currentRepetitionAlternatingEnumerationHaving_executeResult_hasNoConsumerErrors
    (plan : CheckedCurrentRepetitionAlternatingEnumerationHaving model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (numberPayloadAt : CellAddr → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (chainStringResidualMessages consumerResidualMessages :
      List StringResidual)
    (outcomes : CurrentRepetitionAlternatingEnumerationHavingOutcomes)
    (executed : plan.execute patterns input = .ok outcomes) :
    (plan.executeResult patterns input numberPayloadAt numberMessages
      chainStringResidualMessages consumerResidualMessages).map
      (fun view => view.consumer.withErrors) = .ok [] := by
  unfold CheckedCurrentRepetitionAlternatingEnumerationHaving.executeResult
  rw [executed]
  change Except.ok (projectAddressedEnumerationResults input
    consumerResidualMessages outcomes.consumer).withErrors = Except.ok []
  rw [addressedEnumerationResults_haveNoTargetErrors]

/-- Same-family application delegates to the completed middle String and final Enumeration folds in checked phase order. -/
theorem currentRepetitionAlternatingEnumerationHavingRun_applyStrings_delegates
    (view : CurrentRepetitionAlternatingEnumerationHavingRunView
      model NumberPayload StringResidual)
    (destination : CheckedDocument model) :
    view.applyStringsToChecked destination = (do
      let afterChain ← view.chain.string.applyTo
        destination.sourceStringTargetStateAt
      view.consumer.applyTo afterChain) := by
  rfl

end A12Kernel
