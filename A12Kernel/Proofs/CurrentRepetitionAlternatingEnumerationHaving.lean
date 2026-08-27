import A12Kernel.Elaboration.CurrentRepetitionAlternatingEnumerationHaving

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

end A12Kernel
