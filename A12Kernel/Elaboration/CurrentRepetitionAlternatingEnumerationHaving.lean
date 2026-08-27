import A12Kernel.Elaboration.CurrentRepetitionAlternatingChain
import A12Kernel.Elaboration.AddressedNumberEnumerationHavingCascade

/-! # Four-stage CurrentRepetition Number/String/Number/Enumeration route

This bounded SG4 route completes the existing three-computation alternating chain before one direct-then-filtered Enumeration `FirstFilledValue` reads its completed Number phases. The final read remains lazy and exact-addressed; this is not a generic scheduler or document state.
-/

namespace A12Kernel

inductive CurrentRepetitionAlternatingEnumerationHavingElabError where
  | consumerSourceShape
  | missingFilterDependency (field : FieldId)
  deriving Repr, DecidableEq

/-- One existing alternating prefix followed by the exact filtered Enumeration consumer that reads its terminal Number target. -/
structure CheckedCurrentRepetitionAlternatingEnumerationHaving
    (model : FlatModel) where
  private mk ::
  chain : CheckedCurrentRepetitionAlternatingChain model
  consumer : CheckedAddressedEnumerationFirstFilledComputation model
  havingDependencies : List FieldId
  consumerSourceShape :
    directThenFilteredEnumerationHavingDependencies? consumer.source =
      some havingDependencies
  filterDependency :
    havingDependencies.contains chain.third.placement.targetField = true

/-- Certify only the final direct-then-filtered source shape and its terminal Number edge. -/
def checkCurrentRepetitionAlternatingEnumerationHaving
    (chain : CheckedCurrentRepetitionAlternatingChain model)
    (consumer : CheckedAddressedEnumerationFirstFilledComputation model) :
    Except CurrentRepetitionAlternatingEnumerationHavingElabError
      (CheckedCurrentRepetitionAlternatingEnumerationHaving model) :=
  match hShape :
      directThenFilteredEnumerationHavingDependencies? consumer.source with
  | none => .error .consumerSourceShape
  | some dependencies =>
      if hDependency : dependencies.contains
          chain.third.placement.targetField = true then
        .ok {
          chain, consumer, havingDependencies := dependencies
          consumerSourceShape := hShape
          filterDependency := hDependency
        }
      else .error (.missingFilterDependency
        chain.third.placement.targetField)

structure CurrentRepetitionAlternatingEnumerationHavingAnalysis where
  structuralGroup : GroupPath
  scope : List RepeatableLevel
  thirdProjection : EnumerationProjectionRef
  consumerTarget : FieldId
  fieldDependencies : List (FieldId × List FieldId)
  deriving Repr, DecidableEq

structure CurrentRepetitionAlternatingEnumerationHavingOutcomes where
  chain : CurrentRepetitionAlternatingChainOutcomes
  consumer : List AddressedEnumerationComputationOutcome
  deriving Repr, DecidableEq

inductive CurrentRepetitionAlternatingEnumerationHavingFault where
  | chain (cause : CurrentRepetitionAlternatingChainFault)
  | consumer (cause : AddressedEnumerationFirstFilledComputationFault)
  deriving Repr, DecidableEq

namespace CheckedCurrentRepetitionAlternatingEnumerationHaving

/-- Expose the complete structural scope, all four typed edges, and the terminal conversion identity. -/
def analyze (plan : CheckedCurrentRepetitionAlternatingEnumerationHaving model) :
    CurrentRepetitionAlternatingEnumerationHavingAnalysis := {
  structuralGroup := plan.chain.numberToString.source.path
  scope := plan.chain.numberToString.source.completeScope
  thirdProjection := plan.chain.third.projectionRef
  consumerTarget := plan.consumer.target.field
  fieldDependencies := plan.chain.analyze.fieldDependencies ++ [
    (plan.consumer.target.field, plan.consumer.source.fieldDependencies)]
}

/-- Complete all three prefix phases, expose both completed Number phases, then run the lazy Enumeration consumer. -/
def execute (plan : CheckedCurrentRepetitionAlternatingEnumerationHaving model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    Except CurrentRepetitionAlternatingEnumerationHavingFault
      CurrentRepetitionAlternatingEnumerationHavingOutcomes := do
  let chain ← plan.chain.execute patterns input |>.mapError .chain
  let numberOutcomes := chain.rows.flatMap fun row => [row.first, row.third]
  let consumer ← plan.consumer.executeWithRead input
      (readAfterNumericDependencies input numberOutcomes) |>.mapError .consumer
  pure { chain, consumer }

end CheckedCurrentRepetitionAlternatingEnumerationHaving

end A12Kernel
