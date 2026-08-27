import A12Kernel.Elaboration.CurrentRepetitionAlternatingChain
import A12Kernel.Elaboration.AddressedNumberEnumerationHavingCascade
import A12Kernel.Elaboration.ComputationFormalInput
import A12Kernel.Elaboration.StringComputationRunApplication

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

/-- Family-preserving source-relative results for the exact four-computation route. -/
structure CurrentRepetitionAlternatingEnumerationHavingRunView
    (model : FlatModel) (NumberPayload StringResidual : Type) where
  private mk ::
  plan : CheckedCurrentRepetitionAlternatingEnumerationHaving model
  chain : StringNumberComputationRunView StringResidual NumberPayload CellAddr
  consumer : StringComputationRunView StringResidual CellAddr

/-- One completed four-stage run paired with its call-global direct-field formal-input inventory. -/
structure CurrentRepetitionAlternatingEnumerationHavingFormalInputRunView
    (model : FlatModel) where
  private mk ::
  phases : CurrentRepetitionAlternatingEnumerationHavingRunView
    model Unit ComputationFormalInputFinding
  formalErrorsInOperands : List ComputationFormalInputFinding

inductive CurrentRepetitionAlternatingEnumerationHavingFault where
  | chain (cause : CurrentRepetitionAlternatingChainFault)
  | consumer (cause : AddressedEnumerationFirstFilledComputationFault)
  deriving Repr, DecidableEq

/-- Failure while composing the checked call-global inventory with four-stage execution. -/
inductive CurrentRepetitionAlternatingEnumerationHavingCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | execution (cause : CurrentRepetitionAlternatingEnumerationHavingFault)
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

/-- Execute once and classify the alternating prefix and final Enumeration phase against the same immutable source. -/
def executeResult
    (plan : CheckedCurrentRepetitionAlternatingEnumerationHaving model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (numberPayloadAt : CellAddr → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (chainStringResidualMessages consumerResidualMessages :
      List StringResidual) :
    Except CurrentRepetitionAlternatingEnumerationHavingFault
      (CurrentRepetitionAlternatingEnumerationHavingRunView
        model NumberPayload StringResidual) := do
  let outcomes ← plan.execute patterns input
  pure {
    plan
    chain := {
      string := StringComputationRunView.fromSourcedOutcomes
        chainStringResidualMessages (outcomes.chain.rows.map (·.second))
      number := NumericComputationRunView.fromSourceOutcomesWithMessages
        MessagePointer.ofCellAddr numberPayloadAt numberMessages
        (outcomes.chain.rows.flatMap fun row => [row.first, row.third])
    }
    consumer := projectAddressedEnumerationResults input
      consumerResidualMessages outcomes.consumer
  }

/-- Bind the complete four-operation Analyze inventory to one checked direct-field plan. -/
def formalInputPlan
    (plan : CheckedCurrentRepetitionAlternatingEnumerationHaving model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputOperations model plan.analyze.fieldDependencies

/-- Collect the global inventory eagerly, then execute all four phases without supplied family residuals. Number retains its independently derived target-message semantics. -/
def executeResultWithFormalInputs
    (plan : CheckedCurrentRepetitionAlternatingEnumerationHaving model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    Except CurrentRepetitionAlternatingEnumerationHavingCheckedResultFault
      (CurrentRepetitionAlternatingEnumerationHavingFormalInputRunView model) := do
  let inputPlan ← plan.formalInputPlan |>.mapError .formalInput
  let phases ← plan.executeResult patterns input (fun _ => ()) [] [] []
    |>.mapError .execution
  pure {
    phases
    formalErrorsInOperands := inputPlan.findings input
  }

end CheckedCurrentRepetitionAlternatingEnumerationHaving

namespace CurrentRepetitionAlternatingEnumerationHavingRunView

/-- Apply the middle String phase and final Enumeration phase in checked order to one separately supplied same-model destination projection. -/
def applyStringsToChecked
    (view : CurrentRepetitionAlternatingEnumerationHavingRunView
      model NumberPayload StringResidual)
    (destination : CheckedDocument model) :
    Except (StringComputationRunView.StringComputationRunApplicationError CellAddr)
      (StringComputationDestination CellAddr) := do
  let afterChain ← view.chain.string.applyTo
    destination.sourceStringTargetStateAt
  view.consumer.applyTo afterChain

end CurrentRepetitionAlternatingEnumerationHavingRunView

end A12Kernel
