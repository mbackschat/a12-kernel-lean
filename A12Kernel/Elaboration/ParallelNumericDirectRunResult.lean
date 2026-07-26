import A12Kernel.Elaboration.NumericComputation.RunResult
import A12Kernel.Elaboration.ParallelNumericDirectRun

/-! # Isolated direct parallel Number result

This boundary executes the complete isolated Number-operation inventory and classifies its exact addressed outcomes against the same checked preliminary document. Post-loop index clears come from every participating checked route and the same input as a second semantic source of public clearing; callers can supply neither outcomes nor clear addresses. Residual messages remain explicit because their construction belongs to the later computation-message boundary. -/

namespace A12Kernel

inductive ParallelNumericDirectRunResultError where
  | execution
      (error : CheckedIsolatedParallelNumericDirectRun.ExecutionError)
  | sourceTarget (error : NumericSourceTargetError)
  | clearing (error : ParallelNumericClearingError)
  | incoherentClassifiedIndexClear (address : CellAddr)
  deriving Repr, DecidableEq

/-- Find the first outcome-classified target also claimed by the independently classified post-loop index clears. -/
def parallelNumericDirectClassifiedIndexClear?
    (view : NumericComputationRunView ResidualMessage CellAddr)
    (indexClears : List CellAddr) : Option CellAddr :=
  (view.withoutErrors.map (·.targetField) ++
    view.withErrors.map (·.targetField) ++ view.cleared).find?
      indexClears.contains

/-- Merge post-loop index clears only when they do not also claim an outcome-classified target. -/
def addParallelNumericDirectIndexClears
    (view : NumericComputationRunView ResidualMessage CellAddr)
    (indexClears : List CellAddr) :
    Except ParallelNumericDirectRunResultError
      (NumericComputationRunView ResidualMessage CellAddr) :=
  match parallelNumericDirectClassifiedIndexClear? view indexClears with
  | some address =>
      .error (.incoherentClassifiedIndexClear address)
  | none =>
      .ok (view.withAdditionalClears indexClears)

/-- Classify addressed outcomes and merge source-filled index clears from one complete static route inventory. Execution remains with the owning singleton or table. -/
def classifyParallelNumericOutcomes
    (preliminary : CheckedIndexPreliminary model)
    (routes : List (CheckedParallelNumericTargetRoute model))
    (residualMessages : List ResidualMessage)
    (outcomes : List ParallelNumericDirectOutcome) :
    Except ParallelNumericDirectRunResultError
      (NumericComputationRunView ResidualMessage CellAddr) := do
  let entries ← outcomes.mapM fun result => do
    let source ←
      preliminary.base.numericTargetStateAt result.address
        |>.mapError ParallelNumericDirectRunResultError.sourceTarget
    pure {
      targetField := result.address
      outcome := result.outcome
      source
    }
  let classified :=
    NumericComputationRunView.fromSourceOutcomes
      residualMessages entries
  let indexClearings ← routes.mapM fun route =>
    route.clearedSourceTargets preliminary
      |>.mapError ParallelNumericDirectRunResultError.clearing
  let indexClears :=
    (indexClearings.flatMap (·.cleared)).eraseDups
  addParallelNumericDirectIndexClears classified indexClears

namespace CheckedIsolatedParallelNumericDirectRun

/-- Execute and classify one isolated repeatable direct Number computation from one checked preliminary input. -/
def executeResult
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (preliminary : CheckedIndexPreliminary model)
    (residualMessages : List ResidualMessage) :
    Except ParallelNumericDirectRunResultError
      (NumericComputationRunView ResidualMessage CellAddr) := do
  let outcomes ←
    checked.execute preliminary
      |>.mapError .execution
  classifyParallelNumericOutcomes preliminary
    checked.operandRoutes residualMessages outcomes

end CheckedIsolatedParallelNumericDirectRun

end A12Kernel
