import A12Kernel.Elaboration.NumericComputation.FormalInput
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

/-- Failure while composing one checked parallel Number operation's complete formal-input preparation with its existing addressed execution and result boundary. -/
inductive ParallelNumericDirectFormalInputRunFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : ParallelNumericDirectRunResultError)
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
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload))
    (outcomes : List ParallelNumericDirectOutcome) :
    Except ParallelNumericDirectRunResultError
      (NumericComputationRunView (ComputationFormalMessage Payload) CellAddr) := do
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
    NumericComputationRunView.fromSourceOutcomesWithMessages
      MessagePointer.ofCellAddr payloadAt supplied entries
  let indexClearings ← routes.mapM fun route =>
    route.clearedSourceTargets preliminary
      |>.mapError ParallelNumericDirectRunResultError.clearing
  let indexClears :=
    (indexClearings.flatMap (·.cleared)).eraseDups
  addParallelNumericDirectIndexClears classified indexClears

namespace CheckedIsolatedParallelNumericDirectRun

/-- Model-declaration-ordered expression and guard fields read by this checked operation, excluding the implicit index columns owned by its routes. -/
def ordinaryFieldDependencies
    (checked : CheckedIsolatedParallelNumericDirectRun model) :
    List FieldId :=
  (model.fields.filter fun declaration =>
    checked.referencesField declaration.id).map (·.id)

/-- Whether one field is an index column consumed by any checked target-to-operand route. -/
def referencesIndexField
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (field : FieldId) : Bool :=
  checked.operandRoutes.any fun route =>
    route.groups.leftIndexDeclaration.id == field ||
      route.groups.rightIndexDeclaration.id == field

/-- Model-declaration-ordered index columns needed by the checked parallel joins. -/
def indexFieldDependencies
    (checked : CheckedIsolatedParallelNumericDirectRun model) :
    List FieldId :=
  (model.fields.filter fun declaration =>
    checked.referencesIndexField declaration.id).map (·.id)

/-- Bind the complete ordinary-plus-index field inventory and computed target to the shared call-global formal-input plan. -/
def formalInputPlan
    (checked : CheckedIsolatedParallelNumericDirectRun model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model
    (model.fields.filterMap fun declaration =>
      if checked.referencesField declaration.id ||
          checked.referencesIndexField declaration.id then
        some declaration.id
      else
        none)
    [checked.route.targetField]

/-- Execute and classify one isolated repeatable direct Number computation from one checked preliminary input. -/
def executeResult
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (preliminary : CheckedIndexPreliminary model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except ParallelNumericDirectRunResultError
      (NumericComputationRunView (ComputationFormalMessage Payload) CellAddr) := do
  let outcomes ←
    checked.execute preliminary
      |>.mapError .execution
  classifyParallelNumericOutcomes preliminary
    checked.operandRoutes payloadAt supplied outcomes

/-- Prepare selected cached and generated inputs once, execute against that same preliminary view, and retain the eager inventory beside either the addressed result or a later execution failure. -/
def executeResultWithFormalInputs
    (checked : CheckedIsolatedParallelNumericDirectRun model)
    (input : CheckedDocument model) :
    Except ParallelNumericDirectFormalInputRunFault
      (NumericComputationFormalInputRunView model CellAddr) := do
  let plan ← checked.formalInputPlan |>.mapError .formalInput
  let prepared ← plan.prepare input |>.mapError .preliminary
  match checked.executeResult prepared.preliminary (fun _ => ()) [] with
  | .error cause =>
      .error (.execution prepared.formalErrorsInOperands cause)
  | .ok numeric =>
      .ok (NumericComputationFormalInputRunView.of numeric
        prepared.formalErrorsInOperands)

end CheckedIsolatedParallelNumericDirectRun

end A12Kernel
