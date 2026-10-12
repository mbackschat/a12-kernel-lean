import A12Kernel.Elaboration.ParallelNumericMixedTable

/-! # Parallel Number steps in a mixed computation plan

The existing singleton and alternative table keep their evaluators. This boundary supplies their
complete dependency inventory and retains skipped target rows as clean clears for the shared overlay.
-/
namespace A12Kernel

inductive CheckedParallelNumericStep (model : FlatModel) where
  | single (operation : CheckedIsolatedParallelNumericDirectRun model)
  | alternatives (table : CheckedParallelNumericAlternativeTable model)
  | mixed (table : CheckedMixedParallelNumericTable model)

inductive ParallelNumericStepFault where
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (cause : CheckedIsolatedParallelNumericDirectRun.ExecutionError)
  deriving Repr, DecidableEq

/-- Resolve presence and numeric comparison leaves without pretending that sibling scopes are
bound. The checked run certifies their field routes and ordinary comparison admission together. -/
def FlatModel.resolveParallelNumericCondition (model : FlatModel) (group targetGroup : GroupPath) :
    SurfaceComputationConditionOf SurfaceNumericComputationAtom SurfaceComputationPredicate →
      Except ParallelNumericDirectPlanError (CheckedComputationCondition model)
  | .fieldFilled path =>
      (.fieldFilled ∘ FlatFieldDecl.id) <$> (model.resolvePresenceOperand group targetGroup path
        (model.resolveFieldDeclarationUnchecked group path)).mapError .expressionResolve
  | .fieldNotFilled path =>
      (.fieldNotFilled ∘ FlatFieldDecl.id) <$> (model.resolvePresenceOperand group targetGroup path
        (model.resolveFieldDeclarationUnchecked group path)).mapError .expressionResolve
  | .numeric comparison => do
      let resolve := model.resolveParallelNumericGuardAtom group targetGroup
      let left ← comparison.left.mapM resolve
      let right ← comparison.right.mapM resolve
      let resolved : NumericComparisonOf (CheckedNumericComputationAtom model) := {
        left, right, op := comparison.op
        suppressExactScaleWarning := comparison.suppressExactScaleWarning }
      pure (.leaf (.numeric resolved))
  | .and left right => do
      pure (.and (← model.resolveParallelNumericCondition group targetGroup left)
        (← model.resolveParallelNumericCondition group targetGroup right))
  | .or left right => do
      pure (.or (← model.resolveParallelNumericCondition group targetGroup left)
        (← model.resolveParallelNumericCondition group targetGroup right))
  | _ => .error .guardNotLimitedToOperand

namespace CheckedParallelNumericStep

def targetField : CheckedParallelNumericStep model → FieldId
  | .single operation => operation.route.targetField
  | .alternatives table => table.targetField
  | .mixed table => table.targetField

/-- Only joined members contribute index routes; complete member inventories are retained by
`asMixedTable` for guards and dependencies, including ordinary operations sharing the target. -/
def operations : CheckedParallelNumericStep model → List (CheckedIsolatedParallelNumericDirectRun model)
  | .single operation => [operation]
  | .alternatives table => table.alternatives.map (·.operation)
  | .mixed table => table.operations

def asMixedTable (step : CheckedParallelNumericStep model) : CheckedMixedParallelNumericTable model :=
  match step with
  | .single operation => {
      targetField := operation.route.targetField, primary := operation.route, primaryMatches := rfl
      members := [.joined {
        operation, precondition := operation.precondition,
        preconditionOwned := rfl, targetMatches := rfl }] }
  | .alternatives table => {
      targetField := table.targetField, primary := table.first.operation.route
      primaryMatches := table.first.targetMatches, members := table.alternatives.map .joined }
  | .mixed table => table

/-- Separate declarations retain their already-admitted singleton guards, including absence;
the mandatory-guard rule applies within one authored multi-row declaration (spec/09 §1.1). -/
def appendSameTarget (left right : CheckedParallelNumericStep model)
    (sameTarget : right.targetField = left.targetField) : CheckedParallelNumericStep model :=
  let leftTable := left.asMixedTable
  let rightTable := right.asMixedTable
  have leftTarget : leftTable.targetField = left.targetField := by cases left <;> rfl
  have rightTarget : rightTable.targetField = right.targetField := by cases right <;> rfl
  let rightMembers := (rightTarget.trans (sameTarget.trans leftTarget.symm)) ▸ rightTable.members
  .mixed { leftTable with members := leftTable.members ++ rightMembers }

/-- Retain an ordinary table's checked operations and guards when another declaration supplies
its target's joined coverage. No source expression is reconstructed or re-elaborated. -/
def withBoundTable (joined : CheckedParallelNumericStep model)
    (bound : CheckedNumericComputationTable model)
    (sameTarget : bound.targetField = joined.targetField) (before : Bool) : CheckedParallelNumericStep model :=
  let table := joined.asMixedTable
  have target : table.targetField = joined.targetField := by cases joined <;> rfl
  let members := (sameTarget.trans target.symm) ▸
    (bound.checkedAlternatives.map (CheckedParallelNumericMember.bound bound.targetPolicy))
  .mixed { table with members := if before then members ++ table.members else table.members ++ members }

def primary : CheckedParallelNumericStep model → CheckedParallelNumericTargetRoute model
  | .single operation => operation.route
  | .alternatives table => table.first.operation.route
  | .mixed table => table.primary

def operandRoutes : CheckedParallelNumericStep model → List (CheckedParallelNumericTargetRoute model)
  | .single operation => operation.operandRoutes
  | .alternatives table => table.operandRoutes
  | .mixed table => table.operandRoutes

def protectionConditions (step : CheckedParallelNumericStep model) : List (Option (CheckedComputationCondition model)) :=
  step.asMixedTable.members.map (·.precondition)

/-- Index columns participate statically even when a guard prevents the numeric read (spec/07 §2). -/
def referencesField (step : CheckedParallelNumericStep model) (field : FieldId) : Bool :=
  step.asMixedTable.members.any (·.referencesField field)

def requiresProducer (step : CheckedParallelNumericStep model)
    (producerProtected : FieldId → ResolvedGroupReference → Bool) (field : FieldId) : Bool :=
  step.asMixedTable.members.any (·.requiresProducer (producerProtected field) field)

/-- Select the same checked target coverage for execution and clearing. Reading an overlaid document
keeps producer values fresh; source-relative change classification belongs to the caller's immutable
input. An invalid-index or over-limit target clears without selecting a guard or observing an operand. -/
def execute (step : CheckedParallelNumericStep model) (document : CheckedDocument model) :
    Except ParallelNumericStepFault (List ParallelNumericDirectOutcome) := do
  let selected := model.fields.filterMap fun declaration =>
    if step.referencesField declaration.id then some declaration.id else none
  let preliminary ← (document.applySelectedFullIndexPreliminary selected).mapError .preliminary
  let targets ← (CheckedIsolatedParallelNumericDirectRun.targetCoverage
    step.primary (step.operandRoutes.drop 1) preliminary).mapError .execution
  targets.mapM fun target => do
    if target.indexInvalid || target.overLimit then
      pure { address := target.address, outcome := .noValue }
    else
      match step with
      | .single operation =>
          (operation.executeTargetWith preliminary document.read target.environment target.address).mapError .execution
      | .alternatives table =>
          (table.executeTargetWith preliminary document.read target).mapError .execution
      | .mixed table => (table.executeTarget preliminary document target).mapError .execution

end CheckedParallelNumericStep
end A12Kernel
