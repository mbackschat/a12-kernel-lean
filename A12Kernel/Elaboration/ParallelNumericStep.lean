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

def protectionConditions (step : CheckedParallelNumericStep model) : List (Option ComputationProtectionView) :=
  step.asMixedTable.members.map (·.protectionView)

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
    step.primary.join ((step.operandRoutes.drop 1).map (·.join)) preliminary).mapError .execution
  targets.mapM fun target => do
    if target.indexInvalid || target.overLimit then
      pure { address := target.address, outcome := .noValue }
    else
      match step with
      | .single operation =>
          (operation.executeTargetWith preliminary document.read document.parallelGuardContextAt
            target.environment target.address).mapError .execution
      | .alternatives table =>
          (table.executeTargetWith preliminary document.read document.parallelGuardContextAt target).mapError .execution
      | .mixed table => (table.executeTarget preliminary document target).mapError .execution

end CheckedParallelNumericStep
end A12Kernel
