import A12Kernel.Elaboration.ParallelNumericDirectRunResult

/-! # Checked parallel Number alternative tables

This boundary consolidates two or more already-checked guarded parallel Number operations for one repeatable target. It reuses the shared first-selected condition scan and delegates only the selected row to the direct operation's target evaluator. Static route collection and target-row iteration remain with the next execution capsule.
-/

namespace A12Kernel

inductive ParallelNumericAlternativeTableError where
  | fewerThanTwo
  | unguarded (alternative : Nat)
  | targetMismatch (alternative : Nat) (expected actual : FieldId)
  deriving Repr, DecidableEq

/-- One guarded parallel operation certified against the table's shared target. The complete checked operation remains intact because it owns expression, routes, scale directive, and target policy. -/
structure CheckedParallelNumericAlternative (model : FlatModel)
    (target : FieldId) where
  operation : CheckedIsolatedParallelNumericDirectRun model
  precondition : ComputationCondition
  preconditionOwned : operation.precondition = some precondition
  targetMatches : operation.route.targetField = target

namespace CheckedParallelNumericAlternative

def toSelectable
    (alternative : CheckedParallelNumericAlternative model target) :
    ComputationAlternative
      (CheckedIsolatedParallelNumericDirectRun model) where
  precondition := alternative.precondition
  operation := alternative.operation

end CheckedParallelNumericAlternative

/-- One already-flattened guarded table. Two rows are stored explicitly because a singleton has its existing optional-guard owner. -/
structure CheckedParallelNumericAlternativeTable (model : FlatModel) where
  targetField : FieldId
  first : CheckedParallelNumericAlternative model targetField
  second : CheckedParallelNumericAlternative model targetField
  remaining : List (CheckedParallelNumericAlternative model targetField)

private def certifyParallelNumericAlternative
    (target : FieldId) (alternativeIndex : Nat)
    (operation : CheckedIsolatedParallelNumericDirectRun model) :
    Except ParallelNumericAlternativeTableError
      (CheckedParallelNumericAlternative model target) :=
  match guarded : operation.precondition with
  | none => .error (.unguarded alternativeIndex)
  | some precondition =>
      if targetMatches : operation.route.targetField = target then
        .ok {
          operation
          precondition
          preconditionOwned := guarded
          targetMatches
        }
      else
        .error (.targetMismatch alternativeIndex target
          operation.route.targetField)

/-- Consolidate checked rows without reordering them. Alternative positions are one-based. -/
def certifyParallelNumericAlternativeTable
    (operations : List (CheckedIsolatedParallelNumericDirectRun model)) :
    Except ParallelNumericAlternativeTableError
      (CheckedParallelNumericAlternativeTable model) :=
  match operations with
  | first :: second :: remaining => do
      let target := first.route.targetField
      let checkedFirst ← certifyParallelNumericAlternative target 1 first
      let checkedSecond ← certifyParallelNumericAlternative target 2 second
      let checkedRemaining ← remaining.zipIdx.mapM fun (operation, index) =>
        certifyParallelNumericAlternative target (index + 3) operation
      pure {
        targetField := target
        first := checkedFirst
        second := checkedSecond
        remaining := checkedRemaining
      }
  | _ => .error .fewerThanTwo

namespace CheckedParallelNumericAlternativeTable

def alternatives
    (table : CheckedParallelNumericAlternativeTable model) :
    List (CheckedParallelNumericAlternative model table.targetField) :=
  table.first :: table.second :: table.remaining

def selectableAlternatives
    (table : CheckedParallelNumericAlternativeTable model) :
    List (ComputationAlternative
      (CheckedIsolatedParallelNumericDirectRun model)) :=
  table.alternatives.map (·.toSelectable)

/-- Whether any row's guard or complete numeric expression reads one exact field. -/
def referencesField
    (table : CheckedParallelNumericAlternativeTable model)
    (field : FieldId) : Bool :=
  table.alternatives.any fun alternative =>
    alternative.operation.referencesField field

/-- Select through the shared computation-condition scan, then evaluate only the selected checked parallel operation. -/
def evaluate (table : CheckedParallelNumericAlternativeTable model)
    (context : ScalarComputationContext) :
    Except CheckedIsolatedParallelNumericDirectRun.ExecutionError
      NumericTargetOutcome :=
  match ComputationAlternative.selectFirst
      table.selectableAlternatives context with
  | .noMatch => .ok .noValue
  | .poison cause => .ok (.inheritedPoison cause)
  | .selected operation => operation.evaluateSelected context

def WellFormed
    (table : CheckedParallelNumericAlternativeTable model) : Prop :=
  ∀ alternative ∈ table.alternatives,
    alternative.operation.WellFormed ∧
      alternative.operation.precondition =
        some alternative.precondition ∧
      alternative.operation.route.targetField = table.targetField

private def appendRouteIfNew
    (routes : List (CheckedParallelNumericTargetRoute model))
    (candidate : CheckedParallelNumericTargetRoute model) :
    List (CheckedParallelNumericTargetRoute model) :=
  if routes.any fun route =>
      route.groups.rightGroup.path == candidate.groups.rightGroup.path then
    routes
  else
    routes ++ [candidate]

/-- Every expression and guard group from every row participates, deduplicated by the checked indexed-group path while retaining first encounter order. -/
def operandRoutes
    (table : CheckedParallelNumericAlternativeTable model) :
    List (CheckedParallelNumericTargetRoute model) :=
  table.alternatives.foldl
    (fun routes alternative =>
      alternative.operation.operandRoutes.foldl appendRouteIfNew routes) []

/-- Fetch every row's checked carriers through one addressed read at one matched target key without observing any guard or expression. -/
def operandCellsWith
    (table : CheckedParallelNumericAlternativeTable model)
    (preliminary : CheckedIndexPreliminary model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (targetEnvironment : Env) (key : SemanticIndexKey) :
    Except CheckedIsolatedParallelNumericDirectRun.ExecutionError
      (List (FieldId × CheckedCell)) := do
  let nested ← table.alternatives.mapM fun alternative =>
    alternative.operation.operandCellsWith preliminary read
      targetEnvironment key
  pure nested.flatten

/-- Evaluate the selected table row at one already-certified target coverage entry. The supplied target owns the returned exact address. -/
def executeTargetWith
    (table : CheckedParallelNumericAlternativeTable model)
    (preliminary : CheckedIndexPreliminary model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (target : ParallelNumericTargetCoverage) :
    Except CheckedIsolatedParallelNumericDirectRun.ExecutionError
      ParallelNumericDirectOutcome := do
  let key ← table.first.operation.targetKeyFor preliminary
    target.environment target.address
  let cells ← table.operandCellsWith preliminary read
    target.environment key
  let context : ScalarComputationContext := {
    read := fun field =>
      match cells.find? fun cell => cell.1 == field with
      | some cell => cell.2
      | none => malformedCheckedCell
  }
  pure {
    address := target.address
    outcome := ← table.evaluate context
  }

/-- Execute the table through one addressed carrier read at every actual target whose complete all-row route inventory has clean checked index columns. -/
def executeWithRead
    (table : CheckedParallelNumericAlternativeTable model)
    (preliminary : CheckedIndexPreliminary model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except CheckedIsolatedParallelNumericDirectRun.ExecutionError
      (List ParallelNumericDirectOutcome) := do
  let targets ←
    CheckedIsolatedParallelNumericDirectRun.executableTargets
      table.first.operation.route.asTargetRoute
      (table.operandRoutes.drop 1) preliminary
  targets.mapM (table.executeTargetWith preliminary read)

/-- Preserve the standalone table entry point by reading carriers from the immutable preliminary document. -/
def execute
    (table : CheckedParallelNumericAlternativeTable model)
    (preliminary : CheckedIndexPreliminary model) :
    Except CheckedIsolatedParallelNumericDirectRun.ExecutionError
      (List ParallelNumericDirectOutcome) :=
  table.executeWithRead preliminary preliminary.base.read

/-- Execute and classify the table against the same immutable preliminary, including source-filled clears from every statically participating row route. -/
def executeResult
    (table : CheckedParallelNumericAlternativeTable model)
    (preliminary : CheckedIndexPreliminary model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except ParallelNumericDirectRunResultError
      (NumericComputationRunView (ComputationFormalMessage Payload) CellAddr) := do
  let outcomes ← table.execute preliminary |>.mapError .execution
  classifyParallelNumericOutcomes preliminary table.operandRoutes
    payloadAt supplied outcomes

end CheckedParallelNumericAlternativeTable

end A12Kernel
