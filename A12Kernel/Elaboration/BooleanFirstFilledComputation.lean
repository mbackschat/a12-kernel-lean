import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.FirstFilledStarSource
import A12Kernel.Elaboration.BooleanComputationResult
import A12Kernel.Semantics.FirstFilledValue

/-! # Typed Boolean `FirstFilledValue` result and fixed computation

This module owns the fixed direct one-star Boolean computation and specializes the shared target-polymorphic typed result/application fold.
-/

namespace A12Kernel

inductive BooleanFirstFilledComputationElabError where
  | target (cause : ResolveError)
  | targetRepeatable (path : List String)
  | targetKind (path : List String) (actual : SurfaceScalarKind)
  | source (cause : StarPathElabError)
  | sourceKind (path : List String) (actual : SurfaceScalarKind)
  | sourceShape (path : List String)
  deriving Repr, DecidableEq

/-- One fixed Boolean target and one direct single-level starred Boolean source certified against the same model. -/
structure CheckedBooleanFirstFilledComputation (model : FlatModel) where
  private mk ::
  target : FlatFieldDecl
  source : CheckedStarFieldPath model
  /-- The group the computation is declared in, which the target need not lie in. -/
  declaringGroup : GroupPath
  targetBoolean : target.policy.kind = .boolean
  targetFixed : target.repeatableScope = []
  sourceBoolean : source.declaration.policy.kind = .boolean
  sourceDirectSingleStar : source.isDirectSingleStar = true

/-- Check the exact externally measured Boolean computation shape. Wider `entitySpec`, nested repetition, validation use, and target application remain outside this boundary. -/
def checkBooleanFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except BooleanFirstFilledComputationElabError
      (CheckedBooleanFirstFilledComputation model) := do
  let source ← elaborateStarFieldPath model declaringGroup authored
    |>.mapError .source
  let target ← model.lookupUniqueId targetField |>.mapError .target
  -- No placement test. `elaborateStarFieldPath` already rejects an unrepresentable declaring
  -- group, and placement itself is unconstrained here: a fixed target under a star aggregate
  -- derives no iteration, so the Kernel admits it from an unrelated group.
  if hFixed : target.repeatableScope = [] then
    if hTargetKind : target.policy.kind = .boolean then
      if hSourceKind : source.declaration.policy.kind = .boolean then
        if hShape : source.isDirectSingleStar = true then
          pure {
            target
            source
            declaringGroup
            targetBoolean := hTargetKind
            targetFixed := hFixed
            sourceBoolean := hSourceKind
            sourceDirectSingleStar := hShape
          }
        else
          throw (.sourceShape source.declaration.path)
      else
        throw (.sourceKind source.declaration.path
          source.declaration.policy.kind.surfaceKind)
    else
      throw (.targetKind target.path target.policy.kind.surfaceKind)
  else
    throw (.targetRepeatable target.path)
/-- Classify one checked Boolean source cell for computation-phase first-filled selection. -/
def booleanFirstFilledCellAt (cell : CheckedCell) : FirstFilledBooleanCell :=
  match observeCell .computation cell with
  | .empty => .empty
  | .value (.bool value) => .present value
  | .value _ => .unknown .malformed
  | .unknown cause | .poison cause => .unknown cause

/-- Five extensional result collections for one model-certified Boolean `FirstFilledValue` computation. Retaining the checked operation makes every possible action target-owned. -/
structure BooleanFirstFilledComputationRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedBooleanFirstFilledComputation model
  boolean : BooleanComputationRunView ResidualMessage FieldId

namespace BooleanFirstFilledComputationRunView

def withoutErrors (view : BooleanFirstFilledComputationRunView model ResidualMessage) :=
  view.boolean.withoutErrors

def withChanges (view : BooleanFirstFilledComputationRunView model ResidualMessage) :=
  view.boolean.withChanges

def withErrors (view : BooleanFirstFilledComputationRunView model ResidualMessage) :=
  view.boolean.withErrors

def cleared (view : BooleanFirstFilledComputationRunView model ResidualMessage) :=
  view.boolean.cleared

def formalErrorsInOperands
    (view : BooleanFirstFilledComputationRunView model ResidualMessage) :=
  view.boolean.formalErrorsInOperands

/-- The fixed result's public error predicate delegates to the shared typed channels. -/
def noErrorOccurred
    (view : BooleanFirstFilledComputationRunView model ResidualMessage) : Bool :=
  view.boolean.noErrorOccurred

/-- Build the fixed Boolean result from the shared exact-target classifier. -/
def fromOutcome (operation : CheckedBooleanFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (outcome : FirstFilledBooleanComputationResult) :
    BooleanFirstFilledComputationRunView model ResidualMessage := {
  operation
  boolean := BooleanComputationRunView.fromSourcedOutcomes residualMessages [(
    operation.target.id, outcome,
    input.sourceBooleanTargetState operation.target.id)]
}

end BooleanFirstFilledComputationRunView

namespace CheckedBooleanFirstFilledComputation

/-- Execute the checked source against immutable rows. Structural addressing failure stays outside the semantic no-value/poison result. -/
def execute (operation : CheckedBooleanFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except CheckedStarDocumentError FirstFilledBooleanComputationResult := do
  let resolved ← operation.source.resolveCheckedField input []
  pure (evalFirstFilledBoolean
    (resolved.cells.map fun cell => booleanFirstFilledCellAt cell.cell))

/-- Execute and classify one checked Boolean selection against the immutable source target. Successful payloads stay typed; exhaustion and reached poison clear only a source-filled target. -/
def executeResult (operation : CheckedBooleanFirstFilledComputation model)
    (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except CheckedStarDocumentError
      (BooleanFirstFilledComputationRunView model ResidualMessage) := do
  let result ← operation.execute input
  pure (BooleanFirstFilledComputationRunView.fromOutcome operation input
    residualMessages result)

end CheckedBooleanFirstFilledComputation

namespace BooleanFirstFilledComputationRunView

/-- Targets consumed by the retained Boolean actions. -/
def actionTargets
    (view : BooleanFirstFilledComputationRunView model ResidualMessage) :
    List FieldId :=
  view.boolean.actionTargets

/-- Apply source-classified Boolean actions to a separately supplied checked document of the same certified model. Unchanged successes and residual messages are inert. -/
def applyToChecked
    (view : BooleanFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) : BooleanComputationDestination :=
  view.boolean.applyTo destination.sourceBooleanTargetState

end BooleanFirstFilledComputationRunView

end A12Kernel
