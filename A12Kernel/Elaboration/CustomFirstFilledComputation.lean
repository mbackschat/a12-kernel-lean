import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.ExactTokenComputationResult
import A12Kernel.Elaboration.FirstFilledStarSource
import A12Kernel.Elaboration.StringComputationRunApplication
import A12Kernel.Semantics.FirstFilledValue

/-! # Direct one-star Custom `FirstFilledValue` computation -/

namespace A12Kernel

inductive CustomFirstFilledComputationElabError where
  | target (cause : ResolveError)
  | targetRepeatable (path : List String)
  | targetNotCustom (path : List String)
  | source (cause : StarPathElabError)
  | sourceCustomTypeMismatch (path : List String)
      (expected : CustomFieldTypeDeclaration)
      (actual : Option CustomFieldTypeDeclaration)
  | sourceShape (path : List String)
  deriving Repr, DecidableEq

/-- One fixed Custom target and one direct single-level starred source carrying the same Custom declaration. -/
structure CheckedCustomFirstFilledComputation (model : FlatModel) where
  private mk ::
  target : FlatFieldDecl
  source : CheckedStarFieldPath model
  customType : CustomFieldTypeDeclaration
  /-- The group the computation is declared in, which the target need not lie in. -/
  declaringGroup : GroupPath
  /-- The declaring group is a representable path, certified by the star elaboration above rather
  than re-tested here. Placement itself is unconstrained; only representability survives. -/
  declaringGroupValid : GroupPath.isValid declaringGroup = true
  targetCustom : target.customType = some customType
  targetFixed : target.repeatableScope = []
  sourceCustom : source.declaration.customType = some customType
  sourceDirectSingleStar : source.isDirectSingleStar = true

/-- Check the exact externally measured Custom computation shape. The validated model already guarantees that every Custom declaration is an evaluated String field. -/
def checkCustomFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except CustomFirstFilledComputationElabError
      (CheckedCustomFirstFilledComputation model) := do
  match hStar : elaborateStarFieldPath model declaringGroup authored with
  | .error cause => .error (.source cause)
  | .ok source => do
    let target ← model.lookupUniqueId targetField |>.mapError .target
    -- No placement test. `elaborateStarFieldPath` already rejects an unrepresentable declaring
    -- group, and placement itself is unconstrained here: a fixed target under a star aggregate
    -- derives no iteration, so the Kernel admits it from an unrelated group.
    if hFixed : target.repeatableScope = [] then
      match hTarget : target.customType with
      | none => throw (.targetNotCustom target.path)
      | some customType =>
        if hSource : source.declaration.customType = some customType then
          if hShape : source.isDirectSingleStar = true then
            pure {
              target
              source
              customType
              declaringGroup
              declaringGroupValid :=
                elaborateStarFieldPath_declaringGroupValid hStar
              targetCustom := hTarget
              targetFixed := hFixed
              sourceCustom := hSource
              sourceDirectSingleStar := hShape
            }
          else
            throw (.sourceShape source.declaration.path)
        else
          throw (.sourceCustomTypeMismatch source.declaration.path customType
            source.declaration.customType)
    else
      throw (.targetRepeatable target.path)

/-- Classify one already prepared Custom source cell for computation-phase first-filled selection. -/
def customFirstFilledCellAt (cell : CheckedCell) : ValueListCell .token :=
  match observeCell .computation cell with
  | .empty => .empty
  | .value (.str value) => .present value
  | .value _ => .unknown .malformed
  | .unknown cause | .poison cause => .unknown cause

/-- One checked Custom `FirstFilledValue` result backed by the common String-shaped public channels. Retaining the private checked operation keeps every action tied to its exact admitted target and Custom declaration. -/
structure CustomFirstFilledComputationRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedCustomFirstFilledComputation model
  string : StringComputationRunView ResidualMessage

namespace CheckedCustomFirstFilledComputation

/-- Execute the checked source over immutable rows without resampling its registered validator. -/
def execute (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except CheckedStarDocumentError TokenComputationResult := do
  let resolved ← operation.source.resolveCheckedField input []
  let side : ResolvedValueListSide .token := {
    cells := resolved.cells.map fun cell => customFirstFilledCellAt cell.cell
    hasUninstantiatedTail := resolved.topology.domain.hasOpenTail
    hasHaving := false
  }
  pure (evalFirstFilledToken side).asComputationResult

/-- Execute one checked Custom selection and classify its exact token relative to the immutable source target. The matching Custom declaration makes a separately rejected target outcome unreachable. -/
def executeResult (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except CheckedStarDocumentError
      (CustomFirstFilledComputationRunView model ResidualMessage) := do
  let result ← operation.execute input
  let string := StringComputationRunView.fromSourcedOutcomes residualMessages [{
    targetField := operation.target.id
    outcome := result.asExactStringTargetOutcome
    source := input.sourceStringTargetState operation.target.id
  }]
  pure {
    operation
    string
  }

end CheckedCustomFirstFilledComputation

namespace CustomFirstFilledComputationRunView

/-- Apply retained source-relative Custom actions to a separately supplied checked document of the same model. The result is the exact root text-state projection and does not resample the registered validator or run implicit validation. -/
def applyToChecked
    (view : CustomFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (StringComputationRunView.StringComputationRunApplicationError FieldId)
      (StringComputationDestination FieldId) :=
  view.string.applyTo destination.sourceStringTargetState

end CustomFirstFilledComputationRunView

end A12Kernel
