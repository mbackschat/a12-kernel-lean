import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Semantics.FirstFilledValue

/-! # Direct one-star Boolean `FirstFilledValue` computation -/

namespace A12Kernel

inductive BooleanFirstFilledComputationElabError where
  | target (cause : ResolveError)
  | targetGroup (actual expected : GroupPath)
  | targetRepeatable (path : List String)
  | targetKind (path : List String) (actual : SurfaceScalarKind)
  | source (cause : StarPathElabError)
  | sourceKind (path : List String) (actual : SurfaceScalarKind)
  | sourceShape (path : List String)
  deriving Repr, DecidableEq

/-- Whether a checked star is exactly one reopened repeatable group and its field is declared directly in that group. -/
def booleanFirstFilledDirectSingleStar (model : FlatModel)
    (source : CheckedStarFieldPath model) : Bool :=
  match source.path.axes, source.declaration.repeatableScope with
  | [axis], [level] =>
      source.path.firstStar == 0 && axis.level == level &&
        model.repeatableGroups.any fun group =>
          group.level == level && group.path == source.declaration.groupPath
  | _, _ => false

/-- One fixed Boolean target and one direct single-level starred Boolean source certified against the same model. -/
structure CheckedBooleanFirstFilledComputation (model : FlatModel) where
  private mk ::
  target : FlatFieldDecl
  source : CheckedStarFieldPath model
  targetGroup : GroupPath
  targetBoolean : target.policy.kind = .boolean
  targetFixed : target.repeatableScope = []
  targetOwnedByGroup : target.groupPath = targetGroup
  sourceBoolean : source.declaration.policy.kind = .boolean
  sourceDirectSingleStar :
    booleanFirstFilledDirectSingleStar model source = true

/-- Check the exact externally measured Boolean computation shape. Wider `entitySpec`, nested repetition, validation use, and target application remain outside this boundary. -/
def checkBooleanFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except BooleanFirstFilledComputationElabError
      (CheckedBooleanFirstFilledComputation model) := do
  let source ← elaborateStarFieldPath model declaringGroup authored
    |>.mapError .source
  let target ← model.lookupUniqueId targetField |>.mapError .target
  if hGroup : target.groupPath = declaringGroup then
    if hFixed : target.repeatableScope = [] then
      if hTargetKind : target.policy.kind = .boolean then
        if hSourceKind : source.declaration.policy.kind = .boolean then
          if hShape : booleanFirstFilledDirectSingleStar model source = true then
            pure {
              target
              source
              targetGroup := declaringGroup
              targetBoolean := hTargetKind
              targetFixed := hFixed
              targetOwnedByGroup := hGroup
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
  else
    throw (.targetGroup target.groupPath declaringGroup)

/-- Classify one checked Boolean source cell for computation-phase first-filled selection. -/
def booleanFirstFilledCellAt (cell : CheckedCell) : FirstFilledBooleanCell :=
  match observeCell .computation cell with
  | .empty => .empty
  | .value (.bool value) => .present value
  | .value _ => .unknown .malformed
  | .unknown cause | .poison cause => .unknown cause

namespace CheckedBooleanFirstFilledComputation

/-- Execute the checked source against immutable rows. Structural addressing failure stays outside the semantic no-value/poison result. -/
def execute (operation : CheckedBooleanFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except CheckedStarDocumentError FirstFilledBooleanComputationResult := do
  let resolved ← operation.source.resolveCheckedField input []
  pure (evalFirstFilledBoolean
    (resolved.cells.map fun cell => booleanFirstFilledCellAt cell.cell))

end CheckedBooleanFirstFilledComputation

end A12Kernel
