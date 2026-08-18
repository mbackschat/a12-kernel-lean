import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.FirstFilledStarSource
import A12Kernel.Semantics.FirstFilledValue

/-! # Direct one-star DateFragment `FirstFilledValue` computation -/

namespace A12Kernel

/-- Whether this declaration fits the bounded `MM` DateFragment `FirstFilledValue` path. The opt-in pre-1900 check is excluded until the checked-document temporal reader represents that declaration-owned formal check. -/
def FlatFieldDecl.supportsMmDateFragmentFirstFilled
    (declaration : FlatFieldDecl) : Bool :=
  match declaration.policy.kind, declaration.toTemporalTargetPolicy? with
  | .temporal .date components, some policy =>
      components == TemporalComponents.fullDate &&
        policy.format == "MM" &&
        policy.partialMode == .yearOptional &&
        !policy.youngerThan1900Check
  | _, _ => false

inductive DateFragmentFirstFilledComputationElabError where
  | target (cause : ResolveError)
  | targetGroup (actual expected : GroupPath)
  | targetRepeatable (path : List String)
  | targetCarrier (path : List String)
  | source (cause : StarPathElabError)
  | sourceCarrier (path : List String)
  | sourceShape (path : List String)
  deriving Repr, DecidableEq

/-- One fixed `MM` DateFragment target and one direct single-level starred source of the same exact represented carrier. -/
structure CheckedDateFragmentFirstFilledComputation (model : FlatModel) where
  private mk ::
  target : FlatFieldDecl
  source : CheckedStarFieldPath model
  targetGroup : GroupPath
  targetCarrier : target.supportsMmDateFragmentFirstFilled = true
  targetFixed : target.repeatableScope = []
  targetOwnedByGroup : target.groupPath = targetGroup
  sourceCarrier : source.declaration.supportsMmDateFragmentFirstFilled = true
  sourceDirectSingleStar : source.isDirectSingleStar = true

/-- Check the exact externally measured DateFragment computation shape. Wider formats, operands, nesting, validation use, and target application remain outside this boundary. -/
def checkDateFragmentFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except DateFragmentFirstFilledComputationElabError
      (CheckedDateFragmentFirstFilledComputation model) := do
  let source ← elaborateStarFieldPath model declaringGroup authored
    |>.mapError .source
  let target ← model.lookupUniqueId targetField |>.mapError .target
  if hGroup : target.groupPath = declaringGroup then
    if hFixed : target.repeatableScope = [] then
      if hTarget : target.supportsMmDateFragmentFirstFilled = true then
        if hSource :
            source.declaration.supportsMmDateFragmentFirstFilled = true then
          if hShape : source.isDirectSingleStar = true then
            pure {
              target
              source
              targetGroup := declaringGroup
              targetCarrier := hTarget
              targetFixed := hFixed
              targetOwnedByGroup := hGroup
              sourceCarrier := hSource
              sourceDirectSingleStar := hShape
            }
          else
            throw (.sourceShape source.declaration.path)
        else
          throw (.sourceCarrier source.declaration.path)
      else
        throw (.targetCarrier target.path)
    else
      throw (.targetRepeatable target.path)
  else
    throw (.targetGroup target.groupPath declaringGroup)

/-- Project one checked DateFragment cell to the token consumed by the shared first-filled scan. The reviewed row establishes the `MM` output value, not whether the engine copies or renders it. -/
def dateFragmentFirstFilledCellAt
    (addressed : CheckedAddressedCell) : ValueListCell .token :=
  match observeCell .computation addressed.cell, addressed.stored with
  | .value (.temporal (.date _ _ _)), some token => .present token
  | .value _, _ => .unknown .malformed
  | .empty, _ => .empty
  | .unknown cause, _ | .poison cause, _ => .unknown cause

namespace CheckedDateFragmentFirstFilledComputation

/-- Execute the checked source over immutable rows and retain only the measured value/clear/poison result boundary. -/
def execute (operation : CheckedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except CheckedStarDocumentError TokenComputationResult := do
  let resolved ← operation.source.resolveCheckedField input []
  let side : ResolvedValueListSide .token := {
    cells := resolved.cells.map dateFragmentFirstFilledCellAt
    hasUninstantiatedTail := resolved.topology.domain.hasOpenTail
    hasHaving := false
  }
  pure (evalFirstFilledToken side).asComputationResult

end CheckedDateFragmentFirstFilledComputation

end A12Kernel
