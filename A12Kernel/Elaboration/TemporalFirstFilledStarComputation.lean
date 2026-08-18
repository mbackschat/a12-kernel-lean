import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.FirstFilledStarSource

/-! # Shared direct-star temporal `FirstFilledValue` computation shape -/

namespace A12Kernel

/-- Exact temporal computation carriers completed through the shared direct-star shape. This closed set does not include Time, DateTime, wider Date formats, or additional DateFragment policies. -/
inductive TemporalFirstFilledStarCarrier where
  | monthFragment
  | fullDateIso
  deriving Repr, DecidableEq

/-- Classify only the two completed temporal declaration profiles. Optional pre-1900 checking remains outside until checked temporal input represents that declaration-owned source check. -/
def FlatFieldDecl.temporalFirstFilledStarCarrier?
    (declaration : FlatFieldDecl) : Option TemporalFirstFilledStarCarrier :=
  match declaration.policy.kind, declaration.toTemporalTargetPolicy? with
  | .temporal .date components, some policy =>
      if components != TemporalComponents.fullDate ||
          policy.youngerThan1900Check then
        none
      else if policy.format == "MM" &&
          policy.partialMode == .yearOptional then
        some .monthFragment
      else if policy.format == "yyyy-MM-dd" &&
          policy.partialMode == .full then
        some .fullDateIso
      else
        none
  | _, _ => none

inductive TemporalFirstFilledStarComputationElabError where
  | target (cause : ResolveError)
  | targetGroup (actual expected : GroupPath)
  | targetRepeatable (path : List String)
  | targetCarrier (path : List String)
  | source (cause : StarPathElabError)
  | sourceCarrier (path : List String)
  | sourceShape (path : List String)
  deriving Repr, DecidableEq

/-- One fixed target and one direct single-level starred source with the same exact completed temporal carrier. -/
structure CheckedTemporalFirstFilledStarComputation
    (model : FlatModel) (carrier : TemporalFirstFilledStarCarrier) where
  private mk ::
  target : FlatFieldDecl
  source : CheckedStarFieldPath model
  targetGroup : GroupPath
  targetCarrier : target.temporalFirstFilledStarCarrier? = some carrier
  targetFixed : target.repeatableScope = []
  targetOwnedByGroup : target.groupPath = targetGroup
  sourceCarrier : source.declaration.temporalFirstFilledStarCarrier? = some carrier
  sourceDirectSingleStar : source.isDirectSingleStar = true

/-- Check the target/source/direct-star shape shared by the completed DateFragment and full-Date computations. Runtime payload and target-policy evaluation remain carrier-owned. -/
def checkTemporalFirstFilledStarComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) (carrier : TemporalFirstFilledStarCarrier) :
    Except TemporalFirstFilledStarComputationElabError
      (CheckedTemporalFirstFilledStarComputation model carrier) := do
  let source ← elaborateStarFieldPath model declaringGroup authored
    |>.mapError .source
  let target ← model.lookupUniqueId targetField |>.mapError .target
  if hGroup : target.groupPath = declaringGroup then
    if hFixed : target.repeatableScope = [] then
      if hTarget : target.temporalFirstFilledStarCarrier? = some carrier then
        if hSource :
            source.declaration.temporalFirstFilledStarCarrier? = some carrier then
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

end A12Kernel
