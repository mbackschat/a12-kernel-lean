import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.FirstFilledStarSource

/-! # Shared direct-star temporal `FirstFilledValue` computation shape -/

namespace A12Kernel

/-- Exact date-bearing and scalar temporal computation carriers completed through the shared direct-star shape. Additional policies remain excluded. -/
inductive TemporalFirstFilledStarCarrier where
  | monthFragment
  | yearFragment
  | yearMonthFragment
  | monthDayFragment
  | fullDateIso
  | fullDateDotted
  | timeHms
  | dateTimeIso
  | dateRangeIsoSlash
  | dateRangeDayMonthYearDash
  deriving Repr, DecidableEq

/-- Classify only the completed temporal declaration profiles. Date profiles with optional pre-1900 checking remain outside until checked temporal input represents that declaration-owned source check. -/
def FlatFieldDecl.temporalFirstFilledStarCarrier?
    (declaration : FlatFieldDecl) : Option TemporalFirstFilledStarCarrier :=
  match declaration.policy.kind, declaration.toTemporalTargetPolicy?,
      declaration.toDateRangeDeclarationPolicy? with
  | .temporal .date components, some policy, _ =>
      if components != TemporalComponents.fullDate ||
          policy.youngerThan1900Check then
        none
      else if policy.partialMode == .yearOptional then
        if policy.format == "MM" then
          some .monthFragment
        else if policy.format == "yyyy" then
          some .yearFragment
        else if policy.format == "yyyy-MM" then
          some .yearMonthFragment
        else if policy.format == "MM-dd" then
          some .monthDayFragment
        else
          none
      else if policy.partialMode == .full then
        if policy.format == "yyyy-MM-dd" then
          some .fullDateIso
        else if policy.format == "dd.MM.yyyy" then
          some .fullDateDotted
        else
          none
      else
        none
  | .temporal .time components, some policy, _ =>
      if components == TemporalComponents.time &&
          policy.format == "HH:mm:ss" then
        some .timeHms
      else
        none
  | .temporal .dateTime components, some policy, _ =>
      if components == TemporalComponents.now &&
          policy.format == "yyyy-MM-dd'T'HH:mm:ss" then
        some .dateTimeIso
      else
        none
  | .dateRange, _, some policy =>
      match DateRangeFormat.ofPolicy? policy with
      | some .isoSlash => some .dateRangeIsoSlash
      | some .dayMonthYearDash => some .dateRangeDayMonthYearDash
      | none => none
  | _, _, _ => none

inductive TemporalFirstFilledStarComputationElabError where
  | target (cause : ResolveError)
  | targetGroup (actual expected : GroupPath)
  | targetRepeatable (path : List String)
  | targetCarrier (path : List String)
  | source (cause : StarPathElabError)
  | sourceCarrier (path : List String)
  | sourceShape (path : List String)
  deriving Repr, DecidableEq

/-- One fixed target and one direct single-level starred source with the same exact completed date-bearing or scalar temporal carrier. -/
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

/-- Check the target/source/direct-star shape shared by the completed DateFragment, full-Date, Time, DateTime, and DateRange computations. Runtime payload and target-policy evaluation remain carrier-owned. -/
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
