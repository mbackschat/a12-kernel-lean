import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.FirstFilledStarSource

/-! # Shared direct-star temporal `FirstFilledValue` computation shape -/

namespace A12Kernel

/-- Completed scalar temporal and DateRange declaration profiles sharing the direct-star computation shape. Additional policies remain excluded. -/
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
  | dateRangeYearFragment
  | dateRangeYearMonthFragment
  | dateRangeMonthFragment
  | dateRangeMonthDayFragment
  | dateRangeMonthConcatenated
  | dateRangeDayMonthDotted
  deriving Repr, DecidableEq

/-- Whether one shared temporal first-filled carrier is one of the four exact DateFragment profiles. -/
def TemporalFirstFilledStarCarrier.isDateFragment :
    TemporalFirstFilledStarCarrier → Bool
  | .monthFragment | .yearFragment | .yearMonthFragment |
      .monthDayFragment => true
  | _ => false

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
      match DateRangeInputFormat.ofPolicy? policy with
      | some (.exact .isoSlash) => some .dateRangeIsoSlash
      | some (.exact .dayMonthYearDash) => some .dateRangeDayMonthYearDash
      | some .yearFragment => some .dateRangeYearFragment
      | some .yearMonthFragment => some .dateRangeYearMonthFragment
      | some .yearlessMonth => some .dateRangeMonthFragment
      | some .yearlessMonthDay => some .dateRangeMonthDayFragment
      | some .yearlessMonthConcatenated => some .dateRangeMonthConcatenated
      | some .yearlessDayMonthDotted => some .dateRangeDayMonthDotted
      | none => none
  | _, _, _ => none

/-- The declared date-component set one DateRange carrier exposes. Two profiles exposing the same set are mutually assignable, and the target's own spelling decides the stored text inside the represented field-local fragment. -/
inductive DateRangeCarrierComponents where
  | yearMonthDay
  | year
  | yearMonth
  | month
  | monthDay
  deriving Repr, DecidableEq

/-- Project a DateRange carrier onto its declared component set. A scalar temporal carrier is not a DateRange carrier and exposes none. -/
def TemporalFirstFilledStarCarrier.dateRangeComponents? :
    TemporalFirstFilledStarCarrier → Option DateRangeCarrierComponents
  | .dateRangeIsoSlash | .dateRangeDayMonthYearDash => some .yearMonthDay
  | .dateRangeYearFragment => some .year
  | .dateRangeYearMonthFragment => some .yearMonth
  | .dateRangeMonthFragment | .dateRangeMonthConcatenated => some .month
  | .dateRangeMonthDayFragment | .dateRangeDayMonthDotted => some .monthDay
  | _ => none

/-- Whether a target carrier accepts a source carrier. A DateRange target accepts every profile exposing its own declared component set, which is the Kernel's own comparability gate; every other carrier requires identity because no crossing is measured for it. -/
def TemporalFirstFilledStarCarrier.acceptsSource
    (target source : TemporalFirstFilledStarCarrier) : Bool :=
  match target.dateRangeComponents?, source.dateRangeComponents? with
  | some targetComponents, some sourceComponents =>
      targetComponents == sourceComponents
  | _, _ => target == source

inductive TemporalFirstFilledStarComputationElabError where
  | target (cause : ResolveError)
  | targetRepeatable (path : List String)
  | targetCarrier (path : List String)
  | source (cause : StarPathElabError)
  | sourceCarrier (path : List String)
  | sourceShape (path : List String)
  deriving Repr, DecidableEq

/-- One fixed target and one direct single-level starred source with the same completed scalar temporal or DateRange carrier.

The declaring group is retained because it is the base the star operand resolved against, **not** because it constrains where the target may sit. This family carries no placement gate: its target is always fixed and its operand is always a star aggregate, so no iteration is ever derived and the Kernel's containment gate cannot fire. See [the fixed-target star placement checkpoint](../../docs/SOURCES.md#src-fixed-target-star-placement), which admits this exact shape from an unrelated sibling group. -/
structure CheckedTemporalFirstFilledStarComputation
    (model : FlatModel) (carrier : TemporalFirstFilledStarCarrier) where
  private mk ::
  target : FlatFieldDecl
  source : CheckedStarFieldPath model
  /-- The group the computation is declared in, which the target need not lie in or below. -/
  declaringGroup : GroupPath
  /-- The source's own declared profile, which a DateRange crossing lets differ from the target's. -/
  sourceProfile : TemporalFirstFilledStarCarrier
  targetCarrier : target.temporalFirstFilledStarCarrier? = some carrier
  targetFixed : target.repeatableScope = []
  sourceCarrier :
    source.declaration.temporalFirstFilledStarCarrier? = some sourceProfile
  sourceAccepted : carrier.acceptsSource sourceProfile = true
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
  -- No placement test. `elaborateStarFieldPath` above already rejects an unrepresentable declaring
  -- group, and placement itself is unconstrained for this shape: a fixed target under a star
  -- aggregate derives no iteration, so the Kernel admits it from an unrelated sibling group.
  if hFixed : target.repeatableScope = [] then
    if hTarget : target.temporalFirstFilledStarCarrier? = some carrier then
      match hSource : source.declaration.temporalFirstFilledStarCarrier? with
      | none => throw (.sourceCarrier source.declaration.path)
      | some sourceProfile =>
        if hAccepted : carrier.acceptsSource sourceProfile = true then
          if hShape : source.isDirectSingleStar = true then
            pure {
              target
              source
              declaringGroup
              sourceProfile
              targetCarrier := hTarget
              targetFixed := hFixed
              sourceCarrier := hSource
              sourceAccepted := hAccepted
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

end A12Kernel
