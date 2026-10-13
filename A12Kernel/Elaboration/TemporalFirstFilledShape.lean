import A12Kernel.Elaboration.FirstFilledPlacement

/-! # Shared temporal `FirstFilledValue` carrier site

One placed target, fixed or repeatable, and its source sharing a completed scalar temporal or
DateRange profile, over the shared first-filled site. A DateRange list is the direct DateRange
carrier's, which owns its measured profile classes, so this site admits a list only over the scalar
temporal profiles. -/

namespace A12Kernel

/-- Scalar temporal and DateRange profiles sharing the first-filled site. Full-format Date
sources allow partial precision because selection completes their earliest day (spec/05, KF508);
the computation target still owes its separate full-precision target check. -/
inductive TemporalFirstFilledStarCarrier where
  | dateFragment (format : OmittingDateFormat)
  | fullDate (format : FullDateTargetFormat)
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

/-- Classify only the completed temporal declaration profiles.

    **The three scalar arms read the declared component set and format, never the declared kind.**
    That is the measured Kernel rule at this position: a DATE-declared field whose components and
    format are the clock's takes a clock value exactly as a TIME-declared one does, and a
    TIME-declared field spelled `yyyy-MM-dd` takes a Date
    ([checkpoint](../../docs/sources/repeatable-temporal-computation-probes.md#src-temporal-computed-target-gate-reads-format-not-kind)).
    Keying on the kind here was one mechanism producing the same over-refusal at every scalar
    temporal first-filled carrier, so it is corrected once rather than per carrier.

    `DATE_RANGE` stays keyed on its kind, and correctly: it is the one kind whose format is
    allowlisted as a `(format, separator)` **pair** rather than as a bare format string, so its
    profile genuinely cannot be read off a format alone. Scalar Date sources retain their pre-1900
    policy for the input classifier; targets apply their own policy after rendering, as the K11
    profile-completion capture separates source poison from target rejection
    ([checkpoint](../../docs/sources/repeatable-temporal-computation-probes.md#src-temporal-target-profiles-k11)).

    A DateFragment is a component-omitting Date: its declared components are the ones its format
    names, at full precision, as the reader decodes a `DateFragmentType` and as the Kernel reads it
    ([checkpoint](../../docs/sources/temporal-and-message-probes.md#src-partial-date-presence)). A
    Date at partial precision uses a full-format Date carrier, never a fragment (spec/05, KF508). -/
def FlatFieldDecl.temporalFirstFilledStarCarrier?
    (declaration : FlatFieldDecl) : Option TemporalFirstFilledStarCarrier :=
  match declaration.policy.kind, declaration.toTemporalTargetPolicy?,
      declaration.toDateRangeDeclarationPolicy? with
  | .temporal _ components, some policy, _ =>
      if components == TemporalComponents.time then
        if policy.format == "HH:mm:ss" then some .timeHms else none
      else if components == TemporalComponents.now then
        if policy.format == "yyyy-MM-dd'T'HH:mm:ss" then some .dateTimeIso else none
      else if policy.partialMode != .full &&
          (components != TemporalComponents.fullDate ||
            (FullDateTargetFormat.ofSource? policy.format).isNone) then
        none
      else
        let carrier? : Option TemporalFirstFilledStarCarrier :=
          match FullDateTargetFormat.ofSource? policy.format with
          | some format => some (.fullDate format)
          | none => (OmittingDateFormat.ofSource? policy.format).map .dateFragment
        if components == TemporalComponents.ofFormat policy.format then carrier? else none
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

/-- Pure Date profiles retain year presence separately from exact source-list spelling
(spec/05 comparison gate; K11 target-profile capture). -/
def TemporalFirstFilledStarCarrier.dateYearPresence? : TemporalFirstFilledStarCarrier → Option Bool
  | .dateFragment format => some format.carriesYear
  | .fullDate _ => some true
  | _ => none

/-- Target compatibility is distinct from the source list's exact-profile gate. Date values
may change spelling or precision; a Base Year bridges year presence (spec/05). -/
def TemporalFirstFilledStarCarrier.acceptsSource
    (target source : TemporalFirstFilledStarCarrier) (hasBaseYear : Bool) : Bool :=
  match target.dateYearPresence?, source.dateYearPresence? with
  | some targetYear, some sourceYear => hasBaseYear || targetYear == sourceYear
  | _, _ => match target.dateRangeComponents?, source.dateRangeComponents? with
    | some targetComponents, some sourceComponents => targetComponents == sourceComponents
    | _, _ => target == source

/-- A target declaration as a carrier whose target policy owns the pre-1900 check reads it: that
policy reports an earlier Date as errored rather than refusing the target, measured for a full-Date
copy at a fixed target ([checkpoint](../../docs/sources/computation-scheduling-probes.md#src-document-step-join)),
a Date constant at a repeatable one ([checkpoint](../../docs/sources/temporal-constant-and-base-year-probes.md#src-date-constant-pre-1900-target)),
and this operation at a repeatable one ([checkpoint](../../docs/sources/repeatable-temporal-computation-probes.md#src-full-date-repeatable-first-filled)).
A source keeps the check for formal input classification before selection. -/
def FlatFieldDecl.withoutBefore1900Check (declaration : FlatFieldDecl) : FlatFieldDecl :=
  { declaration with temporalTargetPolicy :=
      declaration.temporalTargetPolicy.map ({ · with youngerThan1900Check := false }) }

/-- The target as a carrier reads it: without the pre-1900 check when its own policy owns it. -/
def FlatFieldDecl.firstFilledTargetProfile (declaration : FlatFieldDecl)
    (ownsBefore1900 : Bool) : FlatFieldDecl :=
  if ownsBefore1900 then declaration.withoutBefore1900Check else declaration

/-- The temporal `FirstFilledValue` carriers, one per family. -/
inductive TemporalFirstFilledFamily where
  | time
  | dateTime
  | dateFragment
  | fullDate
  | dateRange
  deriving Repr, DecidableEq

/-- The carrier family a target selects, read off its profile as every carrier reads it: by format
and never by declared kind, so a DATE declared `HH:mm:ss` is a Time target as the Kernel measures it
([checkpoint](../../docs/sources/repeatable-temporal-computation-probes.md#src-temporal-computed-target-gate-reads-format-not-kind)). The
pre-1900 check is set aside for family choice alone; the source classifier and target policy retain
its phase-specific meaning. A declaration with no profile falls back on its declared kind, so the carrier
that kind names states the refusal. -/
def FlatFieldDecl.temporalFirstFilledFamily? (target : FlatFieldDecl) :
    Option TemporalFirstFilledFamily :=
  match target.withoutBefore1900Check.temporalFirstFilledStarCarrier?, target.policy.kind with
  | some .timeHms, _ => some .time
  | some .dateTimeIso, _ => some .dateTime
  | some (.fullDate _), _ => some .fullDate
  | some (.dateFragment _), _ => some .dateFragment
  | some _, _ => some .dateRange
  | none, .temporal .time _ => some .time
  | none, .temporal .dateTime _ => some .dateTime
  | none, .temporal .date _ => some .fullDate
  | none, .dateRange => some .dateRange
  | none, _ => none

inductive TemporalFirstFilledSiteElabError where
  | site (cause : FirstFilledPlacementElabError)
  | targetCarrier (path : List String)
  | sourceCarrier (path : List String)
  /-- A list over a DateRange profile, which the direct DateRange carrier owns. -/
  | sourceShape (path : List String)
  | targetSelfReference (path : List String)
  deriving Repr, DecidableEq

/-- One placed target, fixed or repeatable, and its source, sharing a completed scalar temporal or
DateRange carrier. Every source declaration repeats one exact profile; the target uses the separate
Date year-presence or DateRange component-set compatibility gate. -/
structure CheckedTemporalFirstFilledSite (model : FlatModel) where
  private mk ::
  site : CheckedFirstFilledSite model
  carrier : TemporalFirstFilledStarCarrier
  sourceProfile : TemporalFirstFilledStarCarrier
  /-- Whether the carrier's target policy owns the target's pre-1900 check. -/
  ownsBefore1900 : Bool
  targetCarrier :
    (site.target.firstFilledTargetProfile ownsBefore1900).temporalFirstFilledStarCarrier? = some carrier
  sourceCarrier :
    site.source.declarations.all (·.temporalFirstFilledStarCarrier? == some sourceProfile) = true
  sourceAccepted : carrier.acceptsSource sourceProfile model.hasBaseYear = true
  excludesTarget : site.referencesWith site.targetField (·.forbidsTarget site.targetField) = false

namespace CheckedTemporalFirstFilledSite

def referencesWith (shape : CheckedTemporalFirstFilledSite model) (field : FieldId)
    (filterReads : CorrelatedHaving → Bool) : Bool :=
  shape.site.referencesWith field filterReads

def referencesField (shape : CheckedTemporalFirstFilledSite model) (field : FieldId) : Bool :=
  shape.referencesWith field (·.referencesField field)

end CheckedTemporalFirstFilledSite

/-- Place the target and source, then check both carriers against the target's own profile, read
without the pre-1900 check when the calling carrier's target policy owns it. -/
def checkTemporalFirstFilledSite (model : FlatModel) (declaringGroup : GroupPath)
    (targetField : FieldId) (authored : SurfaceFirstFilledSource) (ownsBefore1900 : Bool := false) :
    Except TemporalFirstFilledSiteElabError (CheckedTemporalFirstFilledSite model) := do
  let site ← (checkFirstFilledSite model declaringGroup targetField authored).mapError .site
  match hTarget : (site.target.firstFilledTargetProfile ownsBefore1900).temporalFirstFilledStarCarrier? with
  | none => throw (.targetCarrier site.target.path)
  | some carrier =>
    let first := (site.source.declarations.head?).getD site.target
    match first.temporalFirstFilledStarCarrier? with
    | none => throw (.sourceCarrier first.path)
    | some sourceProfile =>
      if hSource : site.source.declarations.all
          (·.temporalFirstFilledStarCarrier? == some sourceProfile) = true then
        if hAccepted : carrier.acceptsSource sourceProfile model.hasBaseYear = true then
          if let .list _ := site.source then
            if carrier.dateRangeComponents?.isSome then throw (.sourceShape site.target.path)
          if hExcludes : site.referencesWith site.targetField (·.forbidsTarget site.targetField) = false then
            pure { site, carrier, sourceProfile, ownsBefore1900
                   targetCarrier := hTarget
                   sourceCarrier := hSource
                   sourceAccepted := hAccepted
                   excludesTarget := hExcludes }
          else throw (.targetSelfReference site.target.path)
        else throw (.sourceCarrier first.path)
      else
        -- Source-list spelling equality remains independent of target rendering compatibility
        -- (`MVK_VARYING_TYPES_NOT_ALLOWED`,
        -- docs/sources/static-admission-and-class-probes.md#src-first-filled-reads-the-format-string).
        throw (.sourceCarrier ((site.source.declarations.find?
          (·.temporalFirstFilledStarCarrier? != some sourceProfile)).map (·.path) |>.getD first.path))

end A12Kernel
