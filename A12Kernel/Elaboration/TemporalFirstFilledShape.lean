import A12Kernel.Elaboration.FirstFilledFieldSource

/-! # Shared fixed-target temporal `FirstFilledValue` computation shape

One fixed target and one source, a direct single-level star or a direct list of plain nonrepeatable
fields, sharing a completed scalar temporal or DateRange profile. A DateRange list is the direct
DateRange carrier's, which owns its measured profile classes, so this shape admits a list only over the
scalar temporal profiles. -/

namespace A12Kernel

/-- Completed scalar temporal and DateRange declaration profiles sharing the fixed-target computation shape. Additional policies remain excluded.

One of those exclusions is now known legal rather than undecided, and is named so its absence is not
read as a gate. A **partially known** Date — a full-format DATE declaration carrying `DAY_OPTIONAL`,
`MONTH_OPTIONAL` or `YEAR_OPTIONAL` — is admitted as a `FirstFilledValue` operand on every precision,
measured against a full-precision control across the family's five field-list operators
([inbound](../../docs/SOURCES.md#inbound-2026-09-07-dispositions)). The split runs three against two:
the extrema and the distinct count refuse `MVK_PARTIAL_DATE_NOT_ALLOWED` and own that gate, while
uniqueness and this operator accept them. The two `fullDate…` carriers below are full-precision profiles,
so this certificate does not reach a partial one at all — it neither admits nor refuses it, and the
silence is carrier coverage rather than a gate. An extension that adds the precision must therefore
widen the carrier set, not add a check. -/
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

/-- Classify only the completed temporal declaration profiles.

    **The three scalar arms read the declared component set and format, never the declared kind.**
    That is the measured Kernel rule at this position: a DATE-declared field whose components and
    format are the clock's takes a clock value exactly as a TIME-declared one does, and a
    TIME-declared field spelled `yyyy-MM-dd` takes a Date
    ([checkpoint](../../docs/SOURCES.md#src-temporal-computed-target-gate-reads-format-not-kind)).
    Keying on the kind here was one mechanism producing the same over-refusal at every scalar
    temporal first-filled carrier, so it is corrected once rather than per carrier.

    `DATE_RANGE` stays keyed on its kind, and correctly: it is the one kind whose format is
    allowlisted as a `(format, separator)` **pair** rather than as a bare format string, so its
    profile genuinely cannot be read off a format alone. Date profiles with optional pre-1900
    checking remain outside until checked temporal input represents that declaration-owned source
    check.

    A DateFragment is a component-omitting Date: its declared components are the ones its format
    names, at full precision, as the reader decodes a `DateFragmentType` and as the Kernel reads it
    ([checkpoint](../../docs/sources/temporal-and-message-probes.md#src-partial-date-presence)). A
    Date at a partial precision is a partially known full-format Date, never a fragment, so it stays
    outside. -/
def FlatFieldDecl.temporalFirstFilledStarCarrier?
    (declaration : FlatFieldDecl) : Option TemporalFirstFilledStarCarrier :=
  match declaration.policy.kind, declaration.toTemporalTargetPolicy?,
      declaration.toDateRangeDeclarationPolicy? with
  | .temporal _ components, some policy, _ =>
      if components == TemporalComponents.time then
        if policy.format == "HH:mm:ss" then some .timeHms else none
      else if components == TemporalComponents.now then
        if policy.format == "yyyy-MM-dd'T'HH:mm:ss" then some .dateTimeIso else none
      else if policy.partialMode != .full || policy.youngerThan1900Check then
        none
      else
        let carrier? : Option TemporalFirstFilledStarCarrier := match policy.format with
          | "MM" => some .monthFragment
          | "yyyy" => some .yearFragment
          | "yyyy-MM" => some .yearMonthFragment
          | "MM-dd" => some .monthDayFragment
          | "yyyy-MM-dd" => some .fullDateIso
          | "dd.MM.yyyy" => some .fullDateDotted
          | _ => none
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

/-- Whether a target carrier accepts a source carrier. A DateRange target accepts every profile exposing its own declared component set, which is the Kernel's own comparability gate; every other carrier requires identity because no crossing is measured for it. -/
def TemporalFirstFilledStarCarrier.acceptsSource
    (target source : TemporalFirstFilledStarCarrier) : Bool :=
  match target.dateRangeComponents?, source.dateRangeComponents? with
  | some targetComponents, some sourceComponents =>
      targetComponents == sourceComponents
  | _, _ => target == source

inductive TemporalFirstFilledShapeElabError where
  | target (cause : ResolveError)
  | targetRepeatable (path : List String)
  | targetCarrier (path : List String)
  | source (cause : StarPathElabError)
  | sourceCarrier (path : List String)
  | sourceShape (path : List String)
  /-- A list source the shared entity list or its plain-field reading refuses. -/
  | list (cause : FirstFilledListElabError)
  /-- A list source naming the target itself. -/
  | targetSelfReference (path : List String)
  deriving Repr, DecidableEq

/-- One fixed target and one source sharing a completed scalar temporal or DateRange carrier.

The declaring group is retained because a consumer needs the authored declaration site, **not** because it constrains where the target may sit, and not because it is always the operand's resolution base — an absolute operand resolves from the model root regardless of it. This family carries no placement gate: its target is always fixed and its source is a star aggregate or a list of nonrepeatable fields, so no iteration is ever derived and the Kernel's containment gate cannot fire. See [the fixed-target star placement checkpoint](../../docs/SOURCES.md#src-fixed-target-star-placement), which admits the star shape from an unrelated sibling group. -/
structure CheckedTemporalFirstFilledShape
    (model : FlatModel) (carrier : TemporalFirstFilledStarCarrier) where
  private mk ::
  target : FlatFieldDecl
  source : FirstFilledFieldSource model
  /-- The group the computation is declared in, which the target need not lie in or below. -/
  declaringGroup : GroupPath
  /-- The declaring group is a representable path, certified by the source's elaboration rather
  than re-tested here. Placement itself is unconstrained; only representability survives. -/
  declaringGroupValid : GroupPath.isValid declaringGroup = true
  /-- The source's own declared profile, which a DateRange crossing lets differ from the target's;
  every listed field repeats it. -/
  sourceProfile : TemporalFirstFilledStarCarrier
  targetCarrier : target.temporalFirstFilledStarCarrier? = some carrier
  targetFixed : target.repeatableScope = []
  sourceCarrier :
    source.declarations.all (·.temporalFirstFilledStarCarrier? == some sourceProfile) = true
  sourceAccepted : carrier.acceptsSource sourceProfile = true
  sourceShape : source.admittedShape = true
  excludesTarget : source.referencesField target.id = false

private def checkTemporalFirstFilledSourceAgainst (model : FlatModel)
    (target : FlatFieldDecl) (carrier : TemporalFirstFilledStarCarrier)
    (declaringGroup : GroupPath) (declaringGroupValid : GroupPath.isValid declaringGroup = true)
    (source : FirstFilledFieldSource model) :
    Except TemporalFirstFilledShapeElabError (CheckedTemporalFirstFilledShape model carrier) := do
  if hFixed : target.repeatableScope = [] then
    if hTarget : target.temporalFirstFilledStarCarrier? = some carrier then
      match source.declarations with
      | [] => throw (.sourceShape target.path)
      | first :: _ =>
        match first.temporalFirstFilledStarCarrier? with
        | none => throw (.sourceCarrier first.path)
        | some sourceProfile =>
          if hSource : source.declarations.all
              (·.temporalFirstFilledStarCarrier? == some sourceProfile) = true then
            if hAccepted : carrier.acceptsSource sourceProfile = true then
              if hShape : source.admittedShape = true then
                if hExcludes : source.referencesField target.id = false then
                  pure {
                    target, source, declaringGroup, declaringGroupValid, sourceProfile
                    targetCarrier := hTarget
                    targetFixed := hFixed
                    sourceCarrier := hSource
                    sourceAccepted := hAccepted
                    sourceShape := hShape
                    excludesTarget := hExcludes }
                else throw (.targetSelfReference target.path)
              else throw (.sourceShape first.path)
            else throw (.sourceCarrier first.path)
          else
            -- A list whose fields do not all repeat the first's profile. Each profile has one
            -- format, so two differing profiles either differ in format or share one across kinds.
            -- The Kernel refuses a differing format on the pairs measured
            -- (`MVK_VARYING_TYPES_NOT_ALLOWED`, docs/sources/static-admission-and-class-probes.md#src-first-filled-reads-the-format-string)
            -- and admits a shared one across kinds, which this carrier set does not represent;
            -- neither claims a Kernel class here.
            throw (.sourceCarrier ((source.declarations.find?
              (·.temporalFirstFilledStarCarrier? != some sourceProfile)).map (·.path) |>.getD first.path))
    else throw (.targetCarrier target.path)
  else throw (.targetRepeatable target.path)

/-- Check the target and source shared by the completed DateFragment, full-Date, Time, DateTime, and DateRange computations. Runtime payload and target-policy evaluation remain carrier-owned, and a list over a DateRange profile is refused here because the direct DateRange carrier owns it. -/
def checkTemporalFirstFilledShape
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceFirstFilledSource) (carrier : TemporalFirstFilledStarCarrier) :
    Except TemporalFirstFilledShapeElabError
      (CheckedTemporalFirstFilledShape model carrier) := do
  match authored with
  | .star path =>
    match hStar : elaborateStarFieldPath model declaringGroup path with
    | .error cause => .error (.source cause)
    | .ok source => do
      let target ← model.lookupUniqueId targetField |>.mapError .target
      -- No placement test. `elaborateStarFieldPath` above already rejects an unrepresentable
      -- declaring group, and placement itself is unconstrained for this shape: a fixed target under
      -- a star aggregate derives no iteration, so the Kernel admits it from an unrelated sibling group.
      checkTemporalFirstFilledSourceAgainst model target carrier declaringGroup
        (elaborateStarFieldPath_declaringGroupValid hStar) (.star source)
  | .list list => do
    -- The shape resolves first, placed at the target's group as on every measured computation
    -- carrier, and the target after it, as the direct DateRange list does.
    let targetGroup :=
      ((model.lookupUniqueId targetField).toOption.map (·.groupPath)).getD declaringGroup
    let checked ← elaborateFirstFilledFieldList model declaringGroup targetGroup list
      |>.mapError .list
    let target ← model.lookupUniqueId targetField |>.mapError .target
    if carrier.dateRangeComponents?.isSome then throw (.sourceShape target.path)
    checkTemporalFirstFilledSourceAgainst model target carrier declaringGroup
      checked.declaringGroupValid (.list checked.fields)

end A12Kernel
