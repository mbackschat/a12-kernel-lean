import A12Kernel.Elaboration.ConstructedDateDifferenceEvaluation

/-! # Checked constructed-Date execution laws -/

namespace A12Kernel

/-- The omitted-year form cannot consult document state for its injected model Base Year. -/
theorem checkedConstructedDateBaseYear_read
    (year : Int) (phase : Phase) (input : CheckedDocument model)
    (world : Option World) :
    CheckedConstructedDateYear.read (.baseYear year) phase input world =
      .ok (.value year) := by
  rfl

/-- A checked quoted constant is fixed input and cannot consult document state. -/
theorem checkedConstructedDateConstant_read
    (value : Int) (phase : Phase) (input : CheckedDocument model)
    (world : Option World) :
    CheckedConstructedDateSource.read
        (.constant value) phase input world =
      .ok (.value value) := by
  rfl

/-- A fresh or shifted Date value exposes its retained instant directly to temporal
    comparison and preserves its missing provenance. Calendar parts are not used to
    reconstruct the instant at this boundary. -/
@[simp] theorem constructedDateValue_comparisonOperand_value
    (instant : Instant) (parts : DateParts) (notGiven : Bool) :
    ConstructedDateValue.comparisonOperand (.value instant parts notGiven) =
      .value instant (!notGiven) := by
  rfl

/-- Constructed-Date non-values retain the established temporal-comparison boundary:
    semantic absence is not evaluated, while a formal cause stays UNKNOWN. -/
theorem constructedDateValue_comparisonOperand_nonvalues
    (notGiven : Bool) (cause : FormalCause) :
    ConstructedDateValue.comparisonOperand (.noValue notGiven) = .notEvaluated ∧
      ConstructedDateValue.comparisonOperand (.unavailable cause) = .unknown cause := by
  constructor <;> rfl

/-- A real fresh construction resolves once and retains exactly the instant selected
    by its certified model-zone profile. -/
theorem checkedConstructedDateComponents_evaluateValue_real
    (checked : CheckedConstructedDateComponents model)
    (phase : Phase) (input : CheckedDocument model) (world : Option World)
    (parts : DateParts) (instant : Instant)
    (observed :
      checked.evaluateComponents phase input world =
        .ok (.resolved (.real parts)))
    (resolved :
      checked.resolveFreshInstant parts = .ok (some instant)) :
    checked.evaluateValue phase input world =
      .ok (.value instant parts false) := by
  unfold CheckedConstructedDateComponents.evaluateValue
    CheckedConstructedDateComponents.evaluateValueWith
  unfold CheckedConstructedDateComponents.evaluateComponents at observed
  rw [observed]
  simp only [bind, Except.bind, CheckedConstructedDateComponents.finishValue]
  have h := Except.ok.inj resolved
  simp only [ResolvedConstructedDateComponents.finishValue, h]
  rfl

/-- A checked Base-Year extraction delegates to its configured direct or range-selected Date source and cannot consult document state. -/
theorem checkedConstructedDateBaseYearExtractor_read
    (checked : CheckedConstructedDateBaseYearExtractor model)
    (phase : Phase) (input : CheckedDocument model) :
    checked.read phase input =
      .ok (.value
        (baseYearDateSourceNumericPart
          checked.year checked.source checked.part).num) := by
  rfl

/-- Dynamic `Today` has no implicit clock fallback. -/
theorem checkedConstructedDateTodayExtractor_requires_world
    (checked : CheckedConstructedDatePointInTimeExtractor model)
    (isToday : checked.point = .today) :
    checked.read none = .error .todayWorldRequired := by
  simp [CheckedConstructedDatePointInTimeExtractor.read, readConstructedDateClock, projectConstructedDateClock,
    ConstructedDateComponentFault.toEvaluationFault, isToday]
  rfl

/-- A resolved `Today` projects exactly the certified local calendar component. -/
theorem checkedConstructedDateTodayExtractor_read
    (checked : CheckedConstructedDatePointInTimeExtractor model)
    (world : World) (instant : Instant) (label : LegacyCalendarLabel)
    (isToday : checked.point = .today)
    (resolved : world.today? model.timeZoneId = some instant)
    (decoded : checked.profile.calendarLabel? instant = some label) :
    checked.read (some world) =
      .ok (.value (checked.part.extract label.parts).num) := by
  simp [CheckedConstructedDatePointInTimeExtractor.read, readConstructedDateClock, projectConstructedDateClock,
    ConstructedDateComponentFault.toEvaluationFault, isToday,
    CheckedConstructedDatePointInTimeExtractor.project, resolved, decoded]
  rfl

/-- Dynamic `Now` has no implicit clock fallback. -/
theorem checkedConstructedDateNowExtractor_requires_world
    (checked : CheckedConstructedDatePointInTimeExtractor model)
    (isNow : checked.point = .now) :
    checked.read none = .error .nowWorldRequired := by
  simp [CheckedConstructedDatePointInTimeExtractor.read, readConstructedDateClock, projectConstructedDateClock,
    ConstructedDateComponentFault.toEvaluationFault, isNow]
  rfl

/-- `Now` projects the retained exact world instant without consulting zone rules. -/
theorem checkedConstructedDateNowExtractor_read
    (checked : CheckedConstructedDatePointInTimeExtractor model)
    (world : World) (label : LegacyCalendarLabel)
    (isNow : checked.point = .now)
    (decoded : checked.profile.calendarLabel? world.now = some label) :
    checked.read (some world) =
      .ok (.value (checked.part.extract label.parts).num) := by
  simp [CheckedConstructedDatePointInTimeExtractor.read, readConstructedDateClock, projectConstructedDateClock,
    ConstructedDateComponentFault.toEvaluationFault,
    CheckedConstructedDatePointInTimeExtractor.project, isNow, decoded]
  rfl

/-- A reached checked String contributes its decoded and narrowed host-integer component. -/
@[simp] theorem checkedConstructedDateString_classify_value
    (checked : CheckedConstructedDateStringField model)
    (text : String) (amount : Int)
    (parsed : parseTemporalComponentInt32? text = some amount) :
    checked.classify (.value (.str text)) = .ok (.value amount) := by
  simp [CheckedConstructedDateStringField.classify, classifyConstructedDateString, parsed]
  rfl

/-- A reached `yyyy`-declared temporal field contributes the year parsed from its retained stored text; it does not silently become the `YearFromDate` projection. The hypothesis is the formal check's own format-family test on the observed **payload**, not the declaration, so this covers every declared kind the gate admits. -/
@[simp] theorem checkedConstructedDateYear_classify_value
    (checked : CheckedConstructedDateYearField model)
    (value : TemporalValue) (text : String) (amount : Nat)
    (holds : checked.source.holdsValue value = true)
    (parsed : parseAsciiNatural? text = some amount) :
    checked.classify (.value (.temporal value)) (some text) =
      .ok (.value amount) := by
  simp [CheckedConstructedDateYearField.classify, classifyConstructedDateYear, holds, parsed]
  rfl

/-- Direct temporal extraction preserves the distinction between an empty operand and one unavailable for an exact formal cause. -/
theorem checkedConstructedDateExtractor_classify_empty_unavailable
    (checked : CheckedConstructedDateExtractorField model)
    (cause : FormalCause) :
    checked.classify .empty = .ok .empty ∧
      checked.classify (.unknown cause) = .ok (.unavailable cause) ∧
      checked.classify (.poison cause) = .ok (.unavailable cause) := by
  constructor
  · rfl
  · constructor <;> rfl

/-- Computation poison at Century stops the split year before Short-Year is consulted. -/
theorem checkedConstructedDateCentury_read_unavailable
    (century shortYear : CheckedConstructedDateSource model)
    (phase : Phase) (computation : phase = .computation) (input : CheckedDocument model) (cause : FormalCause)
    (world : Option World)
    (observed :
      century.read phase input world = .ok (.unavailable cause)) :
    CheckedConstructedDateYear.read
        (.centuryAndShortYear century shortYear) phase input world =
      .ok (.unavailable cause) := by
  subst phase
  simp [CheckedConstructedDateYear.read, CheckedConstructedDateYear.readWith,
    CheckedConstructedDateYear.resolved, ResolvedConstructedDateYear.readWith, observed,
    bind, Except.bind, pure, Except.pure]

/-- Two reached split-year parts retain the zero-Century gate before decimal-place composition. -/
theorem checkedConstructedDateCentury_read_values
    (century shortYear : CheckedConstructedDateSource model)
    (phase : Phase) (input : CheckedDocument model)
    (world : Option World)
    (centuryValue shortYearValue : Int)
    (observedCentury :
      century.read phase input world = .ok (.value centuryValue))
    (observedShortYear :
      shortYear.read phase input world = .ok (.value shortYearValue)) :
    CheckedConstructedDateYear.read
        (.centuryAndShortYear century shortYear) phase input world =
      .ok (.value (if centuryValue == 0 then 0 else centuryValue * 100 + shortYearValue)) := by
  simp [CheckedConstructedDateYear.read, CheckedConstructedDateYear.readWith,
    CheckedConstructedDateYear.resolved, ResolvedConstructedDateYear.readWith, observedCentury, observedShortYear,
    bind, Except.bind, pure, Except.pure]

/-- A computation stops at a poisoned Day before either later component can be read, for
any effectful reader used by ordinary constructors or correlated filters (spec/05 §3). -/
theorem resolvedConstructedDateComponentsWith_day_unavailable
    {Source : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (source : ResolvedConstructedDateComponents Source)
    (readSource : Source → m CheckedConstructedDateComponent)
    (cause : FormalCause) (observed : readSource source.day = pure (.unavailable cause)) :
    source.evaluateComponentsWith readSource = pure (.unavailable cause) := by
  simp [ResolvedConstructedDateComponents.evaluateComponentsWith, observed]

/-- A reached Day poison stops the shared component fold, for immutable documents and scalar
expression contexts alike; the later Month and Year readers are arbitrary. -/
theorem checkedConstructedDateComponentsWith_day_unavailable
    {Source : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (checked : CheckedConstructedDateComponents model Source)
    (readSource : Source → m CheckedConstructedDateComponent)
    (cause : FormalCause) (observed : readSource checked.day = pure (.unavailable cause)) :
    checked.evaluateComponentsWith readSource = pure (.unavailable cause) := by
  exact resolvedConstructedDateComponentsWith_day_unavailable checked.resolved readSource cause observed

/-- The document reader specializes the shared ordered component fold. -/
theorem checkedConstructedDateComponents_day_unavailable
    (checked : CheckedConstructedDateComponents model)
    (phase : Phase) (computation : phase = .computation) (input : CheckedDocument model) (cause : FormalCause)
    (world : Option World)
    (observed : checked.day.read phase input world = .ok (.unavailable cause)) :
    checked.evaluate phase input world = .ok (.unavailable cause) := by
  subst phase
  simp [CheckedConstructedDateComponents.evaluate, CheckedConstructedDateComponents.evaluateComponents,
    checkedConstructedDateComponentsWith_day_unavailable checked
      (fun source => source.read .computation input world) cause observed,
    CheckedConstructedDateComponents.applyProfileReality]
  rfl

/-- Resolving cause-free checked components cannot manufacture the cause-free UNKNOWN fallback. -/
theorem constructedDateObservation_ofAvailableComponents_ne_unknown
    (day month year : Option Int) :
    ConstructedDateObservation.ofAvailableComponents day month year ≠
      .resolved .unknown := by
  cases day <;> cases month <;> cases year <;>
    simp [ConstructedDateObservation.ofAvailableComponents,
      classifyDateConstruction3]
  split <;> simp_all

/-- Profile reality can retain a cause-free UNKNOWN only when its input already was
    UNKNOWN; profile selection never manufactures that fallback. -/
@[simp] theorem checkedConstructedDate_applyProfileReality_eq_unknown_iff
    (checked : CheckedConstructedDateComponents model)
    (observation : ConstructedDateObservation) :
    checked.applyProfileReality observation =
        .ok (.resolved .unknown) ↔
      observation = .resolved .unknown := by
  cases observation with
  | unavailable cause =>
      simp [CheckedConstructedDateComponents.applyProfileReality,
        pure, Except.pure]
  | resolved result =>
      cases result with
      | real parts =>
          cases accepted : checked.profileAcceptsDate parts with
          | error error =>
              simp [CheckedConstructedDateComponents.applyProfileReality,
                accepted, bind, Except.bind]
          | ok isReal =>
              cases isReal <;>
                simp [CheckedConstructedDateComponents.applyProfileReality,
                  accepted, bind, Except.bind, pure, Except.pure]
      | incomplete | unreal | unknown =>
          simp [CheckedConstructedDateComponents.applyProfileReality,
            pure, Except.pure]

/-- Component reads route every reached formal cause through `unavailable`; their
    resolved branch therefore never contains the cause-free UNKNOWN fallback. -/
theorem checkedConstructedDateComponents_evaluateComponents_ne_resolved_unknown
    (checked : CheckedConstructedDateComponents model)
    (phase : Phase) (input : CheckedDocument model)
    (world : Option World) :
    checked.evaluateComponents phase input world ≠
      .ok (.resolved .unknown) := by
  unfold CheckedConstructedDateComponents.evaluateComponents
    CheckedConstructedDateComponents.evaluateComponentsWith
    ResolvedConstructedDateComponents.evaluateComponentsWith
    CheckedConstructedDateComponents.resolved
  dsimp only
  simp only [bind, Except.bind, discard, Functor.mapConst, pure, Except.pure]
  generalize dayRead :
    CheckedConstructedDateSource.read checked.day phase input world = day
  cases day with
  | error error => simp
  | ok day =>
      cases day with
      | unavailable cause =>
          simp
          split
          · cases hm : checked.month.read phase input world <;>
              cases hy : checked.year.resolved.readWith (fun source => source.read phase input world) phase <;>
              simp_all [Except.map]
          · simp
      | value amount =>
          generalize monthRead :
            CheckedConstructedDateSource.read checked.month phase input world = month
          cases month with
          | error error => simp
          | ok month =>
              cases month with
              | unavailable cause =>
                  simp
                  split
                  · cases hy : checked.year.resolved.readWith (fun source => source.read phase input world) phase <;>
                      simp_all [Except.map]
                  · simp
              | value amount =>
                  generalize yearRead :
                    ResolvedConstructedDateYear.readWith
                      checked.year.resolved (fun source => source.read phase input world) phase = year
                  cases year with
                  | error error => simp
                  | ok year =>
                      cases year <;>
                        simp [constructedDateObservation_ofAvailableComponents_ne_unknown]
              | empty =>
                  generalize yearRead :
                    ResolvedConstructedDateYear.readWith
                      checked.year.resolved (fun source => source.read phase input world) phase = year
                  cases year with
                  | error error => simp
                  | ok year =>
                      cases year <;>
                        simp [constructedDateObservation_ofAvailableComponents_ne_unknown]
      | empty =>
          generalize monthRead :
            CheckedConstructedDateSource.read checked.month phase input world = month
          cases month with
          | error error => simp
          | ok month =>
              cases month with
              | unavailable cause =>
                  simp
                  split
                  · cases hy : checked.year.resolved.readWith (fun source => source.read phase input world) phase <;>
                      simp_all [Except.map]
                  · simp
              | value amount =>
                  generalize yearRead :
                    ResolvedConstructedDateYear.readWith
                      checked.year.resolved (fun source => source.read phase input world) phase = year
                  cases year with
                  | error error => simp
                  | ok year =>
                      cases year <;>
                        simp [constructedDateObservation_ofAvailableComponents_ne_unknown]
              | empty =>
                  generalize yearRead :
                    ResolvedConstructedDateYear.readWith
                      checked.year.resolved (fun source => source.read phase input world) phase = year
                  cases year with
                  | error error => simp
                  | ok year =>
                      cases year <;>
                        simp [constructedDateObservation_ofAvailableComponents_ne_unknown]

/-- Profile application cannot introduce the cause-free UNKNOWN fallback after
    checked component execution. -/
theorem checkedConstructedDateComponents_ne_resolved_unknown
    (checked : CheckedConstructedDateComponents model)
    (phase : Phase) (input : CheckedDocument model)
    (world : Option World) :
    checked.evaluate phase input world ≠ .ok (.resolved .unknown) := by
  intro resolvedUnknown
  unfold CheckedConstructedDateComponents.evaluate at resolvedUnknown
  generalize observed :
    checked.evaluateComponents phase input world = result at resolvedUnknown
  cases result with
  | error error => simp [bind, Except.bind] at resolvedUnknown
  | ok observation =>
      have observationUnknown :
          observation = .resolved .unknown :=
        (checkedConstructedDate_applyProfileReality_eq_unknown_iff
          checked observation).mp resolvedUnknown
      subst observation
      exact
        checkedConstructedDateComponents_evaluateComponents_ne_resolved_unknown
          checked phase input world observed

/-- Validation and numeric consumers retain the same exact formal cause instead of collapsing it into their cause-free UNKNOWN cases. -/
theorem constructedDateObservation_consumers_preserve_unavailable
    (cause : FormalCause) (part : DateNumericPart) :
    ConstructedDateObservation.validVerdict (.unavailable cause) =
        .error cause ∧
      ConstructedDateObservation.invalidVerdict (.unavailable cause) =
        .error cause ∧
      ConstructedDateObservation.numericPart (.unavailable cause) part =
        .error cause := by
  simp [ConstructedDateObservation.validVerdict,
    ConstructedDateObservation.invalidVerdict,
    ConstructedDateObservation.numericPart]

/-- All three default-cutover shifts preserve a checked formal cause exactly. -/
theorem constructedDateObservation_shifts_preserve_unavailable
    (cause : FormalCause) (offset : Int) :
    ConstructedDateObservation.addLegacyDays? (.unavailable cause) offset =
        some (.unavailable cause) ∧
      ConstructedDateObservation.addLegacyMonths? (.unavailable cause) offset =
        some (.unavailable cause) ∧
      ConstructedDateObservation.addLegacyYears? (.unavailable cause) offset =
        some (.unavailable cause) := by
  simp [ConstructedDateObservation.addLegacyDays?,
    ConstructedDateObservation.addLegacyMonths?,
    ConstructedDateObservation.addLegacyYears?]

/-- Checked shift composition keeps the existing incomplete/unreal distinction. -/
theorem constructedDateObservation_shifts_preserve_resolved_nonvalues
    (offset : Int) :
    ConstructedDateObservation.addLegacyDays? (.resolved .incomplete) offset =
        some (.resolved .incomplete) ∧
      ConstructedDateObservation.addLegacyMonths? (.resolved .unreal) offset =
        some (.resolved .unreal) ∧
      ConstructedDateObservation.addLegacyYears? (.resolved .incomplete) offset =
        some (.resolved .incomplete) := by
  simp [ConstructedDateObservation.addLegacyDays?,
    ConstructedDateObservation.addLegacyMonths?,
    ConstructedDateObservation.addLegacyYears?,
    DateConstructionResult.addLegacyDays?,
    DateConstructionResult.addLegacyMonths?,
    DateConstructionResult.addLegacyYears?]

/-- A reached source cause decides the generated source-before-amount composition without any hypothesis about the checked amount or its document cell. -/
theorem checkedConstructedDateShift_source_unavailable
    (checked : CheckedConstructedDateShift model)
    (phase : Phase) (input : CheckedDocument model)
    (world : Option World)
    (cause : FormalCause)
    (source :
      checked.source.evaluateValue phase input world =
        .ok (.unavailable cause)) :
    checked.evaluate phase input world = .ok (.unavailable cause) := by
  simp [CheckedConstructedDateShift.evaluate, source]

/-- A reached inner-shift cause decides nested generated evaluation before the outer
    amount is read. -/
theorem checkedConstructedDateShift_evaluateThen_inner_unavailable
    (checked : CheckedConstructedDateShift model)
    (nextUnit : DateShiftUnit)
    (nextAmount : CheckedTemporalShiftAmount model)
    (phase : Phase) (input : CheckedDocument model)
    (world : Option World) (cause : FormalCause)
    (inner :
      checked.evaluate phase input world = .ok (.unavailable cause)) :
    checked.evaluateThen nextUnit nextAmount phase input world =
      .ok (.unavailable cause) := by
  simp [CheckedConstructedDateShift.evaluateThen, inner]

/-- Arithmetic domain failure after a real source remains cause-free no-value; it is not a zero shift and does not acquire omission provenance. -/
theorem checkedConstructedDateShift_real_domain_failure
    (checked : CheckedConstructedDateShift model)
    (phase : Phase) (input : CheckedDocument model)
    (instant : Instant) (parts : DateParts)
    (world : Option World)
    (source :
      checked.source.evaluateValue phase input world =
        .ok (.value instant parts false))
    (amount :
      checked.amount.read phase input = .ok (.ok .notEvaluated)) :
    checked.evaluate phase input world = .ok (.noValue false) := by
  unfold CheckedConstructedDateShift.evaluate
  rw [source]
  rw [amount]
  rfl

/-- In computation, a reached first-source cause decides the difference before the second source (spec/05 §2). -/
theorem checkedConstructedDateDifference_first_unavailable
    (checked : CheckedConstructedDateDifference model)
    (input : CheckedDocument model)
    (world : Option World)
    (cause : FormalCause)
    (first :
      checked.first.evaluate .computation input world = .ok (.unavailable cause)) :
    checked.evaluate .computation input world = .ok (.error cause) := by
  simp [CheckedConstructedDateDifference.evaluate, readTemporalPair, readTemporalPairWith, bind, Except.bind, pure, Except.pure, Except.mapError, first]

/-- Once the first source resolves, the second source's exact reached formal cause is retained. -/
theorem checkedConstructedDateDifference_second_unavailable
    (checked : CheckedConstructedDateDifference model)
    (phase : Phase) (input : CheckedDocument model)
    (world : Option World)
    (firstResult : DateConstructionResult) (cause : FormalCause)
    (first :
      checked.first.evaluate phase input world = .ok (.resolved firstResult))
    (second :
      checked.second.evaluate phase input world = .ok (.unavailable cause)) :
    checked.evaluate phase input world = .ok (.error cause) := by
  cases phase <;> simp [CheckedConstructedDateDifference.evaluate, readTemporalPair, readTemporalPairWith, bind, Except.bind, pure, Except.pure, Except.mapError, first, second]

/-- A structural first-source failure stops before the second source and remains outside semantic unreal. -/
theorem checkedConstructedDateDifference_first_fault
    (checked : CheckedConstructedDateDifference model)
    (phase : Phase) (input : CheckedDocument model) (world : Option World)
    (error : ConstructedDateEvaluationFault)
    (first : checked.first.evaluate phase input world = .error error) :
    checked.evaluate phase input world = .error (.source error) := by
  simp [CheckedConstructedDateDifference.evaluate, readTemporalPair, readTemporalPairWith, bind, Except.bind, Except.mapError, first]

/-- Both constructed sources necessarily carry the same selected profile because they were checked against one model zone id. -/
theorem checkedConstructedDateDifference_profiles_eq
    (checked : CheckedConstructedDateDifference model) :
    checked.first.profile = checked.second.profile := by
  have selected :
      some checked.first.profile = some checked.second.profile :=
    checked.first.profileSelected.symm.trans
      checked.second.profileSelected
  exact Option.some.inj selected

/-- Every unit is now available for each implemented constructed-Date profile. The certificate still prevents silent widening when another profile is added. -/
@[simp] theorem concreteProfile_admitsConstructedDateDifference
    (profile : ModelZone.ConcreteProfile) (unit : DateShiftUnit) :
    profile.admitsConstructedDateDifference unit = true := by
  cases profile <;> cases unit <;> rfl

/-- Widening the checked profile gate leaves all three UTC/GMT result branches definitionally unchanged. -/
theorem checkedConstructedDateDifference_utc_unchanged
    (unit : DateShiftUnit) (first second : DateConstructionResult) :
    CheckedConstructedDateDifference.differenceResolved?
        .utc unit first second =
      match unit with
      | .days => first.differenceLegacyDays? second
      | .months => first.differenceLegacy? .months second
      | .years => first.differenceLegacy? .years second := by
  cases unit <;> rfl

/-- Computation stops at the first shifted source's formal cause (spec/05 §2). -/
theorem checkedConstructedDateShift_difference_first_unavailable
    (checked : CheckedConstructedDateShift model)
    (other : CheckedConstructedDateComponents model)
    (unit : DateShiftUnit)
    (unitAdmitted :
      checked.source.profile.admitsConstructedDateDifference unit = true)
    (input : CheckedDocument model)
    (world : Option World) (cause : FormalCause)
    (shift :
      checked.evaluate .computation input world = .ok (.unavailable cause)) :
    checked.evaluateDifferenceWith other .first unit unitAdmitted
        .computation input world =
      .ok (.error cause) := by
  simp [CheckedConstructedDateShift.evaluateDifferenceWith, readTemporalPair, readTemporalPairWith, bind, Except.bind, pure, Except.pure, Except.mapError, shift]

/-- Computation stops at the first constructed source's formal cause (spec/05 §2). -/
theorem checkedConstructedDateShift_difference_second_constructed_unavailable
    (checked : CheckedConstructedDateShift model)
    (other : CheckedConstructedDateComponents model)
    (unit : DateShiftUnit)
    (unitAdmitted :
      checked.source.profile.admitsConstructedDateDifference unit = true)
    (input : CheckedDocument model)
    (world : Option World) (cause : FormalCause)
    (constructed :
      other.evaluateValue .computation input world = .ok (.unavailable cause)) :
    checked.evaluateDifferenceWith other .second unit unitAdmitted
        .computation input world =
      .ok (.error cause) := by
  simp [CheckedConstructedDateShift.evaluateDifferenceWith, readTemporalPair, readTemporalPairWith, bind, Except.bind, pure, Except.pure, Except.mapError, constructed]

/-- The mixed difference's direct and shifted sources select the same concrete
    profile because both were checked against one model zone id. -/
theorem checkedConstructedDateShift_difference_profiles_eq
    (checked : CheckedConstructedDateShift model)
    (other : CheckedConstructedDateComponents model) :
    checked.source.profile = other.profile := by
  have selected :
      some checked.source.profile = some other.profile :=
    checked.source.profileSelected.symm.trans other.profileSelected
  exact Option.some.inj selected

end A12Kernel
