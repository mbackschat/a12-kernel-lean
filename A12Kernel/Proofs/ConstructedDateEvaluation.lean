import A12Kernel.Elaboration.ConstructedDateEvaluation

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
  simp [CheckedConstructedDatePointInTimeExtractor.read, isToday]
  rfl

/-- A resolved `Today` projects exactly the certified local calendar component. -/
theorem checkedConstructedDateTodayExtractor_read
    (checked : CheckedConstructedDatePointInTimeExtractor model)
    (world : World) (instant : Instant) (date : FullDate)
    (isToday : checked.point = .today)
    (resolved : world.today? model.timeZoneId = some instant)
    (decoded : checked.profile.localDate? instant = some date) :
    checked.read (some world) =
      .ok (.value (checked.part.extract date.civil.parts).num) := by
  simp [CheckedConstructedDatePointInTimeExtractor.read, isToday,
    CheckedConstructedDatePointInTimeExtractor.project, resolved, decoded]
  rfl

/-- Dynamic `Now` has no implicit clock fallback. -/
theorem checkedConstructedDateNowExtractor_requires_world
    (checked : CheckedConstructedDatePointInTimeExtractor model)
    (isNow : checked.point = .now) :
    checked.read none = .error .nowWorldRequired := by
  simp [CheckedConstructedDatePointInTimeExtractor.read, isNow]
  rfl

/-- `Now` projects the retained exact world instant without consulting zone rules. -/
theorem checkedConstructedDateNowExtractor_read
    (checked : CheckedConstructedDatePointInTimeExtractor model)
    (world : World) (date : FullDate)
    (isNow : checked.point = .now)
    (decoded : checked.profile.localDate? world.now = some date) :
    checked.read (some world) =
      .ok (.value (checked.part.extract date.civil.parts).num) := by
  simp [CheckedConstructedDatePointInTimeExtractor.read,
    CheckedConstructedDatePointInTimeExtractor.project, isNow, decoded]
  rfl

/-- A reached checked digit String contributes its exact natural-number component without numeric truncation. -/
@[simp] theorem checkedConstructedDateString_classify_value
    (checked : CheckedConstructedDateStringField model)
    (text : String) (amount : Nat)
    (parsed : parseAsciiNatural? text = some amount) :
    checked.classify (.value (.str text)) = .ok (.value amount) := by
  simp [CheckedConstructedDateStringField.classify, parsed]
  rfl

/-- A reached exact-format Date field contributes the year parsed from its retained stored text; it does not silently become the `YearFromDate` projection. -/
@[simp] theorem checkedConstructedDateYear_classify_value
    (checked : CheckedConstructedDateYearField model)
    (value : TemporalValue) (text : String) (amount : Nat)
    (dateKind : value.kind = .date)
    (parsed : parseAsciiNatural? text = some amount) :
    checked.classify (.value (.temporal value)) (some text) =
      .ok (.value amount) := by
  simp [CheckedConstructedDateYearField.classify, dateKind, parsed]
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

/-- A formally unavailable Century stops the split year before Short-Year is consulted. -/
theorem checkedConstructedDateCentury_read_unavailable
    (century shortYear : CheckedConstructedDateSource model)
    (phase : Phase) (input : CheckedDocument model) (cause : FormalCause)
    (world : Option World)
    (observed :
      century.read phase input world = .ok (.unavailable cause)) :
    CheckedConstructedDateYear.read
        (.centuryAndShortYear century shortYear) phase input world =
      .ok (.unavailable cause) := by
  simp [CheckedConstructedDateYear.read, observed]

/-- Two reached fixed split-year parts compose by decimal place, not addition. -/
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
      .ok (.value (centuryValue * 100 + shortYearValue)) := by
  simp [CheckedConstructedDateYear.read, observedCentury, observedShortYear]

/-- A formally unavailable Day prevents every later component read. -/
theorem checkedConstructedDateComponents_day_unavailable
    (checked : CheckedConstructedDateComponents model)
    (phase : Phase) (input : CheckedDocument model) (cause : FormalCause)
    (world : Option World)
    (observed :
      checked.day.read phase input world = .ok (.unavailable cause)) :
    checked.evaluate phase input world = .ok (.unavailable cause) := by
  unfold CheckedConstructedDateComponents.evaluate
  rw [observed]

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

/-- Checked component execution routes every reached formal cause through `unavailable`; its resolved branch therefore never contains the cause-free UNKNOWN fallback. -/
theorem checkedConstructedDateComponents_ne_resolved_unknown
    (checked : CheckedConstructedDateComponents model)
    (phase : Phase) (input : CheckedDocument model)
    (world : Option World) :
    checked.evaluate phase input world ≠ .ok (.resolved .unknown) := by
  unfold CheckedConstructedDateComponents.evaluate
  generalize dayRead :
    CheckedConstructedDateSource.read checked.day phase input world = day
  cases day with
  | error error => simp
  | ok day =>
      cases day with
      | unavailable cause => simp
      | value amount =>
          generalize monthRead :
            CheckedConstructedDateSource.read checked.month phase input world = month
          cases month with
          | error error => simp
          | ok month =>
              cases month with
              | unavailable cause => simp
              | value amount =>
                  generalize yearRead :
                    CheckedConstructedDateYear.read
                      checked.year phase input world = year
                  cases year with
                  | error error => simp
                  | ok year =>
                      cases year <;>
                        simp [constructedDateObservation_ofAvailableComponents_ne_unknown]
              | empty =>
                  generalize yearRead :
                    CheckedConstructedDateYear.read
                      checked.year phase input world = year
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
              | unavailable cause => simp
              | value amount =>
                  generalize yearRead :
                    CheckedConstructedDateYear.read
                      checked.year phase input world = year
                  cases year with
                  | error error => simp
                  | ok year =>
                      cases year <;>
                        simp [constructedDateObservation_ofAvailableComponents_ne_unknown]
              | empty =>
                  generalize yearRead :
                    CheckedConstructedDateYear.read
                      checked.year phase input world = year
                  cases year with
                  | error error => simp
                  | ok year =>
                      cases year <;>
                        simp [constructedDateObservation_ofAvailableComponents_ne_unknown]

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
      checked.source.evaluate phase input world = .ok (.unavailable cause)) :
    checked.evaluate phase input world = .ok (.unavailable cause) := by
  simp [CheckedConstructedDateShift.evaluate, source]

/-- Arithmetic domain failure after a real source remains cause-free no-value; it is not a zero shift and does not acquire omission provenance. -/
theorem checkedConstructedDateShift_real_domain_failure
    (checked : CheckedConstructedDateShift model)
    (phase : Phase) (input : CheckedDocument model) (parts : DateParts)
    (world : Option World)
    (source :
      checked.source.evaluate phase input world =
        .ok (.resolved (.real parts)))
    (amount :
      checked.amount.read phase input = .ok (.ok .notEvaluated)) :
    checked.evaluate phase input world = .ok (.noValue false) := by
  unfold CheckedConstructedDateShift.evaluate
  rw [source]
  simp [amount, CheckedConstructedDateShift.applyAmount,
    CheckedConstructedDateShift.sourceNotGiven]
  rfl

/-- A reached first-source cause decides the generated two-source difference without any hypothesis about the second checked source. -/
theorem checkedConstructedDateDifference_first_unavailable
    (checked : CheckedConstructedDateDifference model)
    (phase : Phase) (input : CheckedDocument model)
    (world : Option World)
    (cause : FormalCause)
    (first :
      checked.first.evaluate phase input world = .ok (.unavailable cause)) :
    checked.evaluate phase input world = .ok (.error cause) := by
  simp [CheckedConstructedDateDifference.evaluate, first]

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
  simp [CheckedConstructedDateDifference.evaluate, first, second]

end A12Kernel
