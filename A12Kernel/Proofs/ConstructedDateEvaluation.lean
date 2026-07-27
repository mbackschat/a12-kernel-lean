import A12Kernel.Elaboration.ConstructedDateEvaluation

/-! # Checked constructed-Date execution laws -/

namespace A12Kernel

/-- The omitted-year form cannot consult document state for its injected model Base Year. -/
theorem checkedConstructedDateBaseYear_read
    (year : Int) (phase : Phase) (input : CheckedDocument model) :
    CheckedConstructedDateYear.read (.baseYear year) phase input =
      .ok (.value year) := by
  rfl

/-- A formally unavailable Century stops the split year before Short-Year is consulted. -/
theorem checkedConstructedDateCentury_read_unavailable
    (century shortYear : CheckedConstructedDateNumberField model)
    (phase : Phase) (input : CheckedDocument model) (cause : FormalCause)
    (observed :
      century.read phase input = .ok (.unavailable cause)) :
    CheckedConstructedDateYear.read
        (.centuryAndShortYear century shortYear) phase input =
      .ok (.unavailable cause) := by
  simp [CheckedConstructedDateYear.read, observed]

/-- Two reached fixed split-year parts compose by decimal place, not addition. -/
theorem checkedConstructedDateCentury_read_values
    (century shortYear : CheckedConstructedDateNumberField model)
    (phase : Phase) (input : CheckedDocument model)
    (centuryValue shortYearValue : Int)
    (observedCentury :
      century.read phase input = .ok (.value centuryValue))
    (observedShortYear :
      shortYear.read phase input = .ok (.value shortYearValue)) :
    CheckedConstructedDateYear.read
        (.centuryAndShortYear century shortYear) phase input =
      .ok (.value (centuryValue * 100 + shortYearValue)) := by
  simp [CheckedConstructedDateYear.read, observedCentury,
    observedShortYear]

/-- A formally unavailable Day prevents every later component read. -/
theorem checkedConstructedDateComponents_day_unavailable
    (checked : CheckedConstructedDateComponents model)
    (phase : Phase) (input : CheckedDocument model) (cause : FormalCause)
    (observed :
      checked.day.read phase input = .ok (.unavailable cause)) :
    checked.evaluate phase input = .ok (.unavailable cause) := by
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

/-- Checked component execution routes every reached formal cause through `unavailable`; its resolved branch therefore never contains the cause-free UNKNOWN fallback. -/
theorem checkedConstructedDateComponents_ne_resolved_unknown
    (checked : CheckedConstructedDateComponents model)
    (phase : Phase) (input : CheckedDocument model) :
    checked.evaluate phase input ≠ .ok (.resolved .unknown) := by
  unfold CheckedConstructedDateComponents.evaluate
  generalize dayRead :
    CheckedConstructedDateNumberField.read checked.day phase input = day
  cases day with
  | error error => simp
  | ok day =>
      cases day with
      | unavailable cause => simp
      | value amount =>
          generalize monthRead :
            CheckedConstructedDateNumberField.read checked.month phase input = month
          cases month with
          | error error => simp
          | ok month =>
              cases month with
              | unavailable cause => simp
              | value amount =>
                  generalize yearRead :
                    CheckedConstructedDateYear.read checked.year phase input = year
                  cases year with
                  | error error => simp
                  | ok year =>
                      cases year <;>
                        simp [constructedDateObservation_ofAvailableComponents_ne_unknown]
              | empty =>
                  generalize yearRead :
                    CheckedConstructedDateYear.read checked.year phase input = year
                  cases year with
                  | error error => simp
                  | ok year =>
                      cases year <;>
                        simp [constructedDateObservation_ofAvailableComponents_ne_unknown]
      | empty =>
          generalize monthRead :
            CheckedConstructedDateNumberField.read checked.month phase input = month
          cases month with
          | error error => simp
          | ok month =>
              cases month with
              | unavailable cause => simp
              | value amount =>
                  generalize yearRead :
                    CheckedConstructedDateYear.read checked.year phase input = year
                  cases year with
                  | error error => simp
                  | ok year =>
                      cases year <;>
                        simp [constructedDateObservation_ofAvailableComponents_ne_unknown]
              | empty =>
                  generalize yearRead :
                    CheckedConstructedDateYear.read checked.year phase input = year
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
    (cause : FormalCause)
    (source :
      checked.source.evaluate phase input = .ok (.unavailable cause)) :
    checked.evaluate phase input = .ok (.unavailable cause) := by
  simp [CheckedConstructedDateShift.evaluate, source]

/-- Arithmetic domain failure after a real source remains cause-free no-value; it is not a zero shift and does not acquire omission provenance. -/
theorem checkedConstructedDateShift_real_domain_failure
    (checked : CheckedConstructedDateShift model)
    (phase : Phase) (input : CheckedDocument model) (parts : DateParts)
    (source :
      checked.source.evaluate phase input = .ok (.resolved (.real parts)))
    (amount :
      checked.amount.read phase input = .ok (.ok .notEvaluated)) :
    checked.evaluate phase input = .ok (.noValue false) := by
  unfold CheckedConstructedDateShift.evaluate
  rw [source]
  simp [amount, CheckedConstructedDateShift.applyAmount,
    CheckedConstructedDateShift.sourceNotGiven]
  rfl

/-- A reached first-source cause decides the generated two-source difference without any hypothesis about the second checked source. -/
theorem checkedConstructedDateDifference_first_unavailable
    (checked : CheckedConstructedDateDifference model)
    (phase : Phase) (input : CheckedDocument model)
    (cause : FormalCause)
    (first :
      checked.first.evaluate phase input = .ok (.unavailable cause)) :
    checked.evaluate phase input = .ok (.error cause) := by
  simp [CheckedConstructedDateDifference.evaluate, first]

/-- Once the first source resolves, the second source's exact reached formal cause is retained. -/
theorem checkedConstructedDateDifference_second_unavailable
    (checked : CheckedConstructedDateDifference model)
    (phase : Phase) (input : CheckedDocument model)
    (firstResult : DateConstructionResult) (cause : FormalCause)
    (first :
      checked.first.evaluate phase input = .ok (.resolved firstResult))
    (second :
      checked.second.evaluate phase input = .ok (.unavailable cause)) :
    checked.evaluate phase input = .ok (.error cause) := by
  simp [CheckedConstructedDateDifference.evaluate, first, second]

end A12Kernel
