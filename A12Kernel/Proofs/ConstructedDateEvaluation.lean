import A12Kernel.Elaboration.ConstructedDateEvaluation

/-! # Checked constructed-Date execution laws -/

namespace A12Kernel

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
                    CheckedConstructedDateNumberField.read checked.year phase input = year
                  cases year with
                  | error error => simp
                  | ok year =>
                      cases year <;>
                        simp [constructedDateObservation_ofAvailableComponents_ne_unknown]
              | empty =>
                  generalize yearRead :
                    CheckedConstructedDateNumberField.read checked.year phase input = year
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
                    CheckedConstructedDateNumberField.read checked.year phase input = year
                  cases year with
                  | error error => simp
                  | ok year =>
                      cases year <;>
                        simp [constructedDateObservation_ofAvailableComponents_ne_unknown]
              | empty =>
                  generalize yearRead :
                    CheckedConstructedDateNumberField.read checked.year phase input = year
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

end A12Kernel
