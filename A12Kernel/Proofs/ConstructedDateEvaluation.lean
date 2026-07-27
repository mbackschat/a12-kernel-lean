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
  rfl

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
