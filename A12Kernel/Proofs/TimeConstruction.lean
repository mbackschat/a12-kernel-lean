import A12Kernel.Elaboration.ValueAsDate

/-! # Laws for resolved `Time(...)` construction -/

namespace A12Kernel

/-- The zero-argument constructor observes none of the caller's component values. -/
theorem timeConstruction_zero_ignores_inputs
    (hour minute second otherHour otherMinute otherSecond :
      TimeConstructionComponent) :
    TimeConstructionArity.zero.evaluate hour minute second =
      TimeConstructionArity.zero.evaluate
        otherHour otherMinute otherSecond := by
  rfl

/-- Formal unavailability in the first supplied slot wins before every later missing or invalid component. -/
theorem timeConstruction_first_unavailable
    (cause : FormalCause)
    (minute second : TimeConstructionComponent) :
    TimeConstructionArity.second.evaluate
        (.unavailable cause) minute second =
      .unavailable cause := by
  rfl

/-- Missingness prevents a later present-but-invalid component from reclassifying the result as unreal. -/
theorem timeConstruction_missing_precedes_reality
    (minute second : Int) :
    TimeConstructionArity.second.evaluate
        .empty (.value minute) (.value second) =
      .incomplete := by
  rfl

/-- Reached runtime non-relevance dominates ordinary component missingness. -/
theorem timeConstruction_nonRelevant_precedes_missing :
    TimeConstructionArity.second.evaluate
        (.value 10) .empty .nonRelevant =
      .nonRelevant := by
  rfl

end A12Kernel
