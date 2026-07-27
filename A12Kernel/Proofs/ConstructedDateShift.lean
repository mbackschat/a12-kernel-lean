import A12Kernel.Semantics.ConstructedDateShift

/-! # Constructed-Date legacy-hybrid shift laws -/

namespace A12Kernel

/-- Month shifting cannot collapse the three reason-bearing constructed no-values. -/
theorem constructedDate_addLegacyMonths_preserves_nonvalues (offset : Int) :
    DateConstructionResult.incomplete.addLegacyMonths? offset = some .incomplete ∧
      DateConstructionResult.unreal.addLegacyMonths? offset = some .unreal ∧
      DateConstructionResult.unknown.addLegacyMonths? offset = some .unknown := by
  simp [DateConstructionResult.addLegacyMonths?]

/-- Year shifting cannot collapse the three reason-bearing constructed no-values. -/
theorem constructedDate_addLegacyYears_preserves_nonvalues (offset : Int) :
    DateConstructionResult.incomplete.addLegacyYears? offset = some .incomplete ∧
      DateConstructionResult.unreal.addLegacyYears? offset = some .unreal ∧
      DateConstructionResult.unknown.addLegacyYears? offset = some .unknown := by
  simp [DateConstructionResult.addLegacyYears?]

/-- Both nominal cutover-hole landings normalize to the same first-selected legacy label. -/
theorem constructedDate_legacyCutover_month_year :
    (DateConstructionResult.real { year := 1582, month := 9, day := 10 }).addLegacyMonths? 1 =
        some (.real { year := 1582, month := 10, day := 20 }) ∧
      (DateConstructionResult.real { year := 1581, month := 10, day := 10 }).addLegacyYears? 1 =
        some (.real { year := 1582, month := 10, day := 20 }) := by
  decide

/-- The February-28 promotion uses Gregorian rather than Julian leap status on both sides of the cutover. -/
theorem constructedDate_addLegacyYears_gregorianLeapPredicate :
    (DateConstructionResult.real { year := 1499, month := 2, day := 28 }).addLegacyYears? 1 =
      some (.real { year := 1500, month := 2, day := 28 }) := by
  decide

end A12Kernel
