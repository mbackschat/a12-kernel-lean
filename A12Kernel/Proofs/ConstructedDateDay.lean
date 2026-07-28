import A12Kernel.Semantics.ConstructedDateDay

/-! # Constructed-Date legacy-hybrid day laws -/

namespace A12Kernel

/-- A resolved coordinate pair determines the signed day difference exactly. -/
theorem legacyHybrid_differenceInDays_of_epochDay
    (first second : DateParts) (firstDay secondDay : Int)
    (firstResolved : DateParts.LegacyHybrid.epochDay? first = some firstDay)
    (secondResolved : DateParts.LegacyHybrid.epochDay? second = some secondDay) :
    DateParts.LegacyHybrid.differenceInDays? first second =
      some (secondDay - firstDay) := by
  simp [DateParts.LegacyHybrid.differenceInDays?,
    firstResolved, secondResolved]

/-- Day shifting cannot collapse the three reason-bearing constructed no-values. -/
theorem constructedDate_addLegacyDays_preserves_nonvalues (offset : Int) :
    DateConstructionResult.incomplete.addLegacyDays? offset = some .incomplete ∧
      DateConstructionResult.unreal.addLegacyDays? offset = some .unreal ∧
      DateConstructionResult.unknown.addLegacyDays? offset = some .unknown := by
  simp [DateConstructionResult.addLegacyDays?]

/-- Day difference preserves unavailable-before-missing precedence and missing-versus-fixed zero provenance. -/
theorem constructedDateDifferenceDays_nonvalue_provenance
    (right : DateConstructionResult) :
    DateConstructionResult.unknown.differenceLegacyDays? right =
        some .unavailable ∧
      DateConstructionResult.incomplete.differenceLegacyDays? right =
        (if right = .unknown then some .unavailable else some (.value 0 true)) ∧
      DateConstructionResult.unreal.differenceLegacyDays? right =
        (if right = .unknown then some .unavailable else
          if right = .incomplete then some (.value 0 true)
          else some (.value 0 false)) := by
  cases right <;>
    simp [DateConstructionResult.differenceLegacyDays?,
      DateConstructionResult.differenceWith?]

/-- The adjacent default-cutover labels are one signed calendar day apart. -/
theorem constructedDateDay_legacyCutover :
    (DateConstructionResult.real { year := 1582, month := 10, day := 4 }).addLegacyDays? 1 =
        some (.real { year := 1582, month := 10, day := 15 }) ∧
      (DateConstructionResult.real { year := 1582, month := 10, day := 4 }).differenceLegacyDays?
        (.real { year := 1582, month := 10, day := 15 }) =
        some (.value 1 false) := by
  set_option maxRecDepth 2000 in
    decide

/-- Exact UTC midnight follows the same one-day cutover adjacency as the hybrid label. -/
theorem constructedDateDay_legacyCutover_instant :
    DateParts.LegacyHybrid.midnightInstant?
        { year := 1582, month := 10, day := 4 } =
      some { epochMillis := -12219379200000 } ∧
    DateParts.LegacyHybrid.midnightInstant?
        { year := 1582, month := 10, day := 15 } =
      some { epochMillis := -12219292800000 } := by
  set_option maxRecDepth 2000 in
    decide

end A12Kernel
