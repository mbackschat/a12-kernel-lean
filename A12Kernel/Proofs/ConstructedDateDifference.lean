import A12Kernel.Semantics.ConstructedDateDifference

/-! # Constructed-Date legacy-hybrid difference laws -/

namespace A12Kernel

/-- A formally unavailable first operand dominates every constructed-Date completed-period branch. -/
theorem constructedDateDifference_unavailable_left
    (unit : DateDifferenceUnit) (right : DateConstructionResult) :
    DateConstructionResult.unknown.differenceLegacy? unit right =
      some .unavailable := by
  cases right <;> rfl

/-- Incomplete and unreal operands both produce zero but remain distinguishable by missing provenance. -/
theorem constructedDateDifference_nonvalue_provenance
    (unit : DateDifferenceUnit) (right : DateConstructionResult) :
    DateConstructionResult.incomplete.differenceLegacy? unit right =
        (if right = .unknown then some .unavailable else some (.value 0 true)) ∧
      DateConstructionResult.unreal.differenceLegacy? unit right =
        (if right = .unknown then some .unavailable else
          if right = .incomplete then some (.value 0 true)
          else some (.value 0 false)) := by
  cases right <;> simp [DateConstructionResult.differenceLegacy?]

/-- The canonical cutover labels separate incomplete from complete legacy months and years. -/
theorem constructedDateDifference_legacyCutover :
    (DateConstructionResult.real { year := 1582, month := 9, day := 10 }).differenceLegacy?
        .months (.real { year := 1582, month := 10, day := 15 }) =
        some (.value 0 false) ∧
      (DateConstructionResult.real { year := 1582, month := 9, day := 10 }).differenceLegacy?
        .months (.real { year := 1582, month := 10, day := 20 }) =
        some (.value 1 false) ∧
      (DateConstructionResult.real { year := 1581, month := 10, day := 10 }).differenceLegacy?
        .years (.real { year := 1582, month := 10, day := 15 }) =
        some (.value 0 false) ∧
      (DateConstructionResult.real { year := 1581, month := 10, day := 10 }).differenceLegacy?
        .years (.real { year := 1582, month := 10, day := 20 }) =
        some (.value 1 false) := by
  decide

end A12Kernel
