import A12Kernel.Semantics.DateConstruction

/-! # A12Kernel.Proofs.DateConstruction — resolved classification and validity laws

These laws characterize how already-checked component availability combines with separately supplied calendar reality, then how `Valid` and `Invalid` consume the reason-bearing result. They do not prove component authoring, concrete calendar resolution, row eligibility, the stored/computed Date floor, or external kernel equivalence.
-/

namespace A12Kernel

/-- Formal unavailability dominates every empty or present component position. -/
theorem classifyDateConstruction3_unknown_iff
    (day month year : DateComponentAvailability)
    (reality : PresentDateReality) :
    classifyDateConstruction3 day month year reality = .unknown ↔
      day = .unknown ∨ month = .unknown ∨ year = .unknown := by
  cases day <;> cases month <;> cases year <;> cases reality <;>
    simp [classifyDateConstruction3]

/-- Incompleteness means that at least one component is empty and none is formally unavailable. -/
theorem classifyDateConstruction3_incomplete_iff
    (day month year : DateComponentAvailability)
    (reality : PresentDateReality) :
    classifyDateConstruction3 day month year reality = .incomplete ↔
      day ≠ .unknown ∧ month ≠ .unknown ∧ year ≠ .unknown ∧
        (day = .empty ∨ month = .empty ∨ year = .empty) := by
  cases day <;> cases month <;> cases year <;> cases reality <;>
    simp [classifyDateConstruction3]

/-- With three present components, a supplied real date is retained exactly. -/
theorem classifyDateConstruction3_present_real
    (parts : DateParts) :
    classifyDateConstruction3 .present .present .present (.real parts) =
      .real parts := by
  rfl

/-- With three present components, supplied calendar rejection remains distinct from incompleteness. -/
theorem classifyDateConstruction3_present_unreal :
    classifyDateConstruction3 .present .present .present .unreal =
      .unreal := by
  rfl

/-- `Valid` fires exactly for carried calendar-accepted parts. -/
theorem dateConstruction_valid_fired_iff
    (result : DateConstructionResult) :
    result.validVerdict = .fired .value ↔
      ∃ parts, result = .real parts := by
  cases result <;> simp [DateConstructionResult.validVerdict]

/-- `Invalid` fires as OMISSION exactly for an incomplete construction. -/
theorem dateConstruction_invalid_omission_iff
    (result : DateConstructionResult) :
    result.invalidVerdict = .fired .omission ↔
      result = .incomplete := by
  cases result <;> simp [DateConstructionResult.invalidVerdict]

/-- `Invalid` fires as VALUE exactly for a complete but unreal construction. -/
theorem dateConstruction_invalid_value_iff
    (result : DateConstructionResult) :
    result.invalidVerdict = .fired .value ↔
      result = .unreal := by
  cases result <;> simp [DateConstructionResult.invalidVerdict]

/-- Both predicates are UNKNOWN together exactly when component checking made the construction unavailable. -/
theorem dateConstruction_both_unknown_iff
    (result : DateConstructionResult) :
    (result.validVerdict = .unknown ∧ result.invalidVerdict = .unknown) ↔
      result = .unknown := by
  cases result <;>
    simp [DateConstructionResult.validVerdict,
      DateConstructionResult.invalidVerdict]

/-- `Valid` deliberately forgets whether its non-value was incomplete or unreal. -/
theorem dateConstruction_valid_forgets_nonvalue_reason :
    DateConstructionResult.incomplete.validVerdict =
      DateConstructionResult.unreal.validVerdict := by
  rfl

/-- `Invalid` must recover that reason because incomplete and unreal failures have different polarity. -/
theorem dateConstruction_invalid_preserves_nonvalue_reason :
    DateConstructionResult.incomplete.invalidVerdict ≠
      DateConstructionResult.unreal.invalidVerdict := by
  decide

/-- `Valid` and `Invalid` are exact strong-Kleene complements after verdict polarity is forgotten. The three clauses state the true, false, and UNKNOWN arms without adding a generic language-level negation operator. -/
theorem dateConstruction_truth_complement
    (result : DateConstructionResult) :
    (result.validVerdict = .fired .value ↔
      result.invalidVerdict = .notFired) ∧
    (result.validVerdict = .notFired ↔
      ∃ polarity, result.invalidVerdict = .fired polarity) ∧
    (result.validVerdict = .unknown ↔
      result.invalidVerdict = .unknown) := by
  cases result <;>
    simp [DateConstructionResult.validVerdict,
      DateConstructionResult.invalidVerdict]

end A12Kernel
