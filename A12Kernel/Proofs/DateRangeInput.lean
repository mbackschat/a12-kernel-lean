import A12Kernel.Elaboration.DateRangeInput

/-! # Checked stored DateRange input laws

These laws connect declaration admission to stored-input capability. They are internal
consequences of the two owners, not claims about the Kernel's own dispatch.
-/

namespace A12Kernel

/-- Every statically admitted declaration pair selects exactly one stored-input profile. The `unsupportedPolicy` refusal therefore has no witness among admitted declarations, so it stays fail-closed for callers that bypass declaration validation rather than being claimed unreachable. -/
theorem dateRangeInputFormat_ofPolicy_isSome_of_admitted
    (policy : DateRangeDeclarationPolicy)
    (admitted : policy.admitted = true) :
    (DateRangeInputFormat.ofPolicy? policy).isSome = true := by
  unfold DateRangeDeclarationPolicy.admitted at admitted
  split at admitted <;>
    simp_all [DateRangeInputFormat.ofPolicy?, DateRangeFormat.ofPolicy?]

/-- Both wrapping placements span exactly one calendar-year boundary: the anchored endpoint keeps the Base Year and its counterpart lands in the immediately adjacent year, so no interpretation can stretch a yearless pair across two boundaries. -/
theorem dateRangeYearInterpretation_wrappingYears_span_one_boundary
    (interpretation : DateRangeYearInterpretation) (baseYear : Int) :
    (interpretation.wrappingYears baseYear).2 =
      (interpretation.wrappingYears baseYear).1 + 1 := by
  cases interpretation <;> simp [DateRangeYearInterpretation.wrappingYears] <;> omega

private theorem completionYears_ignores_interpretation_off_wrap
    (interpretation : Option DateRangeYearInterpretation) (baseYear : Int)
    (yearless : DateRangeCellValue)
    (ordered : yearless.wrapsYearBoundary = false) :
    completionYears interpretation baseYear yearless = some (baseYear, baseYear) := by
  simp [completionYears, ordered]

private theorem completionYears_none_of_wrap
    (baseYear : Int) (yearless : DateRangeCellValue)
    (wraps : yearless.wrapsYearBoundary = true) :
    completionYears none baseYear yearless = none := by
  simp [completionYears, wraps]

/-- Declaring a year interpretation cannot move an ordered range's endpoints. Adding, changing, or removing the key leaves every non-wrapping yearless pair with the identical classification under every Base Year state, so the key widens admission rather than reinterpreting an already valid range. -/
theorem resolveYearlessForModel_ignores_interpretation_off_wrap
    (zoneId : String) (baseYear : Option Int)
    (left right : Option DateRangeYearInterpretation)
    (yearless : DateRangeCellValue)
    (ordered : yearless.wrapsYearBoundary = false) :
    resolveYearlessForModel zoneId baseYear left yearless =
      resolveYearlessForModel zoneId baseYear right yearless := by
  cases baseYear with
  | none => simp [resolveYearlessForModel]
  | some year =>
      simp [resolveYearlessForModel,
        completionYears_ignores_interpretation_off_wrap _ _ _ ordered]

/-- The standard reading refuses every wrapping yearless pair with the inverted-order cause, whether or not a Base Year is declared. The refusal is therefore a property of the absent interpretation alone, not of the completion route it would otherwise take. -/
theorem resolveYearlessForModel_wrap_rejected_without_interpretation
    (zoneId : String) (baseYear : Option Int) (yearless : DateRangeCellValue)
    (wraps : yearless.wrapsYearBoundary = true) :
    resolveYearlessForModel zoneId baseYear none yearless =
      .ok (.rejected .dateRangeInvalid) := by
  cases baseYear with
  | none => simp [resolveYearlessForModel, wraps]
  | some year => simp [resolveYearlessForModel, completionYears_none_of_wrap _ _ wraps]

end A12Kernel
