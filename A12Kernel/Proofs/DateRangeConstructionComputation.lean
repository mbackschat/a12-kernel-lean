import A12Kernel.Elaboration.DateRangeConstructionComputation

/-! # Checked DateRange construction computation laws -/

namespace A12Kernel

@[simp] theorem dateRangeTarget_evaluateComputationResult_noValue
    (format : DateRangeFormat) :
    format.evaluateComputationResult .noValue = .ok .noValue := rfl

@[simp] theorem dateRangeTarget_evaluateComputationResult_poison
    (format : DateRangeFormat) (cause : FormalCause) :
    format.evaluateComputationResult (.poison cause) =
      .ok (.poison cause) := rfl

/-- A resolved typed range reaches the exact checked target renderer. -/
theorem dateRangeTarget_evaluateComputationResult_value
    (format : DateRangeFormat) (range : DateRangeValue)
    (resolved : ResolvedDateRange)
    (projects : range.toResolvedDateRange? = some resolved)
    (ordered : resolved.direction = .ordered) :
    format.evaluateComputationResult (.value (.exact range)) =
      .ok (.accepted (format.render resolved)) := by
  simp [DateRangeFormat.evaluateComputationResult, projects, ordered]

/-- An inverted resolved range retains its exact rendered attempt in the target-error outcome. -/
theorem dateRangeTarget_evaluateComputationResult_inverted
    (format : DateRangeFormat) (range : DateRangeValue)
    (resolved : ResolvedDateRange)
    (projects : range.toResolvedDateRange? = some resolved)
    (inverted : resolved.direction = .inverted) :
    format.evaluateComputationResult (.value (.exact range)) =
      .ok (.errored (format.render resolved) .inverted) := by
  simp [DateRangeFormat.evaluateComputationResult, projects, inverted]

@[simp] theorem dateRangeConstructionTarget_evaluateComputationResult_noValue
    (format : DateRangeConstructionTargetFormat) :
    format.evaluateComputationResult .noValue = .ok .noValue := by
  cases format <;> rfl

@[simp] theorem dateRangeConstructionTarget_evaluateComputationResult_poison
    (format : DateRangeConstructionTargetFormat) (cause : FormalCause) :
    format.evaluateComputationResult (.poison cause) =
      .ok (.poison cause) := by
  cases format <;> rfl

/-- Every resolved typed range reaches the checked supported target renderer. -/
theorem dateRangeConstructionTarget_evaluateComputationResult_value
    (format : DateRangeConstructionTargetFormat) (range : DateRangeValue)
    (resolved : ResolvedDateRange)
    (projects : range.toResolvedDateRange? = some resolved)
    (ordered : resolved.direction = .ordered) :
    format.evaluateComputationResult (.value (.exact range)) =
      .ok (.accepted (format.render resolved)) := by
  cases format <;>
    simp [DateRangeConstructionTargetFormat.evaluateComputationResult,
      DateRangeConstructionTargetFormat.render,
      DateRangeConstructionTargetFormat.toInputFormat,
      DateRangeInputFormat.evaluateComputationResult,
      DateRangeInputFormat.evaluateExactValue,
      DateRangeInputFormat.renderResolved,
      DateRangeFormat.evaluateComputationResult, projects, ordered]

/-- Every inverted resolved range retains the exact presentation attempted by the checked target. -/
theorem dateRangeConstructionTarget_evaluateComputationResult_inverted
    (format : DateRangeConstructionTargetFormat) (range : DateRangeValue)
    (resolved : ResolvedDateRange)
    (projects : range.toResolvedDateRange? = some resolved)
    (inverted : resolved.direction = .inverted) :
    format.evaluateComputationResult (.value (.exact range)) =
      .ok (.errored (format.render resolved) .inverted) := by
  cases format <;>
    simp [DateRangeConstructionTargetFormat.evaluateComputationResult,
      DateRangeConstructionTargetFormat.render,
      DateRangeConstructionTargetFormat.toInputFormat,
      DateRangeInputFormat.evaluateComputationResult,
      DateRangeInputFormat.evaluateExactValue,
      DateRangeInputFormat.renderResolved,
      DateRangeFormat.evaluateComputationResult, projects, inverted]

/-- An ordered yearless month construction reaches the component-only target without manufacturing a year. -/
theorem dateRangeConstructionTarget_evaluateComputationResult_yearlessMonth
    (start finish : Nat) (ordered : ¬ finish < start) :
    DateRangeConstructionTargetFormat.monthFragment.evaluateComputationResult
        (.value (.yearlessMonth start finish)) =
      .ok (.accepted (DateRangeInputFormat.renderYearlessMonth start finish)) := by
  simp [DateRangeConstructionTargetFormat.evaluateComputationResult,
    DateRangeConstructionTargetFormat.toInputFormat,
    DateRangeInputFormat.evaluateComputationResult, ordered]

/-- An inverted yearless month construction retains its component-only attempted value. -/
theorem dateRangeConstructionTarget_evaluateComputationResult_yearlessMonth_inverted
    (start finish : Nat) (inverted : finish < start) :
    DateRangeConstructionTargetFormat.monthFragment.evaluateComputationResult
        (.value (.yearlessMonth start finish)) =
      .ok (.errored (DateRangeInputFormat.renderYearlessMonth start finish)
        .inverted) := by
  simp [DateRangeConstructionTargetFormat.evaluateComputationResult,
    DateRangeConstructionTargetFormat.toInputFormat,
    DateRangeInputFormat.evaluateComputationResult, inverted]

/-- An ordered yearless month/day construction reaches the component-only target without manufacturing a year. -/
theorem dateRangeConstructionTarget_evaluateComputationResult_yearlessMonthDay
    (start finish : MonthDayValue)
    (ordered : DateRangeInputFormat.monthDayBefore finish start = false) :
    DateRangeConstructionTargetFormat.monthDayFragment.evaluateComputationResult
        (.value (.yearlessMonthDay start finish)) =
      .ok (.accepted
        (DateRangeInputFormat.renderYearlessMonthDay start finish)) := by
  simp [DateRangeConstructionTargetFormat.evaluateComputationResult,
    DateRangeConstructionTargetFormat.toInputFormat,
    DateRangeInputFormat.evaluateComputationResult, ordered]

/-- An inverted yearless month/day construction retains its component-only attempted value. -/
theorem dateRangeConstructionTarget_evaluateComputationResult_yearlessMonthDay_inverted
    (start finish : MonthDayValue)
    (inverted : DateRangeInputFormat.monthDayBefore finish start = true) :
    DateRangeConstructionTargetFormat.monthDayFragment.evaluateComputationResult
        (.value (.yearlessMonthDay start finish)) =
      .ok (.errored
        (DateRangeInputFormat.renderYearlessMonthDay start finish) .inverted) := by
  simp [DateRangeConstructionTargetFormat.evaluateComputationResult,
    DateRangeConstructionTargetFormat.toInputFormat,
    DateRangeInputFormat.evaluateComputationResult, inverted]

/-- A yearless result cannot acquire an exact target presentation by bypassing checked profile admission. -/
theorem dateRangeTarget_evaluateComputationResult_yearlessMonth_refused
    (format : DateRangeFormat) (start finish : Nat) :
    format.evaluateComputationResult (.value (.yearlessMonth start finish)) =
      .ok (.poison .malformed) := rfl

/-- A yearless month/day result likewise fails closed at an exact target. -/
theorem dateRangeTarget_evaluateComputationResult_yearlessMonthDay_refused
    (format : DateRangeFormat) (start finish : MonthDayValue) :
    format.evaluateComputationResult (.value (.yearlessMonthDay start finish)) =
      .ok (.poison .malformed) := rfl

/-- Two exact endpoint observations project to the one typed range consumed by the target. -/
theorem dateRangeConstructionObservation_asComputationResult_exact
    (start finish : DateValue) :
    (DateRangeConstructionObservation.mk
      (.value (.exact start)) (.value (.exact finish))).asComputationResult =
      .value (.exact { start, finish }) := rfl

/-- Two present month endpoints retain their ordered yearless component identity for target evaluation. -/
theorem dateRangeConstructionObservation_asComputationResult_yearlessMonth
    (start finish : Nat) :
    (DateRangeConstructionObservation.mk
      (.value (.month start)) (.value (.month finish))).asComputationResult =
      .value (.yearlessMonth start finish) := rfl

/-- Two present month/day endpoints retain their ordered yearless component identity for target evaluation. -/
theorem dateRangeConstructionObservation_asComputationResult_yearlessMonthDay
    (start finish : MonthDayValue) :
    (DateRangeConstructionObservation.mk
      (.value (.monthDay start))
      (.value (.monthDay finish))).asComputationResult =
      .value (.yearlessMonthDay start finish) := rfl

/-- The checked target retains its declaring-group ownership and construction-profile certificate. -/
theorem checkedDateRangeConstructionComputation_target_admitted
    (operation : CheckedDateRangeConstructionComputation model) :
    model.ownsDirectDateRangeTarget
        operation.declaringGroup operation.target = true ∧
      DateRangeConstructionTargetFormat.ofProfiles?
        operation.construction.start.format operation.target.format =
          some operation.format :=
  ⟨operation.targetOwnedByGroup, operation.profileOwned⟩

/-- One supported construction evaluation reaches its checked target renderer without rereading either endpoint. -/
theorem checkedDateRangeConstructionComputation_execute_value
    (operation : CheckedDateRangeConstructionComputation model)
    (input : CheckedDocument model)
    (observation : DateRangeConstructionObservation)
    (range : DateRangeValue) (resolved : ResolvedDateRange)
    (evaluated : operation.construction.evaluate .computation input =
      .ok observation)
    (projectsResult : observation.asComputationResult = .value (.exact range))
    (projectsRange : range.toResolvedDateRange? = some resolved)
    (ordered : resolved.direction = .ordered) :
    operation.execute input = .ok {
      construction := observation
      outcome := .accepted (operation.format.render resolved)
    } := by
  rw [CheckedDateRangeConstructionComputation.execute, evaluated]
  simp [Except.mapError, bind, Except.bind, pure, Except.pure, projectsResult,
    dateRangeConstructionTarget_evaluateComputationResult_value
      operation.format range resolved projectsRange ordered]

end A12Kernel
