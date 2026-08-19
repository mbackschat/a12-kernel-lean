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
    format.evaluateComputationResult (.value range) =
      .ok (.accepted (format.render resolved)) := by
  simp [DateRangeFormat.evaluateComputationResult, projects, ordered]

/-- An inverted resolved range retains its exact rendered attempt in the target-error outcome. -/
theorem dateRangeTarget_evaluateComputationResult_inverted
    (format : DateRangeFormat) (range : DateRangeValue)
    (resolved : ResolvedDateRange)
    (projects : range.toResolvedDateRange? = some resolved)
    (inverted : resolved.direction = .inverted) :
    format.evaluateComputationResult (.value range) =
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

/-- Every resolved typed range reaches the checked exact or year-bearing target renderer. -/
theorem dateRangeConstructionTarget_evaluateComputationResult_value
    (format : DateRangeConstructionTargetFormat) (range : DateRangeValue)
    (resolved : ResolvedDateRange)
    (projects : range.toResolvedDateRange? = some resolved)
    (ordered : resolved.direction = .ordered) :
    format.evaluateComputationResult (.value range) =
      .ok (.accepted (format.render resolved)) := by
  cases format <;>
    simp [DateRangeConstructionTargetFormat.evaluateComputationResult,
      DateRangeConstructionTargetFormat.render,
      DateRangeFormat.evaluateComputationResult, projects, ordered]

/-- Every inverted resolved range retains the exact presentation attempted by the checked target. -/
theorem dateRangeConstructionTarget_evaluateComputationResult_inverted
    (format : DateRangeConstructionTargetFormat) (range : DateRangeValue)
    (resolved : ResolvedDateRange)
    (projects : range.toResolvedDateRange? = some resolved)
    (inverted : resolved.direction = .inverted) :
    format.evaluateComputationResult (.value range) =
      .ok (.errored (format.render resolved) .inverted) := by
  cases format <;>
    simp [DateRangeConstructionTargetFormat.evaluateComputationResult,
      DateRangeConstructionTargetFormat.render,
      DateRangeFormat.evaluateComputationResult, projects, inverted]

/-- Two exact endpoint observations project to the one typed range consumed by the target. -/
theorem dateRangeConstructionObservation_asComputationResult_exact
    (start finish : DateValue) :
    (DateRangeConstructionObservation.mk
      (.value (.exact start)) (.value (.exact finish))).asComputationResult =
      .value { start, finish } := rfl

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
    (projectsResult : observation.asComputationResult = .value range)
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
