import A12Kernel.Elaboration.NumberToStringComputationRun
import A12Kernel.Proofs.StringAlternatives
import A12Kernel.Proofs.StringCascade

/-! # Number-to-String computation-run laws

These laws fix the family bridge, exact Number-outcome preservation, and read-driven poison boundary of the bounded heterogeneous run.
-/

namespace A12Kernel

/-- An accepted Number target shadows stale document state with its exact canonical stored text. -/
theorem acceptedNumericDependency_readsStoredText
    (context : StringComputationContext) (field : FieldId)
    (stored : StoredNumber) :
    (context.withDependencyCell field
      (StringDependencyCell.ofNumericOutcome (.accepted stored))).read field =
        {
          rawPresent := true
          parsed := some (.str stored.render)
          findings := []
        } := by
  simp [StringComputationContext.withDependencyCell,
    StringDependencyCell.ofNumericOutcome]

/-- Clean Number no-value becomes the established empty String dependency cell. -/
theorem noValueNumericDependency_isEmpty :
    StringDependencyCell.ofNumericOutcome .noValue =
      StringDependencyCell.empty := by
  rfl

/-- Every invalid Number outcome lowers to the same cause-blind String dependency poison. -/
theorem invalidNumericDependency_isCauseBlind
    (outcome : NumericTargetOutcome)
    (invalid : outcome.dependencyObservation = .poisoned) :
    StringDependencyCell.ofNumericOutcome outcome =
      StringDependencyCell.poison .computedDependency := by
  cases outcome <;>
    simp [NumericTargetOutcome.dependencyObservation,
      StringDependencyCell.ofNumericOutcome] at invalid ⊢

/-- The heterogeneous run exposes both completions as their exact rich family outcomes rather than a common projection. -/
theorem numberToStringRun_preservesFamilyOutcomes
    (run : CheckedNumberToStringComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (number : NumericComputationRunCompletion)
    (string : StringComputationRunCompletion)
    (outcomes : NumberToStringComputationOutcomes)
    (numberEvaluated :
      run.number.evaluateCompletion
        (input.scalarComputationContext world) =
        .ok number)
    (stringEvaluated :
      run.string.evaluateCompletion patterns
        (run.stringContext input number.outcome) = .ok string)
    (executed : run.execute world patterns input = .ok outcomes) :
    outcomes.number = (number.targetField, number.outcome) ∧
      outcomes.string = (string.targetField, string.outcome) := by
  simp [CheckedNumberToStringComputationRun.execute,
    numberEvaluated, stringEvaluated] at executed
  cases executed
  exact ⟨rfl, rfl⟩

/-- Overlaying one completed Number leaves every distinct ordinary String read unchanged. -/
theorem numericOutcomeOverlay_preservesOtherRead
    (context : StringComputationContext)
    (producer other : FieldId)
    (outcome : NumericTargetOutcome)
    (different : other ≠ producer) :
    (context.withDependencyCell producer
      (StringDependencyCell.ofNumericOutcome outcome)).read other =
        context.read other :=
  dependencyCell_preserves_other_read context producer other
    (StringDependencyCell.ofNumericOutcome outcome) different

/-- Even a poisoned Number producer cannot affect a syntactic dependency hidden in the unread suffix after a holding String row. -/
theorem numericOutcomeOverlay_holdingHead_suffixIrrelevant
    (context : StringComputationContext)
    (producer : FieldId)
    (outcome : NumericTargetOutcome)
    (computation : StringAlternativeComputation)
    (head : ComputationAlternative StringExpr)
    (firstSuffix secondSuffix :
      List (ComputationAlternative StringExpr))
    (guard : ComputationCondition)
    (guarded : head.precondition = some guard)
    (holds :
      guard.eval
        (context.withDependencyCell producer
          (StringDependencyCell.ofNumericOutcome outcome)) = .holds) :
    ({ computation with alternatives := head :: firstSuffix }).evaluateOutcome
        (context.withDependencyCell producer
          (StringDependencyCell.ofNumericOutcome outcome)) =
      ({ computation with alternatives := head :: secondSuffix }).evaluateOutcome
        (context.withDependencyCell producer
          (StringDependencyCell.ofNumericOutcome outcome)) :=
  stringAlternatives_holdingHead_suffixIrrelevant
    computation
    (context.withDependencyCell producer
      (StringDependencyCell.ofNumericOutcome outcome))
    head firstSuffix secondSuffix guard guarded holds

end A12Kernel
