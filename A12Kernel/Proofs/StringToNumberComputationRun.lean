import A12Kernel.Elaboration.StringToNumberComputationRun
import A12Kernel.Proofs.ComputationCondition
import A12Kernel.Proofs.NumericComputation
import A12Kernel.Proofs.StringCascade

/-! # String-to-Number computation-run laws

These laws fix the exact String dependency cell consumed by numeric conversion, the family outcomes, and the read-driven poison boundary of the bounded heterogeneous run.
-/

namespace A12Kernel

/-- An accepted String target shadows stale document state with the exact stored text consumed by `FieldValueAsNumber`. -/
theorem acceptedStringDependency_fieldValueAsNumber
    (context : ScalarComputationContext)
    (source : ResolvedFieldValueAsNumberSource)
    (stored : StoredString)
    (amount : Rat)
    (converted : source.valueFor? (.str stored.text) = some amount) :
    (StringComputationContext.withDependencyCell context source.fieldId
      (StringDependencyCell.value stored)).readNumericComputationAtom
        (.fieldValueAsNumber source) = .ok (.value amount) := by
  apply numericComputation_fieldValueAsNumber_value
  · rw [dependencyCell_shadows_target]
    exact computation_observes_clean_value (Value.str stored.text)
  · exact converted

/-- Clean String no-value enters the established numeric conversion as zero. -/
theorem noValueStringDependency_fieldValueAsNumber_zero
    (context : ScalarComputationContext)
    (source : ResolvedFieldValueAsNumberSource) :
    (StringComputationContext.withDependencyCell context source.fieldId
      StringDependencyCell.empty).readNumericComputationAtom
        (.fieldValueAsNumber source) = .ok (.value 0) := by
  apply numericComputation_fieldValueAsNumber_empty_zero
  rw [dependencyCell_shadows_target]
  rfl

/-- A reached invalid String dependency enters numeric conversion with the cause-blind computed-dependency poison. -/
theorem invalidStringDependency_fieldValueAsNumber_poison
    (context : ScalarComputationContext)
    (source : ResolvedFieldValueAsNumberSource) :
    (StringComputationContext.withDependencyCell context source.fieldId
      (StringDependencyCell.poison
        .computedDependency)).readNumericComputationAtom
          (.fieldValueAsNumber source) =
      .ok (.poison .computedDependency) := by
  apply numericComputation_fieldValueAsNumber_poison_preservesCause
  rw [dependencyCell_shadows_target]
  exact computation_observes_single_poison .computedDependency (by decide)

/-- The heterogeneous run exposes both completions as their exact rich family outcomes rather than a common projection. -/
theorem stringToNumberRun_preservesFamilyOutcomes
    (run : CheckedStringToNumberComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (string : StringComputationRunCompletion)
    (number : NumericComputationRunCompletion)
    (outcomes : StringToNumberComputationOutcomes)
    (stringEvaluated :
      run.string.evaluateCompletion patterns
        input.stringComputationContext = .ok string)
    (numberEvaluated :
      run.number.evaluateCompletion
        (run.numberContextWithString world input string) = .ok number)
    (executed : run.execute world patterns input = .ok outcomes) :
    outcomes.string = (string.targetField, string.outcome) ∧
      outcomes.number = (number.targetField, number.outcome) := by
  simp [CheckedStringToNumberComputationRun.execute,
    stringEvaluated, numberEvaluated] at executed
  cases executed
  exact ⟨rfl, rfl⟩

/-- Overlaying one completed String leaves every distinct ordinary Number read unchanged. -/
theorem stringOutcomeOverlay_preservesOtherRead
    (context : ScalarComputationContext)
    (producer other : FieldId)
    (dependency : StringDependencyCell)
    (different : other ≠ producer) :
    (StringComputationContext.withDependencyCell
      context producer dependency).read other = context.read other :=
  dependencyCell_preserves_other_read
    context producer other dependency different

/-- Even a poisoned String producer cannot affect a syntactic dependency hidden in the unread suffix after a holding Number row. -/
theorem stringOutcomeOverlay_holdingNumberHead_suffixIrrelevant
    (context : ScalarComputationContext)
    (producer : FieldId)
    (dependency : StringDependencyCell)
    (head : ComputationAlternative
      (CheckedNumericTargetComputationOperation model))
    (firstSuffix secondSuffix : List
      (ComputationAlternative
        (CheckedNumericTargetComputationOperation model)))
    (holds :
      head.precondition.eval
        (StringComputationContext.withDependencyCell
          context producer dependency) = .holds) :
    ComputationAlternative.selectFirst (head :: firstSuffix)
        (StringComputationContext.withDependencyCell
          context producer dependency) =
      ComputationAlternative.selectFirst (head :: secondSuffix)
        (StringComputationContext.withDependencyCell
          context producer dependency) := by
  rw [alternativeSelection_holdingHead_selects _ _ firstSuffix holds,
    alternativeSelection_holdingHead_selects _ _ secondSuffix holds]

end A12Kernel
