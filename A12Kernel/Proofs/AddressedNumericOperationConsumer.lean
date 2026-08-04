import A12Kernel.Proofs.AddressedNumberExtremum
import A12Kernel.Elaboration.AddressedNumericOperationConsumer

/-! # Addressed numeric-operation Analyze/Transform laws -/

namespace A12Kernel

namespace CheckedAddressedNumericOperation

/-- A checked addressed numeric operation never reports its written target among its ordered operand dependencies. -/
theorem operandField_ne_targetField
    (leaf : CheckedAddressedNumericOperation model) :
    ∀ field ∈ leaf.analyze.sourceFields,
      field ≠ leaf.analyze.targetField := by
  cases leaf with
  | fieldValueAsNumber operation =>
      simpa [analyze] using operation.placement.sourceNotTarget
  | rangeAsNumber operation =>
      simpa [analyze] using operation.placement.sourceNotTarget
  | numberField operation =>
      simpa [analyze] using operation.placement.sourceNotTarget
  | abs operation =>
      simpa [analyze] using operation.numberSource.placement.sourceNotTarget
  | round operation =>
      simpa [analyze] using operation.numberSource.placement.sourceNotTarget
  | extremum operation =>
      simpa [analyze] using
        checkedAddressedNumberExtremum_sourceField_ne_targetField operation

/-- Fingerprint comparison recognizes exact identity. -/
theorem matchingFingerprint_self
    (leaf : CheckedAddressedNumericOperation model) :
    leaf.matchingFingerprint? leaf = some leaf.analyze := by
  simp [matchingFingerprint?]

/-- A reported fingerprint match is exactly equality of both bounded analyses; it makes no wider semantic-equivalence claim. -/
theorem matchingFingerprint_some_iff
    (before after : CheckedAddressedNumericOperation model)
    (view : AddressedNumericOperationAnalysis) :
    before.matchingFingerprint? after = some view ↔
      before.analyze = view ∧ after.analyze = view := by
  unfold matchingFingerprint?
  by_cases same : before.analyze = after.analyze
  · rw [if_pos same]
    constructor
    · intro accepted
      have candidate : after.analyze = view :=
        Option.some.inj accepted
      exact ⟨same.trans candidate, candidate⟩
    · rintro ⟨_, candidate⟩
      exact congrArg some candidate
  · rw [if_neg same]
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨beforeView, afterView⟩
      exact False.elim (same (beforeView.trans afterView.symm))

/-- A fingerprint match preserves every represented parameter rather than only source and target identity. -/
theorem matchingFingerprint_preservesParameters
    (before after : CheckedAddressedNumericOperation model)
    (view : AddressedNumericOperationAnalysis)
    (matched : before.matchingFingerprint? after = some view) :
    before.analyze.parameters = after.analyze.parameters := by
  have exactView :=
    (matchingFingerprint_some_iff before after view).mp matched
  rw [exactView.1, exactView.2]

/-- Equal declared and derived scales are admitted whatever the capability, which is the whole reason plain equality reads as the rule for every non-capable form. -/
private theorem admitsTargetScale_of_exact (scale : Nat)
    (summary : NumericScaleSummary)
    (derived : summary.scale = .exact (scale : Int)) :
    exactNumericScaleComparisonAllowedWithSuppression false
      (NumericScaleSummary.field scale) summary = true := by
  simp [exactNumericScaleComparisonAllowedWithSuppression,
    exactNumericScaleComparisonAllowed, NumericScaleSummary.field, derived]

/-- Every checked operation's own declared target scale is admitted by the consumer's decision procedure. The Analyze view and the elaborator therefore share one admission gate: a retargeting consumer reading only the fingerprint can never reject the operation it was given, and never needs a second rule. -/
theorem analyze_admitsTargetScale_self
    (leaf : CheckedAddressedNumericOperation model) :
    leaf.analyze.admitsTargetScale leaf.analyze.targetPolicy.info.scale = true := by
  cases leaf with
  | fieldValueAsNumber operation =>
      refine admitsTargetScale_of_exact _ _ ?_
      have shared := operation.sameScale
      simp only [CheckedAddressedNumericPlacement.targetPolicy] at shared
      simp only [analyze, AddressedNumericOperationParameters.derivedScaleSummary,
        NumericScaleSummary.field]
      exact congrArg (fun scale : Nat => ScaleInfo.exact (scale : Int)) shared
  | rangeAsNumber operation =>
      refine admitsTargetScale_of_exact _ _ ?_
      have shared := operation.sameScale
      simp only [CheckedAddressedNumericPlacement.targetPolicy] at shared
      simp only [analyze, AddressedNumericOperationParameters.derivedScaleSummary,
        NumericScaleSummary.field]
      exact congrArg (fun scale : Nat => ScaleInfo.exact (scale : Int)) shared.symm
  | numberField operation =>
      refine admitsTargetScale_of_exact _ _ ?_
      have shared := operation.sameScale
      simp only [CheckedAddressedNumericPlacement.targetPolicy] at shared
      simp only [analyze, AddressedNumericOperationParameters.derivedScaleSummary,
        NumericScaleSummary.field]
      exact congrArg (fun scale : Nat => ScaleInfo.exact (scale : Int)) shared.symm
  | abs operation =>
      refine admitsTargetScale_of_exact _ _ ?_
      have shared := operation.numberSource.sameScale
      simp only [CheckedAddressedNumericPlacement.targetPolicy] at shared
      simp only [analyze, AddressedNumericOperationParameters.derivedScaleSummary,
        NumericScaleSummary.field]
      exact congrArg (fun scale : Nat => ScaleInfo.exact (scale : Int)) shared.symm
  | round operation =>
      refine admitsTargetScale_of_exact _ _ ?_
      have shared := operation.sameScale
      simp only [CheckedAddressedNumericPlacement.targetPolicy] at shared
      simp only [analyze, AddressedNumericOperationParameters.derivedScaleSummary,
        NumericScaleSummary.rounded]
      exact congrArg (fun scale : Nat => ScaleInfo.exact (scale : Int)) shared.symm
  | extremum operation =>
      simpa [analyze, AddressedNumericOperationAnalysis.admitsTargetScale,
        AddressedNumericOperationParameters.derivedScaleSummary,
        CheckedAddressedNumberExtremum.scaleSummary]
        using operation.targetAdmitted

/-- The admitted identity Transform preserves the complete Analyze fingerprint universally, so no individual probe case needs to recheck it: target, sources, scope, target policy, and every operation parameter including the derived scale summary and ordered operand identities are retained. -/
theorem identityTransform_analyze
    (leaf : CheckedAddressedNumericOperation model) :
    leaf.identityTransform.analyze = leaf.analyze := by
  rfl

/-- The admitted identity Transform preserves every addressed rich outcome for every checked document. -/
theorem identityTransform_execute
    (leaf : CheckedAddressedNumericOperation model)
    (input : CheckedDocument model) :
    leaf.identityTransform.execute input = leaf.execute input := by
  rfl

/-- The admitted identity Transform likewise preserves the complete source-relative result view and message partition. -/
theorem identityTransform_executeResult
    (leaf : CheckedAddressedNumericOperation model)
    (input : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    leaf.identityTransform.executeResult input payloadAt supplied =
      leaf.executeResult input payloadAt supplied := by
  rfl

end CheckedAddressedNumericOperation

end A12Kernel
