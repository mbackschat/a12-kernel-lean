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
      intro field member
      simp only [analyze, List.mem_append, List.mem_flatMap] at member
      rcases member with first | ⟨operand, operandMember, nestedMember⟩
      · exact operation.first.sourceField_ne_targetField field first
      · intro sourceIsTarget
        apply operand.sourceField_ne_targetField field nestedMember
        exact sourceIsTarget.trans
          (operation.restSameTarget operand operandMember)

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
