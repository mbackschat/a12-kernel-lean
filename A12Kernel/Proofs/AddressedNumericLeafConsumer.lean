import A12Kernel.Elaboration.AddressedNumericLeafConsumer

/-! # Addressed numeric-leaf Analyze/Transform laws -/

namespace A12Kernel

namespace CheckedAddressedNumericLeaf

/-- A checked addressed numeric leaf never reports its written target as its read dependency. -/
theorem operandField_ne_targetField
    (leaf : CheckedAddressedNumericLeaf model) :
    leaf.analyze.sourceField ≠ leaf.analyze.targetField := by
  cases leaf with
  | fieldValueAsNumber operation =>
      exact operation.placement.sourceNotTarget
  | rangeAsNumber operation =>
      exact operation.placement.sourceNotTarget
  | numberField operation =>
      exact operation.placement.sourceNotTarget
  | abs operation =>
      exact operation.numberSource.placement.sourceNotTarget
  | round operation =>
      exact operation.numberSource.placement.sourceNotTarget

/-- Fingerprint comparison recognizes exact identity. -/
theorem matchingFingerprint_self
    (leaf : CheckedAddressedNumericLeaf model) :
    leaf.matchingFingerprint? leaf = some leaf.analyze := by
  simp [matchingFingerprint?]

/-- A reported fingerprint match is exactly equality of both bounded analyses; it makes no wider semantic-equivalence claim. -/
theorem matchingFingerprint_some_iff
    (before after : CheckedAddressedNumericLeaf model)
    (view : AddressedNumericLeafAnalysis) :
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
    (before after : CheckedAddressedNumericLeaf model)
    (view : AddressedNumericLeafAnalysis)
    (matched : before.matchingFingerprint? after = some view) :
    before.analyze.parameters = after.analyze.parameters := by
  have exactView :=
    (matchingFingerprint_some_iff before after view).mp matched
  rw [exactView.1, exactView.2]

/-- The admitted identity Transform preserves every addressed rich outcome for every checked document. -/
theorem identityTransform_execute
    (leaf : CheckedAddressedNumericLeaf model)
    (input : CheckedDocument model) :
    leaf.identityTransform.execute input = leaf.execute input := by
  rfl

/-- The admitted identity Transform likewise preserves the complete source-relative result view and message partition. -/
theorem identityTransform_executeResult
    (leaf : CheckedAddressedNumericLeaf model)
    (input : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    leaf.identityTransform.executeResult input payloadAt supplied =
      leaf.executeResult input payloadAt supplied := by
  rfl

end CheckedAddressedNumericLeaf

end A12Kernel
