import A12Kernel.Elaboration.GeneratedRuleIdentity

/-! # The generated rules' three projections are mutually underivable

One law carries the family: the code separates all four kinds, the message key and the omission flag
each separate only two, and they separate *different* twos. So a consumer holding any one projection
cannot recover another, and the code is the only faithful identity.
-/

namespace A12Kernel

/-- **The code is injective.** Distinct kinds have distinct codes, so a consumer reading the code
always knows which generated rule fired. -/
theorem formalCode_injective (left right : GeneratedRuleKind)
    (h : left.formalCode = right.formalCode) : left = right := by
  cases left <;> cases right <;> simp_all [GeneratedRuleKind.formalCode]

/-- **The message key is not.** The two uniqueness kinds share one, which is the counterexample that
makes the injectivity above worth stating. -/
theorem formalMessageKey_not_injective :
    GeneratedRuleKind.uniqueIndexField.formalMessageKey =
      GeneratedRuleKind.uniqueValue.formalMessageKey ∧
    GeneratedRuleKind.uniqueIndexField ≠ GeneratedRuleKind.uniqueValue := by
  exact ⟨rfl, by decide⟩

/-- **The two coarse projections disagree.** The mandatory field and the solitary index share an
omission flag while having different message keys; the two uniqueness kinds share a message key while
— together — differing in omission from that pair. Neither projection refines the other, so a
consumer cannot derive either from the other. -/
theorem projections_cross :
    (GeneratedRuleKind.mandatoryField.isOmissionError =
        GeneratedRuleKind.solitaryIndexField.isOmissionError ∧
      GeneratedRuleKind.mandatoryField.formalMessageKey ≠
        GeneratedRuleKind.solitaryIndexField.formalMessageKey) ∧
    (GeneratedRuleKind.uniqueIndexField.formalMessageKey =
        GeneratedRuleKind.uniqueValue.formalMessageKey ∧
      GeneratedRuleKind.uniqueIndexField.isOmissionError ≠
        GeneratedRuleKind.mandatoryField.isOmissionError) := by
  refine ⟨⟨rfl, by decide⟩, ⟨rfl, by decide⟩⟩

/-- Exactly the generated rules are preliminary, in both directions. -/
@[simp] theorem generatedRuleIsPreliminary_iff (kind : Option GeneratedRuleKind) :
    generatedRuleIsPreliminary kind = true ↔ kind.isSome := by
  simp [generatedRuleIsPreliminary]

/-- An authored rule is never preliminary, which is the direction a consumer uses to tell the two
apart on a rule it did not generate. -/
theorem generatedRuleIsPreliminary_authored : generatedRuleIsPreliminary none = false := rfl

/-- The unraised codes are disjoint from the live ones, so extending the live vocabulary with any of
them would be a change in kind rather than an addition. -/
theorem unraised_disjoint_from_live (kind : GeneratedRuleKind) (unraised : UnraisedFormalCode) :
    kind.formalCode ≠ unraised.code := by
  cases kind <;> cases unraised <;> simp [GeneratedRuleKind.formalCode, UnraisedFormalCode.code]

end A12Kernel
