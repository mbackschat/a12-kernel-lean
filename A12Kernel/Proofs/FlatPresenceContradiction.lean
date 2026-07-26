import A12Kernel.Elaboration.Flat.PresenceContradiction

/-! # Exact flat presence-contradiction law -/

namespace A12Kernel

namespace FlatPresenceContradictionWitness

/-- Every certified exact same-field presence conjunction is semantically dead: evaluation can be cleanly false or formally unknown, but it can never fire an error. -/
theorem neverFires
    (witness : FlatPresenceContradictionWitness condition)
    (context : FlatContext)
    (polarity : Polarity)
    (isRelevant : FlatRelevance := fun _ => true) :
    condition.evalSelected context isRelevant ≠ .fired polarity := by
  rw [witness.exactShape]
  cases witness.order <;>
    simp only [FlatPresenceContradictionOrder.condition]
  all_goals
    cases relevant : isRelevant witness.field.id
    · simp [FlatCondition.evalSelected, relevant, Verdict.conj]
    · cases observation : witness.field.observeValidation context <;>
        simp [FlatCondition.evalSelected, relevant, FlatField.evalFilled,
          FlatField.evalNotFilled, observation, Verdict.conj]

end FlatPresenceContradictionWitness

end A12Kernel
