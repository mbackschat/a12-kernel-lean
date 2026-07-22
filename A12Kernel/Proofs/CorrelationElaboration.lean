import A12Kernel.Elaboration.Correlation

/-! # A12Kernel.Proofs.CorrelationElaboration — checked repeatable-binding invariants -/

namespace A12Kernel

/-- Eliminate the core static-legality certificate carried by a checked correlated rule. -/
theorem checkedSingleCorrelatedRule_wellFormed
    (checked : CheckedSingleCorrelatedRule model) :
    checked.core.WellFormed model :=
  checked.wellFormed

/-- Eliminate the expanded-model validity certificate carried by a checked correlated rule. -/
theorem checkedSingleCorrelatedRule_modelWellFormed
    (checked : CheckedSingleCorrelatedRule model) :
    model.validate.isOk = true :=
  checked.modelWellFormed

/-- The full one-group well-formedness predicate implies the operator-specific equality-scale law at every nested filter node. -/
theorem correlatedHaving_wellFormed_equalityScalesAgree
    (condition : CorrelatedHaving) (model : FlatModel) (group : RepeatableGroupDecl)
    (wellFormed : condition.wellFormedForSingleGroup model group = true) :
    condition.equalityScalesAgree = true := by
  induction condition with
  | compareNumbers op left right =>
      cases op <;>
        simp [CorrelatedHaving.wellFormedForSingleGroup,
          CorrelatedHaving.equalityScalesAgree] at wellFormed ⊢ <;>
        exact wellFormed.2
  | compareRepetitions => simp [CorrelatedHaving.equalityScalesAgree]
  | and left right leftIh rightIh =>
      simp only [CorrelatedHaving.wellFormedForSingleGroup, Bool.and_eq_true] at wellFormed
      simp only [CorrelatedHaving.equalityScalesAgree, Bool.and_eq_true]
      exact ⟨leftIh wellFormed.1, rightIh wellFormed.2⟩

/-- Every checked correlated rule carries the scale law; it is not a caller-supplied assumption attached after lowering. -/
theorem resolvedSingleCorrelatedRule_wellFormed_equalityScalesAgree
    (rule : ResolvedSingleCorrelatedRule) (model : FlatModel)
    (wellFormed : rule.WellFormed model) :
    rule.star.having.condition.equalityScalesAgree = true := by
  simp only [ResolvedSingleCorrelatedRule.WellFormed,
    ResolvedSingleCorrelatedRule.wellFormedBool, Bool.and_eq_true] at wellFormed
  exact correlatedHaving_wellFormed_equalityScalesAgree
    rule.star.having.condition model rule.group wellFormed.2

end A12Kernel
