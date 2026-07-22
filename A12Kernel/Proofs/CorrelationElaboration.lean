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

/-- The checked one-group route cannot be forged with resolved-only `Or`; its core stays inside the conjunction-only authored surface. -/
theorem checkedSingleCorrelatedRule_conjunctive
    (checked : CheckedSingleCorrelatedRule model) :
    checked.core.star.having.condition.isConjunctive = true := by
  have wellFormed := checked.wellFormed
  simp only [ResolvedSingleCorrelatedRule.WellFormed,
    ResolvedSingleCorrelatedRule.wellFormedBool, Bool.and_eq_true] at wellFormed
  exact wellFormed.1.2

/-- The full one-group well-formedness predicate implies the operator-specific equality-scale law at every nested filter node. -/
theorem correlatedHaving_wellFormed_equalityScalesAgree
    (condition : CorrelatedHaving) (model : FlatModel) (group : RepeatableGroupDecl)
    (wellFormed : condition.wellFormedForSingleGroup model group = true) :
    condition.equalityScalesAgree = true := by
  induction condition with
  | leaf leaf =>
      cases leaf with
      | compareNumbers op left right =>
          cases op with
          | equal | notEqual =>
              simp only [CorrelatedHaving.wellFormedForSingleGroup,
                ConditionTree.allLeaves,
                CorrelatedHavingLeaf.wellFormedForSingleGroup,
                CorrelatedHaving.equalityScalesAgree,
                CorrelatedHavingLeaf.equalityScalesAgree,
                Bool.and_eq_true] at wellFormed ⊢
              exact wellFormed.2
          | lessThan =>
              rfl
      | compareRepetitions =>
          rfl
  | and left right leftIh rightIh =>
      simp only [CorrelatedHaving.wellFormedForSingleGroup,
        CorrelatedHaving.equalityScalesAgree, ConditionTree.allLeaves,
        Bool.and_eq_true] at wellFormed ⊢
      exact ⟨leftIh wellFormed.1, rightIh wellFormed.2⟩
  | or left right leftIh rightIh =>
      simp only [CorrelatedHaving.wellFormedForSingleGroup,
        CorrelatedHaving.equalityScalesAgree, ConditionTree.allLeaves,
        Bool.and_eq_true] at wellFormed ⊢
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
