import A12Kernel.Elaboration.FieldEntityList

/-! # A12Kernel.Proofs.CorrelationElaboration — checked repeatable-binding invariants -/

namespace A12Kernel

private theorem repeatableScope_prefix (model : FlatModel) (left right : GroupPath)
    (isPrefix : left.IsPrefix right) :
    (model.repeatableScopeForGroupPath left).IsPrefix
      (model.repeatableScopeForGroupPath right) := by
  rcases isPrefix with ⟨tail, rfl⟩
  unfold FlatModel.repeatableScopeForGroupPath
  rw [List.length_append, List.range_add, List.filterMap_append]
  have same :
      (List.range left.length).filterMap (fun offset =>
        (model.repeatableGroups.find? fun group =>
          group.path == (left ++ tail).take (offset + 1)).map (·.level)) =
      (List.range left.length).filterMap (fun offset =>
        (model.repeatableGroups.find? fun group =>
          group.path == left.take (offset + 1)).map (·.level)) := by
    generalize offsetsEq : List.range left.length = offsets
    have below : ∀ offset ∈ offsets, offset < left.length := by
      intro offset inside
      rw [← offsetsEq] at inside
      exact List.mem_range.mp inside
    clear offsetsEq
    induction offsets with
    | nil => rfl
    | cons offset rest ih =>
        simp only [List.filterMap_cons]
        rw [List.take_append_of_le_length
          (Nat.succ_le_of_lt (below offset (by simp)))]
        rw [ih (fun index inside => below index (by simp [inside]))]
  rw [same]
  exact List.prefix_append _ _

/-- For a model-derived environment, a uniquely named repeatable level carries all its ancestors.
    The terminal-membership hypothesis states that the named declaration is the path lookup's result;
    the uniqueness hypothesis rules out reusing its level on another branch. -/
theorem repeatableScope_available_iff_terminal (model : FlatModel)
    (group : RepeatableGroupDecl) (environmentPath : GroupPath)
    (unique : ∀ candidate ∈ model.repeatableGroups,
      candidate.level = group.level → candidate.path = group.path)
    (terminal : group.level ∈ model.repeatableScopeForGroupPath group.path) :
    repeatableScopeAvailable (model.repeatableScopeForGroupPath group.path)
      (model.repeatableScopeForGroupPath environmentPath) =
      (model.repeatableScopeForGroupPath environmentPath).contains group.level := by
  apply Bool.eq_iff_iff.mpr
  simp only [repeatableScopeAvailable, List.isPrefixOf_iff_prefix, List.contains_iff_mem]
  constructor
  · intro isPrefix
    exact isPrefix.sublist.subset terminal
  · intro present
    obtain ⟨offset, _, found⟩ := List.mem_filterMap.mp present
    obtain ⟨candidate, lookup, level⟩ := Option.map_eq_some_iff.mp found
    have path : candidate.path = environmentPath.take (offset + 1) :=
      by simpa using List.find?_some lookup
    have samePath := unique candidate (List.mem_of_find?_eq_some lookup) level
    apply repeatableScope_prefix
    rw [← samePath, path]
    exact List.take_prefix _ _

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

/-- Candidate and captured reads of the same declaration are distinct exact operands. This is the
    reusable identity law behind the reviewed `$P, P` authoring row
    ([checkpoint](../../docs/SOURCES.md#src-pr2-correlated-operand-identity)); carrier kind gates
    remain separate. -/
theorem havingDirectField_inner_outer_pair_unique
    (model : FlatModel) (declaration : FlatFieldDecl) (form : FieldEntityReadForm) :
    firstDuplicateResolvedHavingDirectField? [
      ({ origin := .inner, declaration, form } :
        ResolvedHavingDirectFieldOperand model),
      { origin := .outer, declaration, form }] = none := by
  rfl

/-- The identity law is independent of authored slot order. This internal theorem does not claim
    Kernel correspondence for the unmeasured reverse order. -/
theorem havingDirectField_outer_inner_pair_unique
    (model : FlatModel) (declaration : FlatFieldDecl) (form : FieldEntityReadForm) :
    firstDuplicateResolvedHavingDirectField? [
      ({ origin := .outer, declaration, form } :
        ResolvedHavingDirectFieldOperand model),
      { origin := .inner, declaration, form }] = none := by
  rfl

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
      | numeric comparison =>
          simp only [CorrelatedHaving.wellFormedForSingleGroup, ConditionTree.allLeaves,
            CorrelatedHavingLeaf.wellFormedForSingleGroup,
            NumericComparisonOf.havingAdmitted, NumericComparisonOf.admittedWith,
            Bool.and_eq_true] at wellFormed
          exact wellFormed.2.2
      | simpleComparison | compareStringLiteral | literalMembership | fieldMembership | fieldFill | presence
          | groupPresence | groupFill | typeValidity | stringPattern =>
          -- Vacuous: the legacy one-group predicate refuses these leaves outright, so each
          -- branch's hypothesis is `false = true`. The scale law itself admits them.
          simp [CorrelatedHaving.wellFormedForSingleGroup, ConditionTree.allLeaves,
            CorrelatedHavingLeaf.wellFormedForSingleGroup] at wellFormed
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
