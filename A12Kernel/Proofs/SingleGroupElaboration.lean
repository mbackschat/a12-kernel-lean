import A12Kernel.Elaboration.SingleGroup

/-! # A12Kernel.Proofs.SingleGroupElaboration — shared checked one-group invariants -/

namespace A12Kernel

private theorem all_positive_of_find_zero_none (rows : List RowIndex)
    (noZero : rows.find? (· == 0) = none) :
    rows.all (0 < ·) = true := by
  induction rows with
  | nil => rfl
  | cons row rest inductionHypothesis =>
      by_cases rowZero : row = 0
      · subst row
        simp at noZero
      · have tailNoZero : rest.find? (· == 0) = none := by
          simpa [rowZero] using noZero
        simp [Nat.pos_of_ne_zero rowZero, inductionHypothesis tailNoZero]

/-- The public raw-context guard establishes the semantic topology predicate for the checked view; candidate validation and evaluation cannot drift apart. -/
theorem rawSingleGroupContext_validate_wellFormed
    (model : FlatModel) (group : RepeatableGroupDecl) (raw : RawSingleGroupContext)
    (valid : raw.validate = .ok ()) :
    (model.checkSingleGroupContext group raw).WellFormed := by
  unfold RawSingleGroupContext.validate at valid
  generalize noZeroEq : raw.candidates.find? (· == 0) = zeroResult at valid
  cases zeroResult with
  | some row =>
      change (Except.error (.zeroCandidate row) : Except SingleGroupContextError Unit) =
        .ok () at valid
      contradiction
  | none =>
      generalize noDuplicateEq : RowIndex.firstDuplicate? raw.candidates = duplicateResult at valid
      cases duplicateResult with
      | some row =>
          change (Except.error (.duplicateCandidate row) : Except SingleGroupContextError Unit) =
            .ok () at valid
          contradiction
      | none =>
          constructor
          · simp [FlatModel.checkSingleGroupContext, RowIndex.hasDuplicates, noDuplicateEq]
          · exact all_positive_of_find_zero_none raw.candidates noZeroEq

/-- An admitted one-group Number reference has one matching declaration at the exact group path and singleton repeatable scope. -/
theorem admitsSingleGroupNumber_has_unique_matching_declaration
    (model : FlatModel) (group : RepeatableGroupDecl) (field : FlatNumberField)
    (admitted : model.admitsSingleGroupNumber group field = true) :
    ∃ declaration,
      model.lookupUniqueId field.id = .ok declaration ∧
      declaration.groupPath = group.path ∧
      declaration.repeatableScope = [group.level] ∧
      (FlatField.number field).matchesDecl declaration = true := by
  unfold FlatModel.admitsSingleGroupNumber at admitted
  generalize lookupEq : model.lookupUniqueId field.id = lookup at admitted
  cases lookup with
  | error error => simp at admitted
  | ok declaration =>
      simp only [Bool.and_eq_true] at admitted
      exact ⟨declaration, rfl, by simpa using admitted.1.1,
        by simpa using admitted.1.2, admitted.2⟩

/-- Raw repeatable cells are formally checked with the unique declaration selected by the same model, group path, and singleton scope as elaboration. -/
theorem checkSingleGroupContext_lookup_coherent
    (model : FlatModel) (group : RepeatableGroupDecl) (raw : RawSingleGroupContext)
    (row : RowIndex) (id : FieldId) (declaration : FlatFieldDecl)
    (lookup : model.lookupUniqueId id = .ok declaration)
    (sameGroup : declaration.groupPath = group.path)
    (sameScope : declaration.repeatableScope = [group.level]) :
    (model.checkSingleGroupContext group raw).read row id =
      formalCheck declaration.policy (raw.read row id) := by
  simp [FlatModel.checkSingleGroupContext, lookup, sameGroup, sameScope]

/-- Missing or ambiguous identifiers fail closed at the repeatable raw-to-checked boundary. -/
theorem checkSingleGroupContext_lookup_error_is_malformed
    (model : FlatModel) (group : RepeatableGroupDecl) (raw : RawSingleGroupContext)
    (row : RowIndex) (id : FieldId) (error : ResolveError)
    (lookup : model.lookupUniqueId id = .error error) :
    (model.checkSingleGroupContext group raw).read row id = malformedCheckedCell := by
  simp [FlatModel.checkSingleGroupContext, lookup]

/-- A uniquely identified field from another group still fails closed. -/
theorem checkSingleGroupContext_wrong_group_is_malformed
    (model : FlatModel) (group : RepeatableGroupDecl) (raw : RawSingleGroupContext)
    (row : RowIndex) (id : FieldId) (declaration : FlatFieldDecl)
    (lookup : model.lookupUniqueId id = .ok declaration)
    (wrongGroup : declaration.groupPath ≠ group.path) :
    (model.checkSingleGroupContext group raw).read row id = malformedCheckedCell := by
  simp [FlatModel.checkSingleGroupContext, lookup, wrongGroup]

/-- A field at the right path with a different repeatable scope also fails closed. -/
theorem checkSingleGroupContext_wrong_scope_is_malformed
    (model : FlatModel) (group : RepeatableGroupDecl) (raw : RawSingleGroupContext)
    (row : RowIndex) (id : FieldId) (declaration : FlatFieldDecl)
    (lookup : model.lookupUniqueId id = .ok declaration)
    (sameGroup : declaration.groupPath = group.path)
    (wrongScope : declaration.repeatableScope ≠ [group.level]) :
    (model.checkSingleGroupContext group raw).read row id = malformedCheckedCell := by
  simp [FlatModel.checkSingleGroupContext, lookup, sameGroup, wrongScope]

/-- Every core-admitted repeatable Number reference therefore reads a cell checked by its one exact model declaration. -/
theorem checkSingleGroupContext_admittedNumber_coherent
    (model : FlatModel) (group : RepeatableGroupDecl) (raw : RawSingleGroupContext)
    (row : RowIndex) (field : FlatNumberField)
    (admitted : model.admitsSingleGroupNumber group field = true) :
    ∃ declaration,
      model.lookupUniqueId field.id = .ok declaration ∧
      declaration.groupPath = group.path ∧
      declaration.repeatableScope = [group.level] ∧
      (FlatField.number field).matchesDecl declaration = true ∧
      (model.checkSingleGroupContext group raw).read row field.id =
        formalCheck declaration.policy (raw.read row field.id) := by
  obtain ⟨declaration, lookup, sameGroup, sameScope, matching⟩ :=
    admitsSingleGroupNumber_has_unique_matching_declaration model group field admitted
  exact ⟨declaration, lookup, sameGroup, sameScope, matching,
    checkSingleGroupContext_lookup_coherent model group raw row field.id declaration
      lookup sameGroup sameScope⟩

end A12Kernel
