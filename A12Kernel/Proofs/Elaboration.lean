import A12Kernel.Elaboration.Flat

/-! # A12Kernel.Proofs.Elaboration — checked flat-elaboration invariants

These theorems expose the guarantee carried by successful elaboration and connect the
resolved model declaration to the policy used to check runtime cells. The latter closes
the previously admitted boundary between typed core references and caller-supplied
checked cells.
-/

namespace A12Kernel

/-- Public elimination theorem for the checked elaboration boundary. -/
theorem elaborate_success_wellFormed (model : FlatModel) (declaringGroup : GroupPath)
    (condition : SurfaceCondition) (checked : CheckedFlatCondition model)
    (_success : elaborate model declaringGroup condition = .ok checked) :
    checked.core.WellFormed model :=
  checked.wellFormed

/-- Successful elaboration also certifies the model checks that make name and identifier
    resolution unambiguous. -/
theorem elaborate_success_modelWellFormed (model : FlatModel) (declaringGroup : GroupPath)
    (condition : SurfaceCondition) (checked : CheckedFlatCondition model)
    (_success : elaborate model declaringGroup condition = .ok checked) :
    model.validate.isOk = true :=
  checked.modelWellFormed

/-- A field admitted by the core well-formedness check has a unique model declaration
    with the same typed field representation and no repeatable scope. -/
theorem admitsField_has_unique_matching_declaration (model : FlatModel) (field : FlatField)
    (admitted : model.admitsField field = true) :
    ∃ declaration,
      model.lookupUniqueId field.id = .ok declaration ∧
      declaration.repeatableScope.isEmpty = true ∧
      field.matchesDecl declaration = true := by
  unfold FlatModel.admitsField at admitted
  generalize lookupEq : model.lookupUniqueId field.id = lookup at admitted
  cases lookup with
  | error error => simp at admitted
  | ok declaration =>
      refine ⟨declaration, rfl, ?_⟩
      cases nonrepeatable : declaration.repeatableScope.isEmpty <;>
        cases matching : field.matchesDecl declaration <;> simp_all

/-- Model-derived context construction checks a resolved cell with exactly the policy
    carried by its unique declaration. -/
theorem checkContext_lookup_coherent (model : FlatModel) (raw : RawFlatContext)
    (id : FieldId) (declaration : FlatFieldDecl)
    (lookup : model.lookupUniqueId id = .ok declaration) :
    (model.checkContext raw).read id = formalCheck declaration.policy (raw.read id) := by
  simp [FlatModel.checkContext, lookup]

/-- A core-admitted reference therefore reads a cell checked by a unique matching model
    declaration, rather than by caller-supplied field metadata. -/
theorem checkContext_admittedField_coherent (model : FlatModel) (raw : RawFlatContext)
    (field : FlatField) (admitted : model.admitsField field = true) :
    ∃ declaration,
      model.lookupUniqueId field.id = .ok declaration ∧
      declaration.repeatableScope.isEmpty = true ∧
      field.matchesDecl declaration = true ∧
      (model.checkContext raw).read field.id =
        formalCheck declaration.policy (raw.read field.id) := by
  obtain ⟨declaration, lookup, nonrepeatable, matching⟩ :=
    admitsField_has_unique_matching_declaration model field admitted
  exact ⟨declaration, lookup, nonrepeatable, matching,
    checkContext_lookup_coherent model raw field.id declaration lookup⟩

/-- Missing or ambiguous identifiers fail closed at the raw-to-checked boundary. -/
theorem checkContext_lookup_error_is_malformed (model : FlatModel) (raw : RawFlatContext)
    (id : FieldId) (error : ResolveError)
    (lookup : model.lookupUniqueId id = .error error) :
    (model.checkContext raw).read id = malformedCheckedCell := by
  simp [FlatModel.checkContext, lookup]

/-- The fail-closed cell has the ordinary validation face of malformed input. -/
theorem checkContext_lookup_error_observes_unknown (model : FlatModel)
    (raw : RawFlatContext) (id : FieldId) (error : ResolveError)
    (lookup : model.lookupUniqueId id = .error error) :
    (model.checkContext raw).observeValidationAt id = .unknown .malformed := by
  simp [FlatContext.observeValidationAt, checkContext_lookup_error_is_malformed,
    lookup, malformedCheckedCell, observeCell]

end A12Kernel
