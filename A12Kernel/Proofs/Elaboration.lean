import A12Kernel.Elaboration.Flat

/-! # A12Kernel.Proofs.Elaboration — checked flat-elaboration invariants

These theorems eliminate certificates carried by checked values and connect the resolved model declaration to the policy used to check runtime cells. The latter closes the previously admitted boundary between typed core references and caller-supplied checked cells.
-/

namespace A12Kernel

/-- Eliminate the core static-legality certificate carried by a checked flat condition. -/
theorem checkedFlatCondition_wellFormed (checked : CheckedFlatCondition model) :
    checked.core.WellFormed model :=
  checked.wellFormed

/-- Eliminate the model-validity certificate carried by a checked flat condition. -/
theorem checkedFlatCondition_modelWellFormed (checked : CheckedFlatCondition model) :
    model.validate.isOk = true :=
  checked.modelWellFormed

/-- Surface elaboration retains its exact declaring group in the checked certificate. -/
theorem elaborate_checkedFlatCondition_rowGroup
    (model : FlatModel) (declaringGroup : GroupPath)
    (condition : SurfaceCondition) (checked : CheckedFlatCondition model)
    (elaborated : elaborate model declaringGroup condition = .ok checked) :
    checked.rowGroup = declaringGroup := by
  unfold elaborate at elaborated
  split at elaborated
  · contradiction
  · simp only [bind, Except.bind] at elaborated
    split at elaborated
    · contradiction
    · unfold FlatCondition.checkAgainstValidatedModel at elaborated
      split at elaborated
      · cases elaborated
        rfl
      · contradiction

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

/-- A resolved direct textual profile is available only for a field admitted by the shared typed-field gate. -/
theorem directComparableProfile_admitsField (model : FlatModel)
    (operand : FlatTextFieldOperand) (profile : DirectComparableField)
    (resolved : model.directComparableFor? operand = some profile) :
    model.admitsField operand.field = true := by
  unfold FlatModel.directComparableFor? at resolved
  unfold FlatModel.admitsField
  split at resolved <;> simp_all

/-- A reconstructed checked Enumeration operand necessarily passes the shared typed-field gate. -/
theorem checkedEnumerationOperand_admitsField (model : FlatModel)
    (operand : FlatEnumerationOperand) (checked : CheckedEnumerationProjection)
    (resolved : model.checkedEnumerationOperand? operand = some checked) :
    model.admitsField (.enumeration operand.field) = true := by
  unfold FlatModel.checkedEnumerationOperand? at resolved
  generalize lookupEq : model.lookupUniqueId operand.field.id = lookup at resolved
  cases lookup with
  | error error => simp at resolved
  | ok declaration =>
      generalize gateEq : (declaration.repeatableScope.isEmpty &&
        (FlatField.enumeration operand.field).matchesDecl declaration) = gate at resolved
      cases gate with
      | false => simp [gateEq] at resolved
      | true =>
          simpa [FlatModel.admitsField, FlatField.id, lookupEq] using gateEq

/-- Value-reading admission strengthens, rather than replaces, ordinary String presence admission. -/
theorem admitsStringValueField_admitsField (model : FlatModel)
    (field : FlatStringField)
    (admitted : model.admitsStringValueField field = true) :
    model.admitsField (.string field) = true := by
  unfold FlatModel.admitsStringValueField at admitted
  unfold FlatModel.admitsField
  generalize lookupEq : model.lookupUniqueId field.id = lookup at admitted ⊢
  cases lookup with
  | error error => simp at admitted
  | ok declaration =>
      cases kindEq : declaration.policy.kind <;>
        cases modeEq : declaration.stringValueMode
      all_goals try simp_all [FlatFieldDecl.toStringValueField?,
        FlatFieldDecl.toPresenceField, FlatField.matchesDecl, FlatField.id]

/-- Every field read by an admitted comparison independently passes the shared typed-field admission check. -/
theorem admitsComparison_fields_admitted (model : FlatModel)
    (comparison : FlatComparison) (admitted : model.admitsComparison comparison = true) :
    ∀ field, field ∈ comparison.fields → model.admitsField field = true := by
  intro field member
  cases comparison with
  | number op target expected =>
      rcases List.mem_singleton.mp member with rfl
      simpa [FlatModel.admitsComparison, FlatComparison.fields,
        List.all_eq_true] using admitted
  | boolean op target expected =>
      rcases List.mem_singleton.mp member with rfl
      simpa [FlatModel.admitsComparison, FlatComparison.fields,
        List.all_eq_true] using admitted
  | string op target expected =>
      rcases List.mem_singleton.mp member with rfl
      exact admitsStringValueField_admitsField model target (by
        simpa [FlatModel.admitsComparison] using admitted)
  | stringLength op target expected =>
      rcases List.mem_singleton.mp member with rfl
      exact admitsStringValueField_admitsField model target (by
        simpa [FlatModel.admitsComparison] using admitted)
  | confirm op target =>
      rcases List.mem_singleton.mp member with rfl
      simpa [FlatModel.admitsComparison, FlatComparison.fields,
        List.all_eq_true] using admitted
  | enumeration op operand expected =>
      rcases List.mem_singleton.mp member with rfl
      unfold FlatModel.admitsComparison at admitted
      generalize resolved : model.checkedEnumerationOperand? operand = checked at admitted
      cases checked with
      | none => simp [resolved] at admitted
      | some checked =>
          exact checkedEnumerationOperand_admitsField model operand checked resolved
  | textFields op left right =>
      unfold FlatModel.admitsComparison at admitted
      generalize leftEq : model.directComparableFor? left = leftProfile at admitted
      generalize rightEq : model.directComparableFor? right = rightProfile at admitted
      cases leftProfile <;> cases rightProfile <;> simp_all
      simp [FlatComparison.fields] at member
      rcases member with rfl | rfl
      · exact directComparableProfile_admitsField model left _ leftEq
      · exact directComparableProfile_admitsField model right _ rightEq
  | temporal op left right =>
      simp [FlatModel.admitsComparison, List.all_eq_true] at admitted
      exact admitted.2 field member

/-- Model-derived context construction checks a resolved cell with exactly the policy
    carried by its unique declaration. -/
theorem checkContext_lookup_coherent (model : FlatModel) (raw : RawFlatContext)
    (id : FieldId) (declaration : FlatFieldDecl)
    (lookup : model.lookupUniqueId id = .ok declaration) :
    (model.checkContext raw).read id = declaration.checkRaw (raw.read id) := by
  simp only [FlatModel.checkContext, lookup]

/-- A core-admitted reference therefore reads a cell checked by a unique matching model
    declaration, rather than by caller-supplied field metadata. -/
theorem checkContext_admittedField_coherent (model : FlatModel) (raw : RawFlatContext)
    (field : FlatField) (admitted : model.admitsField field = true) :
    ∃ declaration,
      model.lookupUniqueId field.id = .ok declaration ∧
      declaration.repeatableScope.isEmpty = true ∧
      field.matchesDecl declaration = true ∧
      (model.checkContext raw).read field.id = declaration.checkRaw (raw.read field.id) := by
  obtain ⟨declaration, lookup, nonrepeatable, matching⟩ :=
    admitsField_has_unique_matching_declaration model field admitted
  exact ⟨declaration, lookup, nonrepeatable, matching,
    checkContext_lookup_coherent model raw field.id declaration lookup⟩

/-- Every field read by a core-admitted comparison therefore receives the policy of its own unique compatible declaration. -/
theorem checkContext_admittedComparison_field_coherent (model : FlatModel)
    (raw : RawFlatContext) (comparison : FlatComparison)
    (admitted : model.admitsComparison comparison = true)
    (field : FlatField) (member : field ∈ comparison.fields) :
    ∃ declaration,
      model.lookupUniqueId field.id = .ok declaration ∧
      declaration.repeatableScope.isEmpty = true ∧
      field.matchesDecl declaration = true ∧
      (model.checkContext raw).read field.id = declaration.checkRaw (raw.read field.id) := by
  exact checkContext_admittedField_coherent model raw field
    (admitsComparison_fields_admitted model comparison admitted field member)

/-- Missing or ambiguous identifiers fail closed at the raw-to-checked boundary. -/
theorem checkContext_lookup_error_is_malformed (model : FlatModel) (raw : RawFlatContext)
    (id : FieldId) (error : ResolveError)
    (lookup : model.lookupUniqueId id = .error error) :
    (model.checkContext raw).read id = malformedCheckedCell := by
  simp only [FlatModel.checkContext, lookup]

/-- The fail-closed cell has the ordinary validation face of malformed input. -/
theorem checkContext_lookup_error_observes_unknown (model : FlatModel)
    (raw : RawFlatContext) (id : FieldId) (error : ResolveError)
    (lookup : model.lookupUniqueId id = .error error) :
    (model.checkContext raw).observeValidationAt id = .unknown .malformed := by
  simp [FlatContext.observeValidationAt, checkContext_lookup_error_is_malformed,
    lookup, malformedCheckedCell, observeCell]

end A12Kernel
