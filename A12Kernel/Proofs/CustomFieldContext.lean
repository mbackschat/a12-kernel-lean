import A12Kernel.Elaboration.StringContext

/-! # A12Kernel.Proofs.CustomFieldContext — prepared flat custom context laws -/

namespace A12Kernel

theorem customField_checkValueRaw_acceptance_exact
    (checked : CheckedCustomFieldType) (locale value : String)
    (nonempty : value.isEmpty = false)
    (accepted : checked.validator value
      (checked.declaration.validationContext locale) = none) :
    checked.checkValueRaw locale (.parsed (.str value)) = {
      rawPresent := true
      parsed := some (.str value)
      findings := []
    } := by
  simp [CheckedCustomFieldType.checkValueRaw,
    CheckedCustomFieldType.classifyValue,
    CheckedCustomFieldType.classifyString, nonempty, accepted]

theorem customField_checkValueRaw_rejection_exact
    (checked : CheckedCustomFieldType) (locale value : String)
    (rejection : RegisteredCustomRejection)
    (nonempty : value.isEmpty = false)
    (rejected : checked.validator value
      (checked.declaration.validationContext locale) = some rejection) :
    checked.checkValueRaw locale (.parsed (.str value)) = {
      rawPresent := true
      parsed := none
      findings := [.registeredCustomValidation rejection]
    } := by
  simp [CheckedCustomFieldType.checkValueRaw,
    CheckedCustomFieldType.classifyValue,
    CheckedCustomFieldType.classifyString, nonempty, rejected,
    BaseFormalCause.toFormalCause]

@[simp]
theorem customField_checkValueRaw_empty (checked : CheckedCustomFieldType)
    (locale : String) :
    checked.checkValueRaw locale .empty = {
      rawPresent := false
      parsed := none
      findings := []
    } := by
  rfl

@[simp]
theorem customField_checkValueRaw_wrongKind (checked : CheckedCustomFieldType)
    (locale : String) (value : Rat) :
    checked.checkValueRaw locale (.parsed (.num value)) = {
      rawPresent := true
      parsed := none
      findings := [.malformed]
    } := by
  rfl

/-- A coherent prepared overlay delegates the exact declaration to its resolved custom checker. -/
theorem preparedCustomContext_lookup_exact
    (prepared : PreparedFlatCustomFields model) (locale : String)
    (raw : RawFlatContext) (id : FieldId) (declaration : FlatFieldDecl)
    (customField : PreparedFlatCustomField)
    (modelLookup : model.lookupUniqueId id = .ok declaration)
    (customLookup : prepared.lookup? id = some customField)
    (matching : customField.declaration = declaration)
    (typeMatching :
      declaration.customType = some customField.customType.declaration) :
    (prepared.checkContext locale raw).read id =
      customField.customType.checkValueRaw locale (raw.read id) := by
  simp [PreparedFlatCustomFields.checkContext,
    PreparedFlatCustomFields.checkContextOver, modelLookup, customLookup,
    matching, typeMatching]

/-- A declaration with no overlay entry retains its declaration-owned checker exactly. -/
theorem preparedCustomContext_noOverlay_exact
    (prepared : PreparedFlatCustomFields model) (locale : String)
    (raw : RawFlatContext) (id : FieldId) (declaration : FlatFieldDecl)
    (modelLookup : model.lookupUniqueId id = .ok declaration)
    (customLookup : prepared.lookup? id = none) :
    (prepared.checkContext locale raw).read id =
      declaration.checkRaw (raw.read id) := by
  cases customType : declaration.customType <;>
    simp [PreparedFlatCustomFields.checkContext,
      PreparedFlatCustomFields.checkContextOver, modelLookup, customLookup,
      customType, FlatModel.checkContext, FlatFieldDecl.checkRaw]

/-- An ordinary declaration delegates to a caller-supplied checked context, enabling the second prepared String consumer without duplicating custom classification. -/
theorem preparedCustomContextOver_ordinary_exact
    (prepared : PreparedFlatCustomFields model) (locale : String)
    (fallback : FlatContext) (raw : RawFlatContext) (id : FieldId)
    (declaration : FlatFieldDecl)
    (modelLookup : model.lookupUniqueId id = .ok declaration)
    (customLookup : prepared.lookup? id = none)
    (ordinary : declaration.customType = none) :
    (prepared.checkContextOver locale fallback raw).read id =
      fallback.read id := by
  simp [PreparedFlatCustomFields.checkContextOver, modelLookup, customLookup,
    ordinary]

/-- A forged custom checker for a different custom declaration fails closed even when its flat declaration field was copied. -/
theorem preparedCustomContext_typeMismatch_is_malformed
    (prepared : PreparedFlatCustomFields model) (locale : String)
    (fallback : FlatContext) (raw : RawFlatContext) (id : FieldId)
    (declaration : FlatFieldDecl) (customField : PreparedFlatCustomField)
    (modelLookup : model.lookupUniqueId id = .ok declaration)
    (customLookup : prepared.lookup? id = some customField)
    (matching : customField.declaration = declaration)
    (typeMismatch :
      declaration.customType ≠ some customField.customType.declaration) :
    (prepared.checkContextOver locale fallback raw).read id =
      malformedCheckedCell := by
  simp [PreparedFlatCustomFields.checkContextOver, modelLookup, customLookup,
    matching, typeMismatch]

/-- The shared prepared String context selects the ordinary pattern checker when no custom declaration exists. -/
theorem preparedFlatStringContext_pattern_exact
    (prepared : PreparedFlatStringContext model compilePattern)
    (locale : String) (raw : RawFlatContext) (id : FieldId)
    (declaration : FlatFieldDecl)
    (modelLookup : model.lookupUniqueId id = .ok declaration)
    (customLookup : prepared.customFields.lookup? id = none)
    (ordinary : declaration.customType = none) :
    (prepared.checkContext locale raw).read id =
      (prepared.patterns.checkContext raw).read id := by
  simp [PreparedFlatStringContext.checkContext,
    PreparedFlatCustomFields.checkContextOver, modelLookup, customLookup,
    ordinary]

/-- The shared prepared String context selects the exact registered custom checker when that declaration owns the field. -/
theorem preparedFlatStringContext_custom_exact
    (prepared : PreparedFlatStringContext model compilePattern)
    (locale : String) (raw : RawFlatContext) (id : FieldId)
    (declaration : FlatFieldDecl) (customField : PreparedFlatCustomField)
    (modelLookup : model.lookupUniqueId id = .ok declaration)
    (customLookup :
      prepared.customFields.lookup? id = some customField)
    (matching : customField.declaration = declaration)
    (typeMatching :
      declaration.customType = some customField.customType.declaration) :
    (prepared.checkContext locale raw).read id =
      customField.customType.checkValueRaw locale (raw.read id) := by
  simp [PreparedFlatStringContext.checkContext,
    PreparedFlatCustomFields.checkContextOver, modelLookup, customLookup,
    matching, typeMatching]

/-- The unprepared legacy context cannot silently treat a declared custom field as an ordinary String. -/
theorem unpreparedCustomContext_failsClosed
    (model : FlatModel) (raw : RawFlatContext) (id : FieldId)
    (declaration : FlatFieldDecl)
    (modelLookup : model.lookupUniqueId id = .ok declaration)
    (custom : declaration.customType.isNone = false) :
    (model.checkContext raw).read id = malformedCheckedCell := by
  cases customType : declaration.customType with
  | none => simp [customType] at custom
  | some customDeclaration =>
      simp [FlatModel.checkContext, modelLookup, FlatFieldDecl.checkRaw, customType]

@[simp]
theorem preparedCustomContext_unknownId
    (prepared : PreparedFlatCustomFields model) (locale : String)
    (raw : RawFlatContext) (id : FieldId) (error : ResolveError)
    (modelLookup : model.lookupUniqueId id = .error error) :
    (prepared.checkContext locale raw).read id = malformedCheckedCell := by
  simp [PreparedFlatCustomFields.checkContext,
    PreparedFlatCustomFields.checkContextOver, modelLookup]

end A12Kernel
