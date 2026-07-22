import A12Kernel.Elaboration.CustomField

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
    (prepared : PreparedFlatCustomFields) (locale : String)
    (raw : RawFlatContext) (id : FieldId) (declaration : FlatFieldDecl)
    (customField : PreparedFlatCustomField)
    (modelLookup : prepared.model.lookupUniqueId id = .ok declaration)
    (customLookup : prepared.lookup? id = some customField)
    (matching : customField.declaration = declaration) :
    (prepared.checkContext locale raw).read id =
      customField.customType.checkValueRaw locale (raw.read id) := by
  simp [PreparedFlatCustomFields.checkContext, modelLookup, customLookup, matching]

/-- An ordinary declaration with no overlay entry retains the existing formal checker exactly. -/
theorem preparedCustomContext_ordinary_exact
    (prepared : PreparedFlatCustomFields) (locale : String)
    (raw : RawFlatContext) (id : FieldId) (declaration : FlatFieldDecl)
    (modelLookup : prepared.model.lookupUniqueId id = .ok declaration)
    (customLookup : prepared.lookup? id = none)
    (ordinary : declaration.customType = none) :
    (prepared.checkContext locale raw).read id =
      formalCheck declaration.policy (raw.read id) := by
  simp [PreparedFlatCustomFields.checkContext, modelLookup, customLookup, ordinary]

/-- The unprepared legacy context cannot silently treat a declared custom field as an ordinary String. -/
theorem unpreparedCustomContext_failsClosed
    (model : FlatModel) (raw : RawFlatContext) (id : FieldId)
    (declaration : FlatFieldDecl)
    (modelLookup : model.lookupUniqueId id = .ok declaration)
    (custom : declaration.customType.isNone = false) :
    (model.checkContext raw).read id = malformedCheckedCell := by
  cases customType : declaration.customType with
  | none => simp [customType] at custom
  | some declaration =>
      simp [FlatModel.checkContext, modelLookup, customType]

@[simp]
theorem preparedCustomContext_unknownId
    (prepared : PreparedFlatCustomFields) (locale : String)
    (raw : RawFlatContext) (id : FieldId) (error : ResolveError)
    (modelLookup : prepared.model.lookupUniqueId id = .error error) :
    (prepared.checkContext locale raw).read id = malformedCheckedCell := by
  simp [PreparedFlatCustomFields.checkContext, modelLookup]

end A12Kernel
