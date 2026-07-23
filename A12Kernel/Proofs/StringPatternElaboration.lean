import A12Kernel.Proofs.PatternAdmission

/-! # Checked authored String-pattern laws -/

namespace A12Kernel

/-- Prepared declaration checking delegates exactly once to the declaration policy and the compiler-associated optional matcher. -/
@[simp]
theorem preparedDeclaredStringField_checkRaw
    (prepared : PreparedDeclaredStringField model compilePattern)
    (raw : RawCell) :
    prepared.checkRaw raw =
      prepared.declaration.stringPolicy.checkRawWithPattern
        (prepared.pattern.map (·.wholeValueMatches)) raw := by
  rfl

/-- The one-field prepared overlay replaces exactly its certified field and leaves model-owned checking for every other identifier. -/
@[simp]
theorem preparedDeclaredStringField_checkContext_own
    (prepared : PreparedDeclaredStringField model compilePattern)
    (raw : RawFlatContext) :
    (prepared.checkContext raw).read prepared.field =
      prepared.checkRaw (raw.read prepared.field) := by
  simp [PreparedDeclaredStringField.checkContext]

/-- Every different identifier continues through the ordinary model-owned checked context. -/
theorem preparedDeclaredStringField_checkContext_other
    (prepared : PreparedDeclaredStringField model compilePattern)
    (raw : RawFlatContext) (field : FieldId)
    (different : field ≠ prepared.field) :
    (prepared.checkContext raw).read field =
      (model.checkContext raw).read field := by
  simp [PreparedDeclaredStringField.checkContext, different]

/-- A prepared declaration can never detach its matcher from the exact effective source retained by the declaration. -/
theorem preparedDeclaredStringField_source_coherent
    (prepared : PreparedDeclaredStringField model compilePattern) :
    DeclaredStringPatternCoherent prepared.declaration prepared.pattern :=
  prepared.patternCoherent

/-- A checked authored pattern condition delegates its reached read to the exact matcher returned for its admitted source. -/
@[simp]
theorem checkedStringPattern_evalSelected
    (checked : CheckedStringPatternCondition model compilePattern)
    (context : FlatContext) :
    checked.evalSelected context =
      checked.op.evalResolved checked.pattern.wholeValueMatches
        (context.resolveDirectStringComparisonOperand checked.field) := by
  rfl

/-- Pattern leaves never bypass the all-empty full-validation row gate. -/
@[simp]
theorem checkedStringPattern_emptyRow_notFired
    (checked : CheckedStringPatternCondition model compilePattern)
    (raw : RawFlatContext) :
    checked.evalFull raw false = .notFired := by
  rfl

/-- Any firing from the checked authored route retains the resolved pattern family's VALUE-only polarity. -/
theorem checkedStringPattern_fired_is_value
    (checked : CheckedStringPatternCondition model compilePattern)
    (context : FlatContext) (polarity : Polarity)
    (fired : checked.evalSelected context = .fired polarity) :
    polarity = .value := by
  exact admittedStringPattern_fired_is_value checked.pattern checked.op
    (context.resolveDirectStringComparisonOperand checked.field) polarity fired

/-- The checked direct field is the authored condition's sole reference. -/
@[simp]
theorem checkedStringPattern_referencesField
    (checked : CheckedStringPatternCondition model compilePattern) :
    checked.referencesField checked.field.id = true := by
  simp [CheckedStringPatternCondition.referencesField]

end A12Kernel
