import A12Kernel.Proofs.PatternAdmission

/-! # Checked authored String-pattern laws -/

namespace A12Kernel

/-- Prepared declaration checking delegates exactly once to the declaration policy and the compiler-associated optional matcher. -/
@[simp]
theorem preparedDeclaredStringField_checkRaw
    (prepared : PreparedDeclaredStringField compilePattern)
    (raw : RawCell) :
    prepared.checkRaw raw =
      prepared.declaration.stringPolicy.checkRawWithPattern
        (prepared.pattern.map (·.wholeValueMatches)) raw := by
  rfl

/-- A prepared declaration can never detach its matcher from the exact effective source retained by the declaration. -/
theorem preparedDeclaredStringField_source_coherent
    (prepared : PreparedDeclaredStringField compilePattern) :
    DeclaredStringPatternCoherent prepared.declaration prepared.pattern :=
  prepared.patternCoherent

/-- An exact prepared declaration replaces its model-owned raw read. -/
theorem preparedFlatStringPatterns_checkContext_prepared
    (prepared : PreparedFlatStringPatterns model compilePattern)
    (raw : RawFlatContext) (field : FieldId)
    (declaration : FlatFieldDecl)
    (preparedField : PreparedDeclaredStringField compilePattern)
    (modelLookup : model.lookupUniqueId field = .ok declaration)
    (preparedLookup : prepared.lookup? field = some preparedField)
    (matching : preparedField.declaration = declaration) :
    (prepared.checkContext raw).read field =
      preparedField.checkRaw (raw.read field) := by
  simp [PreparedFlatStringPatterns.checkContext, modelLookup, preparedLookup,
    matching]

/-- A missing entry for an effective declared pattern fails closed rather than bypassing the matcher. -/
theorem preparedFlatStringPatterns_missingPattern_is_malformed
    (prepared : PreparedFlatStringPatterns model compilePattern)
    (raw : RawFlatContext) (field : FieldId)
    (declaration : FlatFieldDecl)
    (modelLookup : model.lookupUniqueId field = .ok declaration)
    (preparedLookup : prepared.lookup? field = none)
    (required : declaration.effectiveStringPatternSource.isSome = true) :
    (prepared.checkContext raw).read field = malformedCheckedCell := by
  simp [PreparedFlatStringPatterns.checkContext, modelLookup, preparedLookup,
    required]

/-- A declaration without an effective pattern retains the ordinary model-owned checked read. -/
theorem preparedFlatStringPatterns_noPattern_delegates
    (prepared : PreparedFlatStringPatterns model compilePattern)
    (raw : RawFlatContext) (field : FieldId)
    (declaration : FlatFieldDecl)
    (modelLookup : model.lookupUniqueId field = .ok declaration)
    (preparedLookup : prepared.lookup? field = none)
    (inactive : declaration.effectiveStringPatternSource = none) :
    (prepared.checkContext raw).read field =
      (model.checkContext raw).read field := by
  simp [PreparedFlatStringPatterns.checkContext, modelLookup, preparedLookup,
    inactive]

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
    (prepared : PreparedFlatStringPatterns model compilePattern)
    (raw : RawFlatContext) :
    checked.evalFull prepared raw false = .notFired := by
  rfl

/-- A content-bearing row evaluates through exactly the model-complete prepared context. -/
@[simp]
theorem checkedStringPattern_full_delegates
    (checked : CheckedStringPatternCondition model compilePattern)
    (prepared : PreparedFlatStringPatterns model compilePattern)
    (raw : RawFlatContext) :
    checked.evalFull prepared raw true =
      checked.evalSelected (prepared.checkContext raw) := by
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
