import A12Kernel.Proofs.PatternAdmission

/-! # Checked authored String-pattern laws -/

namespace A12Kernel

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
