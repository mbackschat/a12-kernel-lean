import A12Kernel.Semantics.Required

/-! # Proofs for absolute-required staging

The main phase law is deliberately universal over checked cells: appending the
validation-scoped required finding cannot change what computation observes. The second
law records the opposite validation face for a clean empty cell.
-/

namespace A12Kernel

/-- Lowering an admitted source declaration to `FieldNotFilled` preserves both its
    mandatory outcome and its message metadata. -/
theorem desugarAbsoluteRequired_preserves (declaration : AbsoluteRequiredDecl)
    (context : FlatContext) :
    (desugarAbsoluteRequired declaration).evaluate context = declaration.evaluate context := by
  cases declaration with
  | mk target =>
      cases target with
      | number field =>
          simp [AbsoluteRequiredRule.evaluate, AbsoluteRequiredDecl.evaluate,
            desugarAbsoluteRequired, mandatoryFieldMetadata, FlatCondition.evalFull,
            FlatCondition.canFireOnEmpty, FlatCondition.evalSelected, FlatField.evalNotFilled]
          cases (FlatField.number field).observeValidation context <;> rfl
      | boolean field =>
          simp [AbsoluteRequiredRule.evaluate, AbsoluteRequiredDecl.evaluate,
            desugarAbsoluteRequired, mandatoryFieldMetadata, FlatCondition.evalFull,
            FlatCondition.canFireOnEmpty, FlatCondition.evalSelected, FlatField.evalNotFilled]
          cases (FlatField.boolean field).observeValidation context <;> rfl
      | confirm field =>
          simp [AbsoluteRequiredRule.evaluate, AbsoluteRequiredDecl.evaluate,
            desugarAbsoluteRequired, mandatoryFieldMetadata, FlatCondition.evalFull,
            FlatCondition.canFireOnEmpty, FlatCondition.evalSelected, FlatField.evalNotFilled]
          cases (FlatField.confirm field).observeValidation context <;> rfl
      | string field =>
          simp [AbsoluteRequiredRule.evaluate, AbsoluteRequiredDecl.evaluate,
            desugarAbsoluteRequired, mandatoryFieldMetadata, FlatCondition.evalFull,
            FlatCondition.canFireOnEmpty, FlatCondition.evalSelected, FlatField.evalNotFilled]
          cases (FlatField.string field).observeValidation context <;> rfl
      | enumeration field =>
          simp [AbsoluteRequiredRule.evaluate, AbsoluteRequiredDecl.evaluate,
            desugarAbsoluteRequired, mandatoryFieldMetadata, FlatCondition.evalFull,
            FlatCondition.canFireOnEmpty, FlatCondition.evalSelected, FlatField.evalNotFilled]
          cases (FlatField.enumeration field).observeValidation context <;> rfl
      | temporal field =>
          simp [AbsoluteRequiredRule.evaluate, AbsoluteRequiredDecl.evaluate,
            desugarAbsoluteRequired, mandatoryFieldMetadata, FlatCondition.evalFull,
            FlatCondition.canFireOnEmpty, FlatCondition.evalSelected, FlatField.evalNotFilled]
          cases (FlatField.temporal field).observeValidation context <;> rfl
/-- Required annotation is computation-inert, even when it follows an ordinary finding.
    This is the preservation property that lets requiredness share `CheckedCell` without
    turning compute-time empty substitution into poison. -/
theorem withRequiredFinding_preserves_computation (cell : CheckedCell) :
    observeCell .computation (cell.withFinding .required) =
      observeCell .computation cell := by
  cases cell with
  | mk rawPresent parsed findings =>
      induction findings with
      | nil => cases parsed <;> rfl
      | cons cause rest ih =>
          cases cause <;> first | exact ih | rfl

/-- The complete two-pass transformation preserves computation observations at every
    field, not only at the required target. -/
theorem applyAbsoluteRequired_preserves_computation (field : FlatField)
    (context : FlatContext) (id : FieldId) :
    observeCell .computation
        ((applyAbsoluteRequired field context).authoredContext.read id) =
      observeCell .computation (context.read id) := by
  unfold applyAbsoluteRequired
  generalize verdictEq :
    (desugarAbsoluteRequired { target := field }).condition.evalFull context false = verdict
  cases verdict with
  | notFired => simp [verdictEq]
  | unknown => simp [verdictEq]
  | fired polarity =>
      cases polarity with
      | value => simp [verdictEq]
      | omission =>
          simp only [verdictEq, FlatContext.withRequiredFindingAt]
          split
          · exact withRequiredFinding_preserves_computation (context.read id)
          · rfl

/-- On a clean empty cell the same annotation is visible to validation but remains
    ordinary empty to computation. -/
theorem requiredFinding_empty_phase_split :
    let base : CheckedCell :=
      { rawPresent := false, parsed := none, findings := [] }
    observeCell .validation (base.withFinding .required) = .unknown .required ∧
      observeCell .computation (base.withFinding .required) = .empty := by
  apply And.intro <;> rfl

/-- Absolute String requiredness consumes evaluation emptiness and keeps a present-empty placement while attaching the staged finding. -/
theorem absoluteRequired_string_presentEmpty_preservesPlacement
    (field : FlatStringField) :
    let context : FlatContext :=
      { read := fun _ => formalCheck { kind := .string } .presentEmpty }
    let result := applyAbsoluteRequired (.string field) context
    result.mandatoryVerdict = .fired .omission ∧
      result.authoredContext.read field.id = {
        rawPresent := true
        parsed := none
        findings := [.required] } := by
  simp [applyAbsoluteRequired, desugarAbsoluteRequired,
    FlatCondition.evalFull, FlatCondition.canFireOnEmpty,
    FlatCondition.evalSelected, FlatField.evalNotFilled,
    FlatField.id, FlatField.observeValidation, FlatContext.observeValidationAt,
    FlatContext.withRequiredFindingAt, formalCheck,
    CheckedCell.withFinding, observeCell]

end A12Kernel
