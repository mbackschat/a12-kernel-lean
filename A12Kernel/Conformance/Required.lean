import A12Kernel.Semantics.Required

/-! # Absolute-required conformance locks

These fixtures cover only a required field with no repeatable ancestor. The generated
mandatory condition runs against the base checked cell before the validation-scoped
required finding is attached.
-/

namespace A12Kernel.Conformance.Required

open A12Kernel

private def numberField : FlatNumberField :=
  { id := 0, info := { scale := 2, signed := false } }

private def field : FlatField :=
  .number numberField

private def policy : FieldPolicy :=
  { kind := .number numberField.info }

private def contextWith (cell : CheckedCell) : FlatContext where
  read _ := cell

private def declaration : AbsoluteRequiredDecl :=
  { target := field }

private def emptyBaseContext : FlatContext :=
  contextWith (formalCheck policy .empty)

private def requiredEmpty : AbsoluteRequiredResult :=
  applyAbsoluteRequired field emptyBaseContext

private def requiredMalformed : AbsoluteRequiredResult :=
  applyAbsoluteRequired field (contextWith (formalCheck policy (.rejected .malformed)))

example : declaration.evaluate emptyBaseContext =
    .mandatory mandatoryFieldMetadata := by
  decide

example : (desugarAbsoluteRequired declaration).evaluate emptyBaseContext =
    declaration.evaluate emptyBaseContext := by
  decide

example : requiredEmpty.generated.metadata.errorCode = "mandatoryField" := by
  decide

example : requiredEmpty.generated.metadata.severity.render = "ERROR" := by
  decide

example : requiredEmpty.generated.metadata.messageType.render = "OMISSION" := by
  decide

example : requiredEmpty.mandatoryVerdict = .fired .omission := by
  decide

example : observeCell .validation (requiredEmpty.authoredContext.read numberField.id) =
    .unknown .required := by
  decide

example : observeCell .computation (requiredEmpty.authoredContext.read numberField.id) =
    .empty := by
  decide

/-- The generated rule was evaluated before annotation: the same condition becomes
    unknown if an authored rule reads the now-required cell. -/
example : requiredEmpty.generated.condition.evalFull requiredEmpty.authoredContext false =
    .unknown := by
  decide

/-- An ordinary formal finding neither becomes `mandatoryField` nor loses computation
    poison semantics. -/
example : requiredMalformed.mandatoryVerdict = .unknown := by
  decide

example : observeCell .computation
    (requiredMalformed.authoredContext.read numberField.id) = .poison .malformed := by
  decide

end A12Kernel.Conformance.Required
