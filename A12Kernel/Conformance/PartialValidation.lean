import A12Kernel.Semantics.PartialValidation

/-! # Flat, nonrepeatable partial-validation separating cases -/

namespace A12Kernel.Conformance.PartialValidation

open A12Kernel

private def errorField : FlatBooleanField := { id := 0 }
private def otherField : FlatBooleanField := { id := 1 }

private def filledContext : FlatContext where
  read id :=
    if id = errorField.id || id = otherField.id then
      formalCheck { kind := .boolean } (.parsed (.bool true))
    else formalCheck { kind := .boolean } .empty

private def errorFilled : FlatCondition := .fieldFilled (.boolean errorField)
private def otherFilled : FlatCondition := .fieldFilled (.boolean otherField)
private def bothFilled : FlatCondition := .and errorFilled otherFilled
private def eitherFilled : FlatCondition := .or errorFilled otherFilled
private def only (field : FieldId) : FlatRelevance := fun candidate => candidate == field
private def bothRelevant : FlatRelevance := fun candidate => candidate == errorField.id || candidate == otherField.id

example :
    bothFilled.evalPartial filledContext errorField.id bothRelevant =
        .evaluated (bothFilled.evalFull filledContext true) ∧
      bothFilled.evalPartial filledContext errorField.id (only errorField.id) =
        .evaluated .unknown ∧
      eitherFilled.evalPartial filledContext errorField.id (only errorField.id) =
        .evaluated (.fired .value) := by
  native_decide

/-! Masking alone would fire `Unknown Or True`; the independent error-field gate skips. -/
example :
    eitherFilled.evalSelected filledContext (only otherField.id) = .fired .value ∧
      eitherFilled.evalPartial filledContext errorField.id (only otherField.id) =
        .skipped := by
  native_decide

/-! Nearest non-law: relevant error-field gating does not make partial equal full. -/
example :
    (FlatCondition.compare (.boolean .equal otherField true)).evalPartial
        filledContext errorField.id (only errorField.id) = .evaluated .unknown ∧
      (FlatCondition.compare (.boolean .equal otherField true)).evalFull
        filledContext true = .fired .value := by
  native_decide

private def numberField : FlatNumberField :=
  { id := 2, info := { scale := 0, signed := false } }
private def emptyNumberContext : FlatContext where
  read _ := formalCheck { kind := .number numberField.info } .empty
private def emptyNumberIsZero : FlatCondition :=
  .compare (.number .equal numberField 0)

/-! A relevant instance bypasses the ordinary full-validation content gate. -/
example :
    emptyNumberIsZero.evalPartial emptyNumberContext numberField.id
        (only numberField.id) = .evaluated (.fired .omission) ∧
      emptyNumberIsZero.evalFull emptyNumberContext false = .notFired := by
  native_decide

end A12Kernel.Conformance.PartialValidation
