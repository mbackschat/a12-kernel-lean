import A12Kernel.Semantics.Observation

/-! # A12Kernel.Conformance.CustomFieldCause — registered rejection identity locks -/

namespace A12Kernel.Conformance.CustomFieldCause

open A12Kernel

private def rejection : RegisteredCustomRejection where
  projectCode := "PROJECT_CODE_INVALID"
  messageTemplate := some "Invalid $<fieldName>$"

private def checked : CheckedCell :=
  checkRawCellWith
    (fun (_ : Value) => .error (.registeredCustomValidation rejection))
    (.parsed (.str "bad"))

/- The registered path retains the project code and optional message instead of collapsing into the fixed fallback. -/
example : checked.findings = [.registeredCustomValidation rejection] := by
  rfl

example : checked.findings != [.customValidation] := by
  decide

/- Ordinary phase observation preserves the complete cause. -/
example : observeCell .validation checked =
    .unknown (.registeredCustomValidation rejection) := by
  rfl

example : observeCell .computation checked =
    .poison (.registeredCustomValidation rejection) := by
  rfl

end A12Kernel.Conformance.CustomFieldCause
