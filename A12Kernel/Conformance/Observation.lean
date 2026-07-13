import A12Kernel.Semantics.Observation

/-! # Observation conformance locks

Small executable examples for the phase-sensitive cell boundary. These are semantic
fixtures, not a transcription of any engine implementation.
-/

namespace A12Kernel.Conformance.Observation

open A12Kernel

private def optionalNumber : FieldPolicy :=
  { kind := .number { scale := 2, signed := false } }

private def confirm : FieldPolicy :=
  { kind := .confirm }

private def requiredEmpty : CheckedCell :=
  (formalCheck optionalNumber .empty).withFinding .required

example : formalCheck optionalNumber .empty =
    { rawPresent := false, parsed := none, findings := [] } := by
  decide

example : observeCell .validation (formalCheck optionalNumber .empty) = .empty := by
  rfl

example : observeCell .computation (formalCheck optionalNumber .empty) = .empty := by
  rfl

example : observeCell .validation requiredEmpty = .unknown .required := by
  decide

example : observeCell .computation requiredEmpty = .empty := by
  decide

example : observeCell .validation (formalCheck optionalNumber (.rejected .malformed)) =
    .unknown .malformed := by
  decide

example : observeCell .computation (formalCheck optionalNumber (.rejected .malformed)) =
    .poison .malformed := by
  decide

example : formalCheck confirm (.parsed (.conf false)) =
    { rawPresent := true, parsed := none, findings := [.malformed] } := by
  decide

end A12Kernel.Conformance.Observation
