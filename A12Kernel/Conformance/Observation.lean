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

private def string : FieldPolicy :=
  { kind := .string }

private def requiredEmpty : CheckedCell :=
  (formalCheck optionalNumber .empty).withFinding .required

example : formalCheck optionalNumber .empty =
    { rawPresent := false, parsed := none, findings := [] } := by
  decide

example : observeCell .validation (formalCheck optionalNumber .empty) = .empty := by
  rfl

example : observeCell .computation (formalCheck optionalNumber .empty) = .empty := by
  rfl

example : formalCheck string .presentEmpty =
    { rawPresent := true, parsed := none, findings := [] } := by
  decide

example : formalCheck string (.parsed (.str "")) = formalCheck string .presentEmpty := by
  decide

example : formalCheck string .presentEmpty != formalCheck string .empty := by
  decide

example :
    observeCell .validation (formalCheck string .presentEmpty) = .empty ∧
      observeCell .computation (formalCheck string .presentEmpty) = .empty := by
  decide

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

/- The shared checked boundary retains a temporal or other typed value without wrapping it in the scalar `Value` sum. -/
example (value : Nat) :
    observeCell .validation
      ({ rawPresent := true, parsed := some value, findings := [] } : CheckedCell Nat) =
        (.value value : CellObservation Nat) := by
  rfl

/- Typed present-empty cells and formal findings use the same phase projection. -/
example :
    observeCell .validation
        ({ rawPresent := true, parsed := none, findings := [] } : CheckedCell Nat) =
          (.empty : CellObservation Nat) ∧
      observeCell .computation
        ({ rawPresent := true, parsed := none, findings := [.malformed] } : CheckedCell Nat) =
          (.poison .malformed : CellObservation Nat) := by
  decide

/- An already-admitted typed parser result retains the same placement and rejection states as scalar ingestion. -/
example :
    checkAdmittedRawCell (.parsed 7 : RawCell Nat) =
        ({ rawPresent := true, parsed := some 7, findings := [] } : CheckedCell Nat) ∧
      checkAdmittedRawCell (.empty : RawCell Nat) =
        ({ rawPresent := false, parsed := none, findings := [] } : CheckedCell Nat) ∧
      checkAdmittedRawCell (.rejected .declaredConstraint : RawCell Nat) =
        ({ rawPresent := true
           parsed := none
           findings := [.declaredConstraint] } : CheckedCell Nat) := by
  decide

end A12Kernel.Conformance.Observation
