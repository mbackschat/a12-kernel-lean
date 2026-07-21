import A12Kernel.Semantics.Observation

/-! # A12Kernel.Proofs.Observation — cell-boundary invariants and phase laws -/

namespace A12Kernel

theorem formalCheck_wellFormed (policy : FieldPolicy) (raw : RawCell) :
    (formalCheck policy raw).WellFormed := by
  cases raw with
  | empty => simp [formalCheck, CheckedCell.WellFormed]
  | presentEmpty => simp [formalCheck, CheckedCell.WellFormed]
  | parsed value =>
      rcases policy with ⟨kind⟩
      cases kind <;> cases value <;>
        simp [formalCheck, CheckedCell.WellFormed, FieldKind.accepts] <;>
        split <;> simp_all
  | rejected cause => simp [formalCheck, CheckedCell.WellFormed]

theorem withFinding_preserves_wellFormed (cell : CheckedCell) (cause : FormalCause)
    (h : cell.WellFormed) : (cell.withFinding cause).WellFormed := by
  exact h

/-- A clean absent cell crosses the shared observation boundary without acquiring a
    kind- or phase-specific substitute. The consuming semantic clause owns that choice. -/
theorem formalCheck_empty_observes_empty (policy : FieldPolicy) (phase : Phase) :
    observeCell phase (formalCheck policy .empty) = .empty := by
  cases phase <;> rfl

/-- A present cell with no raw value preserves its physical placement while carrying no
    evaluation value or finding. -/
theorem formalCheck_presentEmpty_preservesPlacement (policy : FieldPolicy) :
    formalCheck policy .presentEmpty = {
      rawPresent := true
      parsed := none
      findings := [] } := by
  rfl

/-- Present-empty and absent remain different checked cells for every field policy. -/
theorem formalCheck_presentEmpty_notAbsent (policy : FieldPolicy) :
    formalCheck policy .presentEmpty ≠ formalCheck policy .empty := by
  simp [formalCheck]

/-- Present-empty supplies the same unspecified evaluation observation as absence; the
    consuming semantic clause still owns any kind- or operator-specific substitution. -/
theorem formalCheck_presentEmpty_observes_empty (policy : FieldPolicy) (phase : Phase) :
    observeCell phase (formalCheck policy .presentEmpty) = .empty := by
  cases phase <;> rfl

/-- Raw empty String text and a present cell with no raw value share one checked
    present-empty state. -/
theorem formalCheck_parsedEmptyString_eq_presentEmpty :
    formalCheck { kind := .string } (.parsed (.str "")) =
      formalCheck { kind := .string } .presentEmpty := by
  rfl

/-- A parser-boundary empty String supplies the same unspecified evaluation observation
    as an absent raw value while retaining a distinct checked placement. -/
theorem formalCheck_parsedEmptyString_observes_empty (phase : Phase) :
    observeCell phase (formalCheck { kind := .string } (.parsed (.str ""))) = .empty := by
  rw [formalCheck_parsedEmptyString_eq_presentEmpty]
  exact formalCheck_presentEmpty_observes_empty _ phase

/-- A clean synthetic computation cell exposes its parsed value without adding a phase-specific interpretation. -/
theorem computation_observes_clean_value (value : Value) :
    observeCell .computation {
      rawPresent := true
      parsed := some value
      findings := [] } = .value value := by
  rfl

/-- A synthetic computation cell with one non-required finding exposes that finding as poison and ignores its absent parsed payload. -/
theorem computation_observes_single_poison (cause : FormalCause)
    (notRequired : cause ≠ .required) :
    observeCell .computation {
      rawPresent := true
      parsed := none
      findings := [cause] } = .poison cause := by
  cases cause <;> first | contradiction | rfl

theorem required_empty_observes_unknown_in_validation (policy : FieldPolicy) :
    observeCell .validation ((formalCheck policy .empty).withFinding .required) =
      .unknown .required := by
  rfl

theorem required_empty_observes_empty_in_computation (policy : FieldPolicy) :
    observeCell .computation ((formalCheck policy .empty).withFinding .required) = .empty := by
  rfl

theorem ordinary_finding_still_poisons_computation (policy : FieldPolicy)
    (cause : BaseFormalCause) :
    observeCell .computation ((formalCheck policy (.rejected cause)).withFinding .required) =
      .poison cause.toFormalCause := by
  cases cause <;> simp [formalCheck, BaseFormalCause.toFormalCause,
    CheckedCell.withFinding, observeCell] <;> rfl

end A12Kernel
