import A12Kernel.Semantics.Observation

/-! # A12Kernel.Proofs.Observation — cell-boundary invariants and phase laws -/

namespace A12Kernel

theorem formalCheck_wellFormed (policy : FieldPolicy) (raw : RawCell) :
    (formalCheck policy raw).WellFormed := by
  cases raw with
  | empty => simp [formalCheck, CheckedCell.WellFormed]
  | parsed value =>
      simp [formalCheck, CheckedCell.WellFormed]
      split <;> simp_all
  | rejected cause => simp [formalCheck, CheckedCell.WellFormed]

theorem withFinding_preserves_wellFormed (cell : CheckedCell) (cause : FormalCause)
    (h : cell.WellFormed) : (cell.withFinding cause).WellFormed := by
  rcases h with ⟨absent, present⟩
  constructor
  · exact absent
  · intro rawPresent
    rcases present rawPresent with parsed | findings
    · exact Or.inl parsed
    · exact Or.inr (by simp [CheckedCell.withFinding])

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
