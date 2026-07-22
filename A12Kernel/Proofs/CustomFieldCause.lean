import A12Kernel.Semantics.Observation

/-! # A12Kernel.Proofs.CustomFieldCause — registered rejection identity laws -/

namespace A12Kernel

/-- The registered-validator cause is structurally distinct from the fixed declarative fallback. -/
theorem registeredCustomValidation_ne_fixedFallback
    (rejection : RegisteredCustomRejection) :
    FormalCause.registeredCustomValidation rejection ≠
      .customValidation := by
  intro impossible
  cases impossible

/-- The base formal-check result retains the complete registered rejection. -/
theorem registeredCustomValidation_toFormalCause
    (rejection : RegisteredCustomRejection) :
    (BaseFormalCause.registeredCustomValidation rejection).toFormalCause =
      .registeredCustomValidation rejection := by
  rfl

/-- One checked registered rejection supplies the same exact project payload to both phase projections. -/
theorem registeredCustomValidation_phase_projection
    (rejection : RegisteredCustomRejection) (value : Value) :
    let checked : CheckedCell := checkRawCellWith
      (fun (_ : Value) => .error (.registeredCustomValidation rejection))
      (.parsed value)
    observeCell .validation checked =
        .unknown (.registeredCustomValidation rejection) ∧
      observeCell .computation checked =
        .poison (.registeredCustomValidation rejection) := by
  constructor <;> rfl

end A12Kernel
