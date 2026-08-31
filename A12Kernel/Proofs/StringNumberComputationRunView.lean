import A12Kernel.Elaboration.StringNumberComputationRunView
import A12Kernel.Proofs.NumericComputationRunResult
import A12Kernel.Proofs.StringComputationRunResult

/-! # Family-preserving String and Number result laws -/

namespace A12Kernel

/-- The mixed result's status observes exactly the two error channels in each retained family. -/
theorem stringNumberComputationRun_noErrorOccurred_iff
    (view : StringNumberComputationRunView
      StringResidual NumberPayload Target) :
    view.noErrorOccurred = true ↔
      (view.string.withErrors = [] ∧
        view.string.formalErrorsInOperands = []) ∧
      (view.number.withErrors = [] ∧
        view.number.formalErrorsInOperands = []) := by
  simp [StringNumberComputationRunView.noErrorOccurred,
    StringComputationRunView.noErrorOccurred,
    NumericComputationRunView.noErrorOccurred]

/-- Mixed extensional equality is reflexive without choosing an order for either family. -/
theorem stringNumberComputationRun_extensionalEq_refl
    (view : StringNumberComputationRunView
      StringResidual NumberPayload Target) :
    view.ExtensionalEq view := by
  exact ⟨
    ⟨List.Perm.refl _, List.Perm.refl _, List.Perm.refl _,
      List.Perm.refl _, List.Perm.refl _⟩,
    ⟨List.Perm.refl _, List.Perm.refl _, List.Perm.refl _,
      List.Perm.refl _, List.Perm.refl _⟩
  ⟩

/-- Mixed extensional equality remains symmetric independently in both families. -/
theorem stringNumberComputationRun_extensionalEq_symm
    {left right : StringNumberComputationRunView
      StringResidual NumberPayload Target}
    (equal : left.ExtensionalEq right) :
    right.ExtensionalEq left := by
  rcases equal with
    ⟨⟨s₁, s₂, s₃, s₄, s₅⟩, ⟨n₁, n₂, n₃, n₄, n₅⟩⟩
  exact ⟨
    ⟨s₁.symm, s₂.symm, s₃.symm, s₄.symm, s₅.symm⟩,
    ⟨n₁.symm, n₂.symm, n₃.symm, n₄.symm, n₅.symm⟩
  ⟩

/-- Mixed extensional equality remains transitive independently in both families. -/
theorem stringNumberComputationRun_extensionalEq_trans
    {first second third : StringNumberComputationRunView
      StringResidual NumberPayload Target}
    (firstSecond : first.ExtensionalEq second)
    (secondThird : second.ExtensionalEq third) :
    first.ExtensionalEq third := by
  rcases firstSecond with
    ⟨⟨s₁, s₂, s₃, s₄, s₅⟩, ⟨n₁, n₂, n₃, n₄, n₅⟩⟩
  rcases secondThird with
    ⟨⟨s₁', s₂', s₃', s₄', s₅'⟩, ⟨n₁', n₂', n₃', n₄', n₅'⟩⟩
  exact ⟨
    ⟨s₁.trans s₁', s₂.trans s₂', s₃.trans s₃', s₄.trans s₄',
      s₅.trans s₅'⟩,
    ⟨n₁.trans n₁', n₂.trans n₂', n₃.trans n₃', n₄.trans n₄',
      n₅.trans n₅'⟩
  ⟩

end A12Kernel
