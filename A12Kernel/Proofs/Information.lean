import A12Kernel.Core

/-! # A12Kernel.Proofs.Information — the strong-Kleene information order

Information refinement is not a truth order. `unknown` may become either definite truth
value; an already-definite value may only remain itself. This is the precise vocabulary
needed before making any monotonicity claim about validation.
-/

namespace A12Kernel.K

/-- `less ⊑ more`: `more` contains at least the truth information in `less`. -/
def InformationRefines : K → K → Prop
  | .unknown, _ => True
  | .tru, .tru => True
  | .fls, .fls => True
  | _, _ => False

theorem informationRefines_refl (value : K) : InformationRefines value value := by
  cases value <;> trivial

theorem definite_true_stable (value : K) (h : InformationRefines .tru value) :
    value = .tru := by
  cases value <;> simp_all [InformationRefines]

theorem definite_false_stable (value : K) (h : InformationRefines .fls value) :
    value = .fls := by
  cases value <;> simp_all [InformationRefines]

theorem and_information_monotone {left₁ left₂ right₁ right₂ : K}
    (leftRefines : InformationRefines left₁ left₂)
    (rightRefines : InformationRefines right₁ right₂) :
    InformationRefines (and left₁ right₁) (and left₂ right₂) := by
  cases left₁ <;> cases left₂ <;> cases right₁ <;> cases right₂ <;>
    simp_all [InformationRefines, and]

theorem or_information_monotone {left₁ left₂ right₁ right₂ : K}
    (leftRefines : InformationRefines left₁ left₂)
    (rightRefines : InformationRefines right₁ right₂) :
    InformationRefines (or left₁ right₁) (or left₂ right₂) := by
  cases left₁ <;> cases left₂ <;> cases right₁ <;> cases right₂ <;>
    simp_all [InformationRefines, or]

end A12Kernel.K
