import A12Kernel.Proofs.Observation
import A12Kernel.Semantics.ComputationCondition

/-! # A12Kernel.Proofs.ComputationCondition — direct computation-presence laws

These laws characterize presence after computation-phase observation. They do not claim that the external kernel exposes the internal `poison` cause or that direct presence covers composite computation conditions.
-/

namespace A12Kernel

/-- A clean empty computation read does not satisfy `FieldFilled`. -/
theorem fieldFilled_observedEmpty_notTrue
    (context : ScalarComputationContext) (field : FieldId)
    (observed : observeCell .computation (context.read field) = .empty) :
    (ComputationCondition.fieldFilled field).eval context = .notTrue := by
  simp only [ComputationCondition.eval, ComputationCondition.evalFieldFilled, observed]

/-- A clean empty computation read satisfies `FieldNotFilled`. -/
theorem fieldNotFilled_observedEmpty_holds
    (context : ScalarComputationContext) (field : FieldId)
    (observed : observeCell .computation (context.read field) = .empty) :
    (ComputationCondition.fieldNotFilled field).eval context = .holds := by
  simp only [ComputationCondition.eval, ComputationCondition.evalFieldFilled, observed]

/-- Any clean scalar value satisfies `FieldFilled`, independently of its scalar value. -/
theorem fieldFilled_observedValue_holds
    (context : ScalarComputationContext) (field : FieldId) (value : Value)
    (observed : observeCell .computation (context.read field) = .value value) :
    (ComputationCondition.fieldFilled field).eval context = .holds := by
  simp only [ComputationCondition.eval, ComputationCondition.evalFieldFilled, observed]

/-- Any clean scalar value does not satisfy `FieldNotFilled`. -/
theorem fieldNotFilled_observedValue_notTrue
    (context : ScalarComputationContext) (field : FieldId) (value : Value)
    (observed : observeCell .computation (context.read field) = .value value) :
    (ComputationCondition.fieldNotFilled field).eval context = .notTrue := by
  simp only [ComputationCondition.eval, ComputationCondition.evalFieldFilled, observed]

/-- A computation-phase poison remains the exact poison under `FieldFilled`. -/
theorem fieldFilled_observedPoison_preserves
    (context : ScalarComputationContext) (field : FieldId) (cause : FormalCause)
    (observed : observeCell .computation (context.read field) = .poison cause) :
    (ComputationCondition.fieldFilled field).eval context = .poison cause := by
  simp only [ComputationCondition.eval, ComputationCondition.evalFieldFilled, observed]

/-- `FieldNotFilled` reverses only clean truth; it preserves the same poison as `FieldFilled`. -/
theorem fieldNotFilled_observedPoison_preserves
    (context : ScalarComputationContext) (field : FieldId) (cause : FormalCause)
    (observed : observeCell .computation (context.read field) = .poison cause) :
    (ComputationCondition.fieldNotFilled field).eval context = .poison cause := by
  simp only [ComputationCondition.eval, ComputationCondition.evalFieldFilled, observed]

/-- Validation-scoped requiredness on an otherwise empty field remains clean not-filled in computation. -/
theorem requiredOnlyFieldNotFilled_holds
    (policy : FieldPolicy) (field : FieldId) :
    (ComputationCondition.fieldNotFilled field).eval {
      read := fun _ => (formalCheck policy .empty).withFinding .required
    } = .holds := by
  apply fieldNotFilled_observedEmpty_holds
  exact required_empty_observes_empty_in_computation policy

/-- An ordinary formal finding still poisons direct presence even when requiredness is also attached. -/
theorem ordinaryFindingFieldNotFilled_poisons
    (policy : FieldPolicy) (field : FieldId) (cause : BaseFormalCause) :
    (ComputationCondition.fieldNotFilled field).eval {
      read := fun _ => (formalCheck policy (.rejected cause)).withFinding .required
    } = .poison cause.toFormalCause := by
  apply fieldNotFilled_observedPoison_preserves
  exact ordinary_finding_still_poisons_computation policy cause

/-- `FieldNotFilled` is not Boolean negation at the poison boundary: both presence predicates retain the same cause. -/
theorem presencePredicates_agree_on_poison
    (context : ScalarComputationContext) (field : FieldId) (cause : FormalCause)
    (observed : observeCell .computation (context.read field) = .poison cause) :
    (ComputationCondition.fieldFilled field).eval context =
        (ComputationCondition.fieldNotFilled field).eval context ∧
      (ComputationCondition.fieldNotFilled field).eval context = .poison cause := by
  rw [fieldFilled_observedPoison_preserves context field cause observed,
    fieldNotFilled_observedPoison_preserves context field cause observed]
  constructor <;> rfl

end A12Kernel
