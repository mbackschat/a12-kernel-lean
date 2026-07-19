import A12Kernel.Proofs.Observation
import A12Kernel.Semantics.ComputationCondition

/-! # A12Kernel.Proofs.ComputationCondition — computation presence and ordered-connective laws

These laws characterize presence after computation-phase observation and the complete left-to-right decision table for the admitted `And`/`Or` fragment. They do not claim that the external kernel exposes the internal `poison` cause or that this fragment covers comparisons, quantifiers, paths, or alternatives.
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

/-- A clean not-true left operand decides computation `And` without consulting the right operand. -/
theorem computationAnd_leftNotTrue_shortCircuits
    (context : ScalarComputationContext) (left right : ComputationCondition)
    (leftResult : left.eval context = .notTrue) :
    (ComputationCondition.and left right).eval context = .notTrue := by
  simp only [ComputationCondition.eval, leftResult]

/-- A holding left operand delegates computation `And` to the right operand. -/
theorem computationAnd_leftHolds_evaluatesRight
    (context : ScalarComputationContext) (left right : ComputationCondition)
    (leftResult : left.eval context = .holds) :
    (ComputationCondition.and left right).eval context = right.eval context := by
  simp only [ComputationCondition.eval, leftResult]

/-- A poison already read on the left aborts computation `And` with the same cause. -/
theorem computationAnd_leftPoison_preserves
    (context : ScalarComputationContext) (left right : ComputationCondition)
    (cause : FormalCause) (leftResult : left.eval context = .poison cause) :
    (ComputationCondition.and left right).eval context = .poison cause := by
  simp only [ComputationCondition.eval, leftResult]

/-- A holding left operand decides computation `Or` without consulting the right operand. -/
theorem computationOr_leftHolds_shortCircuits
    (context : ScalarComputationContext) (left right : ComputationCondition)
    (leftResult : left.eval context = .holds) :
    (ComputationCondition.or left right).eval context = .holds := by
  simp only [ComputationCondition.eval, leftResult]

/-- A clean not-true left operand delegates computation `Or` to the right operand. -/
theorem computationOr_leftNotTrue_evaluatesRight
    (context : ScalarComputationContext) (left right : ComputationCondition)
    (leftResult : left.eval context = .notTrue) :
    (ComputationCondition.or left right).eval context = right.eval context := by
  simp only [ComputationCondition.eval, leftResult]

/-- A poison already read on the left aborts computation `Or` with the same cause. -/
theorem computationOr_leftPoison_preserves
    (context : ScalarComputationContext) (left right : ComputationCondition)
    (cause : FormalCause) (leftResult : left.eval context = .poison cause) :
    (ComputationCondition.or left right).eval context = .poison cause := by
  simp only [ComputationCondition.eval, leftResult]

/-- Computation `And` is observably order-sensitive when a clean deciding operand can precede a poison. -/
theorem computationAnd_operandOrderObservable
    (context : ScalarComputationContext) (clean poisonous : ComputationCondition)
    (cause : FormalCause) (cleanResult : clean.eval context = .notTrue)
    (poisonousResult : poisonous.eval context = .poison cause) :
    (ComputationCondition.and clean poisonous).eval context ≠
      (ComputationCondition.and poisonous clean).eval context := by
  simp only [ComputationCondition.eval, cleanResult, poisonousResult]
  intro impossible
  cases impossible

/-- Computation `Or` is observably order-sensitive when a clean deciding operand can precede a poison. -/
theorem computationOr_operandOrderObservable
    (context : ScalarComputationContext) (clean poisonous : ComputationCondition)
    (cause : FormalCause) (cleanResult : clean.eval context = .holds)
    (poisonousResult : poisonous.eval context = .poison cause) :
    (ComputationCondition.or clean poisonous).eval context ≠
      (ComputationCondition.or poisonous clean).eval context := by
  simp only [ComputationCondition.eval, cleanResult, poisonousResult]
  intro impossible
  cases impossible

end A12Kernel
