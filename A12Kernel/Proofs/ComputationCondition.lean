import A12Kernel.Proofs.Observation
import A12Kernel.Semantics.ComputationCondition

/-! # A12Kernel.Proofs.ComputationCondition — ordered computation-control laws

These laws characterize presence after computation-phase observation, the complete left-to-right decision table for the admitted `And`/`Or` fragment, and operation-neutral first-match alternative selection. They do not claim that the external kernel exposes the internal `poison` cause or that this fragment covers comparison or quantifier leaves, checked paths, operation evaluation, or model-level alternative legality.
-/

namespace A12Kernel

/-- A clean empty computation read does not satisfy `FieldFilled`. -/
theorem fieldFilled_observedEmpty_notTrue
    (context : ScalarComputationContext) (field : FieldId)
    (observed : observeCell .computation (context.read field) = .empty) :
    (ComputationCondition.fieldFilled field).eval context = .notTrue := by
  simp only [ComputationCondition.eval, ComputationCondition.evalFieldFilled, observed,
    CellObservation.evalComputationFilled]

/-- A clean empty computation read satisfies `FieldNotFilled`. -/
theorem fieldNotFilled_observedEmpty_holds
    (context : ScalarComputationContext) (field : FieldId)
    (observed : observeCell .computation (context.read field) = .empty) :
    (ComputationCondition.fieldNotFilled field).eval context = .holds := by
  simp only [ComputationCondition.eval, observed,
    CellObservation.evalComputationNotFilled]

/-- Any clean scalar value satisfies `FieldFilled`, independently of its scalar value. -/
theorem fieldFilled_observedValue_holds
    (context : ScalarComputationContext) (field : FieldId) (value : Value)
    (observed : observeCell .computation (context.read field) = .value value) :
    (ComputationCondition.fieldFilled field).eval context = .holds := by
  simp only [ComputationCondition.eval, ComputationCondition.evalFieldFilled, observed,
    CellObservation.evalComputationFilled]

/-- Any clean scalar value does not satisfy `FieldNotFilled`. -/
theorem fieldNotFilled_observedValue_notTrue
    (context : ScalarComputationContext) (field : FieldId) (value : Value)
    (observed : observeCell .computation (context.read field) = .value value) :
    (ComputationCondition.fieldNotFilled field).eval context = .notTrue := by
  simp only [ComputationCondition.eval, observed,
    CellObservation.evalComputationNotFilled]

/-- A computation-phase poison remains the exact poison under `FieldFilled`. -/
theorem fieldFilled_observedPoison_preserves
    (context : ScalarComputationContext) (field : FieldId) (cause : FormalCause)
    (observed : observeCell .computation (context.read field) = .poison cause) :
    (ComputationCondition.fieldFilled field).eval context = .poison cause := by
  simp only [ComputationCondition.eval, ComputationCondition.evalFieldFilled, observed,
    CellObservation.evalComputationFilled]

/-- `FieldNotFilled` reverses only clean truth; it preserves the same poison as `FieldFilled`. -/
theorem fieldNotFilled_observedPoison_preserves
    (context : ScalarComputationContext) (field : FieldId) (cause : FormalCause)
    (observed : observeCell .computation (context.read field) = .poison cause) :
    (ComputationCondition.fieldNotFilled field).eval context = .poison cause := by
  simp only [ComputationCondition.eval, observed,
    CellObservation.evalComputationNotFilled]

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

/-- An empty alternative table has no selected operation. This totalizes the semantic function without claiming that an empty authored table is legal. -/
theorem alternativeSelection_empty_is_noMatch
    (context : ScalarComputationContext) :
    ComputationAlternative.selectFirst
      ([] : List (ComputationAlternative Operation)) context = .noMatch := by
  rfl

/-- A holding head selects its operation without consulting the remaining alternatives. -/
theorem alternativeSelection_holdingHead_selects
    (context : ScalarComputationContext)
    (head : ComputationAlternative Operation)
    (remaining : List (ComputationAlternative Operation))
    (holds : head.precondition.eval context = .holds) :
    ComputationAlternative.selectFirst (head :: remaining) context =
      .selected head.operation := by
  simp only [ComputationAlternative.selectFirst, holds]

/-- A clean non-matching head delegates selection to the remaining alternatives. -/
theorem alternativeSelection_notTrueHead_continues
    (context : ScalarComputationContext)
    (head : ComputationAlternative Operation)
    (remaining : List (ComputationAlternative Operation))
    (notTrue : head.precondition.eval context = .notTrue) :
    ComputationAlternative.selectFirst (head :: remaining) context =
      ComputationAlternative.selectFirst remaining context := by
  simp only [ComputationAlternative.selectFirst, notTrue]

/-- A poisoned head aborts selection with the same cause and leaves the remaining alternatives unread. -/
theorem alternativeSelection_poisonedHead_aborts
    (context : ScalarComputationContext)
    (head : ComputationAlternative Operation)
    (remaining : List (ComputationAlternative Operation))
    (cause : FormalCause)
    (poisoned : head.precondition.eval context = .poison cause) :
    ComputationAlternative.selectFirst (head :: remaining) context =
      .poison cause := by
  simp only [ComputationAlternative.selectFirst, poisoned]

/-- Selection has no match exactly when every declared alternative is reached and cleanly not true. -/
theorem alternativeSelection_noMatch_iff
    (context : ScalarComputationContext)
    (alternatives : List (ComputationAlternative Operation)) :
    ComputationAlternative.selectFirst alternatives context = .noMatch ↔
      ∀ alternative ∈ alternatives,
        alternative.precondition.eval context = .notTrue := by
  induction alternatives with
  | nil =>
      simp [ComputationAlternative.selectFirst]
  | cons head remaining inductionHypothesis =>
      cases headResult : head.precondition.eval context with
      | holds =>
          simp [ComputationAlternative.selectFirst, headResult]
      | notTrue =>
          simp [ComputationAlternative.selectFirst, headResult, inductionHypothesis]
      | poison cause =>
          simp [ComputationAlternative.selectFirst, headResult]

/-- Declaration order is observable when two holding alternatives carry different operations. -/
theorem alternativeSelection_holdingOrderObservable
    (context : ScalarComputationContext)
    (first second : ComputationAlternative Operation)
    (firstHolds : first.precondition.eval context = .holds)
    (secondHolds : second.precondition.eval context = .holds)
    (different : first.operation ≠ second.operation) :
    ComputationAlternative.selectFirst [first, second] context ≠
      ComputationAlternative.selectFirst [second, first] context := by
  simp only [ComputationAlternative.selectFirst, firstHolds, secondHolds]
  intro same
  injection same with sameOperation
  exact different sameOperation

/-- Swapping a holding alternative with a poisoned one can change selection into poison. -/
theorem alternativeSelection_holdingPoisonOrderObservable
    (context : ScalarComputationContext)
    (holding poisonous : ComputationAlternative Operation)
    (cause : FormalCause)
    (holds : holding.precondition.eval context = .holds)
    (poisoned : poisonous.precondition.eval context = .poison cause) :
    ComputationAlternative.selectFirst [holding, poisonous] context ≠
      ComputationAlternative.selectFirst [poisonous, holding] context := by
  simp only [ComputationAlternative.selectFirst, holds, poisoned]
  intro impossible
  cases impossible

end A12Kernel
