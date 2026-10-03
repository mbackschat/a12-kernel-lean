import A12Kernel.Proofs.Observation
import A12Kernel.Semantics.ComputationCondition
import A12Kernel.Elaboration.ComputationNumericGuard

/-! # A12Kernel.Proofs.ComputationCondition — ordered computation-control laws

These laws characterize presence after computation-phase observation, the complete left-to-right decision table for the admitted `And`/`Or` fragment, optional common-precondition expansion, and operation-neutral first-match alternative selection. They do not claim that the external kernel exposes the internal `poison` cause or that these laws establish kernel correspondence for every comparison or quantifier leaf, checked paths, operation evaluation, or model-level alternative legality.
-/

namespace A12Kernel

/-- A fixed override is the same observation through direct and addressed reads, independently
of the addressed row. This is the coherence boundary used by fixed computation runs. -/
theorem scalarComputationContext_fixedOverlay_reads
    (context : ScalarComputationContext) (overlay : FieldId → Option CheckedCell)
    (field : FieldId) (cell : CheckedCell) (row : Env)
    (found : overlay field = some cell) :
    (context.withFixedOverlay overlay).read field = cell ∧
      (context.withFixedOverlay overlay).addressed.map (fun addressed => addressed.read row field) =
        context.addressed.map (fun _ => cell) := by
  cases addressed : context.addressed <;>
    simp [ScalarComputationContext.withFixedOverlay, found, addressed]

/-- Ordinary inputs retain both original read policies, including the addressed row choice. -/
theorem scalarComputationContext_fixedOverlay_fallback
    (context : ScalarComputationContext) (overlay : FieldId → Option CheckedCell)
    (field : FieldId) (row : Env) (ordinary : overlay field = none) :
    (context.withFixedOverlay overlay).read field = context.read field ∧
      (context.withFixedOverlay overlay).addressed.map (fun addressed => addressed.read row field) =
        context.addressed.map (fun addressed => addressed.read row field) := by
  cases addressed : context.addressed <;>
    simp [ScalarComputationContext.withFixedOverlay, ordinary, addressed]

/-- Replacing the context outside the comparison's declared field dependencies cannot change a
text guard's computation outcome, including its first poison cause. -/
theorem textComputationComparison_readsOnlyFields (comparison : FlatComparison)
    (left right : ScalarComputationContext)
    (agree : ∀ field ∈ comparison.fieldIds, left.read field = right.read field) :
    ComputationCondition.evalTextComparison comparison left =
      ComputationCondition.evalTextComparison comparison right := by
  cases comparison with
  | string op field expected =>
      have same := agree field.id (by simp [FlatComparison.fieldIds, FlatComparison.fields, FlatField.id])
      simp only [ComputationCondition.evalTextComparison, FlatTextFieldOperand.field, FlatField.id, same]
  | enumeration op operand expected =>
      have same := agree operand.field.id (by simp [FlatComparison.fieldIds, FlatComparison.fields, FlatField.id])
      simp only [ComputationCondition.evalTextComparison, FlatTextFieldOperand.field, FlatField.id, same]
  | textFields op first second =>
      have firstSame := agree first.field.id (by simp [FlatComparison.fieldIds, FlatComparison.fields])
      have secondSame := agree second.field.id (by simp [FlatComparison.fieldIds, FlatComparison.fields])
      simp only [ComputationCondition.evalTextComparison, firstSame, secondSame]
  | _ => rfl

/-- A clean empty computation read does not satisfy `FieldFilled`. -/
theorem fieldFilled_observedEmpty_notTrue
    (context : ScalarComputationContext) (field : FieldId)
    (observed : observeCell .computation (context.read field) = .empty) :
    (ComputationCondition.fieldFilled field).eval context = .notTrue := by
  simp only [ComputationCondition.eval_fieldFilled,
    ComputationCondition.evalFieldFilled, observed,
    CellObservation.evalComputationFilled]

/-- A clean empty computation read satisfies `FieldNotFilled`. -/
theorem fieldNotFilled_observedEmpty_holds
    (context : ScalarComputationContext) (field : FieldId)
    (observed : observeCell .computation (context.read field) = .empty) :
    (ComputationCondition.fieldNotFilled field).eval context = .holds := by
  simp only [ComputationCondition.eval_fieldNotFilled, observed,
    CellObservation.evalComputationNotFilled]

/-- Any clean scalar value satisfies `FieldFilled`, independently of its scalar value. -/
theorem fieldFilled_observedValue_holds
    (context : ScalarComputationContext) (field : FieldId) (value : Value)
    (observed : observeCell .computation (context.read field) = .value value) :
    (ComputationCondition.fieldFilled field).eval context = .holds := by
  simp only [ComputationCondition.eval_fieldFilled,
    ComputationCondition.evalFieldFilled, observed,
    CellObservation.evalComputationFilled]

/-- Any clean scalar value does not satisfy `FieldNotFilled`. -/
theorem fieldNotFilled_observedValue_notTrue
    (context : ScalarComputationContext) (field : FieldId) (value : Value)
    (observed : observeCell .computation (context.read field) = .value value) :
    (ComputationCondition.fieldNotFilled field).eval context = .notTrue := by
  simp only [ComputationCondition.eval_fieldNotFilled, observed,
    CellObservation.evalComputationNotFilled]

/-- A computation-phase poison remains the exact poison under `FieldFilled`. -/
theorem fieldFilled_observedPoison_preserves
    (context : ScalarComputationContext) (field : FieldId) (cause : FormalCause)
    (observed : observeCell .computation (context.read field) = .poison cause) :
    (ComputationCondition.fieldFilled field).eval context = .poison cause := by
  simp only [ComputationCondition.eval_fieldFilled,
    ComputationCondition.evalFieldFilled, observed,
    CellObservation.evalComputationFilled]

/-- `FieldNotFilled` reverses only clean truth; it preserves the same poison as `FieldFilled`. -/
theorem fieldNotFilled_observedPoison_preserves
    (context : ScalarComputationContext) (field : FieldId) (cause : FormalCause)
    (observed : observeCell .computation (context.read field) = .poison cause) :
    (ComputationCondition.fieldNotFilled field).eval context = .poison cause := by
  simp only [ComputationCondition.eval_fieldNotFilled, observed,
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
  simp only [ComputationCondition.eval_and, leftResult]

/-- A holding left operand delegates computation `And` to the right operand. -/
theorem computationAnd_leftHolds_evaluatesRight
    (context : ScalarComputationContext) (left right : ComputationCondition)
    (leftResult : left.eval context = .holds) :
    (ComputationCondition.and left right).eval context = right.eval context := by
  simp only [ComputationCondition.eval_and, leftResult]

/-- A poison already read on the left aborts computation `And` with the same cause. -/
theorem computationAnd_leftPoison_preserves
    (context : ScalarComputationContext) (left right : ComputationCondition)
    (cause : FormalCause) (leftResult : left.eval context = .poison cause) :
    (ComputationCondition.and left right).eval context = .poison cause := by
  simp only [ComputationCondition.eval_and, leftResult]

/-- A holding left operand decides computation `Or` without consulting the right operand. -/
theorem computationOr_leftHolds_shortCircuits
    (context : ScalarComputationContext) (left right : ComputationCondition)
    (leftResult : left.eval context = .holds) :
    (ComputationCondition.or left right).eval context = .holds := by
  simp only [ComputationCondition.eval_or, leftResult]

/-- A clean not-true left operand delegates computation `Or` to the right operand. -/
theorem computationOr_leftNotTrue_evaluatesRight
    (context : ScalarComputationContext) (left right : ComputationCondition)
    (leftResult : left.eval context = .notTrue) :
    (ComputationCondition.or left right).eval context = right.eval context := by
  simp only [ComputationCondition.eval_or, leftResult]

/-- A poison already read on the left aborts computation `Or` with the same cause. -/
theorem computationOr_leftPoison_preserves
    (context : ScalarComputationContext) (left right : ComputationCondition)
    (cause : FormalCause) (leftResult : left.eval context = .poison cause) :
    (ComputationCondition.or left right).eval context = .poison cause := by
  simp only [ComputationCondition.eval_or, leftResult]

/-- Computation `And` is observably order-sensitive when a clean deciding operand can precede a poison. -/
theorem computationAnd_operandOrderObservable
    (context : ScalarComputationContext) (clean poisonous : ComputationCondition)
    (cause : FormalCause) (cleanResult : clean.eval context = .notTrue)
    (poisonousResult : poisonous.eval context = .poison cause) :
    (ComputationCondition.and clean poisonous).eval context ≠
      (ComputationCondition.and poisonous clean).eval context := by
  simp only [ComputationCondition.eval_and, cleanResult, poisonousResult]
  intro impossible
  cases impossible

/-- Computation `Or` is observably order-sensitive when a clean deciding operand can precede a poison. -/
theorem computationOr_operandOrderObservable
    (context : ScalarComputationContext) (clean poisonous : ComputationCondition)
    (cause : FormalCause) (cleanResult : clean.eval context = .holds)
    (poisonousResult : poisonous.eval context = .poison cause) :
    (ComputationCondition.or clean poisonous).eval context ≠
      (ComputationCondition.or poisonous clean).eval context := by
  simp only [ComputationCondition.eval_or, cleanResult, poisonousResult]
  intro impossible
  cases impossible

/-- An empty alternative table has no selected operation. This totalizes the semantic function without claiming that an empty authored table is legal. -/
theorem alternativeSelection_empty_is_noMatch
    (context : ScalarComputationContext) :
    ComputationAlternative.selectFirst
      ([] : List (ComputationAlternative Operation)) context = .noMatch := by
  rfl

/-- An unguarded head selects its operation directly without consulting the context or remaining alternatives. -/
theorem alternativeSelection_unguardedHead_selects
    (context : ScalarComputationContext)
    (head : ComputationAlternative Operation)
    (remaining : List (ComputationAlternative Operation))
    (unguarded : head.precondition = none) :
    ComputationAlternative.selectFirst (head :: remaining) context =
      .selected head.operation := by
  simp [ComputationAlternative.selectFirst_cons, unguarded]

/-- A holding guarded head selects its operation without consulting the remaining alternatives. -/
theorem alternativeSelection_holdingHead_selects
    (context : ScalarComputationContext)
    (head : ComputationAlternative Operation)
    (remaining : List (ComputationAlternative Operation))
    (guard : ComputationCondition) (guarded : head.precondition = some guard)
    (holds : guard.eval context = .holds) :
    ComputationAlternative.selectFirst (head :: remaining) context =
      .selected head.operation := by
  simp [ComputationAlternative.selectFirst_cons, guarded, holds]

/-- A clean non-matching head delegates selection to the remaining alternatives. -/
theorem alternativeSelection_notTrueHead_continues
    (context : ScalarComputationContext)
    (head : ComputationAlternative Operation)
    (remaining : List (ComputationAlternative Operation))
    (guard : ComputationCondition) (guarded : head.precondition = some guard)
    (notTrue : guard.eval context = .notTrue) :
    ComputationAlternative.selectFirst (head :: remaining) context =
      ComputationAlternative.selectFirst remaining context := by
  simp [ComputationAlternative.selectFirst_cons, guarded, notTrue]

/-- A poisoned head aborts selection with the same cause and leaves the remaining alternatives unread. -/
theorem alternativeSelection_poisonedHead_aborts
    (context : ScalarComputationContext)
    (head : ComputationAlternative Operation)
    (remaining : List (ComputationAlternative Operation))
    (cause : FormalCause)
    (guard : ComputationCondition) (guarded : head.precondition = some guard)
    (poisoned : guard.eval context = .poison cause) :
    ComputationAlternative.selectFirst (head :: remaining) context =
      .poison cause := by
  simp [ComputationAlternative.selectFirst_cons, guarded, poisoned]

/-- Selection has no match exactly when every declared alternative is reached and cleanly not true. -/
theorem alternativeSelection_noMatch_iff
    (context : ScalarComputationContext)
    (alternatives : List (ComputationAlternative Operation)) :
    ComputationAlternative.selectFirst alternatives context = .noMatch ↔
      ∀ alternative ∈ alternatives,
        ∃ guard, alternative.precondition = some guard ∧
          guard.eval context = .notTrue := by
  induction alternatives with
  | nil =>
      simp
  | cons head remaining inductionHypothesis =>
      cases guarded : head.precondition with
      | none => simp [ComputationAlternative.selectFirst_cons, guarded]
      | some guard =>
          cases headResult : guard.eval context with
          | holds =>
              simp [ComputationAlternative.selectFirst_cons, guarded, headResult]
          | notTrue =>
              simp [ComputationAlternative.selectFirst_cons, guarded, headResult,
                inductionHypothesis]
          | poison cause =>
              simp [ComputationAlternative.selectFirst_cons, guarded, headResult]

/-- Declaration order is observable when two holding alternatives carry different operations. -/
theorem alternativeSelection_holdingOrderObservable
    (context : ScalarComputationContext)
    (first second : ComputationAlternative Operation)
    (firstGuard secondGuard : ComputationCondition)
    (firstGuarded : first.precondition = some firstGuard)
    (secondGuarded : second.precondition = some secondGuard)
    (firstHolds : firstGuard.eval context = .holds)
    (secondHolds : secondGuard.eval context = .holds)
    (different : first.operation ≠ second.operation) :
    ComputationAlternative.selectFirst [first, second] context ≠
      ComputationAlternative.selectFirst [second, first] context := by
  simp only [ComputationAlternative.selectFirst_cons, firstGuarded, secondGuarded,
    firstHolds, secondHolds]
  intro same
  injection same with sameOperation
  exact different sameOperation

/-- Swapping a holding alternative with a poisoned one can change selection into poison. -/
theorem alternativeSelection_holdingPoisonOrderObservable
    (context : ScalarComputationContext)
    (holding poisonous : ComputationAlternative Operation)
    (holdingGuard poisonousGuard : ComputationCondition) (cause : FormalCause)
    (holdingGuarded : holding.precondition = some holdingGuard)
    (poisonousGuarded : poisonous.precondition = some poisonousGuard)
    (holds : holdingGuard.eval context = .holds)
    (poisoned : poisonousGuard.eval context = .poison cause) :
    ComputationAlternative.selectFirst [holding, poisonous] context ≠
      ComputationAlternative.selectFirst [poisonous, holding] context := by
  simp only [ComputationAlternative.selectFirst_cons, holdingGuarded,
    poisonousGuarded, holds, poisoned]
  intro impossible
  cases impossible

/-- Omitting a common precondition is definitionally the identity on an alternative table. -/
theorem expandCommonPrecondition_none
    (alternatives : List (ComputationAlternative Operation)) :
    ComputationAlternative.expandCommonPrecondition none alternatives =
      alternatives := by
  rfl

/-- Common-precondition expansion changes only guards; it preserves operation payloads and declaration order exactly. -/
theorem expandCommonPrecondition_preserves_operations
    (commonPrecondition : Option ComputationCondition)
    (alternatives : List (ComputationAlternative Operation)) :
    (ComputationAlternative.expandCommonPrecondition
      commonPrecondition alternatives).map (fun alternative => alternative.operation) =
        alternatives.map (fun alternative => alternative.operation) := by
  cases commonPrecondition <;>
    simp [ComputationAlternative.expandCommonPrecondition, ComputationCondition.withCommon, ComputationConditionOf.withCommon]

/-- A holding common precondition leaves the existing first-match result unchanged for every alternative table. -/
theorem alternativeSelection_holdingCommon_preserves
    (context : ScalarComputationContext) (common : ComputationCondition)
    (alternatives : List (ComputationAlternative Operation))
    (commonHolds : common.eval context = .holds) :
    ComputationAlternative.selectFirst
        (ComputationAlternative.expandCommonPrecondition
          (some common) alternatives) context =
      ComputationAlternative.selectFirst alternatives context := by
  induction alternatives with
  | nil => rfl
  | cons head remaining inductionHypothesis =>
      cases head with
      | mk precondition operation =>
          cases precondition with
          | none =>
              simp [ComputationAlternative.expandCommonPrecondition, ComputationCondition.withCommon, ComputationConditionOf.withCommon,
                ComputationAlternative.selectFirst_cons, commonHolds]
          | some guard =>
              simp only [ComputationAlternative.expandCommonPrecondition, ComputationCondition.withCommon, ComputationConditionOf.withCommon,
                List.map_cons, ComputationAlternative.selectFirst_cons,
                ComputationCondition.eval_and, commonHolds]
              cases headResult : guard.eval context with
              | holds => rfl
              | notTrue =>
                  simpa [ComputationAlternative.expandCommonPrecondition, ComputationCondition.withCommon, ComputationConditionOf.withCommon] using
                    inductionHypothesis
              | poison cause => rfl

/-- A clean non-holding common precondition makes every table a clean no-match without evaluating any alternative-specific guard. -/
theorem alternativeSelection_notTrueCommon_noMatch
    (context : ScalarComputationContext) (common : ComputationCondition)
    (alternatives : List (ComputationAlternative Operation))
    (commonNotTrue : common.eval context = .notTrue) :
    ComputationAlternative.selectFirst
        (ComputationAlternative.expandCommonPrecondition
          (some common) alternatives) context = .noMatch := by
  induction alternatives with
  | nil => rfl
  | cons head remaining inductionHypothesis =>
      cases head with
      | mk precondition operation =>
          cases precondition <;>
            simp only [ComputationAlternative.expandCommonPrecondition, ComputationCondition.withCommon, ComputationConditionOf.withCommon,
              List.map_cons, ComputationAlternative.selectFirst_cons,
              ComputationCondition.eval_and, commonNotTrue]
          all_goals
            simpa [ComputationAlternative.expandCommonPrecondition, ComputationCondition.withCommon, ComputationConditionOf.withCommon] using
              inductionHypothesis

/-- On a nonempty table, a poisoned common precondition aborts at the first expanded guard before its alternative-specific guard can contribute. -/
theorem alternativeSelection_poisonedCommon_aborts
    (context : ScalarComputationContext) (common : ComputationCondition)
    (head : ComputationAlternative Operation)
    (remaining : List (ComputationAlternative Operation))
    (cause : FormalCause)
    (commonPoison : common.eval context = .poison cause) :
    ComputationAlternative.selectFirst
        (ComputationAlternative.expandCommonPrecondition
          (some common) (head :: remaining)) context = .poison cause := by
  cases head with
  | mk precondition operation =>
      cases precondition <;>
        simp [ComputationAlternative.expandCommonPrecondition, ComputationCondition.withCommon, ComputationConditionOf.withCommon,
          ComputationAlternative.selectFirst_cons, ComputationCondition.eval_and,
          commonPoison]

/-- Common guards use the same effectful tree and first-match scan for every leaf family. -/
theorem selectFirstWith_withCommon_holds
    (evalLeaf : ComputationConditionLeaf Atom Predicate → Except Error ComputationConditionResult)
    (common : ComputationConditionOf Atom Predicate)
    (alternatives : List (ComputationAlternative Op (ComputationConditionOf Atom Predicate)))
    (holds : common.evalComputationExcept evalLeaf = .ok .holds) :
    ComputationAlternative.selectFirstWith (·.evalComputationExcept evalLeaf)
        (alternatives.map fun a =>
          { a with precondition := ComputationConditionOf.withCommon (some common) a.precondition }) =
      ComputationAlternative.selectFirstWith (·.evalComputationExcept evalLeaf) alternatives := by
  induction alternatives with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk precondition operation =>
          cases precondition with
          | none => simp [ComputationAlternative.selectFirstWith, ComputationConditionOf.withCommon, holds, bind, Except.bind, pure, Except.pure]
          | some own =>
              simp only [List.map_cons, ComputationConditionOf.withCommon,
                ComputationAlternative.selectFirstWith, ConditionTree.evalComputationExcept, holds,
                bind, Except.bind, pure, Except.pure]
              cases h : own.evalComputationExcept evalLeaf with
              | error error => rfl
              | ok result => cases result <;> simp_all [ComputationConditionOf.withCommon]

/-- A false common guard skips all own guards and operations, including structural failures. -/
theorem selectFirstWith_withCommon_notTrue
    (evalLeaf : ComputationConditionLeaf Atom Predicate → Except Error ComputationConditionResult)
    (common : ComputationConditionOf Atom Predicate)
    (alternatives : List (ComputationAlternative Op (ComputationConditionOf Atom Predicate)))
    (notTrue : common.evalComputationExcept evalLeaf = .ok .notTrue) :
    ComputationAlternative.selectFirstWith (·.evalComputationExcept evalLeaf)
        (alternatives.map fun a =>
          { a with precondition := ComputationConditionOf.withCommon (some common) a.precondition }) =
      .ok .noMatch := by
  induction alternatives with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk precondition operation =>
          cases precondition <;>
            simpa [ComputationAlternative.selectFirstWith, ComputationConditionOf.withCommon,
              ConditionTree.evalComputationExcept, notTrue, bind, Except.bind, pure, Except.pure] using ih

/-- Common poison is reached before any own guard in a nonempty table. -/
theorem selectFirstWith_withCommon_poison
    (evalLeaf : ComputationConditionLeaf Atom Predicate → Except Error ComputationConditionResult)
    (common : ComputationConditionOf Atom Predicate)
    (head : ComputationAlternative Op (ComputationConditionOf Atom Predicate)) (tail : List _)
    (cause : FormalCause) (poison : common.evalComputationExcept evalLeaf = .ok (.poison cause)) :
    ComputationAlternative.selectFirstWith (·.evalComputationExcept evalLeaf)
        ((head :: tail).map fun a =>
          { a with precondition := ComputationConditionOf.withCommon (some common) a.precondition }) =
      .ok (.poison cause) := by
  cases head with
  | mk precondition operation =>
      cases precondition <;> simp [ComputationAlternative.selectFirstWith,
        ComputationConditionOf.withCommon, ConditionTree.evalComputationExcept, poison, bind, Except.bind, pure, Except.pure]

/-- A structural common-guard failure is preserved before any own guard in a nonempty table. -/
theorem selectFirstWith_withCommon_error
    (evalLeaf : ComputationConditionLeaf Atom Predicate → Except Error ComputationConditionResult)
    (common : ComputationConditionOf Atom Predicate)
    (head : ComputationAlternative Op (ComputationConditionOf Atom Predicate)) (tail : List _)
    (error : Error) (failed : common.evalComputationExcept evalLeaf = .error error) :
    ComputationAlternative.selectFirstWith (·.evalComputationExcept evalLeaf)
        ((head :: tail).map fun a =>
          { a with precondition := ComputationConditionOf.withCommon (some common) a.precondition }) =
      .error error := by
  cases head with
  | mk precondition operation =>
      cases precondition <;> simp [ComputationAlternative.selectFirstWith,
        ComputationConditionOf.withCommon, ConditionTree.evalComputationExcept, failed, bind, Except.bind]

/-- Successful checked common guards preserve the shared scan, including structural failures. -/
theorem checkedAlternativeSelection_holdingCommon_preserves
    (context : ScalarComputationContext) (common : ComputationCondition)
    (alternatives : List (ComputationAlternative Operation))
    (commonHolds : common.evalChecked context = .ok .holds) :
    ComputationAlternative.selectFirstChecked
      (ComputationAlternative.expandCommonPrecondition (some common) alternatives) context =
      ComputationAlternative.selectFirstChecked alternatives context := by
  simp only [ComputationAlternative.expandCommonPrecondition, ComputationAlternative.selectFirstChecked,
    ComputationCondition.withCommon, ComputationCondition.evalChecked,
    ComputationConditionOf.evalCheckedWith] at commonHolds ⊢
  exact selectFirstWith_withCommon_holds _ common alternatives commonHolds

/-- A checked false common guard prevents every alternative guard from being read. -/
theorem checkedAlternativeSelection_notTrueCommon_noMatch
    (context : ScalarComputationContext) (common : ComputationCondition)
    (alternatives : List (ComputationAlternative Operation))
    (commonNotTrue : common.evalChecked context = .ok .notTrue) :
    ComputationAlternative.selectFirstChecked
      (ComputationAlternative.expandCommonPrecondition (some common) alternatives) context = .ok .noMatch := by
  simp only [ComputationAlternative.expandCommonPrecondition, ComputationAlternative.selectFirstChecked,
    ComputationCondition.withCommon, ComputationCondition.evalChecked,
    ComputationConditionOf.evalCheckedWith] at commonNotTrue ⊢
  exact selectFirstWith_withCommon_notTrue _ common alternatives commonNotTrue

/-- Checked common poison aborts before every alternative-specific read. -/
theorem checkedAlternativeSelection_poisonedCommon_aborts
    (context : ScalarComputationContext) (common : ComputationCondition)
    (head : ComputationAlternative Operation) (tail : List (ComputationAlternative Operation))
    (cause : FormalCause) (commonPoison : common.evalChecked context = .ok (.poison cause)) :
    ComputationAlternative.selectFirstChecked
      (ComputationAlternative.expandCommonPrecondition (some common) (head :: tail)) context =
      .ok (.poison cause) := by
  simp only [ComputationAlternative.expandCommonPrecondition, ComputationAlternative.selectFirstChecked,
    ComputationCondition.withCommon, ComputationCondition.evalChecked,
    ComputationConditionOf.evalCheckedWith] at commonPoison ⊢
  exact selectFirstWith_withCommon_poison _ common head tail cause commonPoison


/-- The model-bound holds case specializes the shared selection law on its running evaluator. -/
theorem modelBoundAlternativeSelection_holds
    (context : ScalarComputationContext) (common : CheckedComputationCondition model)
    (alternatives : List (CheckedComputationAlternative model Op))
    (commonResult : common.evalChecked context = .ok .holds) :
    CheckedComputationAlternative.selectFirstChecked
      (CheckedComputationAlternative.expandCommonPrecondition (some common) alternatives) context =
      CheckedComputationAlternative.selectFirstChecked alternatives context := by
  simp only [CheckedComputationAlternative.selectFirstChecked, CheckedComputationAlternative.expandCommonPrecondition,
    CheckedComputationCondition.withCommon]
  cases addressed : context.addressed <;>
    simp only [CheckedComputationCondition.evalChecked, addressed, CheckedComputationCondition.evalCheckedIn,
      ComputationConditionOf.evalCheckedWith] at commonResult ⊢
  all_goals exact selectFirstWith_withCommon_holds _ common alternatives commonResult

/-- The model-bound notTrue case specializes the shared selection law on its running evaluator. -/
theorem modelBoundAlternativeSelection_notTrue
    (context : ScalarComputationContext) (common : CheckedComputationCondition model)
    (alternatives : List (CheckedComputationAlternative model Op))
    (commonResult : common.evalChecked context = .ok .notTrue) :
    CheckedComputationAlternative.selectFirstChecked
      (CheckedComputationAlternative.expandCommonPrecondition (some common) alternatives) context =
      .ok .noMatch := by
  simp only [CheckedComputationAlternative.selectFirstChecked, CheckedComputationAlternative.expandCommonPrecondition,
    CheckedComputationCondition.withCommon]
  cases addressed : context.addressed <;>
    simp only [CheckedComputationCondition.evalChecked, addressed, CheckedComputationCondition.evalCheckedIn,
      ComputationConditionOf.evalCheckedWith] at commonResult ⊢
  all_goals exact selectFirstWith_withCommon_notTrue _ common alternatives commonResult

/-- The model-bound poison case specializes the shared selection law on its running evaluator. -/
theorem modelBoundAlternativeSelection_poison
    (context : ScalarComputationContext) (common : CheckedComputationCondition model)
    (head : CheckedComputationAlternative model Op) (tail : List (CheckedComputationAlternative model Op))
    (cause : FormalCause)
    (commonResult : common.evalChecked context = .ok (.poison cause)) :
    CheckedComputationAlternative.selectFirstChecked
      (CheckedComputationAlternative.expandCommonPrecondition (some common) (head :: tail)) context =
      .ok (.poison cause) := by
  simp only [CheckedComputationAlternative.selectFirstChecked, CheckedComputationAlternative.expandCommonPrecondition,
    CheckedComputationCondition.withCommon]
  cases addressed : context.addressed <;>
    simp only [CheckedComputationCondition.evalChecked, addressed, CheckedComputationCondition.evalCheckedIn,
      ComputationConditionOf.evalCheckedWith] at commonResult ⊢
  all_goals exact selectFirstWith_withCommon_poison _ common head tail cause commonResult

/-- The model-bound error case specializes the shared selection law on its running evaluator. -/
theorem modelBoundAlternativeSelection_error
    (context : ScalarComputationContext) (common : CheckedComputationCondition model)
    (head : CheckedComputationAlternative model Op) (tail : List (CheckedComputationAlternative model Op))
    (error : CheckedComputationConditionError)
    (commonResult : common.evalChecked context = .error error) :
    CheckedComputationAlternative.selectFirstChecked
      (CheckedComputationAlternative.expandCommonPrecondition (some common) (head :: tail)) context =
      .error error := by
  simp only [CheckedComputationAlternative.selectFirstChecked, CheckedComputationAlternative.expandCommonPrecondition,
    CheckedComputationCondition.withCommon]
  cases addressed : context.addressed <;>
    simp only [CheckedComputationCondition.evalChecked, addressed, CheckedComputationCondition.evalCheckedIn,
      ComputationConditionOf.evalCheckedWith] at commonResult ⊢
  all_goals exact selectFirstWith_withCommon_error _ common head tail error commonResult

/-- The model-bound holds case specializes the shared selection law on its running evaluator. -/
theorem modelBoundAlternativeSelectionIn_holds
    (context : NumericComputationEvaluationContext) (common : CheckedComputationCondition model)
    (alternatives : List (CheckedComputationAlternative model Op))
    (commonResult : common.evalCheckedIn context = .ok .holds) :
    CheckedComputationAlternative.selectFirstCheckedIn
      (CheckedComputationAlternative.expandCommonPrecondition (some common) alternatives) context =
      CheckedComputationAlternative.selectFirstCheckedIn alternatives context := by
  simp only [CheckedComputationAlternative.selectFirstCheckedIn, CheckedComputationAlternative.expandCommonPrecondition,
    CheckedComputationCondition.withCommon]
  simp only [CheckedComputationCondition.evalCheckedIn, ComputationConditionOf.evalCheckedWith] at commonResult ⊢
  all_goals exact selectFirstWith_withCommon_holds _ common alternatives commonResult

/-- The model-bound notTrue case specializes the shared selection law on its running evaluator. -/
theorem modelBoundAlternativeSelectionIn_notTrue
    (context : NumericComputationEvaluationContext) (common : CheckedComputationCondition model)
    (alternatives : List (CheckedComputationAlternative model Op))
    (commonResult : common.evalCheckedIn context = .ok .notTrue) :
    CheckedComputationAlternative.selectFirstCheckedIn
      (CheckedComputationAlternative.expandCommonPrecondition (some common) alternatives) context =
      .ok .noMatch := by
  simp only [CheckedComputationAlternative.selectFirstCheckedIn, CheckedComputationAlternative.expandCommonPrecondition,
    CheckedComputationCondition.withCommon]
  simp only [CheckedComputationCondition.evalCheckedIn, ComputationConditionOf.evalCheckedWith] at commonResult ⊢
  all_goals exact selectFirstWith_withCommon_notTrue _ common alternatives commonResult

/-- The model-bound poison case specializes the shared selection law on its running evaluator. -/
theorem modelBoundAlternativeSelectionIn_poison
    (context : NumericComputationEvaluationContext) (common : CheckedComputationCondition model)
    (head : CheckedComputationAlternative model Op) (tail : List (CheckedComputationAlternative model Op))
    (cause : FormalCause)
    (commonResult : common.evalCheckedIn context = .ok (.poison cause)) :
    CheckedComputationAlternative.selectFirstCheckedIn
      (CheckedComputationAlternative.expandCommonPrecondition (some common) (head :: tail)) context =
      .ok (.poison cause) := by
  simp only [CheckedComputationAlternative.selectFirstCheckedIn, CheckedComputationAlternative.expandCommonPrecondition,
    CheckedComputationCondition.withCommon]
  simp only [CheckedComputationCondition.evalCheckedIn, ComputationConditionOf.evalCheckedWith] at commonResult ⊢
  all_goals exact selectFirstWith_withCommon_poison _ common head tail cause commonResult

/-- The model-bound error case specializes the shared selection law on its running evaluator. -/
theorem modelBoundAlternativeSelectionIn_error
    (context : NumericComputationEvaluationContext) (common : CheckedComputationCondition model)
    (head : CheckedComputationAlternative model Op) (tail : List (CheckedComputationAlternative model Op))
    (error : CheckedComputationConditionError)
    (commonResult : common.evalCheckedIn context = .error error) :
    CheckedComputationAlternative.selectFirstCheckedIn
      (CheckedComputationAlternative.expandCommonPrecondition (some common) (head :: tail)) context =
      .error error := by
  simp only [CheckedComputationAlternative.selectFirstCheckedIn, CheckedComputationAlternative.expandCommonPrecondition,
    CheckedComputationCondition.withCommon]
  simp only [CheckedComputationCondition.evalCheckedIn, ComputationConditionOf.evalCheckedWith] at commonResult ⊢
  all_goals exact selectFirstWith_withCommon_error _ common head tail error commonResult

end A12Kernel
