import A12Kernel.Elaboration.GeneratedComputationValidation

/-! # Two-alternative generated-computation validation laws

These laws cover only the exact structural desugaring, first-match reuse, and target-filled gate of the admitted literal-Number capsule. They do not equate computation-phase guard evaluation with validation-phase evaluation.
-/

namespace A12Kernel

/-- A holding first guard delegates to the existing first-match selector and leaves the second row irrelevant. -/
theorem twoAlternativeLiteralNumber_firstHolds_selects
    (computation : TwoAlternativeLiteralNumberComputation)
    (context : ScalarComputationContext)
    (holds : computation.first.precondition.eval context = .holds) :
    computation.selectFirst context =
      .selected computation.first.operation := by
  simp only [TwoAlternativeLiteralNumberComputation.selectFirst,
    ComputationAlternative.selectFirst, holds]

/-- The generated condition contains both guarded mismatches in declaration order; no first-match decision occurs in this desugaring. -/
theorem twoAlternativeGeneratedNumberCondition_exact
    (target : FlatNumberField)
    (firstGuard secondGuard : FlatCondition)
    (firstOperation secondOperation : Rat) :
    twoAlternativeGeneratedNumberCondition target
        firstGuard firstOperation secondGuard secondOperation =
      .and (.fieldFilled (.number target))
        (.or
          (generatedLiteralNumberMismatch target firstGuard firstOperation)
          (generatedLiteralNumberMismatch target secondGuard secondOperation)) := by
  rfl

/-- An empty target suppresses the complete generated mismatch table, independently of the target-instance content bit. -/
theorem generatedNumberCondition_emptyTarget_notFired
    (target : FlatNumberField)
    (firstGuard secondGuard : FlatCondition)
    (firstOperation secondOperation : Rat)
    (context : FlatContext) (targetHasContent : Bool)
    (empty : (FlatField.number target).observeValidation context = .empty) :
    (twoAlternativeGeneratedNumberCondition target
      firstGuard firstOperation secondGuard secondOperation).evalFull
        context targetHasContent = .notFired := by
  cases targetHasContent <;>
    simp [twoAlternativeGeneratedNumberCondition,
      FlatCondition.evalFull, FlatCondition.canFireOnEmpty,
      FlatCondition.evalSelected, FlatField.evalFilled, empty]

end A12Kernel
