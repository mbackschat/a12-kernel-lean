import A12Kernel.Elaboration.GeneratedComputationValidation
import A12Kernel.Proofs.ComputationCondition

/-! # Two-alternative generated-computation validation laws

These laws cover only the exact structural desugaring, common-precondition placement, first-match reuse, and target-filled gate of the admitted literal-Number capsule. They do not equate computation-phase guard evaluation with validation-phase evaluation.
-/

namespace A12Kernel

/-- Without a common precondition, a holding first guard delegates to the existing first-match selector and leaves the second row irrelevant. -/
theorem twoAlternativeLiteralNumber_firstHolds_selects
    (computation : TwoAlternativeLiteralNumberComputation)
    (context : ScalarComputationContext)
    (noCommon : computation.commonPrecondition = none)
    (holds : computation.first.precondition.eval context = .holds) :
    computation.selectFirst context =
      .selected computation.first.operation := by
  simp only [TwoAlternativeLiteralNumberComputation.selectFirst,
    noCommon, ComputationAlternative.expandCommonPrecondition,
    ComputationAlternative.selectFirst, holds]

/-- A holding common precondition preserves the ordinary first-holding-row selection for the checked two-alternative fragment. -/
theorem twoAlternativeLiteralNumber_holdingCommon_firstHolds_selects
    (computation : TwoAlternativeLiteralNumberComputation)
    (context : ScalarComputationContext) (common : ComputationCondition)
    (hasCommon : computation.commonPrecondition = some common)
    (commonHolds : common.eval context = .holds)
    (firstHolds : computation.first.precondition.eval context = .holds) :
    computation.selectFirst context =
      .selected computation.first.operation := by
  simp [TwoAlternativeLiteralNumberComputation.selectFirst, hasCommon,
    ComputationAlternative.expandCommonPrecondition,
    ComputationAlternative.selectFirst, ComputationCondition.eval,
    commonHolds, firstHolds]

/-- The generated condition contains both guarded mismatches in declaration order; no first-match decision occurs in this desugaring. -/
theorem twoAlternativeGeneratedNumberCondition_exact
    (target : FlatNumberField)
    (firstGuard secondGuard : FlatCondition)
    (firstOperation secondOperation : Rat)
    (firstTolerance secondTolerance : Option NumericToleranceRange) :
    twoAlternativeGeneratedNumberCondition target
        firstGuard firstOperation firstTolerance
        secondGuard secondOperation secondTolerance =
      .and (.fieldFilled (.number target))
        (.or
          (generatedLiteralNumberMismatch target firstGuard firstOperation
            firstTolerance)
          (generatedLiteralNumberMismatch target secondGuard secondOperation
            secondTolerance)) := by
  rfl

/-- A present common validation guard sits once outside the all-alternatives disjunction and inside the target-filled gate. -/
theorem twoAlternativeGeneratedNumberCondition_withCommon_exact
    (target : FlatNumberField) (common : FlatCondition)
    (firstGuard secondGuard : FlatCondition)
    (firstOperation secondOperation : Rat)
    (firstTolerance secondTolerance : Option NumericToleranceRange) :
    twoAlternativeGeneratedNumberCondition target
        firstGuard firstOperation firstTolerance
        secondGuard secondOperation secondTolerance (some common) =
      .and (.fieldFilled (.number target))
        (.and common
          (.or
            (generatedLiteralNumberMismatch target firstGuard firstOperation
              firstTolerance)
            (generatedLiteralNumberMismatch target secondGuard secondOperation
              secondTolerance))) := by
  rfl

/-- Omitted tolerance metadata produces the source-level strict mismatch branch. -/
theorem generatedLiteralNumberMismatch_withoutTolerance
    (target : FlatNumberField) (guard : FlatCondition) (operation : Rat) :
    generatedLiteralNumberMismatch target guard operation none =
      .and guard (.compare (.number (.ordinary .notEqual) target operation)) := by
  rfl

/-- Present tolerance metadata produces that alternative's source-level tolerance branch. -/
theorem generatedLiteralNumberMismatch_withTolerance
    (target : FlatNumberField) (guard : FlatCondition) (operation : Rat)
    (range : NumericToleranceRange) :
    generatedLiteralNumberMismatch target guard operation (some range) =
      .and guard (.compare (.number (.tolerance range) target operation)) := by
  rfl

/-- Tolerance metadata is validation-only and cannot change first-match computation selection. -/
theorem twoAlternativeLiteralNumber_tolerance_selectionIrrelevant
    (computation : TwoAlternativeLiteralNumberComputation)
    (context : ScalarComputationContext)
    (firstTolerance secondTolerance : Option NumericToleranceRange) :
    ({ computation with
      first := { computation.first with tolerance := firstTolerance }
      second := { computation.second with tolerance := secondTolerance }
    }).selectFirst context = computation.selectFirst context := by
  rfl

/-- An empty target suppresses the complete generated mismatch table, independently of the target-instance content bit. -/
theorem generatedNumberCondition_emptyTarget_notFired
    (target : FlatNumberField)
    (firstGuard secondGuard : FlatCondition)
    (firstOperation secondOperation : Rat)
    (firstTolerance secondTolerance : Option NumericToleranceRange)
    (context : FlatContext) (targetHasContent : Bool)
    (empty : (FlatField.number target).observeValidation context = .empty) :
    (twoAlternativeGeneratedNumberCondition target
      firstGuard firstOperation firstTolerance
      secondGuard secondOperation secondTolerance).evalFull
        context targetHasContent = .notFired := by
  cases targetHasContent <;>
    simp [twoAlternativeGeneratedNumberCondition,
      FlatCondition.evalFull, FlatCondition.canFireOnEmpty,
      FlatCondition.evalSelected, FlatField.evalFilled, empty]

end A12Kernel
