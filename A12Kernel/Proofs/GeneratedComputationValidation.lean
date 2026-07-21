import A12Kernel.Elaboration.GeneratedComputationValidation
import A12Kernel.Proofs.ComputationCondition

/-! # Guarded generated-computation validation laws

These laws cover only declaration-order recovery, structural mismatch desugaring, common-precondition placement, first-match reuse, and the target-filled gate of the admitted guarded literal-Number capsule. They do not equate computation-phase guard evaluation with validation-phase evaluation.
-/

namespace A12Kernel

/-- Every direct or nested reference to the computed target is rejected before guard lowering can produce a phase-specific condition. -/
theorem generatedComputationGuard_targetSelfReference_rejected
    (condition : ComputationCondition) (model : FlatModel)
    (target : FieldId) (position : GeneratedComputationGuardPosition)
    (references : condition.referencesField target = true) :
    condition.lowerForGeneratedValidation model target position =
      .error (.targetSelfReference position) := by
  simp [ComputationCondition.lowerForGeneratedValidation, references]
  rfl

/-- Without a common precondition, a holding first guard delegates to the existing first-match selector and leaves every later row irrelevant. -/
theorem guardedLiteralNumber_firstHolds_selects
    (computation : GuardedLiteralNumberComputation)
    (context : ScalarComputationContext)
    (noCommon : computation.commonPrecondition = none)
    (holds : computation.first.precondition.eval context = .holds) :
    computation.selectFirst context =
      .selected computation.first.operation := by
  simp [GuardedLiteralNumberComputation.selectFirst,
    GuardedLiteralNumberComputation.declaredAlternatives,
    noCommon, ComputationAlternative.expandCommonPrecondition,
    ComputationAlternative.selectFirst, holds]

/-- A holding common precondition preserves the ordinary first-holding-row selection for the checked guarded fragment. -/
theorem guardedLiteralNumber_holdingCommon_firstHolds_selects
    (computation : GuardedLiteralNumberComputation)
    (context : ScalarComputationContext) (common : ComputationCondition)
    (hasCommon : computation.commonPrecondition = some common)
    (commonHolds : common.eval context = .holds)
    (firstHolds : computation.first.precondition.eval context = .holds) :
    computation.selectFirst context =
      .selected computation.first.operation := by
  simp [GuardedLiteralNumberComputation.selectFirst,
    GuardedLiteralNumberComputation.declaredAlternatives, hasCommon,
    ComputationAlternative.expandCommonPrecondition,
    ComputationAlternative.selectFirst, ComputationCondition.eval,
    commonHolds, firstHolds]

/-- The minimum two-branch table is a left-to-right disjunction below the target-filled gate; no first-match decision occurs in this desugaring. -/
theorem minimumGuardedGeneratedNumberCondition_exact
    (target : FlatNumberField)
    (firstMismatch secondMismatch : FlatCondition) :
    guardedGeneratedNumberCondition target none firstMismatch [secondMismatch] =
      .and (.fieldFilled (.number target))
        (.or firstMismatch secondMismatch) := by
  rfl

/-- A present common validation guard sits once outside the all-alternatives disjunction and inside the target-filled gate. -/
theorem minimumGuardedGeneratedNumberCondition_withCommon_exact
    (target : FlatNumberField) (common : FlatCondition)
    (firstMismatch secondMismatch : FlatCondition) :
    guardedGeneratedNumberCondition target (some common)
        firstMismatch [secondMismatch] =
      .and (.fieldFilled (.number target))
        (.and common
          (.or firstMismatch secondMismatch)) := by
  rfl

/-- Appending a mismatch branch extends the source-shaped left fold at the right without reordering or dropping an earlier branch. -/
theorem disjoinGeneratedNumberMismatches_append
    (first : FlatCondition) (remaining : List FlatCondition)
    (last : FlatCondition) :
    disjoinGeneratedNumberMismatches first (remaining ++ [last]) =
      .or (disjoinGeneratedNumberMismatches first remaining) last := by
  simp [disjoinGeneratedNumberMismatches, List.foldl_append]

/-- The guarded source representation exposes every alternative in declaration order. -/
theorem guardedLiteralNumber_declaredOperations_exact
    (computation : GuardedLiteralNumberComputation) :
    computation.declaredAlternatives.map (fun alternative => alternative.operation) =
      computation.first.operation :: computation.second.operation ::
        computation.remaining.map (fun alternative => alternative.operation) := by
  simp [GuardedLiteralNumberComputation.declaredAlternatives]

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

/-- Tolerance metadata is validation-only and erases from every alternative before first-match computation selection. -/
theorem literalNumberAlternative_tolerance_selectionIrrelevant
    (alternative : LiteralNumberComputationAlternative)
    (tolerance : Option NumericToleranceRange) :
    ({ alternative with tolerance := tolerance }).toComputationAlternative =
      alternative.toComputationAlternative := by
  rfl

/-- An empty target suppresses the complete generated mismatch table, independently of the target-instance content bit. -/
theorem generatedNumberCondition_emptyTarget_notFired
    (target : FlatNumberField)
    (commonGuard : Option FlatCondition)
    (firstMismatch : FlatCondition) (remainingMismatches : List FlatCondition)
    (context : FlatContext) (targetHasContent : Bool)
    (empty : (FlatField.number target).observeValidation context = .empty) :
    (guardedGeneratedNumberCondition target commonGuard
      firstMismatch remainingMismatches).evalFull
        context targetHasContent = .notFired := by
  cases targetHasContent <;>
    simp [guardedGeneratedNumberCondition,
      FlatCondition.evalFull, FlatCondition.canFireOnEmpty,
      FlatCondition.evalSelected, FlatField.evalFilled, empty]

end A12Kernel
