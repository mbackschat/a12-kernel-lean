import A12Kernel.Elaboration.GeneratedComputationValidation
import A12Kernel.Proofs.ComputationCondition

/-! # Generated-computation validation laws

These laws cover the singleton/guarded table split, declaration-order recovery, structural mismatch desugaring, common-precondition placement, first-match reuse, the target-filled gate of the admitted literal-Number capsule, and the model-wide checked scope of an expression-valued mismatch. They do not equate computation-phase guard evaluation with validation-phase evaluation.
-/

namespace A12Kernel

/-- The generated-validation twin preserves the checked String-length source exactly instead of reconstructing scale-erasing flat syntax. -/
theorem numericComputationAtom_stringLength_toValidationAtom
    (source : FlatStringField) :
    NumericComputationAtom.toValidationAtom (.stringLength source) =
      .ok (.stringLength source) := by
  rfl

/-- The generated-validation twin preserves the checked String range atom exactly instead of reconstructing surface syntax. -/
theorem numericComputationAtom_stringRange_toValidationAtom
    (source : FlatStringField) (start finish : Nat) :
    NumericComputationAtom.toValidationAtom
        (.stringRange source start finish) =
      .ok (.stringRange source start finish) := by
  rfl

/-- The generated-validation twin preserves the checked Enumeration/category conversion source and derived scale exactly. -/
theorem numericComputationAtom_fieldValueAsNumber_toValidationAtom
    (source : ResolvedFieldValueAsNumberSource) :
    NumericComputationAtom.toValidationAtom (.fieldValueAsNumber source) =
      .ok (.fieldValueAsNumber source) := by
  rfl

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
theorem guardedGeneratedComputation_firstHolds_selects
    (alternatives : GuardedGeneratedComputationAlternatives Operation)
    (context : ScalarComputationContext)
    (holds : alternatives.first.precondition.eval context = .holds) :
    GuardedGeneratedComputationAlternatives.selectFirst alternatives none context =
      .selected alternatives.first.operation := by
  simp [GuardedGeneratedComputationAlternatives.selectFirst,
    GuardedGeneratedComputationAlternatives.declaredAlternatives,
    ComputationAlternative.expandCommonPrecondition,
    ComputationAlternative.selectFirst, holds]

/-- A holding common precondition preserves the ordinary first-holding-row selection for the checked guarded fragment. -/
theorem guardedGeneratedComputation_holdingCommon_firstHolds_selects
    (alternatives : GuardedGeneratedComputationAlternatives Operation)
    (context : ScalarComputationContext) (common : ComputationCondition)
    (commonHolds : common.eval context = .holds)
    (firstHolds : alternatives.first.precondition.eval context = .holds) :
    GuardedGeneratedComputationAlternatives.selectFirst alternatives
      (some common) context =
      .selected alternatives.first.operation := by
  simp [GuardedGeneratedComputationAlternatives.selectFirst,
    GuardedGeneratedComputationAlternatives.declaredAlternatives,
    ComputationAlternative.expandCommonPrecondition,
    ComputationAlternative.selectFirst, ComputationCondition.eval,
    commonHolds, firstHolds]

/-- A singleton with no authored guard and no common precondition selects directly without inventing an always-true condition. -/
theorem singleGeneratedComputation_unconditional_selects
    (alternative : SingleGeneratedComputationAlternative Operation)
    (context : ScalarComputationContext)
    (unconditional : alternative.precondition = none) :
    SingleGeneratedComputationAlternative.selectFirst alternative none context =
      .selected alternative.operation := by
  simp [SingleGeneratedComputationAlternative.selectFirst, unconditional]

/-- A holding common precondition is the sole runtime guard for an otherwise-unconditional singleton. -/
theorem singleGeneratedComputation_holdingCommon_selects
    (alternative : SingleGeneratedComputationAlternative Operation)
    (context : ScalarComputationContext) (common : ComputationCondition)
    (unconditional : alternative.precondition = none)
    (commonHolds : common.eval context = .holds) :
    SingleGeneratedComputationAlternative.selectFirst alternative
      (some common) context =
      .selected alternative.operation := by
  simp [SingleGeneratedComputationAlternative.selectFirst, unconditional,
    ComputationAlternative.selectFirst, commonHolds]

/-- The minimum two-branch table is a left-to-right disjunction below the target-filled gate; no first-match decision occurs in this desugaring. -/
theorem minimumGuardedGeneratedNumberCondition_exact
    (target : FlatNumberField)
    (firstMismatch secondMismatch : FlatCondition) :
    generatedNumberCondition target none firstMismatch [secondMismatch] =
      .and (FlatCondition.fieldFilled (.number target))
        (.or firstMismatch secondMismatch) := by
  rfl

/-- A present common validation guard sits once outside any already-built alternative body and inside the target-filled gate. -/
theorem generatedConditionWithGate_withCommon_exact
    (gate common alternatives : ConditionTree Leaf) :
    generatedConditionWithGate gate (some common) alternatives =
      .and gate (.and common alternatives) := by
  rfl

/-- Appending a mismatch branch extends the source-shaped left fold at the right without reordering or dropping an earlier branch. -/
theorem disjoinGeneratedNumberMismatches_append
    (first : FlatCondition) (remaining : List FlatCondition)
    (last : FlatCondition) :
    disjoinGeneratedNumberMismatches first (remaining ++ [last]) =
      .or (disjoinGeneratedNumberMismatches first remaining) last := by
  simp [disjoinGeneratedNumberMismatches, List.foldl_append]

/-- The guarded source representation exposes every alternative in declaration order. -/
theorem guardedGeneratedComputation_declaredOperations_exact
    (alternatives : GuardedGeneratedComputationAlternatives Operation) :
    alternatives.declaredAlternatives.map (fun alternative => alternative.operation) =
      alternatives.first.operation :: alternatives.second.operation ::
        alternatives.remaining.map (fun alternative => alternative.operation) := by
  simp [GuardedGeneratedComputationAlternatives.declaredAlternatives]

/-- Omitted tolerance metadata produces the source-level strict mismatch branch. -/
theorem generatedLiteralNumberMismatch_withoutTolerance
    (target : FlatNumberField) (guard : FlatCondition) (operation : Rat) :
    generatedLiteralNumberMismatch target guard operation none =
      .and guard
        (FlatCondition.compare (.number (.ordinary .notEqual) target operation)) := by
  rfl

/-- Present tolerance metadata produces that alternative's source-level tolerance branch. -/
theorem generatedLiteralNumberMismatch_withTolerance
    (target : FlatNumberField) (guard : FlatCondition) (operation : Rat)
    (range : NumericToleranceRange) :
    generatedLiteralNumberMismatch target guard operation (some range) =
      .and guard
        (FlatCondition.compare (.number (.tolerance range) target operation)) := by
  rfl

/-- Tolerance metadata is validation-only and erases from every alternative before first-match computation selection. -/
theorem generatedComputationAlternative_tolerance_selectionIrrelevant
    (alternative : GeneratedComputationAlternative Operation)
    (tolerance : Option NumericToleranceRange) :
    ({ alternative with tolerance := tolerance }).toComputationAlternative =
      alternative.toComputationAlternative := by
  rfl

/-- Singleton tolerance metadata is likewise invisible to its computation selector. -/
theorem singleGeneratedComputation_tolerance_selectionIrrelevant
    (alternative : SingleGeneratedComputationAlternative Operation)
    (tolerance : Option NumericToleranceRange)
    (common : Option ComputationCondition)
    (context : ScalarComputationContext) :
    SingleGeneratedComputationAlternative.selectFirst
        { alternative with tolerance := tolerance } common context =
      SingleGeneratedComputationAlternative.selectFirst alternative common context := by
  rfl

/-- An empty target suppresses the complete generated mismatch table, independently of the target-instance content bit. -/
theorem generatedNumberCondition_emptyTarget_notFired
    (target : FlatNumberField)
    (commonGuard : Option FlatCondition)
    (firstMismatch : FlatCondition) (remainingMismatches : List FlatCondition)
    (context : FlatContext) (targetHasContent : Bool)
    (empty : (FlatField.number target).observeValidation context = .empty) :
    (generatedNumberCondition target commonGuard
      firstMismatch remainingMismatches).evalFull
        context targetHasContent = .notFired := by
  cases targetHasContent <;>
    simp [generatedNumberCondition,
      generatedConditionWithGate,
      FlatCondition.evalFull, FlatCondition.canFireOnEmpty,
      FlatCondition.evalSelected, FlatField.evalFilled, empty]

/-- Generated mismatch construction preserves the already-checked expression exactly, fixes the stored target on the left, and carries warning suppression only as static comparison metadata. -/
theorem generatedNumericOperationMismatch_preservesBoundary
    (operation : NumericComputationOperation)
    (expression : AuthoredNumericExpr NumericValidationAtom)
    (tolerance : Option NumericToleranceRange) :
    let comparison :=
      generatedNumericOperationMismatch operation expression tolerance
    comparison.left = .atom (.field operation.target) ∧
      comparison.right = expression ∧
      comparison.suppressExactScaleWarning = operation.suppressExactScaleWarning := by
  cases tolerance <;> simp [generatedNumericOperationMismatch]

end A12Kernel
