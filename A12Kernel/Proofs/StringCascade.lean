import A12Kernel.Proofs.Observation
import A12Kernel.Proofs.StringComputation
import A12Kernel.Semantics.StringApplication
import A12Kernel.Semantics.StringCascade

/-! # A12Kernel.Proofs.StringCascade — direct dependency-edge laws

These theorems establish the internal laws of the explicit outcome-to-dependency bridge. They do not claim that the external kernel uses this representation or that retained output order identifies a scheduler.
-/

namespace A12Kernel

/-- Every dependency cell admitted by the outcome bridge carries the checked-cell representation invariant. -/
theorem dependencyOutcome_produces_wellFormedCell
    (outcome : StringTargetOutcome) (dependency : StringDependencyCell)
    (_produced : StringDependencyCell.ofOutcome outcome = .ok dependency) :
    dependency.checked.WellFormed :=
  dependency.wellFormed

/-- The overlay reads the producer target from the dependency cell rather than from stale document state. -/
theorem dependencyCell_shadows_target (context : StringComputationContext)
    (field : FieldId) (dependency : StringDependencyCell) :
    (context.withDependencyCell field dependency).read field = dependency.checked := by
  simp [StringComputationContext.withDependencyCell]

/-- Overlaying one producer target leaves every distinct field read unchanged. -/
theorem dependencyCell_preserves_other_read (context : StringComputationContext)
    (field other : FieldId) (dependency : StringDependencyCell)
    (different : other ≠ field) :
    (context.withDependencyCell field dependency).read other = context.read other := by
  simp [StringComputationContext.withDependencyCell, different]

/-- A successful outcome overlay preserves all reads except its named producer target. -/
theorem dependencyOutcome_preserves_other_read (context updated : StringComputationContext)
    (field other : FieldId) (outcome : StringTargetOutcome)
    (different : other ≠ field)
    (bound : context.withDependencyOutcome field outcome = .ok updated) :
    updated.read other = context.read other := by
  cases mapped : StringDependencyCell.ofOutcome outcome with
  | error fault =>
      simp [StringComputationContext.withDependencyOutcome, mapped] at bound
  | ok dependency =>
      simp [StringComputationContext.withDependencyOutcome, mapped] at bound
      cases bound
      exact dependencyCell_preserves_other_read context field other dependency different

/-- A clean no-value producer becomes a clean empty computation read. -/
theorem noValueDependency_reads_noValue (context : StringComputationContext)
    (field : FieldId) :
    (context.withDependencyOutcome field .noValue).map
      (fun updated => updated.readTerm field) = .ok (.ok .noValue) := by
  simp only [StringComputationContext.withDependencyOutcome,
    StringDependencyCell.ofOutcome, pure, Except.pure, Except.map, Except.ok.injEq]
  unfold StringComputationContext.readTerm
  rw [dependencyCell_shadows_target]
  rfl

/-- An accepted producer value becomes the exact nonempty String read by its consumer. -/
theorem acceptedDependency_reads_value (context : StringComputationContext)
    (field : FieldId) (stored : StoredString) :
    (context.withDependencyOutcome field (.accepted stored)).map
      (fun updated => updated.readTerm field) = .ok (.ok (.text stored.text)) := by
  simp only [StringComputationContext.withDependencyOutcome,
    StringDependencyCell.ofOutcome, pure, Except.pure, Except.map, Except.ok.injEq]
  unfold StringComputationContext.readTerm
  rw [dependencyCell_shadows_target]
  rw [show observeCell .computation (StringDependencyCell.value stored).checked =
      .value (.str stored.text) by
    exact computation_observes_clean_value (Value.str stored.text)]
  simp [stored.nonempty, pure, Except.pure]

/-- Either admitted String target error becomes declared-constraint poison when a later computation reads the target. -/
theorem erroredDependency_reads_declaredConstraintPoison
    (context : StringComputationContext) (field : FieldId)
    (attempted : StoredString) (cause : StringTargetError) :
    (context.withDependencyOutcome field (.errored attempted cause)).map
      (fun updated => updated.readTerm field) =
        .ok (.ok (.poison .declaredConstraint)) := by
  cases cause <;>
    simp only [StringComputationContext.withDependencyOutcome,
      StringDependencyCell.ofOutcome, StringTargetError.dependencyCause,
      pure, Except.pure, Except.map, Except.ok.injEq]
  all_goals
    unfold StringComputationContext.readTerm
    rw [dependencyCell_shadows_target]
    rw [show observeCell .computation
        (StringDependencyCell.poison .declaredConstraint).checked =
          .poison .declaredConstraint by
      exact computation_observes_single_poison .declaredConstraint (by decide)]
    rfl

/-- Ordinary inherited computation poison remains the same cause at the dependent read. -/
theorem inheritedDependency_reads_samePoison
    (context : StringComputationContext) (field : FieldId)
    (cause : FormalCause) (notRequired : cause ≠ .required) :
    (context.withDependencyOutcome field (.poison cause)).map
      (fun updated => updated.readTerm field) = .ok (.ok (.poison cause)) := by
  cases cause <;> try contradiction
  all_goals
    simp only [StringComputationContext.withDependencyOutcome,
      StringDependencyCell.ofOutcome, pure, Except.pure, Except.map, Except.ok.injEq]
    unfold StringComputationContext.readTerm
    rw [dependencyCell_shadows_target]
    rw [show observeCell .computation
        (StringDependencyCell.poison _).checked = .poison _ by
      exact computation_observes_single_poison _ notRequired]
    rfl

/-- Validation-scoped requiredness is rejected rather than silently changing computation poison into absence. -/
theorem requiredDependencyPoison_is_rejected
    (context : StringComputationContext) (field : FieldId) :
    context.withDependencyOutcome field (.poison .required) =
      .error .validationScopedRequired := by
  rfl

/-- The attempted invalid payload is deliberately absent from the dependency representation. Only its target-error class affects the later read. -/
theorem erroredDependency_does_not_expose_attempt
    (first second : StoredString) (cause : StringTargetError) :
    StringDependencyCell.ofOutcome (.errored first cause) =
      StringDependencyCell.ofOutcome (.errored second cause) := by
  rfl

/-- Producer prior state does not participate in the checked outcome supplied to a dependent step. -/
theorem stringStep_outcome_independent_of_prior
    (step : StringComputationStep) (otherPrior : PriorStringTarget)
    (context : StringComputationContext) :
    step.evaluateOutcome context =
      ({ step with prior := otherPrior }.evaluateOutcome context) := by
  rfl

/-- A clean not-true common precondition suppresses an arbitrary String body without consulting its expression or context. -/
theorem notTrueStringPrecondition_evaluates_noValue
    (step : StringComputationStep) (context : StringComputationContext) :
    step.evaluateOutcomeWhen .notTrue context = .ok .noValue := by
  rfl

/-- A holding common precondition delegates without changing the ordinary checked outcome. -/
theorem holdingStringPrecondition_preserves_outcome
    (step : StringComputationStep) (context : StringComputationContext) :
    step.evaluateOutcomeWhen .holds context = step.evaluateOutcome context := by
  rfl

/-- A poisoned common precondition preserves its exact cause and suppresses the body. -/
theorem poisonedStringPrecondition_preserves_cause
    (step : StringComputationStep) (context : StringComputationContext)
    (cause : FormalCause) :
    step.evaluateOutcomeWhen (.poison cause) context = .ok (.poison cause) := by
  rfl

/-- Once the common precondition holds, a consumed formally invalid String operand poisons the target instead of becoming quiet no-value. -/
theorem holdingStringPrecondition_consumedInvalidField_poisons
    (context : StringComputationContext) (operand target : FieldId)
    (cause : FormalCause) (policy : StringFieldPolicy)
    (prior : PriorStringTarget)
    (poisonedRead : observeCell .computation (context.read operand) = .poison cause) :
    ({ targetField := target
       expression := .field operand
       targetPolicy := policy
       prior } : StringComputationStep).evaluateOutcomeWhen .holds context =
      .ok (.poison cause) := by
  simp only [StringComputationStep.evaluateOutcomeWhen,
    StringComputationStep.evaluateOutcome,
    poisonedStringField_evaluates_poison context operand cause poisonedRead,
    StringFieldPolicy.checkTarget]

/-- Equal immediate deltas do not imply equal dependency states. Clean no-value and malformed poison both clear the same prior target, but their consumer reads remain different. -/
theorem same_delta_does_not_imply_same_dependency
    (prior : PriorStringTarget) :
    StringTargetOutcome.noValue.projectDelta prior =
        (StringTargetOutcome.poison .malformed).projectDelta prior ∧
      StringDependencyCell.empty.checked ≠
        (StringDependencyCell.poison .malformed).checked := by
  constructor
  · cases prior <;> rfl
  · decide

/-- Equal value-only applied views also do not determine the dependency state. A rejected attempt and quiet no-value both apply no value, while the former must poison a dependent read. -/
theorem same_appliedValue_does_not_imply_same_dependency
    (attempted : StoredString) (cause : StringTargetError) :
    (StringTargetOutcome.errored attempted cause).appliedValue =
        StringTargetOutcome.noValue.appliedValue ∧
      (StringDependencyCell.poison cause.dependencyCause).checked ≠
        StringDependencyCell.empty.checked := by
  constructor
  · rfl
  · cases cause <;> decide

/-- Quiet precondition clearing and consumed-operand poison have identical exact target placement, yet a later read still distinguishes clean empty from poison. -/
theorem same_exact_application_does_not_imply_same_dependency_read
    (context : StringComputationContext) (field : FieldId)
    (prior : StringTargetState) (cause : FormalCause)
    (notRequired : cause ≠ .required) :
    StringTargetOutcome.noValue.applyTo prior =
        (StringTargetOutcome.poison cause).applyTo prior ∧
      (context.withDependencyOutcome field .noValue).map
          (fun updated => updated.readTerm field) ≠
        (context.withDependencyOutcome field (.poison cause)).map
          (fun updated => updated.readTerm field) := by
  constructor
  · cases prior <;> rfl
  · rw [noValueDependency_reads_noValue,
      inheritedDependency_reads_samePoison context field cause notRequired]
    simp

end A12Kernel
