import A12Kernel.Elaboration.ParallelPresenceRule
import A12Kernel.Elaboration.PartialParallelFieldRule
import A12Kernel.Proofs.CheckedIndexColumn

/-! # Bounded checked parallel presence-rule laws -/

namespace A12Kernel

theorem checkedParallelPresenceRule_wellFormed
    (rule : CheckedParallelPresenceRule model) :
    rule.WellFormed :=
  ⟨checkedParallelIndexGroups_wellFormed rule.groups,
    rule.condition.modelWellFormed, rule.condition.wellFormed,
    rule.leftOperandGroup, rule.rightOperandGroup,
    rule.leftOperandScope, rule.rightOperandScope, rule.partnerOperandScope,
    rule.rowGroupOwned, rule.conditionShape, rule.errorFieldIsOperand,
    rule.errorFieldOnFramedSide⟩

@[simp] theorem checkedParallelPresenceRule_conditionShape
    (rule : CheckedParallelPresenceRule model) :
    rule.condition.core =
      .and
        (ValidationCondition.repeatableFieldPresence
          .filled rule.leftDeclaration)
        (ValidationCondition.repeatableFieldPresence
          .filled rule.rightDeclaration) :=
  rule.conditionShape

/-- Positive presence contributes no empty-case exception; the shared static root classification
remains the only possible reason to lift the gate (spec/03 A.4). -/
@[simp] theorem checkedParallelPresenceRule_emptyGate_eq_multipleRoots
    (rule : CheckedParallelPresenceRule model) :
    rule.condition.core.canFireOnEmpty = rule.condition.core.referencesMultipleRoots := by
  rw [rule.conditionShape]
  rfl

@[simp] theorem checkedParallelPresenceRule_errorDeclaration_id
    (rule : CheckedParallelPresenceRule model) :
    rule.errorDeclaration.id = rule.errorField := by
  unfold CheckedParallelPresenceRule.errorDeclaration
  split
  next left =>
    have resolved :
        rule.errorField = rule.leftDeclaration.id := by
      simpa using left
    exact resolved.symm
  next notLeft =>
    have operand := rule.errorFieldIsOperand
    simp [notLeft] at operand
    exact operand.symm

/-- The executable parallel certificate retains both joined sides, typed leaves and a structurally valid guard, at the join, its frames and the error field's levels below the join. -/
theorem checkedParallelFieldRule_wellFormed (rule : CheckedParallelFieldRule model) :
    rule.pair.groups.WellFormed ∧ model.validate.isOk = true ∧
    rule.condition.errorTargetRefusal rule.pair = none ∧
    rule.condition.allLeaves (ParallelFieldLeaf.admitted rule.pair rule.suppressExactScaleWarning) = true ∧
    rule.condition.anyLeaf (ParallelFieldLeaf.uses rule.pair .left) = true ∧
    rule.condition.anyLeaf (ParallelFieldLeaf.uses rule.pair .right) = true ∧
    rule.condition.guarded rule.pair = true ∧
    ParallelFieldCondition.framesGuarded rule.pair rule.condition = true ∧
    ParallelFieldCondition.innerGuarded rule.pair rule.condition = true := by
  refine ⟨checkedParallelIndexGroups_wellFormed rule.pair.groups,
    rule.pair.groups.modelWellFormed, rule.errorTargetAllowed, ?_⟩
  simpa only [ParallelFieldCondition.admitted, Bool.and_eq_true, and_assoc] using rule.admitted

/-- Full relevance admits every outer dispatch, independently of the selected error side. -/
theorem checkedParallelFieldPair_fullRelevance (pair : CheckedParallelFieldPair model) (outer : Env) :
    pair.admitsPartialOuter .full outer = true := rfl

/-- An absent error-field projection suppresses dispatch even when the other side supplies join keys. -/
theorem checkedParallelFieldPair_noRelevantError (pair : CheckedParallelFieldPair model) (outer : Env) :
    pair.admitsPartialOuter (.partialSet []) outer = false := rfl

/-- Silent partial unavailability reaches both presence operators without inventing a formal cause. -/
theorem parallelFieldPresence_silentUnavailable (pair : CheckedParallelFieldPair model)
    (read : ParallelFieldOperand → Except ParallelPresenceRuleEvaluationError (Option CellObservation))
    (readGroup : ResolvedGroupReference → Except ParallelPresenceRuleEvaluationError GroupPresenceState)
    (readOrdinary : ValidationConditionLeaf model → Except ParallelPresenceRuleEvaluationError Verdict)
    (readAtom : ValidationConditionLeaf model →
      Except ParallelPresenceRuleEvaluationError (Except NumericValidationUnavailable NumericArithmeticOutcome))
    (side : ParallelFieldOperand) (op : RepeatableFieldPresenceOperator)
    (unavailable : read side = .ok none) :
    ParallelFieldLeaf.evalWith pair read readGroup readOrdinary readAtom (.presence side op) = .ok .unknown := by
  simp [ParallelFieldLeaf.evalWith, unavailable]
  rfl

end A12Kernel
