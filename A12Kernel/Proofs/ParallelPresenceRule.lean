import A12Kernel.Elaboration.ParallelPresenceRule
import A12Kernel.Elaboration.ParallelFieldRule
import A12Kernel.Proofs.CheckedIndexColumn

/-! # Bounded checked parallel presence-rule laws -/

namespace A12Kernel

theorem checkedParallelPresenceRule_wellFormed
    (rule : CheckedParallelPresenceRule model) :
    rule.WellFormed :=
  ⟨checkedParallelIndexGroups_wellFormed rule.groups,
    rule.condition.modelWellFormed, rule.condition.wellFormed,
    rule.leftOperandGroup, rule.rightOperandGroup,
    rule.leftOperandScope, rule.rightOperandScope,
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

/-- The executable parallel certificate retains both joined sides, typed leaves and a structurally valid guard. -/
theorem checkedParallelFieldRule_wellFormed (rule : CheckedParallelFieldRule model) :
    rule.pair.groups.WellFormed ∧ model.validate.isOk = true ∧
    rule.condition.errorTargetRefusal rule.pair = none ∧
    rule.condition.allLeaves (ParallelFieldLeaf.admitted rule.pair rule.suppressExactScaleWarning) = true ∧
    rule.condition.anyLeaf (ParallelFieldLeaf.uses rule.pair .left) = true ∧
    rule.condition.anyLeaf (ParallelFieldLeaf.uses rule.pair .right) = true ∧
    rule.condition.guarded rule.pair = true ∧
    ParallelFieldCondition.framesGuarded rule.pair rule.condition = true := by
  refine ⟨checkedParallelIndexGroups_wellFormed rule.pair.groups,
    rule.pair.groups.modelWellFormed, rule.errorTargetAllowed, ?_⟩
  simpa only [ParallelFieldCondition.admitted, Bool.and_eq_true, and_assoc] using rule.admitted

end A12Kernel
