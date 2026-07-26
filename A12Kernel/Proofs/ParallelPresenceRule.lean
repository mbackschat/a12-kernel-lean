import A12Kernel.Elaboration.ParallelPresenceRule
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

@[simp] theorem checkedParallelPresenceRule_cannotFireOnEmpty
    (rule : CheckedParallelPresenceRule model) :
    rule.condition.core.canFireOnEmpty = false := by
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

end A12Kernel
