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

end A12Kernel
