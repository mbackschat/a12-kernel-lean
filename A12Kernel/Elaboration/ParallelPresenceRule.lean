import A12Kernel.Elaboration.ParallelFieldPair
import A12Kernel.Elaboration.ValidationRule

/-! # Bounded checked parallel presence rules

This capsule places one existing positive presence conjunction into the checked exact-text parallel join. The join owns key construction and optional physical environments; the shared condition tree owns short-circuiting; the shared rule emitter owns messages. Nonrepeatable path segments around either keyed group and operand are transparent because they add no environment binding. One non-indexed repeatable frame may surround the error side and recalculates the same join inside each actual frame row. Number ordering, two framed sides, negative leaves, and partial validation remain outside. Error pointers use the shared joined-side projection.
-/

namespace A12Kernel

/-- The positive-presence specialization of a shared checked parallel field pair. -/
structure CheckedParallelPresenceRule (model : FlatModel) extends CheckedParallelFieldPair model where
  private mk ::
  condition : CheckedValidationCondition model
  rowGroupOwned : condition.rowGroup = groups.commonParent
  conditionShape :
    condition.core =
      .and
        (ValidationCondition.repeatableFieldPresence .filled leftDeclaration)
        (ValidationCondition.repeatableFieldPresence .filled rightDeclaration)

namespace CheckedParallelPresenceRule

/-- The public certificate boundary: group compatibility, checked tree coherence, exact positive shape, and error-field membership remain independently inspectable. -/
def WellFormed (rule : CheckedParallelPresenceRule model) : Prop :=
  rule.groups.WellFormed ∧
    model.validate.isOk = true ∧
    rule.condition.core.wellFormedBool rule.condition.rowGroup rule.condition.declaringGroup = true ∧
    rule.groups.leftGroup.path.isPrefixOf
      rule.leftDeclaration.groupPath = true ∧
    rule.groups.rightGroup.path.isPrefixOf
      rule.rightDeclaration.groupPath = true ∧
    (rule.leftDeclaration.repeatableScope ==
      model.repeatableScopeForGroupPath rule.groups.leftGroup.path) =
        true ∧
    (rule.rightDeclaration.repeatableScope ==
      model.repeatableScopeForGroupPath rule.groups.rightGroup.path) =
        true ∧
    rule.condition.rowGroup = rule.groups.commonParent ∧
    rule.condition.core =
      .and
        (ValidationCondition.repeatableFieldPresence
          .filled rule.leftDeclaration)
        (ValidationCondition.repeatableFieldPresence
          .filled rule.rightDeclaration) ∧
    (rule.errorField == rule.leftDeclaration.id ||
      rule.errorField == rule.rightDeclaration.id) = true ∧
    rule.groups.outerScopePlan.admitsErrorOnLeft
      (rule.errorField == rule.leftDeclaration.id) = true

def core (rule : CheckedParallelPresenceRule model) :
    ResolvedValidationRule model := {
  condition := rule.condition.core
  errorField := rule.errorField
  errorCode := rule.errorCode
  severity := rule.severity
  messagePlan := rule.messagePlan
}

def errorDeclaration
    (rule : CheckedParallelPresenceRule model) : FlatFieldDecl :=
  if rule.errorField == rule.leftDeclaration.id then
    rule.leftDeclaration
  else
    rule.rightDeclaration

private def evalLeaf (row : ResolvedParallelIndexRow)
    (preliminary : CheckedIndexPreliminary model) :
    ValidationConditionLeaf model →
      Except ParallelPresenceRuleEvaluationError Verdict
  | .repeatableFieldPresence .filled declaration =>
      (row.readValidation preliminary declaration.id)
        |>.mapError .join
        |>.map CellObservation.evalValidationFilled
  | _ => .error .unsupportedCondition

/-- Positive presence reuses the same checked join traversal as other pair-condition families. -/
def evalFull (rule : CheckedParallelPresenceRule model)
    (preliminary : CheckedIndexPreliminary model) (outer : Env := []) :
    Except ParallelPresenceRuleEvaluationError (List ParallelRuleRowOutcome) :=
  rule.toCheckedParallelFieldPair.evalFullWith rule.condition.core
    (fun row view => rule.condition.core.evalVerdictExcept (evalLeaf row view)) preliminary outer

end CheckedParallelPresenceRule

/-- Preserve the established presence API while deriving its layout from the shared pair certificate. -/
def checkParallelPresenceRule (model : FlatModel)
    (leftField rightField errorField : FieldId)
    (errorCode : String) (severity : ValidationSeverity) (messagePlan : MessageRenderPlan) :
    Except ParallelPresenceRuleAssemblyError (CheckedParallelPresenceRule model) := do
  let pair ← checkParallelFieldPair model leftField rightField errorField errorCode severity messagePlan
  let core : ValidationCondition model := .and
    (ValidationCondition.repeatableFieldPresence .filled pair.leftDeclaration)
    (ValidationCondition.repeatableFieldPresence .filled pair.rightDeclaration)
  let rowGroup := pair.groups.commonParent
  if hCore : core.wellFormedBool rowGroup = true then
    pure {
      toCheckedParallelFieldPair := pair
      condition := { rowGroup, core, modelWellFormed := pair.groups.modelWellFormed, wellFormed := hCore }
      rowGroupOwned := rfl
      conditionShape := rfl
    }
  else throw .incoherentCondition

end A12Kernel
