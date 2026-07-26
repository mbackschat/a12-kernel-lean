import A12Kernel.Elaboration.CheckedIndexColumn
import A12Kernel.Elaboration.ValidationRule

/-! # Bounded checked parallel presence rules

This capsule places one existing positive presence conjunction into the checked exact-text direct-sibling join. The join owns key construction and optional physical environments; the shared condition tree owns short-circuiting; the shared rule emitter owns messages. Number ordering, framed topology, negative leaves, partial validation, and nonphysical error pointers remain outside.
-/

namespace A12Kernel

inductive ParallelPresenceRuleAssemblyError where
  | model (error : ResolveError)
  | join (error : CheckedIndexColumnError)
  | incoherentCondition
  | incoherentOperandGroup (field : FieldId) (group : GroupPath)
  | errorFieldNotOperand (field left right : FieldId)
  deriving Repr, DecidableEq

inductive ParallelPresenceRuleEvaluationError where
  | join (error : CheckedIndexColumnError)
  | missingErrorEnvironment (key : SemanticIndexKey)
  | environment (error : EnvBindingError)
  | unsupportedCondition
  deriving Repr, DecidableEq

/-- One key-preserving whole-rule result. Silent outcomes retain their join key even though no physical error address is needed. -/
structure ParallelRuleRowOutcome where
  key : SemanticIndexKey
  outcome : FlatRuleOutcome
  deriving Repr, DecidableEq

/-- A checked full-validation rule for the exact positive conjunction `FieldFilled(left) And FieldFilled(right)` over two direct sibling index groups. -/
structure CheckedParallelPresenceRule (model : FlatModel) where
  private mk ::
  condition : CheckedValidationCondition model
  groups : CheckedParallelIndexGroups model
  leftDeclaration : FlatFieldDecl
  rightDeclaration : FlatFieldDecl
  errorField : FieldId
  errorCode : String
  severity : ValidationSeverity
  messagePlan : MessageRenderPlan
  leftOperandGroup :
    (leftDeclaration.groupPath == groups.leftGroup.path) = true
  rightOperandGroup :
    (rightDeclaration.groupPath == groups.rightGroup.path) = true
  rowGroupOwned :
    condition.rowGroup = groups.leftGroup.path.dropLast
  conditionShape :
    condition.core =
      .and
        (ValidationCondition.repeatableFieldPresence
          .filled leftDeclaration)
        (ValidationCondition.repeatableFieldPresence
          .filled rightDeclaration)
  errorFieldIsOperand :
    (errorField == leftDeclaration.id ||
      errorField == rightDeclaration.id) = true

namespace CheckedParallelPresenceRule

/-- The public certificate boundary: group compatibility, checked tree coherence, exact positive shape, and error-field membership remain independently inspectable. -/
def WellFormed (rule : CheckedParallelPresenceRule model) : Prop :=
  rule.groups.WellFormed ∧
    model.validate.isOk = true ∧
    rule.condition.core.wellFormedBool rule.condition.rowGroup = true ∧
    (rule.leftDeclaration.groupPath == rule.groups.leftGroup.path) =
      true ∧
    (rule.rightDeclaration.groupPath == rule.groups.rightGroup.path) =
      true ∧
    rule.condition.rowGroup = rule.groups.leftGroup.path.dropLast ∧
    rule.condition.core =
      .and
        (ValidationCondition.repeatableFieldPresence
          .filled rule.leftDeclaration)
        (ValidationCondition.repeatableFieldPresence
          .filled rule.rightDeclaration) ∧
    (rule.errorField == rule.leftDeclaration.id ||
      rule.errorField == rule.rightDeclaration.id) = true

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

private def errorSide (rule : CheckedParallelPresenceRule model)
    (row : ResolvedParallelIndexRow) : ResolvedParallelIndexSide :=
  if rule.errorField == rule.leftDeclaration.id then
    row.left
  else
    row.right

private def evalRow (rule : CheckedParallelPresenceRule model)
    (preliminary : CheckedIndexPreliminary model)
    (row : ResolvedParallelIndexRow) :
    Except ParallelPresenceRuleEvaluationError ParallelRuleRowOutcome := do
  let verdict ← rule.condition.core.evalVerdictExcept
    (evalLeaf row preliminary)
  let outcome ← match verdict with
    | .fired _ => do
        let environment ← match (rule.errorSide row).environment with
          | some environment => pure environment
          | none => throw (.missingErrorEnvironment row.key)
        let path ←
          environment.pathForScope rule.errorDeclaration.repeatableScope
            |>.mapError .environment
        pure (rule.core.emitAt path verdict)
    | .notFired | .unknown =>
        -- `emitAt` does not inspect the address for a silent verdict, so no
        -- nonphysical placeholder enters `CellAddr`.
        pure (rule.core.emitAt [] verdict)
  pure { key := row.key, outcome }

/-- Evaluate the checked rule once per lexical join key. The join, leaf reads, connective fold, and emitter each remain at their existing owner. -/
def evalFull (rule : CheckedParallelPresenceRule model)
    (preliminary : CheckedIndexPreliminary model) (outer : Env := []) :
    Except ParallelPresenceRuleEvaluationError
      (List ParallelRuleRowOutcome) := do
  let join ←
    preliminary.resolveCheckedParallelIndexJoin rule.groups outer
      |>.mapError .join
  join.rows.mapM (rule.evalRow preliminary)

end CheckedParallelPresenceRule

/-- Check the narrow parallel rule plan without passing caller-selected groups or iteration rows. Each operand declaration determines its exact keyed group in the validated model. -/
def checkParallelPresenceRule (model : FlatModel)
    (leftField rightField errorField : FieldId)
    (errorCode : String) (severity : ValidationSeverity)
    (messagePlan : MessageRenderPlan) :
    Except ParallelPresenceRuleAssemblyError
      (CheckedParallelPresenceRule model) := do
  let leftDeclaration ←
    model.lookupUniqueId leftField |>.mapError .model
  let rightDeclaration ←
    model.lookupUniqueId rightField |>.mapError .model
  let leftGroup ←
    model.lookupUniqueRepeatablePath leftDeclaration.groupPath
      |>.mapError .model
  let rightGroup ←
    model.lookupUniqueRepeatablePath rightDeclaration.groupPath
      |>.mapError .model
  let groups ←
    checkParallelIndexGroups model leftGroup rightGroup
      |>.mapError .join
  if hLeftGroup :
      (leftDeclaration.groupPath == groups.leftGroup.path) = true then
    if hRightGroup :
        (rightDeclaration.groupPath == groups.rightGroup.path) = true then
      if hError :
          (errorField == leftDeclaration.id ||
            errorField == rightDeclaration.id) = true then
        let core : ValidationCondition model :=
          .and
            (ValidationCondition.repeatableFieldPresence
              .filled leftDeclaration)
            (ValidationCondition.repeatableFieldPresence
              .filled rightDeclaration)
        let rowGroup := groups.leftGroup.path.dropLast
        if hCore : core.wellFormedBool rowGroup = true then
          let condition : CheckedValidationCondition model := {
            rowGroup
            core
            modelWellFormed := groups.modelWellFormed
            wellFormed := hCore
          }
          pure {
            condition
            groups
            leftDeclaration
            rightDeclaration
            errorField
            errorCode
            severity
            messagePlan
            leftOperandGroup := hLeftGroup
            rightOperandGroup := hRightGroup
            rowGroupOwned := rfl
            conditionShape := rfl
            errorFieldIsOperand := hError
          }
        else
          throw .incoherentCondition
      else
        throw (.errorFieldNotOperand errorField
          leftDeclaration.id rightDeclaration.id)
    else
      throw (.incoherentOperandGroup
        rightDeclaration.id groups.rightGroup.path)
  else
    throw (.incoherentOperandGroup
      leftDeclaration.id groups.leftGroup.path)

end A12Kernel
