import A12Kernel.Elaboration.ValidationRule.Execution

/-! # Checked assembly for resolved validation rules

This boundary consumes an existing checked flat or mixed condition and a resolved error entity, a field or a group. Surface rule syntax and authored message templates remain outside it.
-/

namespace A12Kernel

namespace FlatRuleAssemblyError

/-- The reference refusal for either entity kind. -/
def notReferenced : RuleErrorEntity → FlatRuleAssemblyError
  | .field field => .errorFieldNotReferenced field
  | .group path => .groupErrorTarget path .notReferenced

/-- An iterated level no reference to the entity binds. -/
def iterationInvalid : RuleErrorEntity → RepeatableLevel → FlatRuleAssemblyError
  | .field field, level => .errorFieldIterationInvalid field level
  | .group path, level => .groupErrorTarget path (.iterationInvalid level)

end FlatRuleAssemblyError

private def assembleResolvedRule (allowRepeatableOnce : Bool)
    (model : FlatModel)
    (coreOf : CheckedCondition → CoreCondition)
    (referencesField : CoreCondition → RuleErrorEntity → Bool)
    (iterationScopeOf : CoreCondition →
      Except ValidationCondition.RuleIterationScopeError
        (Option (List RepeatableLevel)))
    (condition : CheckedCondition)
    (errorEntity : RuleErrorEntity) (errorCode : String)
    (severity : ValidationSeverity)
    (messagePlan : MessageRenderPlan) :
    Except FlatRuleAssemblyError
      (CheckedResolvedRule allowRepeatableOnce model
        CheckedCondition CoreCondition
        coreOf referencesField iterationScopeOf) :=
  match hIteration : iterationScopeOf (coreOf condition) with
  | .error error => .error (.iterationScope error)
  | .ok iterationScope =>
    match hPlacement : model.ruleErrorPlacement errorEntity with
    | .error error => .error error
    | .ok placement =>
      if hScope :
          ruleErrorScopeCompatible allowRepeatableOnce
            placement.repeatableScope iterationScope = true then
        if hReferenced :
            referencesField (coreOf condition) errorEntity = true then
          .ok {
            condition
            errorEntity
            errorCode
            severity
            messagePlan
            errorPlacement := placement
            errorPlacementOwned := hPlacement
            iterationScope
            iterationScopeOwned := hIteration
            errorFieldScopeCompatible := hScope
            errorFieldReferenced := hReferenced
          }
        else
          .error (.notReferenced errorEntity)
      else
        match iterationScope, errorEntity with
        | none, .field field => .error (.repeatableErrorField field)
        | none, .group path => .error (.groupErrorTarget path .repeatable)
        | some expected, .field field =>
            .error (.iterationScopeMismatch field expected placement.repeatableScope)
        | some expected, .group path =>
            .error (.groupErrorTarget path (.scopeMismatch expected placement.repeatableScope))

/-- Assemble the metadata boundary after condition elaboration. A repeatable error field is rejected before reference membership because this capsule has no row address. -/
def assembleResolvedFlatRule (model : FlatModel)
    (condition : CheckedFlatCondition model)
    (errorField : FieldId) (errorCode : String)
    (severity : ValidationSeverity)
    (messagePlan : MessageRenderPlan) :
  Except FlatRuleAssemblyError (CheckedResolvedFlatRule model) :=
  assembleResolvedRule false model (fun checked => checked.core)
    FlatCondition.referencesErrorEntity
    (fun _ =>
      (.ok none :
        Except ValidationCondition.RuleIterationScopeError
          (Option (List RepeatableLevel))))
    condition (.field errorField) errorCode severity messagePlan

/-- The condition leaves a rule reporting on a group admits: those whose reading at the group's
unindexed level the [group-target checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-group-target-nested-join)
measures or that read it only through a star. -/
private def ValidationConditionLeaf.supportsGroupTarget : ValidationConditionLeaf model → Bool
  | .flat _ | .repeatableFieldPresence _ _ | .groupPresence _ _ | .orderedNumeric _ _ => true
  | _ => false

/-- Assemble the existing message/error-entity boundary around a checked mixed condition. -/
def assembleResolvedValidationRuleFor (model : FlatModel)
    (condition : CheckedValidationCondition model)
    (errorEntity : RuleErrorEntity) (errorCode : String)
    (severity : ValidationSeverity)
    (messagePlan : MessageRenderPlan) :
  Except FlatRuleAssemblyError (CheckedResolvedValidationRule model) :=
  let assembled := (assembleResolvedRule true model (fun checked => checked.core)
    (fun core entity => core.referencesErrorEntity entity)
    ValidationCondition.ordinaryIterationScope
    condition errorEntity errorCode severity messagePlan).bind fun rule =>
      match errorEntity with
      | .field field =>
          if condition.core.authoredErrorReference? field == some false then
            .error (.errorFieldNotReferenced field)
          else .ok rule
      | .group path =>
          if !condition.core.allLeaves ValidationConditionLeaf.supportsGroupTarget ||
              condition.core.rootOnlyGroupTargetReference path then
            .error (.groupErrorTarget path .unsupported)
          else .ok rule
  -- The walk's refusal, measured only where the error field binds the level ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-24c-group-operand-walk)),
  -- and an error field the condition never names ([capture](../../docs/sources/model-structure-and-declaration-probes.md#src-iteration-guard-k04)
  -- rows `o01`–`o03`) answer ahead of the per-level negative-condition gate; other refusals follow it.
  match assembled with
  | .error error =>
      match error.unboundLevel? model condition.declaringGroup, error with
      | some unbound, _ => .error unbound
      | none, .errorFieldNotReferenced _ | none, .groupErrorTarget _ .notReferenced => .error error
      | none, _ =>
          match condition.core.iterationLegality with
          | .ok (.invalid level) => .error (.negativeConditionInIteration level)
          | .ok .legal | .ok (.insufficient _) | .error _ => .error error
  | .ok rule =>
      let errorGroup := rule.errorPlacement.groupPath
      -- With the error field outside the rule group nothing binds a level, the rule group's own
      -- included, so an iterating rule whose error scope matches is refused all the same.
      match rule.iterationScope, WrittenFieldPlacement.of condition.declaringGroup errorGroup with
      | some (level :: _), .outside =>
          let unbound := model.unboundOperandLevel condition.declaringGroup errorGroup level
          .error (match errorEntity with
            | .field field => .unboundOperandLevel field unbound
            | .group path => .groupErrorTarget path (.unbound unbound))
      | _, _ =>
          let innerLevel? := (rule.iterationScope.getD []).find? fun level =>
            (model.repeatableGroupAtLevel? level).any (fun group => group.path.length > 1)
          match errorEntity with
          | .field field =>
              if condition.core.formOnlyErrorReference? field == some true then
                match innerLevel? with
                | some level => .error (.formOnlyIteration field level)
                | none => finish rule
              else finish rule
          | .group _ => finish rule
where
  /-- A group target's own level is not checked: the Kernel judges only the levels above the
  entity ([checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-group-target-nested-join),
  `group-level` row `t6`). -/
  finish (rule : CheckedResolvedValidationRule model) :
      Except FlatRuleAssemblyError (CheckedResolvedValidationRule model) :=
          let unbound? : RepeatableLevel → Bool := match errorEntity with
            | .field field => fun level => condition.core.errorReferenceAt? field level == some false
            | .group path => fun level =>
                !rule.errorPlacement.unindexed.contains level &&
                  !condition.core.groupTargetReferenceAt path level
          match (rule.iterationScope.getD []).find? unbound? with
          | some level => .error (.iterationInvalid errorEntity level)
          | none =>
              match condition.core.iterationLegality with
              | .ok (.invalid level) => .error (.negativeConditionInIteration level)
              | .ok .legal | .ok (.insufficient _) | .error _ => .ok rule

/-- Assemble a rule reporting on a field. -/
def assembleResolvedValidationRule (model : FlatModel)
    (condition : CheckedValidationCondition model)
    (errorField : FieldId) (errorCode : String)
    (severity : ValidationSeverity)
    (messagePlan : MessageRenderPlan) :
  Except FlatRuleAssemblyError (CheckedResolvedValidationRule model) :=
  assembleResolvedValidationRuleFor model condition (.field errorField) errorCode severity messagePlan

end A12Kernel
