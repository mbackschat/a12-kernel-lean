import A12Kernel.Proofs.ValidationCondition

/-! # Group-list validation-condition laws

This module owns the laws specific to direct and starred group-list leaves. General
condition connectives, field leaves, and addressed evaluation remain in
`A12Kernel.Proofs.ValidationCondition`.
-/

namespace A12Kernel

/-- Scalar evaluation delegates a wholly direct field/group list to the shared entity-presence tally and refuses every list that still needs starred topology. -/
@[simp]
theorem validationCondition_groupList_evalSelected
    (model : FlatModel) (operator : GroupFillQuantifier)
    (operands : List (ResolvedGroupListOperand model))
    (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance) :
    (ValidationCondition.groupList (model := model)
        operator operands).evalSelected
        context isRelevant =
      match operands.mapM fun operand =>
          operand.evalDirectPresence? context isRelevant with
      | some states =>
          (operator.evalPresence states).asConservativeVerdict
      | none => .unknown := by
  rfl

/-- Scalar group-list evaluation fires exactly when every operand is direct and the shared tally fires with the same polarity. -/
theorem validationCondition_groupList_fired_iff
    (model : FlatModel) (operator : GroupFillQuantifier)
    (operands : List (ResolvedGroupListOperand model))
    (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance)
    (states : List GroupListPresenceState)
    (direct : operands.mapM (fun operand =>
      operand.evalDirectPresence? context isRelevant) = some states)
    (polarity : Polarity) :
    (ValidationCondition.groupList (model := model)
        operator operands).evalSelected
        context isRelevant = .fired polarity ↔
      operator.evalPresence states = .fired polarity := by
  rw [validationCondition_groupList_evalSelected model, direct]
  exact validationFillOutcome_conservative_fired_iff
    (operator.evalPresence states) polarity

/-- A nonrepeatable terminal below starred ancestry classifies each in-capacity environment through the existing checked group-product owner. -/
theorem resolvedGroupListOperand_starredGroupPresence_checked
    (model : FlatModel)
    (source : CheckedStarredGroupPresenceSource model)
    (scalar : ValidationEvaluationContext) (outer : Env)
    (document : CheckedDocument model) :
    (ResolvedGroupListOperand.starredGroupPresence source).evalAddressedTally {
        scalar, outer, input := .checked document
      } = (do
        let environments ←
          (source.inCapacityEnvironments document.source.toDocument outer)
            |>.mapError CheckedAddressingError.addressing
        let states ← environments.mapM fun environment => do
          let input ←
            (document.groupPresenceInput source.groupPath environment
              .fullyRelevant false).mapError CheckedAddressingError.group
          pure input.derive.asGroupListPresence
        pure (GroupListPresenceTally.ofStates states)) := by
  rfl

/-- The legacy addressed context cannot manufacture descendant-derived group products; that missing checked-document boundary remains structural rather than semantic UNKNOWN. -/
@[simp] theorem resolvedGroupListOperand_starredGroupPresence_legacy
    (model : FlatModel)
    (source : CheckedStarredGroupPresenceSource model)
    (scalar : ValidationEvaluationContext) (outer : Env)
    (document : Document) (read : Env → FieldId → CheckedCell) :
    (ResolvedGroupListOperand.starredGroupPresence source).evalAddressedTally {
        scalar, outer, input := .legacy document read
      } = .error (.checkedDocumentRequired source.groupPath) := by
  rfl

/-- A group-list leaf requires the addressed evaluator exactly when one operand is starred or retains a nonempty repeatable scope already bound by the declaring rule. -/
@[simp]
theorem validationCondition_groupList_requiresAddressed
    (model : FlatModel) (operator : GroupFillQuantifier)
    (operands : List (ResolvedGroupListOperand model)) :
    (ValidationCondition.groupList (model := model)
      operator operands).requiresAddressedValidation =
        operands.any fun operand =>
          operand.isStarred || operand.iterationScope.isSome := by
  rfl

/-- Addressed group-list evaluation combines each direct classification and starred terminal contribution once, then delegates to the established tally table. -/
@[simp]
theorem validationCondition_groupList_evalAddressed
    (model : FlatModel) (operator : GroupFillQuantifier)
    (operands : List (ResolvedGroupListOperand model))
    (context : AddressedValidationEvaluationContext model) :
    (ValidationCondition.groupList (model := model)
        operator operands).evalAddressed context =
      (ResolvedGroupListOperands.evalAddressedTally context operands).map
        fun tally =>
          (operator.evalTally tally).asConservativeVerdict := by
  rfl

/-- A reached topology or document failure stays in the structural error channel and cannot become semantic UNKNOWN. -/
theorem validationCondition_groupList_addressing_failure
    (model : FlatModel) (operator : GroupFillQuantifier)
    (operands : List (ResolvedGroupListOperand model))
    (context : AddressedValidationEvaluationContext model)
    (cause : CheckedAddressingError)
    (fails : ResolvedGroupListOperands.evalAddressedTally
      context operands = .error cause) :
    (ValidationCondition.groupList (model := model)
      operator operands).evalAddressed context = .error cause := by
  rw [validationCondition_groupList_evalAddressed, fails]
  rfl

/-- A sole nonrepeatable terminal below starred ancestry has partial support exactly for the two quantifiers admitted on every sole starred group operand. -/
@[simp]
theorem validationConditionLeaf_starredGroupPresence_partialSupport
    (model : FlatModel) (operator : GroupFillQuantifier)
    (source : CheckedStarredGroupPresenceSource model) :
    (ValidationConditionLeaf.groupList operator
      [.starredGroupPresence source]).supportsAddressedPartial =
        operator.toStarredGroupFillQuantifier?.isSome := by
  rfl

/-- Partial evaluation selects the source's in-capacity ancestry environments, delegates each terminal to the caller's relevance-aware group-product resolver, and combines those classifications through the shared quantifier table. -/
theorem validationConditionLeaf_starredGroupPresence_partialDelegates
    (model : FlatModel) (operator : GroupFillQuantifier)
    (source : CheckedStarredGroupPresenceSource model)
    (context : AddressedValidationEvaluationContext model)
    (scope : ValidationRelevanceScope) (isRelevant : FlatRelevance)
    (resolveGroup :
      GroupPath → Env →
        Except CheckedAddressingError ResolvedGroupPresenceInput)
    (result? : Option RepetitionNotUniqueResult) :
    (ValidationConditionLeaf.groupList operator
      [.starredGroupPresence source]).evalAddressedPartial?
        context scope isRelevant resolveGroup result? =
      (match operator.toStarredGroupFillQuantifier? with
      | none => none
      | some _ =>
          some do
            let document := match context.input with
              | .legacy document _ => document
              | .checked checked | .partialView checked _ =>
                  checked.source.toDocument
            let environments ←
              (source.inCapacityEnvironments document context.outer)
                |>.mapError CheckedAddressingError.addressing
            let states ← environments.mapM fun environment => do
              let input ← resolveGroup source.groupPath environment
              pure input.derive.asGroupListPresence
            pure (operator.evalPresence states).asConservativeVerdict) := by
  rfl

/-- A group-list leaf exposes exactly the captured prefix of its checked starred operands as its ordinary rule-iteration scope. -/
@[simp]
theorem validationCondition_groupList_iterationScope
    (model : FlatModel) (operator : GroupFillQuantifier)
    (operands : List (ResolvedGroupListOperand model)) :
    (ValidationCondition.groupList (model := model)
      operator operands).ordinaryIterationScope =
        ValidationCondition.ResolvedGroupListOperands.iterationScope operands := by
  rfl

/-- The group-list leaf delegates its level-local static classification to the source-faithful positive/negative list rule. -/
@[simp]
theorem validationCondition_groupList_iterationGuardStatusAt
    (model : FlatModel) (operator : GroupFillQuantifier)
    (operands : List (ResolvedGroupListOperand model))
    (level : RepeatableLevel) :
    (ValidationCondition.groupList (model := model)
      operator operands).iterationGuardStatusAt level =
        ValidationCondition.ResolvedGroupListOperands.iterationGuardAt
          operator operands level := by
  rfl

/-- A negative starred group list is unguarded exactly at levels referenced by at least one captured operand prefix. -/
theorem resolvedGroupListOperands_noGroupFilled_unguarded_iff
    (operands : List (ResolvedGroupListOperand model))
    (level : RepeatableLevel) :
    ValidationCondition.ResolvedGroupListOperands.iterationGuardAt
        .noGroupFilled operands level = .unguarded ↔
      (operands.map fun operand =>
        match ResolvedGroupListOperand.iterationScope operand with
        | some scope => scope.contains level
        | none => false).any id = true := by
  let references := operands.map fun operand =>
    match ResolvedGroupListOperand.iterationScope operand with
    | some scope => scope.contains level
    | none => false
  change
    (if !references.any id then IterationGuardStatus.noReference
      else IterationGuardStatus.unguarded) =
        IterationGuardStatus.unguarded ↔
      references.any id = true
  cases references.any id <;> simp

/-- A positive starred group list guards exactly when some operand references the level and every operand does. -/
theorem resolvedGroupListOperands_atLeastOneGroupFilled_guarded_iff
    (operands : List (ResolvedGroupListOperand model))
    (level : RepeatableLevel) :
    ValidationCondition.ResolvedGroupListOperands.iterationGuardAt
        .atLeastOneGroupFilled operands level = .guarded ↔
      let references := operands.map fun operand =>
        match ResolvedGroupListOperand.iterationScope operand with
        | some scope => scope.contains level
        | none => false
      references.any id = true ∧ references.all id = true := by
  let references := operands.map fun operand =>
    match ResolvedGroupListOperand.iterationScope operand with
    | some scope => scope.contains level
    | none => false
  change
    (if !references.any id then IterationGuardStatus.noReference
      else if references.all id then IterationGuardStatus.guarded
      else IterationGuardStatus.unguarded) =
        IterationGuardStatus.guarded ↔
      references.any id = true ∧ references.all id = true
  cases references.any id <;>
    cases references.all id <;>
    simp

/-- Every checked group-list leaf can use the ordinary addressed evaluator; elaboration already excludes unsupported starred/operator combinations. -/
@[simp]
theorem validationCondition_groupList_supported
    (model : FlatModel) (operator : GroupFillQuantifier)
    (operands : List (ResolvedGroupListOperand model)) :
    (ValidationCondition.groupList (model := model)
      operator operands).supportsOrdinaryIteration = true := by
  rfl

end A12Kernel
