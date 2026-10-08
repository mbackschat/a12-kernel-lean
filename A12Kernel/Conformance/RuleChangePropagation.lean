import A12Kernel.Elaboration.RuleChangePropagation

/-! # Locks on the rule-change service

Source-derived; neither class has a witness, because the one tool that performs this propagation
reaches the model through its own editor rather than through this service
([checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-rule-change-propagation)). The matrix separates the two
surfaces against each other, the four name-change combinations, each surface's own staging, and the
three outcomes.
-/

namespace A12Kernel.Conformance.RuleChangePropagation

open A12Kernel

private def moved : NameChange := { parentChanged := true }
private def renamed : NameChange := { shortNameChanged := true }
private def movedAndRenamed : NameChange := { parentChanged := true, shortNameChanged := true }
private def identity : NameChange := {}

private def conditionKey? (request : ConditionRequest) : Option String :=
  (conditionPropagation request).diagnostic?.map KernelStaticDiagnostic.kernelCode

private def errorTextKey? (request : ErrorTextRequest) : Option String :=
  (errorTextPropagation request).diagnostic?.map KernelStaticDiagnostic.kernelCode

/- **One situation, two class names.** The identical A12 move refused on each surface, with the
   matching H-model rows showing the refusal is the model kind's and not the move's alone. -/
example :
    conditionKey? { change := moved } = some "MVK_ENTITY_MOVE_IN_A12_MODEL_CONDITION" ∧
      errorTextKey? { change := moved } = some "MVK_ENTITY_MOVE_IN_A12_MODEL_ERRORTEXT" ∧
      conditionKey? { hModel := true, change := moved } = none ∧
      errorTextKey? { hModel := true, change := moved } = none := by
  native_decide

/- **All four name changes on the condition side.** Only the two carrying a parent change refuse, so
   the axis is the move; and the combined change refuses exactly as the bare move does, losing the
   rename the middle row would have propagated. -/
example :
    conditionPropagation { change := identity } = .unchanged ∧
      conditionPropagation { change := renamed } = .rewritten ∧
      conditionPropagation { change := moved } =
        .refused .entityMoveInA12ModelCondition ∧
      conditionPropagation { change := movedAndRenamed } =
        .refused .entityMoveInA12ModelCondition := by
  native_decide

/- **The two surfaces disagree on an old name the model does not know.** One request, two answers —
   the condition side is silent and the error-text side refuses, because only one of them consults
   the entity container. -/
example :
    conditionPropagation { oldNameKnown := false, change := moved } = .unchanged ∧
      errorTextPropagation { change := moved } =
        .refused .entityMoveInA12ModelErrortext ∧
      conditionPropagation { oldNameKnown := false, change := renamed } = .unchanged := by
  native_decide

/- **Each surface's own staging hides the refusal differently.** The condition side always parses
   first; the error-text side parses only for a parameterised message but always validates, so the
   same unparseable condition abandons one surface and is rewritten by the other. -/
example :
    conditionPropagation { conditionParses := false, change := moved } = .abandoned ∧
      errorTextPropagation { conditionParses := false, change := renamed } = .rewritten ∧
      errorTextPropagation
        { messageUsesParameter := true, conditionParses := false, change := renamed } =
        .abandoned ∧
      errorTextPropagation { errorTextValid := false, change := moved } = .abandoned := by
  native_decide

/- **The H-model field shortcut, and its group counterpart.** One flag apart: a moved un-renamed
   field needs no rewrite because H-model conditions name fields by short name, while the same move
   of a group is rewritten. Renaming the field as well puts it back on the rewrite path. -/
example :
    conditionPropagation { hModel := true, isField := true, change := moved } = .unchanged ∧
      conditionPropagation { hModel := true, isField := false, change := moved } = .rewritten ∧
      conditionPropagation { hModel := true, isField := true, change := movedAndRenamed } =
        .rewritten := by
  native_decide

/- **Three outcomes, and two of them leave the model stale.** The projection a refactoring consumer
   reads collapses refusal and no-op, which is exactly why the silent one must not be read as
   success. -/
example :
    PropagationOutcome.leavesStaleReferences .rewritten = false ∧
      PropagationOutcome.leavesStaleReferences .unchanged = true ∧
      PropagationOutcome.leavesStaleReferences
        (.refused .entityMoveInA12ModelCondition) = true ∧
      PropagationOutcome.leavesStaleReferences .abandoned = true := by
  native_decide

end A12Kernel.Conformance.RuleChangePropagation
