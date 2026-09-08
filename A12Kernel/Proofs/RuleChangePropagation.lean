import A12Kernel.Elaboration.RuleChangePropagation

/-! # Laws of the rule-change service

Four results carry the family. The two entry points refuse the same situation under two different
names, so the class identifies the surface and not the cause. They disagree about an old name the
model does not know — a silent no-op on one side and a refusal on the other — which is the one input
where running one and inferring the other is wrong. A rename alone is always propagated where a move
is refused, so the policy is about moves; and because a combined change counts as a move, the rename
half of a rename-and-move is lost with it. Finally, `unchanged` and `refused` both leave stale
references, which is what makes the middle outcome a trap rather than a success.
-/

namespace A12Kernel

/-- **One situation, two classes.** In an A12 model a move is refused by both entry points, and each
names itself, so a caller can tell which surface declined. -/
theorem propagation_move_refused_by_both (change : NameChange) (h : change.parentChanged = true) :
    conditionPropagation { change } = .refused .entityMoveInA12ModelCondition ∧
      errorTextPropagation { change } = .refused .entityMoveInA12ModelErrortext := by
  simp [conditionPropagation, errorTextPropagation, h]

/-- **The two entry points disagree on an unknown old name.** The condition side treats it as a
deliberate no-op; the error-text side never consults the container and refuses anyway. -/
theorem propagation_unknown_name_disagrees :
    conditionPropagation { oldNameKnown := false, change := { parentChanged := true } } =
        .unchanged ∧
      errorTextPropagation { change := { parentChanged := true } } =
        .refused .entityMoveInA12ModelErrortext :=
  ⟨rfl, rfl⟩

/-- **A rename alone is always propagated**, on both sides and in either model kind, which is what
makes the refusal a policy about moves rather than a limit on rewriting. -/
theorem propagation_rename_always_rewritten (hModel : Bool) :
    conditionPropagation { hModel, change := { shortNameChanged := true } } = .rewritten ∧
      errorTextPropagation { hModel, change := { shortNameChanged := true } } = .rewritten := by
  constructor <;> simp [conditionPropagation, errorTextPropagation]

/-- **Rename-and-move is not rename-then-move.** A change that alters both axes is a move, so in an
A12 model the rename half is refused along with it — where the same rename alone is propagated. -/
theorem propagation_combined_change_loses_the_rename :
    conditionPropagation { change := { parentChanged := true, shortNameChanged := true } } =
        .refused .entityMoveInA12ModelCondition ∧
      conditionPropagation { change := { shortNameChanged := true } } = .rewritten :=
  ⟨rfl, rfl⟩

/-- The condition side's parse gate precedes everything, so an unparseable condition reports no class
however the names changed. -/
theorem conditionPropagation_parse_first (request : ConditionRequest)
    (h : request.conditionParses = false) : conditionPropagation request = .abandoned := by
  simp [conditionPropagation, h]

/-- **The error-text side reads its condition only when a message needs it.** A rule with plain
messages is propagated over an unparseable condition, where the condition side would have abandoned —
a second place the two surfaces answer differently for one rule. -/
theorem errorTextPropagation_parses_only_for_parameters (hModel : Bool) :
    errorTextPropagation { hModel, conditionParses := false } = .rewritten ∧
      errorTextPropagation
        { hModel, messageUsesParameter := true, conditionParses := false } = .abandoned := by
  constructor <;> simp [errorTextPropagation]

/-- An invalid error text hides the move refusal, because the validity gate runs first. -/
theorem errorTextPropagation_validity_hides_refusal :
    errorTextPropagation { errorTextValid := false, change := { parentChanged := true } } =
      .abandoned :=
  rfl

/-- **The H-model field shortcut is the one honest `unchanged` on a move**: a field moved without
renaming needs no rewrite there, because H-model conditions name fields by short name. Moving a
*group* under the same flags is rewritten instead. -/
theorem conditionPropagation_hModel_field_shortcut :
    conditionPropagation
        { hModel := true, isField := true, change := { parentChanged := true } } = .unchanged ∧
      conditionPropagation { hModel := true, change := { parentChanged := true } } = .rewritten :=
  ⟨rfl, rfl⟩

/-- **Only a rewrite clears the stale references.** A refusal and an `unchanged` are alike in the
model they leave behind and differ only in whether anything was reported, which is why a consumer
must not read the silent outcome as success. -/
theorem leavesStaleReferences_iff_not_rewritten (outcome : PropagationOutcome) :
    outcome.leavesStaleReferences = true ↔ outcome ≠ .rewritten := by
  cases outcome <;> simp [PropagationOutcome.leavesStaleReferences]

/-- The identity change rewrites nothing and reports nothing. -/
theorem conditionPropagation_identity (request : ConditionRequest)
    (hparse : request.conditionParses = true) (hknown : request.oldNameKnown = true)
    (h : request.change.isIdentity = true) : conditionPropagation request = .unchanged := by
  simp only [NameChange.isIdentity, Bool.and_eq_true, Bool.not_eq_true'] at h
  simp [conditionPropagation, hparse, hknown, h.1, h.2]

end A12Kernel
