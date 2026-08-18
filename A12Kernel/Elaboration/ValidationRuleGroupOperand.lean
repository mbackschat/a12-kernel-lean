import A12Kernel.Elaboration.ValidationRule

/-! # Rule-owned static admission for one-level unstarred repeatable group uses

Condition-level elaborators cannot decide this boundary because the deciding input is the error
field's locus. This module projects only the exact static matrix measured at one repeatable level.
It deliberately constructs no executable condition for newly admitted group-list or count shapes.
The projection assumes the enclosing rule independently satisfies the ordinary error-field
reference gate; it does not claim whole-rule diagnostic precedence outside the measured matrix.
-/

namespace A12Kernel

/-- A three-way result keeps an unmeasured shape distinct from both admission and a measured diagnostic. -/
inductive RuleGroupOperandStaticAdmission where
  | admitted
  | rejected (diagnostic : KernelStaticDiagnostic)
  | unmapped
  deriving Repr, DecidableEq

/-- The only two error-field loci measured for this one-level profile. -/
inductive OneLevelGroupErrorLocus where
  | outside
  | inside
  deriving Repr, DecidableEq

/-- The exact positive-presence and greater-than-zero count shapes in the maintained matrix. Authored order is part of the paired shapes. -/
inductive OneLevelUnstarredGroupUse where
  | groupFilled
  | atLeastOneSole
  | allThenFixed
  | filledGroupCountSole
  | filledGroupCountThenFixed
  deriving Repr, DecidableEq

namespace OneLevelUnstarredGroupUse

/-- The measured decision table after model-relative shape and error-locus checking. -/
def admission (locus : OneLevelGroupErrorLocus) :
    OneLevelUnstarredGroupUse → RuleGroupOperandStaticAdmission
  | use =>
      match locus, use with
      | .outside, _ => .rejected .noWildcard
      | .inside, .groupFilled
      | .inside, .atLeastOneSole
      | .inside, .allThenFixed => .admitted
      | .inside, .filledGroupCountSole =>
          .rejected .paramSizeInvalidGN
      | .inside, .filledGroupCountThenFixed =>
          .rejected .negativeConditionInIteration

end OneLevelUnstarredGroupUse

private structure OneLevelUnstarredGroupBinding where
  reference : ResolvedGroupReference
  locus : OneLevelGroupErrorLocus

/-- Resolve only the measured one-level ordinary-path profile. Nested scope, `RuleGroup`, a different repeated branch, or an invalid model remains unmapped. -/
private def resolveOneLevelUnstarredGroupBinding?
    (model : FlatModel) (declaringGroup : GroupPath)
    (errorField : FieldId) (surface : SurfaceGroupReference) :
    Option OneLevelUnstarredGroupBinding := do
  match model.validate with
  | .error _ => none
  | .ok () =>
    let reference ← (surface.resolveAgainst declaringGroup).toOption
    match reference.origin with
    | .ruleGroup => none
    | .path =>
      if !model.hasGroupPath reference.path then none
      else
        match model.repeatableScopeForGroupPath reference.path with
        | [level] =>
          let declaration ← (model.lookupUniqueId errorField).toOption
          if reference.path.isPrefixOf declaration.groupPath &&
              declaration.repeatableScope == [level] then
            some { reference, locus := .inside }
          else if declaration.repeatableScope.isEmpty then
            some { reference, locus := .outside }
          else
            none
        | _ => none

private def hasDisjointFixedPeer
    (model : FlatModel) (declaringGroup : GroupPath)
    (binding : OneLevelUnstarredGroupBinding)
    (surface : SurfaceGroupReference) : Bool :=
  match model.resolveFixedGroupReference declaringGroup surface with
  | .error _ => false
  | .ok peer =>
      match peer.origin with
      | .ruleGroup => false
      | .path => !peer.isRoot && !binding.reference.overlaps peer

private def projectOneLevelUse
    (model : FlatModel) (declaringGroup : GroupPath)
    (errorField : FieldId) (surface : SurfaceGroupReference)
    (use : OneLevelUnstarredGroupUse) :
    RuleGroupOperandStaticAdmission :=
  match resolveOneLevelUnstarredGroupBinding?
      model declaringGroup errorField surface with
  | none => .unmapped
  | some binding => use.admission binding.locus

/-- Project the exact scalar `GroupFilled(repeatable)` control. Runtime evaluation remains owned by the existing group-presence condition. -/
def projectGroupFilledRuleAdmission
    (model : FlatModel) (declaringGroup : GroupPath)
    (errorField : FieldId) (group : SurfaceGroupReference) :
    RuleGroupOperandStaticAdmission :=
  projectOneLevelUse model declaringGroup errorField group .groupFilled

/-- Project the two measured positive group-list shapes: sole `AtLeastOneGroupFilled(repeatable)` and `AllGroupsFilled(repeatable, fixed)`. Every other carrier, arity, operand class, or authored order remains unmapped here. -/
def projectGroupListRuleAdmission
    (model : FlatModel) (declaringGroup : GroupPath)
    (errorField : FieldId) (operator : GroupFillQuantifier)
    (operands : List SurfaceGroupListOperand) :
    RuleGroupOperandStaticAdmission :=
  match operator, operands with
  | .atLeastOneGroupFilled, [.group repeatable] =>
      projectOneLevelUse model declaringGroup errorField repeatable
        .atLeastOneSole
  | .allGroupsFilled, [.group repeatable, .group fixed] =>
      match resolveOneLevelUnstarredGroupBinding?
          model declaringGroup errorField repeatable with
      | some binding =>
          if hasDisjointFixedPeer model declaringGroup binding fixed then
            OneLevelUnstarredGroupUse.allThenFixed.admission binding.locus
          else
            .unmapped
      | none => .unmapped
  | _, _ => .unmapped

/-- Project the exact `NumberOfFilledGroups(...) > 0` sole and authored repeatable-then-fixed shapes. No numeric evaluator or comparison form is inferred from this static result. -/
def projectFilledGroupCountGreaterZeroRuleAdmission
    (model : FlatModel) (declaringGroup : GroupPath)
    (errorField : FieldId) (groups : List SurfaceGroupReference) :
    RuleGroupOperandStaticAdmission :=
  match groups with
  | [repeatable] =>
      projectOneLevelUse model declaringGroup errorField repeatable
        .filledGroupCountSole
  | [repeatable, fixed] =>
      match resolveOneLevelUnstarredGroupBinding?
          model declaringGroup errorField repeatable with
      | some binding =>
          if hasDisjointFixedPeer model declaringGroup binding fixed then
            OneLevelUnstarredGroupUse.filledGroupCountThenFixed.admission
              binding.locus
          else
            .unmapped
      | none => .unmapped
  | _ => .unmapped

end A12Kernel
