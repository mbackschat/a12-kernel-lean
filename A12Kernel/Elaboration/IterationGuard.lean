import A12Kernel.Semantics.Condition

/-! # Structural iteration guards

Static admission combines per-leaf reference and guard classifications through the authored condition tree. `IterationNotValidVisitor.visit(ICompositeCondition)` requires one guarding conjunct and a guard in every disjunct, independently at each iteration level.
-/

namespace A12Kernel

/-- Static contribution of one checked condition subtree at one repeatable level. `unclassified` means the subtree references that level but its operator-specific guard rule has not yet been established. -/
inductive IterationGuardStatus where
  | noReference
  | unguarded
  | guarded
  | unclassified
  deriving Repr, DecidableEq

namespace IterationGuardStatus

/-- An `And` is guarded when either referenced conjunct supplies a known guard. An unclassified referenced conjunct matters only when no sibling already guards the level. -/
def and : IterationGuardStatus → IterationGuardStatus → IterationGuardStatus
  | .guarded, _ | _, .guarded => .guarded
  | .unclassified, _ | _, .unclassified => .unclassified
  | .unguarded, _ | _, .unguarded => .unguarded
  | .noReference, .noReference => .noReference

/-- Every `Or` branch must reference and guard the level. A missing or known-unguarded branch decides failure; an unclassified branch remains explicit only when every other branch is guarded. -/
def or : IterationGuardStatus → IterationGuardStatus → IterationGuardStatus
  | .guarded, .guarded => .guarded
  | .unclassified, .guarded
  | .guarded, .unclassified
  | .unclassified, .unclassified => .unclassified
  | .noReference, .noReference => .noReference
  | _, _ => .unguarded

end IterationGuardStatus

namespace ConditionTree

/-- Fold per-leaf static iteration guards through the kernel's level-local `And`/`Or` admission algebra. -/
def iterationGuardStatus (classify : Leaf → IterationGuardStatus) :
    ConditionTree Leaf → IterationGuardStatus
  | .leaf value => classify value
  | .and left right =>
      IterationGuardStatus.and
        (left.iterationGuardStatus classify)
        (right.iterationGuardStatus classify)
  | .or left right =>
      IterationGuardStatus.or
        (left.iterationGuardStatus classify)
        (right.iterationGuardStatus classify)

/-- Specialize the structural fold when every leaf's reference-and-guard classification is settled. -/
def iterationGuarded (classify : Leaf → Bool) (condition : ConditionTree Leaf) : Bool :=
  decide (condition.iterationGuardStatus
    (fun value => if classify value then .guarded else .unguarded) = .guarded)

end ConditionTree

end A12Kernel
