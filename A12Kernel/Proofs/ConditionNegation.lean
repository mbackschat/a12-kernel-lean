import A12Kernel.Semantics.ConditionNegation
import A12Kernel.Proofs.ConditionTree

/-! # Firing laws of De Morgan negation

Both laws are proved once over `ConditionTree.evalVerdict` with an arbitrary leaf evaluator, so every
leaf family inherits them from its own pair facts: **exclusivity** (a tree and its negation never
both fire) needs only that no leaf fires together with its complement, and **exhaustiveness** (one of
them fires) needs in addition that every leaf is *decided*, firing itself or through its complement.
Neither law mentions polarity, which a complement chooses independently, nor the empty-instance gate,
which a rule applies before its tree.
-/

namespace A12Kernel

namespace Verdict

@[simp] theorem fires_conj (left right : Verdict) :
    (Verdict.conj left right).fires = (left.fires && right.fires) := by
  cases left <;> cases right
  all_goals first | rfl | (rename_i a b; cases a <;> cases b <;> rfl) | (rename_i a; cases a <;> rfl)

@[simp] theorem fires_disj (left right : Verdict) :
    (Verdict.disj left right).fires = (left.fires || right.fires) := by
  cases left <;> cases right
  all_goals first | rfl | (rename_i a b; cases a <;> cases b <;> rfl) | (rename_i a; cases a <;> rfl)

end Verdict

namespace ConditionTree

theorem fires_evalVerdict_and (evalLeaf : Leaf → Verdict) (left right : ConditionTree Leaf) :
    ((ConditionTree.and left right).evalVerdict evalLeaf).fires =
      ((left.evalVerdict evalLeaf).fires && (right.evalVerdict evalLeaf).fires) := by
  rw [evalVerdict_and_eq_conj, Verdict.fires_conj]

theorem fires_evalVerdict_or (evalLeaf : Leaf → Verdict) (left right : ConditionTree Leaf) :
    ((ConditionTree.or left right).evalVerdict evalLeaf).fires =
      ((left.evalVerdict evalLeaf).fires || (right.evalVerdict evalLeaf).fires) := by
  rw [evalVerdict_or_eq_disj, Verdict.fires_disj]

/-- A tree and its negation never both fire when none of its leaves fires together with its
complement. -/
theorem negate_exclusive (evalLeaf : Leaf → Verdict) (complement : Leaf → ConditionTree Leaf) :
    ∀ tree : ConditionTree Leaf,
      tree.allLeaves (fun value =>
        !((evalLeaf value).fires && ((complement value).evalVerdict evalLeaf).fires)) →
      !((tree.evalVerdict evalLeaf).fires && ((tree.negate complement).evalVerdict evalLeaf).fires)
  | .leaf value => by simp [allLeaves, negate]
  | .and left right => by
      intro pair
      simp only [allLeaves, Bool.and_eq_true] at pair
      have hl := negate_exclusive evalLeaf complement left pair.1
      have hr := negate_exclusive evalLeaf complement right pair.2
      simp only [negate, fires_evalVerdict_and, fires_evalVerdict_or] at *
      generalize (left.evalVerdict evalLeaf).fires = a at *
      generalize ((left.negate complement).evalVerdict evalLeaf).fires = b at *
      generalize (right.evalVerdict evalLeaf).fires = c at *
      generalize ((right.negate complement).evalVerdict evalLeaf).fires = d at *
      cases a <;> cases b <;> cases c <;> cases d <;> simp_all
  | .or left right => by
      intro pair
      simp only [allLeaves, Bool.and_eq_true] at pair
      have hl := negate_exclusive evalLeaf complement left pair.1
      have hr := negate_exclusive evalLeaf complement right pair.2
      simp only [negate, fires_evalVerdict_and, fires_evalVerdict_or] at *
      generalize (left.evalVerdict evalLeaf).fires = a at *
      generalize ((left.negate complement).evalVerdict evalLeaf).fires = b at *
      generalize (right.evalVerdict evalLeaf).fires = c at *
      generalize ((right.negate complement).evalVerdict evalLeaf).fires = d at *
      cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/-- Where every leaf is decided, a tree or its negation fires. -/
theorem negate_exhaustive (evalLeaf : Leaf → Verdict) (complement : Leaf → ConditionTree Leaf) :
    ∀ tree : ConditionTree Leaf,
      tree.allLeaves (fun value =>
        (evalLeaf value).fires || ((complement value).evalVerdict evalLeaf).fires) →
      ((tree.evalVerdict evalLeaf).fires || ((tree.negate complement).evalVerdict evalLeaf).fires)
  | .leaf value => by simp [allLeaves, negate]
  | .and left right => by
      intro decided
      simp only [allLeaves, Bool.and_eq_true] at decided
      have hl := negate_exhaustive evalLeaf complement left decided.1
      have hr := negate_exhaustive evalLeaf complement right decided.2
      simp only [negate, fires_evalVerdict_and, fires_evalVerdict_or] at *
      generalize (left.evalVerdict evalLeaf).fires = a at *
      generalize ((left.negate complement).evalVerdict evalLeaf).fires = b at *
      generalize (right.evalVerdict evalLeaf).fires = c at *
      generalize ((right.negate complement).evalVerdict evalLeaf).fires = d at *
      cases a <;> cases b <;> cases c <;> cases d <;> simp_all
  | .or left right => by
      intro decided
      simp only [allLeaves, Bool.and_eq_true] at decided
      have hl := negate_exhaustive evalLeaf complement left decided.1
      have hr := negate_exhaustive evalLeaf complement right decided.2
      simp only [negate, fires_evalVerdict_and, fires_evalVerdict_or] at *
      generalize (left.evalVerdict evalLeaf).fires = a at *
      generalize ((left.negate complement).evalVerdict evalLeaf).fires = b at *
      generalize (right.evalVerdict evalLeaf).fires = c at *
      generalize ((right.negate complement).evalVerdict evalLeaf).fires = d at *
      cases a <;> cases b <;> cases c <;> cases d <;> simp_all

end ConditionTree

end A12Kernel
