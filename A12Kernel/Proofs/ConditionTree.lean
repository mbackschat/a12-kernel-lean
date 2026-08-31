import A12Kernel.Proofs.Verdict
import A12Kernel.Semantics.Condition

/-! # A12Kernel.Proofs.ConditionTree — what the shared connective tree does and does not preserve

Two results about `ConditionTree.evalVerdict`. The first is that its short-circuit is a
pure optimization: the tree's outcome is the plain `conj`/`disj` fold of its subtrees, so
no law about the algebra has to be restated against the skipping branches. The second uses
that to state how far an UNKNOWN leaf reaches — nowhere, as long as only the boundary
between `unknown` and `notFired` is at stake.

The claim boundary matters. These are results about the **verdict** a tree evaluates to.
Anything a consumer projects from an individual leaf's own verdict rather than from the
tree's outcome is outside them.
-/

namespace A12Kernel
namespace ConditionTree

/-- `And` short-circuits on `notFired` only, and `conj` maps `notFired` to `notFired` on
    either side, so skipping the right subtree changes nothing. -/
theorem evalVerdict_and_eq_conj {Leaf : Type} (evalLeaf : Leaf → Verdict)
    (left right : ConditionTree Leaf) :
    (ConditionTree.and left right).evalVerdict evalLeaf =
      Verdict.conj (left.evalVerdict evalLeaf) (right.evalVerdict evalLeaf) := by
  simp only [evalVerdict]
  cases left.evalVerdict evalLeaf <;> rfl

/-- The same for `Or`, whose skip is on `fired value`. -/
theorem evalVerdict_or_eq_disj {Leaf : Type} (evalLeaf : Leaf → Verdict)
    (left right : ConditionTree Leaf) :
    (ConditionTree.or left right).evalVerdict evalLeaf =
      Verdict.disj (left.evalVerdict evalLeaf) (right.evalVerdict evalLeaf) := by
  simp only [evalVerdict]
  cases leftVerdict : left.evalVerdict evalLeaf with
  | fired polarity => cases polarity <;> rfl
  | _ => rfl

/-- **An UNKNOWN leaf is invisible at the root, up to the boundary it sits on.** Collapsing
    every leaf's `unknown` to `notFired` collapses the tree's outcome the same way, at any
    depth and under any mixture of connectives.

    The consequence is the one worth stating: two accounts of a leaf that disagree *only*
    about whether it answers `unknown` or `notFired` produce rule outcomes that disagree
    only there too. Since a rule emits a message exactly when its outcome is `fired`, and
    `collapseUnknown` fixes every fired verdict, no document can separate such accounts
    through the message channel. That is a fact about this theory's evaluator, not a
    measurement of the Kernel; it is what makes such a choice unfalsifiable rather than
    merely unmeasured. -/
theorem evalVerdict_collapseUnknown {Leaf : Type} (evalLeaf : Leaf → Verdict)
    (tree : ConditionTree Leaf) :
    (tree.evalVerdict evalLeaf).collapseUnknown =
      tree.evalVerdict (fun leaf => (evalLeaf leaf).collapseUnknown) := by
  induction tree with
  | leaf _ => rfl
  | and left right leftIH rightIH =>
      rw [evalVerdict_and_eq_conj, evalVerdict_and_eq_conj,
        Verdict.conj_collapseUnknown, leftIH, rightIH]
  | or left right leftIH rightIH =>
      rw [evalVerdict_or_eq_disj, evalVerdict_or_eq_disj,
        Verdict.disj_collapseUnknown, leftIH, rightIH]

end ConditionTree

/-! ## Checked non-law

The law is a statement about outcomes *after* collapsing, not an invariance of the raw
outcome. Collapsing the leaves of this tree moves its verdict, which is why the law has to
carry `collapseUnknown` on both sides; reading it as "an unknown leaf never changes the
result" would be the false generalization.
-/

example :
    let tree : ConditionTree Verdict := .or (.leaf .unknown) (.leaf .notFired)
    (tree.evalVerdict id, tree.evalVerdict (fun leaf => leaf.collapseUnknown)) =
      (.unknown, .notFired) := by
  decide

end A12Kernel
