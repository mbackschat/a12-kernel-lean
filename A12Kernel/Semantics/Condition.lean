import A12Kernel.Core

/-! # Shared condition-tree structure

The generic tree owns validation connective shape, verdict-aware short-circuit evaluation, and structurally identical Boolean eligibility folds. Leaf families retain their own evaluation and metadata rules.
-/

namespace A12Kernel

/-- A connective tree shared by resolved validation leaf families. -/
inductive ConditionTree (Leaf : Type) where
  | leaf (value : Leaf)
  | and (left right : ConditionTree Leaf)
  | or (left right : ConditionTree Leaf)
  deriving Repr, DecidableEq

namespace ConditionTree

/-- Change only the leaf representation while preserving connective shape and order. -/
def map (transform : Source → Target) : ConditionTree Source → ConditionTree Target
  | .leaf value => .leaf (transform value)
  | .and left right => .and (left.map transform) (right.map transform)
  | .or left right => .or (left.map transform) (right.map transform)

/-- Whether any leaf satisfies a predicate. Connective structure does not affect reference membership. -/
def anyLeaf (predicate : Leaf → Bool) : ConditionTree Leaf → Bool
  | .leaf value => predicate value
  | .and left right | .or left right =>
      left.anyLeaf predicate || right.anyLeaf predicate

/-- Whether every leaf satisfies a predicate. Connective shape does not weaken static admission. -/
def allLeaves (predicate : Leaf → Bool) : ConditionTree Leaf → Bool
  | .leaf value => predicate value
  | .and left right | .or left right =>
      left.allLeaves predicate && right.allLeaves predicate

/-- Fold Boolean leaf properties through the tree's `And`/`Or` structure. -/
@[simp] def evalBool (evalLeaf : Leaf → Bool) : ConditionTree Leaf → Bool
  | .leaf value => evalLeaf value
  | .and left right => left.evalBool evalLeaf && right.evalBool evalLeaf
  | .or left right => left.evalBool evalLeaf || right.evalBool evalLeaf

/-- Evaluate leaves under the shared A12 connective algebra. `And` skips only after `notFired`; `Or` skips only after `fired value`, because every other verdict can still change through polarity composition. -/
@[simp] def evalVerdict (evalLeaf : Leaf → Verdict) : ConditionTree Leaf → Verdict
  | .leaf value => evalLeaf value
  | .and left right =>
      let leftVerdict := left.evalVerdict evalLeaf
      match leftVerdict with
      | .notFired => .notFired
      | _ => Verdict.conj leftVerdict (right.evalVerdict evalLeaf)
  | .or left right =>
      let leftVerdict := left.evalVerdict evalLeaf
      match leftVerdict with
      | .fired .value => .fired .value
      | _ => Verdict.disj leftVerdict (right.evalVerdict evalLeaf)

end ConditionTree

end A12Kernel
