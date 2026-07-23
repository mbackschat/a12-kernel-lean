import A12Kernel.Cell

/-! # Shared condition-tree structure

The generic tree owns validation connective shape, verdict-aware short-circuit evaluation, and structurally identical Boolean eligibility folds. Leaf families retain their own evaluation and metadata rules.
-/

namespace A12Kernel

/-- Computation conditions retain clean non-holding separately from the first formally invalid read. -/
inductive ComputationConditionResult where
  | holds
  | notTrue
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

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

/-- Evaluate the same verdict algebra while preserving a caller-owned structural failure channel. Decisive left branches retain the exact ordinary short-circuit boundary and therefore do not sample an unreachable effectful leaf. -/
def evalVerdictExcept (evalLeaf : Leaf → Except Error Verdict) :
    ConditionTree Leaf → Except Error Verdict
  | .leaf value => evalLeaf value
  | .and left right => do
      let leftVerdict ← left.evalVerdictExcept evalLeaf
      match leftVerdict with
      | .notFired => pure .notFired
      | _ =>
          pure (Verdict.conj leftVerdict
            (← right.evalVerdictExcept evalLeaf))
  | .or left right => do
      let leftVerdict ← left.evalVerdictExcept evalLeaf
      match leftVerdict with
      | .fired .value => pure (.fired .value)
      | _ =>
          pure (Verdict.disj leftVerdict
            (← right.evalVerdictExcept evalLeaf))

/-- Evaluate leaves under the shared strong-Kleene connective algebra. This is the filter counterpart of `evalVerdict`; leaf families still own their observation and comparison rules. -/
@[simp] def evalK (evalLeaf : Leaf → K) : ConditionTree Leaf → K
  | .leaf value => evalLeaf value
  | .and left right => K.and (left.evalK evalLeaf) (right.evalK evalLeaf)
  | .or left right => K.or (left.evalK evalLeaf) (right.evalK evalLeaf)

/-- Evaluate the same strong-Kleene algebra while preserving a caller-owned structural failure channel. Both branches remain observable because neither strong-Kleene truth value alone makes the other branch structurally unreachable. -/
def evalKExcept (evalLeaf : Leaf → Except Error K) :
    ConditionTree Leaf → Except Error K
  | .leaf value => evalLeaf value
  | .and left right => do
      pure (K.and (← left.evalKExcept evalLeaf)
        (← right.evalKExcept evalLeaf))
  | .or left right => do
      pure (K.or (← left.evalKExcept evalLeaf)
        (← right.evalKExcept evalLeaf))

/-- Evaluate computation leaves left-to-right. Clean false decides `And`, clean true decides `Or`, and the first reached poison aborts either connective. -/
@[simp] def evalComputation
    (evalLeaf : Leaf → ComputationConditionResult) :
    ConditionTree Leaf → ComputationConditionResult
  | .leaf value => evalLeaf value
  | .and left right =>
      match left.evalComputation evalLeaf with
      | .holds => right.evalComputation evalLeaf
      | .notTrue => .notTrue
      | .poison cause => .poison cause
  | .or left right =>
      match left.evalComputation evalLeaf with
      | .holds => .holds
      | .notTrue => right.evalComputation evalLeaf
      | .poison cause => .poison cause

/-- Evaluate the computation connective algebra while preserving a caller-owned structural failure channel. Decisive clean branches retain the ordinary short-circuit boundary and hide an unreachable effectful leaf. -/
def evalComputationExcept
    (evalLeaf : Leaf → Except Error ComputationConditionResult) :
    ConditionTree Leaf → Except Error ComputationConditionResult
  | .leaf value => evalLeaf value
  | .and left right => do
      match ← left.evalComputationExcept evalLeaf with
      | .holds => right.evalComputationExcept evalLeaf
      | .notTrue => pure .notTrue
      | .poison cause => pure (.poison cause)
  | .or left right => do
      match ← left.evalComputationExcept evalLeaf with
      | .holds => pure .holds
      | .notTrue => right.evalComputationExcept evalLeaf
      | .poison cause => pure (.poison cause)

end ConditionTree

end A12Kernel
