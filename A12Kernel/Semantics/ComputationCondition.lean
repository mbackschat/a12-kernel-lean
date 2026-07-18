import A12Kernel.Document
import A12Kernel.Semantics.Observation

/-! # A12Kernel.Semantics.ComputationCondition — checked computation-presence decisions

This capsule admits direct, already-resolved field presence for one non-repeatable computation instance. It separates clean not-true from an invalid cell actually read as poison. Connectives, comparisons, quantifiers, paths, and alternatives remain separate later clauses.
-/

namespace A12Kernel

/-- Pure checked-cell reads shared by the first scalar computation fragments. Model and path checking remain outside this context. -/
structure ScalarComputationContext where
  read : FieldId → CheckedCell

/-- A computation-specific condition result. Unlike validation `Verdict`, it carries no message polarity; unlike `Bool`, it preserves poison from a field actually read. -/
inductive ComputationConditionResult where
  | holds
  | notTrue
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

/-- The first parser-independent computation-condition fragment: direct presence over one resolved field. -/
inductive ComputationCondition where
  | fieldFilled (field : FieldId)
  | fieldNotFilled (field : FieldId)
  deriving Repr, DecidableEq

namespace ComputationCondition

/-- Evaluate `FieldFilled` for one resolved checked field. A clean value counts as filled regardless of its scalar value; ordinary formal invalidity is poison rather than filled or empty. -/
def evalFieldFilled (context : ScalarComputationContext)
    (field : FieldId) : ComputationConditionResult :=
  match observeCell .computation (context.read field) with
  | .empty => .notTrue
  | .value _ => .holds
  | .unknown cause => .poison cause
  | .poison cause => .poison cause

/-- Evaluate direct presence at the computation observation boundary. `FieldNotFilled` reverses only clean truth; poison is preserved rather than Boolean-negated. -/
def eval (condition : ComputationCondition)
    (context : ScalarComputationContext) : ComputationConditionResult :=
  match condition with
  | .fieldFilled field => evalFieldFilled context field
  | .fieldNotFilled field =>
      match evalFieldFilled context field with
      | .holds => .notTrue
      | .notTrue => .holds
      | .poison cause => .poison cause

end ComputationCondition

end A12Kernel
