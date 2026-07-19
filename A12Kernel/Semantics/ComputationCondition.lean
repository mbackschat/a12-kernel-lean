import A12Kernel.Document
import A12Kernel.Semantics.Observation

/-! # A12Kernel.Semantics.ComputationCondition — checked ordered computation conditions

This capsule admits direct, already-resolved field presence plus ordered `And`/`Or` for one non-repeatable computation instance. It separates clean not-true from an invalid cell actually read as poison. Comparisons, quantifiers, paths, and alternatives remain separate later clauses.
-/

namespace A12Kernel

/-- Pure checked-cell reads shared by the first scalar computation fragments. Model and path checking remain outside this context. -/
structure ScalarComputationContext where
  read : FieldId → CheckedCell

/-- A computation-specific condition result. Unlike validation `Verdict`, it carries no message polarity; `notTrue` is the clean non-holding result of the admitted clauses, while poison from a field actually read remains explicit. -/
inductive ComputationConditionResult where
  | holds
  | notTrue
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

/-- The parser-independent computation-condition fragment: direct presence and ordered binary connectives over resolved fields. -/
inductive ComputationCondition where
  | fieldFilled (field : FieldId)
  | fieldNotFilled (field : FieldId)
  | and (left right : ComputationCondition)
  | or (left right : ComputationCondition)
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

/-- Evaluate a computation condition left-to-right. `And` stops on clean not-true, `Or` stops on clean holds, and a poison already read aborts without consulting the remaining operand. -/
def eval (condition : ComputationCondition)
    (context : ScalarComputationContext) : ComputationConditionResult :=
  match condition with
  | .fieldFilled field => evalFieldFilled context field
  | .fieldNotFilled field =>
      match evalFieldFilled context field with
      | .holds => .notTrue
      | .notTrue => .holds
      | .poison cause => .poison cause
  | .and left right =>
      match left.eval context with
      | .holds => right.eval context
      | .notTrue => .notTrue
      | .poison cause => .poison cause
  | .or left right =>
      match left.eval context with
      | .holds => .holds
      | .notTrue => right.eval context
      | .poison cause => .poison cause

end ComputationCondition

end A12Kernel
