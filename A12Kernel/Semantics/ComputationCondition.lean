import A12Kernel.Document
import A12Kernel.Semantics.Observation

/-! # A12Kernel.Semantics.ComputationCondition — checked computation control

This capsule admits direct, already-resolved field presence, ordered `And`/`Or`, and first-match alternative selection for one non-repeatable computation instance. It separates clean not-true and no-match from an invalid cell actually read as poison. Comparison and quantifier leaves, checked paths, operation evaluation, and model-level alternative legality remain separate clauses.
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

/-- One ordered computation alternative whose precondition selects an operation payload. The payload remains unevaluated during selection. -/
structure ComputationAlternative (Operation : Type) where
  precondition : ComputationCondition
  operation : Operation
  deriving Repr, DecidableEq

/-- Result of scanning computation alternatives in declaration order. No-match is clean absence; poison records the first invalid read reached before any selection. -/
inductive ComputationAlternativeSelection (Operation : Type) where
  | noMatch
  | selected (operation : Operation)
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

namespace ComputationAlternative

/-- Select the first alternative whose precondition holds. Clean non-matches continue, while poison aborts without examining the remaining alternatives. -/
def selectFirst (alternatives : List (ComputationAlternative Operation))
    (context : ScalarComputationContext) :
    ComputationAlternativeSelection Operation :=
  match alternatives with
  | [] => .noMatch
  | alternative :: remaining =>
      match alternative.precondition.eval context with
      | .holds => .selected alternative.operation
      | .notTrue => selectFirst remaining context
      | .poison cause => .poison cause

end ComputationAlternative

end A12Kernel
