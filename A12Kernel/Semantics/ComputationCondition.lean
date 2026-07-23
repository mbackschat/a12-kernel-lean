import A12Kernel.Document
import A12Kernel.Semantics.Condition
import A12Kernel.Semantics.Observation

/-! # A12Kernel.Semantics.ComputationCondition — checked computation control

This capsule admits direct, already-resolved field presence, ordered `And`/`Or`, optional common-precondition expansion over guarded alternatives, and first-match selection for one non-repeatable computation instance. It separates clean not-true and no-match from an invalid cell actually read as poison. Comparison and quantifier leaves, checked paths, operation evaluation, and model-level alternative legality remain separate clauses.
-/

namespace A12Kernel

/-- Pure checked-cell reads shared by the first scalar computation fragments. Model and path checking remain outside this context. -/
structure ScalarComputationContext where
  read : FieldId → CheckedCell

/-- Atomic leaves of the parser-independent computation-condition fragment. -/
inductive ComputationConditionLeaf where
  | fieldFilled (field : FieldId)
  | fieldNotFilled (field : FieldId)
  deriving Repr, DecidableEq

/-- Computation control reuses the common checked connective tree; only its phase-specific leaves and result projection differ from validation. -/
abbrev ComputationCondition := ConditionTree ComputationConditionLeaf

namespace CellObservation

/-- Consume one computation-phase observation as `FieldFilled`. The method is shared by direct fields and already-resolved indexed reads. -/
@[simp]
def evalComputationFilled : CellObservation → ComputationConditionResult
  | .empty => .notTrue
  | .value _ => .holds
  | .unknown cause => .poison cause
  | .poison cause => .poison cause

/-- Consume one computation-phase observation as `FieldNotFilled`. Clean truth reverses, while a reached formal cause remains poison. -/
@[simp]
def evalComputationNotFilled : CellObservation → ComputationConditionResult
  | .empty => .holds
  | .value _ => .notTrue
  | .unknown cause => .poison cause
  | .poison cause => .poison cause

end CellObservation

namespace ComputationCondition

abbrev fieldFilled (field : FieldId) : ComputationCondition :=
  .leaf (.fieldFilled field)

abbrev fieldNotFilled (field : FieldId) : ComputationCondition :=
  .leaf (.fieldNotFilled field)

abbrev and (left right : ComputationCondition) : ComputationCondition :=
  ConditionTree.and left right

abbrev or (left right : ComputationCondition) : ComputationCondition :=
  ConditionTree.or left right

/-- Evaluate `FieldFilled` for one resolved checked field. A clean value counts as filled regardless of its scalar value; ordinary formal invalidity is poison rather than filled or empty. -/
def evalFieldFilled (context : ScalarComputationContext)
    (field : FieldId) : ComputationConditionResult :=
  (observeCell .computation (context.read field)).evalComputationFilled

/-- Evaluate one computation presence leaf through its checked computation-phase observation. -/
def ComputationConditionLeaf.eval (context : ScalarComputationContext) :
    ComputationConditionLeaf → ComputationConditionResult
  | .fieldFilled field => evalFieldFilled context field
  | .fieldNotFilled field =>
      (observeCell .computation (context.read field)).evalComputationNotFilled

/-- Evaluate a computation condition left-to-right. `And` stops on clean not-true, `Or` stops on clean holds, and a poison already read aborts without consulting the remaining operand. -/
def eval (condition : ComputationCondition)
    (context : ScalarComputationContext) : ComputationConditionResult :=
  condition.evalComputation (ComputationConditionLeaf.eval context)

@[simp]
theorem eval_fieldFilled (context : ScalarComputationContext) (field : FieldId) :
    (fieldFilled field).eval context = evalFieldFilled context field := by
  rfl

@[simp]
theorem eval_fieldNotFilled (context : ScalarComputationContext) (field : FieldId) :
    (fieldNotFilled field).eval context =
      (observeCell .computation (context.read field)).evalComputationNotFilled := by
  rfl

@[simp]
theorem eval_and (context : ScalarComputationContext)
    (left right : ComputationCondition) :
    (and left right).eval context =
      match left.eval context with
      | .holds => right.eval context
      | .notTrue => .notTrue
      | .poison cause => .poison cause := by
  rfl

@[simp]
theorem eval_or (context : ScalarComputationContext)
    (left right : ComputationCondition) :
    (or left right).eval context =
      match left.eval context with
      | .holds => .holds
      | .notTrue => right.eval context
      | .poison cause => .poison cause := by
  rfl

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

/-- Expand an optional whole-computation precondition into the existing guarded alternative core. A present common guard is the left operand so clean false and poison decide before the alternative-specific guard. -/
def expandCommonPrecondition
    (commonPrecondition : Option ComputationCondition)
    (alternatives : List (ComputationAlternative Operation)) :
    List (ComputationAlternative Operation) :=
  match commonPrecondition with
  | none => alternatives
  | some common =>
      alternatives.map fun alternative => {
        precondition := .and common alternative.precondition
        operation := alternative.operation }

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
