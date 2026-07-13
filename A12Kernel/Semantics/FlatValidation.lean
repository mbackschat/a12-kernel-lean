import A12Kernel.Document
import A12Kernel.Semantics.Observation

/-! # A12Kernel.Semantics.FlatValidation — the first condition fragment

A small core for resolved, non-repeatable field references. It covers typed
Number/Boolean/Confirm equality, presence predicates, and `And`/`Or`. Paths, iteration,
arithmetic, partial validation, and concrete syntax are outside this capsule.
-/

namespace A12Kernel

/-- Equality and inequality are separate surface operators; there is no generic
    condition negation in the language. -/
inductive EqualityOp where
  | equal
  | notEqual
  deriving Repr, DecidableEq

structure FlatNumberField where
  id : FieldId
  info : NumField
  deriving Repr, DecidableEq

structure FlatBooleanField where
  id : FieldId
  deriving Repr, DecidableEq

structure FlatConfirmField where
  id : FieldId
  deriving Repr, DecidableEq

/-- A typed, resolved field reference for presence predicates. -/
inductive FlatField where
  | number (field : FlatNumberField)
  | boolean (field : FlatBooleanField)
  | confirm (field : FlatConfirmField)
  deriving Repr, DecidableEq

namespace FlatField

/-- The resolved field identifier, independent of its scalar kind. -/
def id : FlatField → FieldId
  | .number field => field.id
  | .boolean field => field.id
  | .confirm field => field.id

end FlatField

/-- The typed comparison fragment. Numeric literals are scale-exempt by construction;
    Confirm admits only the legal `True` literal, made implicit in its constructor. -/
inductive FlatComparison where
  | number (op : EqualityOp) (field : FlatNumberField) (expected : Rat)
  | boolean (op : EqualityOp) (field : FlatBooleanField) (expected : Bool)
  | confirm (op : EqualityOp) (field : FlatConfirmField)
  deriving Repr, DecidableEq

/-- Flat core conditions. The closed constructors make unsupported operations
    impossible to represent in this fragment. -/
inductive FlatCondition where
  | compare (comparison : FlatComparison)
  | fieldFilled (field : FlatField)
  | fieldNotFilled (field : FlatField)
  | and (left right : FlatCondition)
  | or (left right : FlatCondition)
  deriving Repr, DecidableEq

/-- Lookup for already-resolved field references. The checked surface route constructs
    this context from the same model policies used by elaboration; the low-level evaluator
    still treats an inconsistent value kind defensively as malformed. -/
structure FlatContext where
  read : FieldId → CheckedCell

/-- Whether an all-empty full-validation instance is eligible for this condition. -/
def FlatCondition.canFireOnEmpty : FlatCondition → Bool
  | .compare _ => false
  | .fieldFilled _ => false
  | .fieldNotFilled _ => true
  | .and left right => left.canFireOnEmpty && right.canFireOnEmpty
  | .or left right => left.canFireOnEmpty || right.canFireOnEmpty

/-- Comparison-local operand classification. `given` preserves whether a concrete value
    came from stored input or from the consuming comparison's empty substitution. -/
inductive ComparisonOperand (α : Type) where
  | value (value : α) (given : Bool)
  | notEvaluated
  | unknown (cause : FormalCause)

def FlatContext.observeValidationAt (context : FlatContext) (id : FieldId) : CellObservation :=
  observeCell .validation (context.read id)

def FlatContext.resolveNumberComparisonOperand (context : FlatContext)
    (field : FlatNumberField) : ComparisonOperand Rat :=
  match context.observeValidationAt field.id with
  | .empty => .value 0 false
  | .value (.num value) => .value value true
  | .value _ => .unknown .malformed
  | .unknown cause => .unknown cause
  | .poison cause => .unknown cause

private def resolveBooleanComparisonOperand (context : FlatContext) (field : FlatBooleanField) :
    ComparisonOperand Bool :=
  match context.observeValidationAt field.id with
  | .empty => .notEvaluated
  | .value (.bool value) => .value value true
  | .value _ => .unknown .malformed
  | .unknown cause => .unknown cause
  | .poison cause => .unknown cause

private def resolveConfirmComparisonOperand (context : FlatContext) (field : FlatConfirmField) :
    ComparisonOperand Bool :=
  match context.observeValidationAt field.id with
  | .empty => .value false false
  | .value (.conf true) => .value true true
  | .value _ => .unknown .malformed
  | .unknown cause => .unknown cause
  | .poison cause => .unknown cause

/-- The fixed decimal scale applied to both numeric operands before every comparison. -/
def comparisonScale : Nat := 19

/-- Decimal `HALF_UP`, i.e. ties round away from zero. -/
def rescaleHalfUp (value : Rat) (scale : Nat) : Rat :=
  let factor : Nat := 10 ^ scale
  let shifted := value * (factor : Rat)
  let half : Rat := 1 / 2
  let rounded := if shifted < 0 then Rat.ceil (shifted - half) else Rat.floor (shifted + half)
  (rounded : Rat) / (factor : Rat)

private def numberEquivalent (left right : Rat) : Bool :=
  rescaleHalfUp left comparisonScale == rescaleHalfUp right comparisonScale

private def EqualityOp.holds (op : EqualityOp) (equivalent : Bool) : Bool :=
  match op with
  | .equal => equivalent
  | .notEqual => !equivalent

private def evalResolved (equivalent : α → α → Bool) (op : EqualityOp)
    (operand : ComparisonOperand α) (expected : α) : Verdict :=
  match operand with
  | .notEvaluated => .notFired
  | .unknown _ => .unknown
  | .value actual given =>
      if op.holds (equivalent actual expected) then
        if given then .fired .value else .fired .omission
      else
        .notFired

private def evalComparison (context : FlatContext) : FlatComparison → Verdict
  | .number op field expected =>
      evalResolved numberEquivalent op (context.resolveNumberComparisonOperand field) expected
  | .boolean op field expected =>
      evalResolved (· == ·) op (resolveBooleanComparisonOperand context field) expected
  | .confirm op field =>
      evalResolved (· == ·) op (resolveConfirmComparisonOperand context field) true

def FlatField.observeValidation (context : FlatContext) : FlatField → CellObservation
  | .number field => context.observeValidationAt field.id
  | .boolean field => context.observeValidationAt field.id
  | .confirm field => context.observeValidationAt field.id

def FlatField.evalFilled (field : FlatField) (context : FlatContext) : Verdict :=
  match field.observeValidation context with
  | .empty => .notFired
  | .value _ => .fired .value
  | .unknown _ => .unknown
  | .poison _ => .unknown

def FlatField.evalNotFilled (field : FlatField) (context : FlatContext) : Verdict :=
  match field.observeValidation context with
  | .empty => .fired .omission
  | .value _ => .notFired
  | .unknown _ => .unknown
  | .poison _ => .unknown

/-- Evaluate an already-selected context. `And` may skip only after `notFired`; `Or` may
    skip only after `fired value`, because any other verdict can still change when the
    right-hand polarity is combined. -/
def FlatCondition.evalSelected (context : FlatContext) : FlatCondition → Verdict
  | .compare comparison => evalComparison context comparison
  | .fieldFilled field => field.evalFilled context
  | .fieldNotFilled field => field.evalNotFilled context
  | .and left right =>
      let leftVerdict := left.evalSelected context
      match leftVerdict with
      | .notFired => .notFired
      | _ => Verdict.conj leftVerdict (right.evalSelected context)
  | .or left right =>
      let leftVerdict := left.evalSelected context
      match leftVerdict with
      | .fired .value => .fired .value
      | _ => Verdict.disj leftVerdict (right.evalSelected context)

/-- Full-validation row gate. Instantiated/content-bearing status is supplied by the
    document/iteration layer and remains independent of cell values. -/
def FlatCondition.evalFull (context : FlatContext) (hasContent : Bool)
    (condition : FlatCondition) : Verdict :=
  if hasContent || condition.canFireOnEmpty then condition.evalSelected context else .notFired

end A12Kernel
