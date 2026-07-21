import A12Kernel.Document
import A12Kernel.Semantics.NumericComparison
import A12Kernel.Semantics.Observation
import A12Kernel.Semantics.ScalarEquality
import A12Kernel.Semantics.String

/-! # A12Kernel.Semantics.FlatValidation — the first condition fragment

A small core for resolved, non-repeatable field references. It covers the admitted
direct Number comparisons, Boolean/Confirm equality and inequality, direct String
equality, two observed String `Length` comparisons, presence predicates, and `And`/`Or`.
It also exposes the leaf-relevance seam used by the separate flat partial-validation
capsule. Paths, iteration, arithmetic, repeatable relevance, and concrete syntax are
outside this capsule.
-/

namespace A12Kernel

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

structure FlatStringField where
  id : FieldId
  deriving Repr, DecidableEq

/-- A typed, resolved field reference for presence predicates. -/
inductive FlatField where
  | number (field : FlatNumberField)
  | boolean (field : FlatBooleanField)
  | confirm (field : FlatConfirmField)
  | string (field : FlatStringField)
  deriving Repr, DecidableEq

namespace FlatField

/-- The resolved field identifier, independent of its scalar kind. -/
def id : FlatField → FieldId
  | .number field => field.id
  | .boolean field => field.id
  | .confirm field => field.id
  | .string field => field.id

end FlatField

/-- The scale-exempt String `Length` ordering comparisons admitted by the reduced flat surface. Exact equality and inequality need an authored-scale-preserving consumer. -/
inductive StringLengthComparisonOp where
  | less
  | lessEqual
  | greater
  | greaterEqual
  deriving Repr, DecidableEq

def StringLengthComparisonOp.toNumeric : StringLengthComparisonOp → NumericComparisonOp
  | .less => .less
  | .lessEqual => .lessEqual
  | .greater => .greater
  | .greaterEqual => .greaterEqual

/-- The typed comparison fragment. The reduced direct-Number route receives only a
    rational literal and therefore cannot enforce authored-scale compatibility; the
    checked numeric-expression route retains that metadata. Confirm admits only the
    legal `True` literal, made implicit in its constructor. -/
inductive FlatComparison where
  | number (op : NumericComparisonOp) (field : FlatNumberField) (expected : Rat)
  | boolean (op : EqualityOp) (field : FlatBooleanField) (expected : Bool)
  | confirm (op : EqualityOp) (field : FlatConfirmField)
  | string (op : EqualityOp) (field : FlatStringField) (expected : String)
  | stringLength (op : StringLengthComparisonOp) (field : FlatStringField) (expected : Rat)
  deriving Repr, DecidableEq

namespace FlatComparison

/-- The single resolved field read by every atomic comparison in the flat fragment. -/
def fieldId : FlatComparison → FieldId
  | .number _ field _ => field.id
  | .boolean _ field _ => field.id
  | .confirm _ field => field.id
  | .string _ field _ => field.id
  | .stringLength _ field _ => field.id

end FlatComparison

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

/-- Per-field relevance for the nonrepeatable flat fragment. This is not the eventual
    wildcardable, row-addressed partial-validation relevant set. -/
abbrev FlatRelevance := FieldId → Bool

/-- Whether an all-empty full-validation instance is eligible for this condition. -/
def FlatCondition.canFireOnEmpty : FlatCondition → Bool
  | .compare _ => false
  | .fieldFilled _ => false
  | .fieldNotFilled _ => true
  | .and left right => left.canFireOnEmpty && right.canFireOnEmpty
  | .or left right => left.canFireOnEmpty || right.canFireOnEmpty

def FlatContext.observeValidationAt (context : FlatContext) (id : FieldId) : CellObservation :=
  observeCell .validation (context.read id)

def FlatContext.resolveNumberComparisonOperand (context : FlatContext)
    (field : FlatNumberField) : NumericOperand :=
  (context.observeValidationAt field.id).asValidationNumericOperand field.info

/-- Resolve a Boolean field for direct comparison. Empty Boolean is not evaluated. -/
def FlatContext.resolveBooleanComparisonOperand
    (context : FlatContext) (field : FlatBooleanField) :
    SimpleComparisonOperand Bool :=
  match context.observeValidationAt field.id with
  | .empty => .notEvaluated
  | .value (.bool value) => .value value true
  | .value _ => .unknown .malformed
  | .unknown cause => .unknown cause
  | .poison cause => .unknown cause

/-- Resolve a Confirm field for direct comparison. Empty Confirm substitutes false. -/
def FlatContext.resolveConfirmComparisonOperand
    (context : FlatContext) (field : FlatConfirmField) :
    SimpleComparisonOperand Bool :=
  match context.observeValidationAt field.id with
  | .empty => .value false false
  | .value (.conf true) => .value true true
  | .value _ => .unknown .malformed
  | .unknown cause => .unknown cause
  | .poison cause => .unknown cause

def FlatContext.resolveDirectStringComparisonOperand (context : FlatContext)
    (field : FlatStringField) :
    SimpleComparisonOperand String :=
  match context.observeValidationAt field.id with
  | .empty => .notEvaluated
  | .value (.str value) => if value.isEmpty then .notEvaluated else .value value true
  | .value _ => .unknown .malformed
  | .unknown cause => .unknown cause
  | .poison cause => .unknown cause

def FlatContext.resolveStringLengthOperand (context : FlatContext) (field : FlatStringField) :
    NumericOperand :=
  match context.observeValidationAt field.id with
  | .empty => .value 0 .growOnly
  | .value (.str value) =>
      if value.isEmpty then .value 0 .growOnly
      else .value (utf16CodeUnitLength value) .fixed
  | .value _ => .unknown .malformed
  | .unknown cause => .unknown cause
  | .poison cause => .unknown cause

/-- Direct String equality suppresses an empty literal only after the field read has
    preserved malformed input as unknown. -/
def SimpleComparisonOperand.evalDirectString
    (operand : SimpleComparisonOperand String) (op : EqualityOp)
    (expected : String) : Verdict :=
  match operand with
  | .unknown _ => .unknown
  | .notEvaluated => .notFired
  | .value actual given =>
      if expected.isEmpty then .notFired
      else op.evalSimple (· == ·) (.value actual given) expected

def FlatComparison.eval (comparison : FlatComparison) (context : FlatContext) : Verdict :=
  match comparison with
  | .number op field expected =>
      op.evalFixedRight (context.resolveNumberComparisonOperand field) expected
  | .boolean op field expected =>
      op.evalSimple (· == ·) (context.resolveBooleanComparisonOperand field) expected
  | .confirm op field =>
      op.evalSimple (· == ·) (context.resolveConfirmComparisonOperand field) true
  | .string op field expected =>
      (context.resolveDirectStringComparisonOperand field).evalDirectString op expected
  | .stringLength op field expected =>
      op.toNumeric.evalFixedRight (context.resolveStringLengthOperand field) expected

def FlatField.observeValidation (context : FlatContext) : FlatField → CellObservation
  | .number field => context.observeValidationAt field.id
  | .boolean field => context.observeValidationAt field.id
  | .confirm field => context.observeValidationAt field.id
  | .string field => context.observeValidationAt field.id

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

/-- Evaluate an already-selected context. The optional relevance predicate makes an
    out-of-set atomic read validation-unknown before `context.read`, so a per-call
    partial-validation exclusion is never misrepresented as a formal finding. Full
    validation uses the all-relevant default. `And` may skip only after `notFired`; `Or`
    may skip only after `fired value`, because any other verdict can still change when
    the right-hand polarity is combined. -/
def FlatCondition.evalSelected (context : FlatContext)
    (isRelevant : FlatRelevance := fun _ => true) : FlatCondition → Verdict
  | .compare comparison =>
      if isRelevant comparison.fieldId then comparison.eval context else .unknown
  | .fieldFilled field =>
      if isRelevant field.id then field.evalFilled context else .unknown
  | .fieldNotFilled field =>
      if isRelevant field.id then field.evalNotFilled context else .unknown
  | .and left right =>
      let leftVerdict := left.evalSelected context isRelevant
      match leftVerdict with
      | .notFired => .notFired
      | _ => Verdict.conj leftVerdict (right.evalSelected context isRelevant)
  | .or left right =>
      let leftVerdict := left.evalSelected context isRelevant
      match leftVerdict with
      | .fired .value => .fired .value
      | _ => Verdict.disj leftVerdict (right.evalSelected context isRelevant)

/-- Full-validation row gate. Instantiated/content-bearing status is supplied by the
    document/iteration layer and remains independent of cell values. -/
def FlatCondition.evalFull (context : FlatContext) (hasContent : Bool)
    (condition : FlatCondition) : Verdict :=
  if hasContent || condition.canFireOnEmpty then condition.evalSelected context else .notFired

end A12Kernel
