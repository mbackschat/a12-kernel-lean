import A12Kernel.Document
import A12Kernel.Semantics.NumericTolerance
import A12Kernel.Semantics.Observation
import A12Kernel.Semantics.ScalarEquality
import A12Kernel.Semantics.String
import A12Kernel.Semantics.DateTimeComparison
import A12Kernel.Semantics.BaseYearDateSource
import A12Kernel.Semantics.DateNumeric
import A12Kernel.Semantics.TimeNumeric
import A12Kernel.Semantics.EnumerationValueList
import A12Kernel.Semantics.Condition

/-! # A12Kernel.Semantics.FlatValidation — the first condition fragment

A small core for resolved, non-repeatable field references. It covers the admitted direct Number comparisons and fixed tolerance, Boolean/Confirm equality and inequality, direct String equality and inequality, four String `Length` ordering comparisons, checked Enumeration/category-to-literal equality and inequality, checked Number/String/Enumeration literal and field-valued list quantifiers, resolved temporal field/literal/`Today`/`Now`/Base-Year range-endpoint comparison, presence predicates, and `And`/`Or`.

It also exposes the leaf-relevance seam used by the separate flat partial-validation capsule. Paths, iteration, arithmetic, repeatable relevance, and concrete syntax are outside this capsule.
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

structure FlatEnumerationField where
  id : FieldId
  deriving Repr, DecidableEq

structure FlatTemporalField where
  id : FieldId
  kind : TemporalKind
  components : TemporalComponents
  deriving Repr, DecidableEq

/-- A typed, resolved field reference for presence predicates. -/
inductive FlatField where
  | number (field : FlatNumberField)
  | boolean (field : FlatBooleanField)
  | confirm (field : FlatConfirmField)
  | string (field : FlatStringField)
  | enumeration (field : FlatEnumerationField)
  | temporal (field : FlatTemporalField)
  deriving Repr, DecidableEq

namespace FlatField

/-- The resolved field identifier, independent of its scalar kind. -/
def id : FlatField → FieldId
  | .number field => field.id
  | .boolean field => field.id
  | .confirm field => field.id
  | .string field => field.id
  | .enumeration field => field.id
  | .temporal field => field.id

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
inductive FlatTemporalOperand where
  | fieldValue (field : FlatTemporalField)
  | literalValue (instant : Instant)
  | todayValue (zoneId : String)
  | baseYearValue (zoneId : String) (year : Int)
  | baseYearRangeValue (zoneId : String) (year : Int)
      (endpoint : BaseYearRangeEndpoint)
  | nowValue
  deriving Repr, DecidableEq

namespace FlatTemporalOperand

def fields : FlatTemporalOperand → List FlatField
  | .fieldValue field => [.temporal field]
  | .literalValue _ => []
  | .todayValue _ => []
  | .baseYearValue _ _ => []
  | .baseYearRangeValue _ _ _ => []
  | .nowValue => []

end FlatTemporalOperand

/-- One resolved Enumeration field and its exact declaration-checked stored/category projection, shared by scalar comparison and value-list consumers. -/
structure FlatEnumerationOperand where
  field : FlatEnumerationField
  projectionRef : EnumerationProjectionRef
  projection : ResolvedEnumerationProjection
  deriving Repr, DecidableEq

/-- One direct field whose checked value participates in String/Enumeration equality. -/
inductive FlatTextFieldOperand where
  | string (field : FlatStringField)
  | enumeration (operand : FlatEnumerationOperand)
  deriving Repr, DecidableEq

namespace FlatTextFieldOperand

def field : FlatTextFieldOperand → FlatField
  | .string field => .string field
  | .enumeration operand => .enumeration operand.field

end FlatTextFieldOperand

inductive FlatComparison where
  | number (op : NumericValidationOp) (field : FlatNumberField) (expected : Rat)
  | boolean (op : EqualityOp) (field : FlatBooleanField) (expected : Bool)
  | confirm (op : EqualityOp) (field : FlatConfirmField)
  | string (op : EqualityOp) (field : FlatStringField) (expected : String)
  | stringLength (op : StringLengthComparisonOp) (field : FlatStringField) (expected : Rat)
  | enumeration (op : EqualityOp) (operand : FlatEnumerationOperand)
      (expected : String)
  | textFields (op : EqualityOp) (left right : FlatTextFieldOperand)
  | temporal (op : TemporalComparisonOp)
      (left right : FlatTemporalOperand)
  deriving Repr, DecidableEq

namespace FlatComparison

/-- Every resolved field read by an atomic comparison, in authored operand order. -/
def fields : FlatComparison → List FlatField
  | .number _ field _ => [.number field]
  | .boolean _ field _ => [.boolean field]
  | .confirm _ field => [.confirm field]
  | .string _ field _ => [.string field]
  | .stringLength _ field _ => [.string field]
  | .enumeration _ operand _ => [.enumeration operand.field]
  | .textFields _ left right => [left.field, right.field]
  | .temporal _ left right => left.fields ++ right.fields

def fieldIds (comparison : FlatComparison) : List FieldId :=
  comparison.fields.map FlatField.id

/-- Partial validation may expose a comparison only when every field it reads is relevant. -/
def allRelevant (comparison : FlatComparison) (isRelevant : FieldId → Bool) : Bool :=
  comparison.fieldIds.all isRelevant

end FlatComparison

/-- The two grammar-level value-side shapes retained by a checked textual list quantifier. Field operands remain distinct from literals because empty and unavailable fields affect `No` and `NotAll` differently from a literal token. -/
inductive FlatTokenValueSide where
  | literals (values : List String)
  | fields (operands : List FlatTextFieldOperand)
  deriving Repr, DecidableEq

def FlatTokenValueSide.operands : FlatTokenValueSide → List FlatTextFieldOperand
  | .literals _ => []
  | .fields operands => operands

/-- The two grammar-level Number value-side shapes. Literal atoms are already checked integral values; field operands retain empty and unavailable observations without the direct-comparison empty-as-zero substitution. -/
inductive FlatNumberValueSide where
  | literals (values : List Rat)
  | fields (operands : List FlatNumberField)
  deriving Repr, DecidableEq

def FlatNumberValueSide.operands : FlatNumberValueSide → List FlatNumberField
  | .literals _ => []
  | .fields operands => operands

/-- Atomic flat conditions. Connectives live in `ConditionTree`, allowing another resolved leaf family to reuse their exact evaluation without wrapping a second complete condition tree. -/
inductive FlatConditionLeaf where
  | compare (comparison : FlatComparison)
  | tokenValueList (quantifier : ValueListQuantifier)
      (operands : List FlatTextFieldOperand) (values : FlatTokenValueSide)
  | numberValueList (quantifier : ValueListQuantifier)
      (operands : List FlatNumberField) (values : FlatNumberValueSide)
  | fieldFilled (field : FlatField)
  | fieldNotFilled (field : FlatField)
  deriving Repr, DecidableEq

/-- The established flat condition is the shared connective tree over only flat leaves. -/
abbrev FlatCondition := ConditionTree FlatConditionLeaf

namespace FlatCondition

abbrev compare (comparison : FlatComparison) : FlatCondition :=
  .leaf (.compare comparison)

abbrev tokenValueList (quantifier : ValueListQuantifier)
    (operands : List FlatTextFieldOperand) (values : FlatTokenValueSide) :
    FlatCondition :=
  .leaf (.tokenValueList quantifier operands values)

abbrev numberValueList (quantifier : ValueListQuantifier)
    (operands : List FlatNumberField) (values : FlatNumberValueSide) :
    FlatCondition :=
  .leaf (.numberValueList quantifier operands values)

abbrev fieldFilled (field : FlatField) : FlatCondition :=
  .leaf (.fieldFilled field)

abbrev fieldNotFilled (field : FlatField) : FlatCondition :=
  .leaf (.fieldNotFilled field)

end FlatCondition

/-- Lookup for already-resolved field references. The checked surface route constructs
    this context from the same model policies used by elaboration; the low-level evaluator
    still treats an inconsistent value kind defensively as malformed. -/
structure FlatContext where
  read : FieldId → CheckedCell
  world : Option World := none

/-- Supply the explicit evaluation world only to consumers that support clock-dependent operands. -/
def FlatContext.withWorld (context : FlatContext) (world : World) : FlatContext :=
  { context with world := some world }

/-- Per-field relevance for the nonrepeatable flat fragment. This is not the eventual
    wildcardable, row-addressed partial-validation relevant set. -/
abbrev FlatRelevance := FieldId → Bool

@[simp] def FlatConditionLeaf.canFireOnEmpty : FlatConditionLeaf → Bool
  | .compare _ => false
  | .tokenValueList quantifier _ _ => quantifier.canFireOnEmpty
  | .numberValueList quantifier _ _ => quantifier.canFireOnEmpty
  | .fieldFilled _ => false
  | .fieldNotFilled _ => true

/-- Whether an all-empty full-validation instance is eligible for this condition. -/
def FlatCondition.canFireOnEmpty (condition : FlatCondition) : Bool :=
  condition.evalBool FlatConditionLeaf.canFireOnEmpty

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

/-- Resolve one checked temporal field to the runtime's exact instant coordinate. The kind check is defensive for low-level callers; checked model contexts already enforce it during formal checking. -/
def FlatContext.resolveTemporalComparisonOperand (context : FlatContext)
    (field : FlatTemporalField) : SimpleComparisonOperand Instant :=
  match context.observeValidationAt field.id with
  | .empty => .notEvaluated
  | .value (.temporal value) =>
      if value.kind == field.kind then .value value.instant true
      else .unknown .malformed
  | .value _ => .unknown .malformed
  | .unknown cause => .unknown cause
  | .poison cause => .unknown cause

/-- Resolve one checked Date or DateTime field for direct numeric date-component extraction. The kind check is defensive; checked authoring separately excludes Time. -/
def FlatContext.resolveDateNumericOperand (context : FlatContext)
    (field : FlatTemporalField) (part : DateNumericPart) : NumericOperand :=
  match context.observeValidationAt field.id with
  | .empty => .value 0 .both
  | .value (.temporal value) =>
      if value.kind == field.kind then
        match value.dateParts? with
        | some parts => .value (part.extract parts) .fixed
        | none => .unknown .malformed
      else
        .unknown .malformed
  | .value _ => .unknown .malformed
  | .unknown cause => .unknown cause
  | .poison cause => .unknown cause

/-- Resolve one checked Time or DateTime field for direct numeric clock-component extraction. The kind check is defensive; checked authoring separately excludes Date. -/
def FlatContext.resolveTimeNumericOperand (context : FlatContext)
    (field : FlatTemporalField) (part : TimeNumericPart) : NumericOperand :=
  match context.observeValidationAt field.id with
  | .empty => .value 0 .both
  | .value (.temporal value) =>
      if value.kind == field.kind then
        match value.time? with
        | some clock => .value (part.extract clock) .fixed
        | none => .unknown .malformed
      else
        .unknown .malformed
  | .value _ => .unknown .malformed
  | .unknown cause => .unknown cause
  | .poison cause => .unknown cause

/-- Resolve one already-selected local calendar label through the injected model-zone capability without imposing stored-Date admission. -/
def FlatContext.resolveLocalDateComparisonOperand
    (context : FlatContext) (zoneId : String) (parts : DateParts) :
    SimpleComparisonOperand Instant :=
  match context.world.bind (fun world =>
    world.resolveLocal? zoneId parts.year parts.month parts.day 0 0 0) with
  | some instant => .value instant true
  | none => .unknown .malformed

def FlatTemporalOperand.resolve (context : FlatContext) : FlatTemporalOperand →
    SimpleComparisonOperand Instant
  | .fieldValue field => context.resolveTemporalComparisonOperand field
  | .literalValue instant => .value instant true
  | .todayValue zoneId =>
      match context.world.bind (·.today? zoneId) with
      | some instant => .value instant true
      | none => .unknown .malformed
  | .baseYearValue zoneId year =>
      context.resolveLocalDateComparisonOperand zoneId (baseYearDateParts year)
  | .baseYearRangeValue zoneId year endpoint =>
      context.resolveLocalDateComparisonOperand zoneId
        (baseYearRangeParts year endpoint)
  | .nowValue =>
      match context.world with
      | some world => .value world.now true
      | none => .unknown .malformed

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

def FlatEnumerationOperand.resolve (operand : FlatEnumerationOperand)
    (context : FlatContext) : SimpleComparisonOperand String :=
  operand.projection.resolveOperand
    (context.observeValidationAt operand.field.id)

def FlatTextFieldOperand.resolve (operand : FlatTextFieldOperand)
    (context : FlatContext) : SimpleComparisonOperand String :=
  match operand with
  | .string field => context.resolveDirectStringComparisonOperand field
  | .enumeration operand => operand.resolve context

def SimpleComparisonOperand.asTokenValueListCell
    (operand : SimpleComparisonOperand String) : ValueListCell .token :=
  match operand with
  | .notEvaluated => .empty
  | .value token _ => .present token
  | .unknown cause => .unknown cause

def FlatTextFieldOperand.valueListCell (operand : FlatTextFieldOperand)
    (context : FlatContext) : ValueListCell .token :=
  (operand.resolve context).asTokenValueListCell

def flatTokenValueListSide (operands : List FlatTextFieldOperand)
    (context : FlatContext) : ResolvedValueListSide .token :=
  { cells := operands.map (·.valueListCell context)
    hasUninstantiatedTail := false
    hasHaving := false }

def literalTokenValueListSide (values : List String) :
    ResolvedValueListSide .token :=
  { cells := values.map .present
    hasUninstantiatedTail := false
    hasHaving := false }

def FlatTokenValueSide.resolve (side : FlatTokenValueSide)
    (context : FlatContext) : ResolvedValueListSide .token :=
  match side with
  | .literals values => literalTokenValueListSide values
  | .fields operands => flatTokenValueListSide operands context

def FlatTokenValueSide.allOperands (values : FlatTokenValueSide)
    (fields : List FlatTextFieldOperand) : List FlatTextFieldOperand :=
  fields ++ values.operands

/-- Number value-list reads deliberately do not reuse direct comparison resolution: an empty member contributes no atom and is never substituted by zero. -/
def FlatNumberField.valueListCell (field : FlatNumberField)
    (context : FlatContext) : ValueListCell .number :=
  match context.observeValidationAt field.id with
  | .empty => .empty
  | .value (.num amount) => .present amount
  | .value _ => .unknown .malformed
  | .unknown cause => .unknown cause
  | .poison cause => .unknown cause

def flatNumberValueListSide (operands : List FlatNumberField)
    (context : FlatContext) : ResolvedValueListSide .number :=
  { cells := operands.map (·.valueListCell context)
    hasUninstantiatedTail := false
    hasHaving := false }

def literalNumberValueListSide (values : List Rat) :
    ResolvedValueListSide .number :=
  { cells := values.map .present
    hasUninstantiatedTail := false
    hasHaving := false }

def FlatNumberValueSide.resolve (side : FlatNumberValueSide)
    (context : FlatContext) : ResolvedValueListSide .number :=
  match side with
  | .literals values => literalNumberValueListSide values
  | .fields operands => flatNumberValueListSide operands context

def FlatNumberValueSide.allOperands (values : FlatNumberValueSide)
    (fields : List FlatNumberField) : List FlatNumberField :=
  fields ++ values.operands

/-- Whether one atomic flat condition references a field ID. -/
def FlatConditionLeaf.referencesField : FlatConditionLeaf → FieldId → Bool
  | .compare comparison, field => comparison.fieldIds.contains field
  | .tokenValueList _ operands values, field =>
      (values.allOperands operands).any fun operand => operand.field.id == field
  | .numberValueList _ operands values, field =>
      (values.allOperands operands).any fun operand => operand.id == field
  | .fieldFilled referenced, field
  | .fieldNotFilled referenced, field => referenced.id == field

/-- Reference traversal ignores connective shape and checks both branches. -/
def FlatCondition.referencesField (condition : FlatCondition) (field : FieldId) : Bool :=
  condition.anyLeaf fun leaf => leaf.referencesField field

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
  | .enumeration op operand expected =>
      operand.projection.evalLiteral op
        (context.observeValidationAt operand.field.id) expected
  | .textFields op left right =>
      op.evalSymmetric (· == ·) (left.resolve context) (right.resolve context)
  | .temporal op left right =>
      op.evalInstant (left.resolve context) (right.resolve context)

def FlatField.observeValidation (context : FlatContext) : FlatField → CellObservation
  | .number field => context.observeValidationAt field.id
  | .boolean field => context.observeValidationAt field.id
  | .confirm field => context.observeValidationAt field.id
  | .string field => context.observeValidationAt field.id
  | .enumeration field => context.observeValidationAt field.id
  | .temporal field => context.observeValidationAt field.id

namespace CellObservation

/-- Consume one validation-phase observation as `FieldFilled`. The method is shared by direct fields and already-resolved indexed reads. -/
@[simp]
def evalValidationFilled : CellObservation → Verdict
  | .empty => .notFired
  | .value _ => .fired .value
  | .unknown _ => .unknown
  | .poison _ => .unknown

/-- Consume one validation-phase observation as `FieldNotFilled`. Only clean empty fires, with omission polarity; formal unavailability remains unknown. -/
@[simp]
def evalValidationNotFilled : CellObservation → Verdict
  | .empty => .fired .omission
  | .value _ => .notFired
  | .unknown _ => .unknown
  | .poison _ => .unknown

end CellObservation

def FlatField.evalFilled (field : FlatField) (context : FlatContext) : Verdict :=
  (field.observeValidation context).evalValidationFilled

def FlatField.evalNotFilled (field : FlatField) (context : FlatContext) : Verdict :=
  (field.observeValidation context).evalValidationNotFilled

/-- Evaluate one atomic flat condition. Out-of-set reads become validation-unknown before `context.read`; connective evaluation remains in `ConditionTree.evalVerdict`. -/
@[simp] def FlatConditionLeaf.evalSelected (context : FlatContext)
    (isRelevant : FlatRelevance := fun _ => true) : FlatConditionLeaf → Verdict
  | .compare comparison =>
      if comparison.allRelevant isRelevant then comparison.eval context else .unknown
  | .tokenValueList quantifier operands values =>
      if values.allOperands operands |>.all fun operand => isRelevant operand.field.id then
        quantifier.eval (flatTokenValueListSide operands context)
          (values.resolve context)
      else
        .unknown
  | .numberValueList quantifier operands values =>
      if values.allOperands operands |>.all fun operand => isRelevant operand.id then
        quantifier.eval (flatNumberValueListSide operands context)
          (values.resolve context)
      else
        .unknown
  | .fieldFilled field =>
      if isRelevant field.id then field.evalFilled context else .unknown
  | .fieldNotFilled field =>
      if isRelevant field.id then field.evalNotFilled context else .unknown

/-- Evaluate an already-selected flat tree through the shared connective evaluator. -/
def FlatCondition.evalSelected (context : FlatContext)
    (isRelevant : FlatRelevance := fun _ => true) (condition : FlatCondition) : Verdict :=
  condition.evalVerdict fun leaf => leaf.evalSelected context isRelevant

/-- Full-validation row gate. Instantiated/content-bearing status is supplied by the
    document/iteration layer and remains independent of cell values. -/
def FlatCondition.evalFull (context : FlatContext) (hasContent : Bool)
    (condition : FlatCondition) : Verdict :=
  if hasContent || condition.canFireOnEmpty then condition.evalSelected context else .notFired

end A12Kernel
