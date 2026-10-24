import A12Kernel.Document
import A12Kernel.Semantics.NumericTolerance
import A12Kernel.Semantics.Observation
import A12Kernel.Semantics.ScalarEquality
import A12Kernel.Semantics.String
import A12Kernel.Semantics.DateTimeComparison
import A12Kernel.Semantics.DateTimeDifference
import A12Kernel.Semantics.TemporalFormat
import A12Kernel.Semantics.DateRangeComparison
import A12Kernel.Semantics.TimeComparison
import A12Kernel.Semantics.BaseYearDateSource
import A12Kernel.Semantics.DateNumeric
import A12Kernel.Semantics.TimeNumeric
import A12Kernel.Semantics.EnumerationValueList
import A12Kernel.Semantics.Condition
import A12Kernel.Semantics.ModelZone

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
  /-- A raw String admitted as a list member, whose filled value the Kernel reads as the token `X`
  rather than its text, in a computation's and a rule's first-filled scan alike, an empty one staying
  empty (k22-static-s4-2026-10-24, `raw-members/artifact*.json`). -/
  rawPlaceholder : Bool := false
  deriving Repr, DecidableEq

/-- The token a String member contributes for its present text. -/
def FlatStringField.token (field : FlatStringField) (value : String) : String :=
  if field.rawPlaceholder then "X" else value

structure FlatEnumerationField where
  id : FieldId
  deriving Repr, DecidableEq

structure FlatTemporalField where
  id : FieldId
  kind : TemporalKind
  components : TemporalComponents
  deriving Repr, DecidableEq

structure FlatDateRangeField where
  id : FieldId
  deriving Repr, DecidableEq

/-- A typed, resolved field reference for presence predicates. -/
inductive FlatField where
  | number (field : FlatNumberField)
  | boolean (field : FlatBooleanField)
  | confirm (field : FlatConfirmField)
  | string (field : FlatStringField)
  | enumeration (field : FlatEnumerationField)
  | temporal (field : FlatTemporalField)
  | dateRange (field : FlatDateRangeField)
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
  | .dateRange field => field.id

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

/-- Literal components remain separate from the resolved instant so year agreement survives model-anchor completion (spec/05 §1). The field payload serves ordinary and correlated readers. -/
inductive FlatTemporalOperand (Field : Type := FlatTemporalField) where
  | fieldValue (field : Field)
  | literalValue (instant : Instant) (components : TemporalComponents := TemporalComponents.fullDate)
  | timeValue (value : TimeOfDay)
  | localDateTimeValue (profile : ModelZone.ConcreteProfile) (label : LegacyCalendarLabel)
  | grouped (source : FlatTemporalOperand Field)
  | todayValue (zoneId : String)
  | baseYearValue (zoneId : String) (year : Int)
  | baseYearRangeValue (zoneId : String) (year : Int)
      (endpoint : BaseYearRangeEndpoint)
  | nowValue
  deriving Repr, DecidableEq

namespace FlatTemporalOperand

def fieldValues : FlatTemporalOperand Field → List Field
  | .fieldValue field => [field]
  | .grouped source => source.fieldValues
  | _ => []

def fields (operand : FlatTemporalOperand) : List FlatField :=
  operand.fieldValues.map FlatField.temporal

/-- Subday admission uses the same field-format identity and full clock components on ordinary and correlated routes (spec/05 §2). -/
def dateTimeDifferenceComponentsWith? (components : Field → TemporalComponents) :
    FlatTemporalOperand Field → Option TemporalComponents
  | .fieldValue source => some (components source)
  | .nowValue => some TemporalComponents.now
  | _ => none

/-- Field reads retain the caller's phase and effects; `Now` reads the exact supplied instant (spec/05 §2), while absent clocks and unsupported source shapes retain separate failure channels. -/
def readDateTimeDifferenceOperand (read : Field → Except Error CellObservation)
    (world : Option World) (missingWorld unsupported : Error) :
    FlatTemporalOperand Field → Except Error DateTimeDifferenceOperand
  | .fieldValue source => DateTimeDifferenceOperand.ofObservation <$> read source
  | .nowValue => match world with
      | some world => pure (.value world.now)
      | none => throw missingWorld
  | _ => throw unsupported

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

inductive FlatBooleanOperand where
  | boolean (field : FlatBooleanField)
  | confirm (field : FlatConfirmField)
  deriving Repr, DecidableEq

def FlatBooleanOperand.field : FlatBooleanOperand → FlatField
  | .boolean field => .boolean field
  | .confirm field => .confirm field

inductive FlatComparison where
  | number (op : NumericValidationOp) (field : FlatNumberField) (expected : Rat)
  | boolean (op : EqualityOp) (field : FlatBooleanField) (expected : Bool)
  | confirm (op : EqualityOp) (field : FlatConfirmField)
  | booleanFields (op : EqualityOp) (left right : FlatBooleanOperand)
  | string (op : EqualityOp) (field : FlatStringField) (expected : String)
  | stringLength (op : StringLengthComparisonOp) (field : FlatStringField) (expected : Rat)
  | enumeration (op : EqualityOp) (operand : FlatEnumerationOperand)
      (expected : String)
  | textFields (op : EqualityOp) (left right : FlatTextFieldOperand)
  | dateRange (op : EqualityOp) (left right : FlatDateRangeField)
  | temporal (op : TemporalComparisonOp)
      (left right : FlatTemporalOperand)
  /-- Two date-free fields, compared by their clocks alone: the Kernel's comparison observes only the
  decoded hour, minute, and second, whatever the declared kind of either side
  ([checkpoint](../../docs/sources/temporal-runtime-fold-probes.md#src-cross-kind-temporal-reads)), and
  the instant a cell carries plays no part. -/
  | time (op : TemporalComparisonOp) (left right : FlatTemporalField)
  deriving Repr, DecidableEq

namespace FlatComparison

/-- Every resolved field read by an atomic comparison, in authored operand order. -/
def fields : FlatComparison → List FlatField
  | .number _ field _ => [.number field]
  | .boolean _ field _ => [.boolean field]
  | .confirm _ field => [.confirm field]
  | .booleanFields _ left right => [left.field, right.field]
  | .string _ field _ => [.string field]
  | .stringLength _ field _ => [.string field]
  | .enumeration _ operand _ => [.enumeration operand.field]
  | .textFields _ left right => [left.field, right.field]
  | .dateRange _ left right => [.dateRange left, .dateRange right]
  | .temporal _ left right => left.fields ++ right.fields
  | .time _ left right => [.temporal left, .temporal right]

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

/-- Singular membership and plural quantification share verdicts but differ in generated
classification eligibility (`IValueListCondition` versus `IEntityListAndValueListCondition`). -/
inductive ValueListAuthoredForm where
  | membership
  | quantifier
  deriving Repr, DecidableEq

/-- Atomic flat conditions. Connectives live in `ConditionTree`, allowing another resolved leaf family to reuse their exact evaluation without wrapping a second complete condition tree. -/
inductive FlatConditionLeaf where
  | compare (comparison : FlatComparison)
  | tokenValueList (quantifier : ValueListQuantifier)
      (operands : List FlatTextFieldOperand) (values : FlatTokenValueSide)
      (form : ValueListAuthoredForm := .quantifier)
  | numberValueList (quantifier : ValueListQuantifier)
      (operands : List FlatNumberField) (values : FlatNumberValueSide)
      (form : ValueListAuthoredForm := .quantifier)
  | fieldFilled (field : FlatField)
  | fieldNotFilled (field : FlatField)
  deriving Repr, DecidableEq

/-- The established flat condition is the shared connective tree over only flat leaves. -/
abbrev FlatCondition := ConditionTree FlatConditionLeaf

namespace FlatCondition

abbrev compare (comparison : FlatComparison) : FlatCondition :=
  .leaf (.compare comparison)

abbrev tokenValueList (quantifier : ValueListQuantifier)
    (operands : List FlatTextFieldOperand) (values : FlatTokenValueSide)
    (form : ValueListAuthoredForm := .quantifier) : FlatCondition :=
  .leaf (.tokenValueList quantifier operands values form)

abbrev numberValueList (quantifier : ValueListQuantifier)
    (operands : List FlatNumberField) (values : FlatNumberValueSide)
    (form : ValueListAuthoredForm := .quantifier) : FlatCondition :=
  .leaf (.numberValueList quantifier operands values form)

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
  storedText : FieldId → Option String := fun _ => none
  world : Option World := none

/-- Supply the explicit evaluation world only to consumers that support clock-dependent operands. -/
def FlatContext.withWorld (context : FlatContext) (world : World) : FlatContext :=
  { context with world := some world }

/-- Per-field relevance for the nonrepeatable flat fragment. This is not the eventual
    wildcardable, row-addressed partial-validation relevant set. -/
abbrev FlatRelevance := FieldId → Bool

@[simp] def FlatConditionLeaf.canFireOnEmpty : FlatConditionLeaf → Bool
  | .compare _ => false
  | .tokenValueList quantifier _ _ _ => quantifier.canFireOnEmpty
  | .numberValueList quantifier _ _ _ => quantifier.canFireOnEmpty
  | .fieldFilled _ => false
  | .fieldNotFilled _ => true

/-- Whether an all-empty full-validation instance is eligible for this condition. -/
def FlatCondition.canFireOnEmpty (condition : FlatCondition) : Bool :=
  condition.evalBool FlatConditionLeaf.canFireOnEmpty

/-- Observe one checked direct field at the caller's phase. -/
@[simp] def FlatContext.observeAt (context : FlatContext) (phase : Phase)
    (id : FieldId) : CellObservation :=
  observeCell phase (context.read id)

/-- Validation specialization retained for established direct-field consumers. -/
def FlatContext.observeValidationAt (context : FlatContext)
    (id : FieldId) : CellObservation :=
  context.observeAt .validation id

/-- Resolve the direct-comparison Number operand after the caller has selected validation or computation observation. -/
def FlatContext.resolveNumberComparisonOperandAt (context : FlatContext)
    (phase : Phase) (field : FlatNumberField) : NumericOperand :=
  (context.observeAt phase field.id).asDirectNumericComparisonOperand field.info

def FlatContext.resolveNumberComparisonOperand (context : FlatContext)
    (field : FlatNumberField) : NumericOperand :=
  context.resolveNumberComparisonOperandAt .validation field

/-- Boolean absence suppresses comparison; Confirm absence substitutes false (spec/02 §A.3).
The same projection serves direct and selected reads in either phase. -/
def CellObservation.asBooleanComparisonOperand (observation : CellObservation)
    (confirm : Bool := false) : SimpleComparisonOperand Bool :=
  match observation with
  | .empty => if confirm then .value false false else .notEvaluated
  | .value (.bool flag) => if confirm then .unknown .malformed else .value flag true
  | .value (.conf true) => if confirm then .value true true else .unknown .malformed
  | .value _ => .unknown .malformed
  | .unknown cause | .poison cause => .unknown cause

/-- Resolve a Boolean field for direct comparison. Empty Boolean is not evaluated. -/
def FlatContext.resolveBooleanComparisonOperandAt
    (context : FlatContext) (phase : Phase) (field : FlatBooleanField) :
    SimpleComparisonOperand Bool :=
  (observeCell phase (context.read field.id)).asBooleanComparisonOperand

def FlatContext.resolveBooleanComparisonOperand (context : FlatContext)
    (field : FlatBooleanField) : SimpleComparisonOperand Bool :=
  context.resolveBooleanComparisonOperandAt .validation field

/-- Resolve a Confirm field for direct comparison. Empty Confirm substitutes false. -/
def FlatContext.resolveConfirmComparisonOperandAt
    (context : FlatContext) (phase : Phase) (field : FlatConfirmField) :
    SimpleComparisonOperand Bool :=
  (observeCell phase (context.read field.id)).asBooleanComparisonOperand true

def FlatContext.resolveConfirmComparisonOperand (context : FlatContext)
    (field : FlatConfirmField) : SimpleComparisonOperand Bool :=
  context.resolveConfirmComparisonOperandAt .validation field

/-- Direct and selected pattern reads use the same checked String observation (spec/06 patterns). -/
@[simp]
def CellObservation.asStringComparisonOperand : CellObservation Value → SimpleComparisonOperand String
  | .empty => .notEvaluated
  | .value (.str text) => if text.isEmpty then .notEvaluated else .value text true
  | .value _ => .unknown .malformed
  | .unknown cause => .unknown cause
  | .poison cause => .unknown cause

/-- Resolve one String field for direct comparison at a chosen phase, mirroring the numeric pair
    above. There are no empty String *values*, so a present-empty cell and an absent one both
    resolve to `notEvaluated` and neither can satisfy an equality. -/
def FlatContext.resolveStringComparisonOperandAt (context : FlatContext)
    (phase : Phase) (field : FlatStringField) : SimpleComparisonOperand String :=
  (context.observeAt phase field.id).asStringComparisonOperand

def FlatContext.resolveDirectStringComparisonOperand (context : FlatContext)
    (field : FlatStringField) :
    SimpleComparisonOperand String :=
  context.resolveStringComparisonOperandAt .validation field

/-- Read one already-checked evaluated String as its UTF-16 numeric length. Both validation and computation reuse this projection after selecting their own phase observation. -/
@[simp]
def CellObservation.asStringLengthOperand :
    CellObservation Value → NumericOperand
  | .empty => .value 0 .growOnly
  | .value (.str text) =>
      if text.isEmpty then .value 0 .growOnly
      else .value (utf16CodeUnitLength text) .fixed
  | .value _ => .unknown .malformed
  | .unknown cause => .unknown cause
  | .poison cause => .unknown cause

/-- Project the checked 1-based inclusive range through the shared UTF-16 numeric conversion (spec/06). -/
def CellObservation.asStringRangeOperand (start finish : Nat) : CellObservation → NumericOperand
  | .empty => .value 0 .growOnly
  | .value (.str text) => .value (utf16RangeAsNatural text start finish) .fixed
  | .value _ => .unknown .malformed
  | .unknown cause | .poison cause => .unknown cause

def FlatContext.resolveStringLengthOperand (context : FlatContext) (field : FlatStringField) :
    NumericOperand :=
  (context.observeValidationAt field.id).asStringLengthOperand

/-- Whether a temporal value belongs to the field's **format family**, the family its formal check
admits ([`TemporalComponents.family?`](../Core.lean)). The declared kind takes no part: a DATE- or
DATE_TIME-declared clock compares and extracts as a clock, and a TIME- or DATE_TIME-declared date as a
date ([checkpoint](../../docs/sources/temporal-runtime-fold-probes.md#src-cross-kind-temporal-reads)).
The test is defensive for low-level callers, since a checked context admits nothing else. -/
def FlatTemporalField.holdsValue (field : FlatTemporalField) (value : TemporalValue) : Bool :=
  some value.kind == field.components.family?

/-- Resolve one checked temporal field to one projection of its value for a comparison. -/
def FlatContext.resolveTemporalFieldBy (context : FlatContext) (field : FlatTemporalField)
    (project : TemporalValue → Option α) (phase : Phase := .validation) : SimpleComparisonOperand α :=
  match context.observeAt phase field.id with
  | .empty => .notEvaluated
  | .value (.temporal value) =>
      match field.holdsValue value, project value with
      | true, some projected => .value projected true
      | _, _ => .unknown .malformed
  | .value _ => .unknown .malformed
  | .unknown cause => .unknown cause
  | .poison cause => .unknown cause

/-- Resolve one checked temporal field to the runtime's exact instant coordinate. -/
def FlatContext.resolveTemporalComparisonOperand (context : FlatContext)
    (field : FlatTemporalField) : SimpleComparisonOperand Instant :=
  context.resolveTemporalFieldBy field fun value => some value.instant

/-- Resolve one checked date-free temporal field to its clock. -/
def FlatContext.resolveTimeComparisonOperand (context : FlatContext)
    (field : FlatTemporalField) : SimpleComparisonOperand TimeOfDay :=
  context.resolveTemporalFieldBy field TemporalValue.time?

/-- Resolve one checked temporal field to one numeric component for direct extraction: empty is the
symmetric zero, and a value its field does not hold, or one without the projected component, is
malformed. -/
def CellObservation.asTemporalNumericOperand (observation : CellObservation)
    (field : FlatTemporalField) (project : TemporalValue → Option Rat) : NumericOperand :=
  match observation with
  | .empty => .value 0 .both
  | .value (.temporal temporalValue) =>
      if field.holdsValue temporalValue then
        match project temporalValue with
        | some amount => .value amount .fixed
        | none => .unknown .malformed
      else
        .unknown .malformed
  | .value _ => .unknown .malformed
  | .unknown cause => .unknown cause
  | .poison cause => .unknown cause

def FlatContext.resolveTemporalNumericOperandBy (context : FlatContext)
    (field : FlatTemporalField) (project : TemporalValue → Option Rat) : NumericOperand :=
  (context.observeValidationAt field.id).asTemporalNumericOperand field project

/-- Numeric Year extraction observes a clock's 1970 anchor; Base Year admits the operation
but does not replace that anchor (spec/05 §3, KF261). Other Date components still need a Date payload. -/
def DateNumericPart.projectTemporal? (part : DateNumericPart) : TemporalValue → Option Rat
  | .time _ _ => if part == .year then some 1970 else none
  | value => value.dateParts?.map part.extract

/-- Resolve one checked field holding a date for direct numeric date-component extraction. -/
def FlatContext.resolveDateNumericOperand (context : FlatContext)
    (field : FlatTemporalField) (part : DateNumericPart) : NumericOperand :=
  context.resolveTemporalNumericOperandBy field part.projectTemporal?

/-- Resolve one checked field holding a clock for direct numeric clock-component extraction. -/
def FlatContext.resolveTimeNumericOperand (context : FlatContext)
    (field : FlatTemporalField) (part : TimeNumericPart) : NumericOperand :=
  context.resolveTemporalNumericOperandBy field fun value => value.time?.map part.extract

/-- The seven direct scalar temporal component functions, grouped by the source half they project. -/
inductive TemporalNumericPart where
  | date (part : DateNumericPart)
  | time (part : TimeNumericPart)
  deriving Repr, DecidableEq

namespace TemporalNumericPart

/-- Static **component** admission for one direct temporal numeric function.

    The declared kind is deliberately not read. Measured on both extraction families with each kind
    on both sides of both outcomes: `HoursFromTime` admits a DATE-declared `HH:mm:ss` field and
    refuses a TIME-declared `yyyy-MM-dd` one, `YearFromDate` does the exact opposite, and the
    Kernel's own code names the format — `MVK_WRONG_DATE_FORMAT_FOR_OP`
    ([checkpoint](../../docs/sources/computation-placement-and-constant-probes.md#src-temporal-operand-family-is-the-formats-not-the-kinds)).
    The component test was already the whole rule; the kind conjunct this replaced refused two of
    those four rows for a reason the Kernel does not have. -/
def admittedBy (part : TemporalNumericPart) (field : FlatTemporalField)
    (hasBaseYear : Bool) : Bool :=
  match part with
  | .date datePart => datePart.admittedBy hasBaseYear field.components
  | .time timePart => timePart.admittedBy field.components

/-- Extract the selected amount from the matching decoded payload half. -/
def project? (part : TemporalNumericPart) (value : TemporalValue) : Option Rat :=
  match part with
  | .date datePart => datePart.projectTemporal? value
  | .time timePart => value.time?.map timePart.extract

end TemporalNumericPart

/-- Validation-phase projection through the existing Date and Time operand owners. -/
def FlatContext.resolveTemporalNumericOperand (context : FlatContext)
    (field : FlatTemporalField) : TemporalNumericPart → NumericOperand
  | .date part => context.resolveDateNumericOperand field part
  | .time part => context.resolveTimeNumericOperand field part

/-- Resolve one already-selected local calendar label through the injected model-zone capability without imposing stored-Date admission. -/
def FlatContext.resolveLocalDateComparisonOperand
    (context : FlatContext) (zoneId : String) (parts : DateParts) :
    SimpleComparisonOperand Instant :=
  match context.world.bind (fun world =>
    world.resolveLocal? zoneId parts.year parts.month parts.day 0 0 0) with
  | some instant => .value instant true
  | none => .unknown .malformed

/-- Date-free comparisons observe wall-clock components, independent of the storage anchor
(spec/05 and the cross-kind temporal-read checkpoint). -/
def FlatTemporalField.comparisonCoordinate? (field : FlatTemporalField) (value : TemporalValue) : Option Instant :=
  if field.components.hasDate then some value.instant
  else value.time?.map fun time => Instant.ofEpochSecond time.secondsSinceMidnight

def FlatTemporalOperand.resolve (context : FlatContext) : FlatTemporalOperand →
    SimpleComparisonOperand Instant
  | .fieldValue field => context.resolveTemporalFieldBy field field.comparisonCoordinate? .validation
  | .literalValue instant _ => .value instant true
  | .timeValue value => .value (Instant.ofEpochSecond value.secondsSinceMidnight) true
  | .localDateTimeValue profile label =>
      match profile.resolveCalendarLabel? label with
      | some instant => .value instant true
      | none => .unknown .malformed
  | .grouped source => source.resolve context
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

/-- Constants use the existing world interpretation; fields retain the caller's observation phase (spec/02, spec/05). -/
def FlatTemporalOperand.resolveAt (context : FlatContext) (phase : Phase) :
    FlatTemporalOperand → SimpleComparisonOperand Instant
  | .fieldValue field => context.resolveTemporalFieldBy field field.comparisonCoordinate? phase
  | .grouped source => source.resolveAt context phase
  | operand => operand.resolve context

/-- A local literal resolves when reached, not at admission (spec/07 §3). The legacy observation
projection above cannot report a runtime exception; effectful consumers use this read. -/
def FlatTemporalOperand.resolveResultAt (context : FlatContext) (phase : Phase) :
    FlatTemporalOperand → Except Unit (SimpleComparisonOperand Instant)
  | .localDateTimeValue profile label =>
      match profile.resolveCalendarLabel? label with
      | some instant => pure (.value instant true)
      | none => throw ()
  | .grouped source => source.resolveResultAt context phase
  | operand => pure (operand.resolveAt context phase)

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

/-- A present String member's cell with its raw placeholder applied; every other cell is unchanged. -/
def FlatTextFieldOperand.placeholderToken : FlatTextFieldOperand → ValueListCell .token → ValueListCell .token
  | .string field, .present value => .present (field.token value)
  | _, cell => cell

def FlatTextFieldOperand.valueListCell (operand : FlatTextFieldOperand)
    (context : FlatContext) : ValueListCell .token :=
  operand.placeholderToken (operand.resolve context).asTokenValueListCell

/-- Project a phase-resolved String or Enumeration observation without rechecking its stored
value; index selection and ordinary rows retain the same declaration-owned token identity. -/
def FlatTextFieldOperand.observedValueListCell
    (operand : FlatTextFieldOperand) (observation : CellObservation) :
    ValueListCell .token :=
  match operand with
  | .string field =>
      match observation with
      | .empty => .empty
      | .value (.str value) =>
          if value.isEmpty then .empty else .present (field.token value)
      | .value _ => .unknown .malformed
      | .unknown cause | .poison cause => .unknown cause
  | FlatTextFieldOperand.enumeration enumOperand =>
      enumOperand.projection.asValueListCell observation

def FlatTextFieldOperand.checkedValueListCellAt
    (operand : FlatTextFieldOperand) (phase : Phase) (cell : CheckedCell) :
    ValueListCell .token :=
  operand.observedValueListCell (observeCell phase cell)

def flatTokenValueListSide (operands : List FlatTextFieldOperand)
    (context : FlatContext) : ResolvedValueListSide .token :=
  { cells := operands.map (·.valueListCell context)
    hasUninstantiatedTail := false
    hasHaving := false }

/-- Classify only relevant flat textual operands, retaining whether any operand was masked so the shared quantifier core can apply its operator-specific UNKNOWN rule. Filtering precedes every field read. -/
def selectedFlatTokenValueListSide (operands : List FlatTextFieldOperand)
    (context : FlatContext) (isRelevant : FlatRelevance) :
    ResolvedValueListQuantifierSide .token :=
  { side := flatTokenValueListSide
      (operands.filter fun operand => isRelevant operand.field.id) context
    hasNonRelevant := operands.any fun operand => !isRelevant operand.field.id }

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

def FlatTokenValueSide.resolveSelected (side : FlatTokenValueSide)
    (context : FlatContext) (isRelevant : FlatRelevance) :
    ResolvedValueListQuantifierSide .token :=
  match side with
  | .literals values => .ofResolved (literalTokenValueListSide values)
  | .fields operands => selectedFlatTokenValueListSide operands context isRelevant

def FlatTokenValueSide.allOperands (values : FlatTokenValueSide)
    (fields : List FlatTextFieldOperand) : List FlatTextFieldOperand :=
  fields ++ values.operands

/-- Classify a phase-indexed Number observation for a list consumer without applying that consumer's empty-value rule. Validation unknown and computation poison retain the same exact formal cause at this shared intermediate boundary. -/
def CellObservation.asNumberValueListCell :
    CellObservation Value → ValueListCell .number
  | .empty => .empty
  | .value (.num amount) => .present amount
  | .value _ => .unknown .malformed
  | .unknown cause => .unknown cause
  | .poison cause => .unknown cause

/-- Classify one direct Number list cell at the caller's phase without applying an aggregate-specific empty rule. -/
def FlatNumberField.valueListCellAt (field : FlatNumberField)
    (phase : Phase) (context : FlatContext) : ValueListCell .number :=
  (context.observeAt phase field.id).asNumberValueListCell

/-- Validation specialization retained for established list consumers. Number value-list reads deliberately do not reuse direct comparison resolution: an empty member contributes no atom and is never substituted by zero. -/
def FlatNumberField.valueListCell (field : FlatNumberField)
    (context : FlatContext) : ValueListCell .number :=
  field.valueListCellAt .validation context

def flatNumberValueListSide (operands : List FlatNumberField)
    (context : FlatContext) : ResolvedValueListSide .number :=
  { cells := operands.map (·.valueListCell context)
    hasUninstantiatedTail := false
    hasHaving := false }

/-- Number operands use the same relevance-before-read construction as textual operands; the distinction is retained outside `ValueListCell` so formal causes and partial nonrelevance cannot be conflated. -/
def selectedFlatNumberValueListSide (operands : List FlatNumberField)
    (context : FlatContext) (isRelevant : FlatRelevance) :
    ResolvedValueListQuantifierSide .number :=
  { side := flatNumberValueListSide
      (operands.filter fun operand => isRelevant operand.id) context
    hasNonRelevant := operands.any fun operand => !isRelevant operand.id }

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

def FlatNumberValueSide.resolveSelected (side : FlatNumberValueSide)
    (context : FlatContext) (isRelevant : FlatRelevance) :
    ResolvedValueListQuantifierSide .number :=
  match side with
  | .literals values => .ofResolved (literalNumberValueListSide values)
  | .fields operands => selectedFlatNumberValueListSide operands context isRelevant

def FlatNumberValueSide.allOperands (values : FlatNumberValueSide)
    (fields : List FlatNumberField) : List FlatNumberField :=
  fields ++ values.operands

/-- Whether one atomic flat condition references a field ID. -/
def FlatConditionLeaf.referencesField : FlatConditionLeaf → FieldId → Bool
  | .compare comparison, field => comparison.fieldIds.contains field
  | .tokenValueList _ operands values _, field =>
      (values.allOperands operands).any fun operand => operand.field.id == field
  | .numberValueList _ operands values _, field =>
      (values.allOperands operands).any fun operand => operand.id == field
  | .fieldFilled referenced, field
  | .fieldNotFilled referenced, field => referenced.id == field

/-- Reference traversal ignores connective shape and checks both branches. -/
def FlatCondition.referencesField (condition : FlatCondition) (field : FieldId) : Bool :=
  condition.anyLeaf fun leaf => leaf.referencesField field

def FlatBooleanOperand.resolveAt (operand : FlatBooleanOperand) (phase : Phase)
    (context : FlatContext) : SimpleComparisonOperand Bool :=
  match operand with
  | .boolean field => context.resolveBooleanComparisonOperandAt phase field
  | .confirm field => context.resolveConfirmComparisonOperandAt phase field

/-- Stored ranges use their exact-or-yearless identity domain (spec/05); phase observation owns
empty and unavailable values, just as for other typed scalar comparisons. -/
def FlatContext.resolveDateRangeComparisonOperandAt (context : FlatContext)
    (phase : Phase) (field : FlatDateRangeField) : SimpleComparisonOperand DateRangeCellValue :=
  match context.observeAt phase field.id with
  | .empty => .notEvaluated
  | .value (.dateRange value) => .value value true
  | .value _ => .unknown .malformed
  | .unknown cause | .poison cause => .unknown cause

def FlatComparison.eval (comparison : FlatComparison) (context : FlatContext) : Verdict :=
  match comparison with
  | .number op field expected =>
      op.evalFixedRight (context.resolveNumberComparisonOperand field) expected
  | .boolean op field expected =>
      op.evalSimple (· == ·) (context.resolveBooleanComparisonOperand field) expected
  | .confirm op field =>
      op.evalSimple (· == ·) (context.resolveConfirmComparisonOperand field) true
  | .booleanFields op left right =>
      op.evalSymmetric (· == ·) (left.resolveAt .validation context) (right.resolveAt .validation context)
  | .string op field expected =>
      (context.resolveDirectStringComparisonOperand field).evalTextLiteral op expected
  | .stringLength op field expected =>
      op.toNumeric.evalFixedRight (context.resolveStringLengthOperand field) expected
  | .enumeration op operand expected =>
      operand.projection.evalLiteral op
        (context.observeValidationAt operand.field.id) expected
  | .textFields op left right =>
      op.evalSymmetric (· == ·) (left.resolve context) (right.resolve context)
  | .dateRange op left right =>
      op.evalDateRangeCellValues (context.resolveDateRangeComparisonOperandAt .validation left)
        (context.resolveDateRangeComparisonOperandAt .validation right)
  | .temporal op left right =>
      op.evalInstant (left.resolve context) (right.resolve context)
  | .time op left right =>
      op.evalTime (context.resolveTimeComparisonOperand left)
        (context.resolveTimeComparisonOperand right)

def FlatField.observeValidation (context : FlatContext) : FlatField → CellObservation
  | .number field => context.observeValidationAt field.id
  | .boolean field => context.observeValidationAt field.id
  | .confirm field => context.observeValidationAt field.id
  | .string field => context.observeValidationAt field.id
  | .enumeration field => context.observeValidationAt field.id
  | .temporal field => context.observeValidationAt field.id
  | .dateRange field => context.observeValidationAt field.id

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

/-- Presence of one field selected by ordinary iteration or semantic index shares the scalar
observation and omission rules (`spec/03` §2). -/
inductive RepeatableFieldPresenceOperator where
  | filled
  | notFilled
  deriving Repr, DecidableEq

namespace RepeatableFieldPresenceOperator

def canFireOnEmpty : RepeatableFieldPresenceOperator → Bool
  | .filled => false
  | .notFilled => true

def eval (operator : RepeatableFieldPresenceOperator)
    (observation : CellObservation) : Verdict :=
  match operator with
  | .filled => observation.evalValidationFilled
  | .notFilled => observation.evalValidationNotFilled

end RepeatableFieldPresenceOperator

def FlatField.evalFilled (field : FlatField) (context : FlatContext) : Verdict :=
  (field.observeValidation context).evalValidationFilled

def FlatField.evalNotFilled (field : FlatField) (context : FlatContext) : Verdict :=
  (field.observeValidation context).evalValidationNotFilled

/-- Evaluate one atomic flat condition. Out-of-set scalar reads become validation-unknown before `context.read`; value-list operands retain nonrelevance separately for their operator-specific per-cell rules. Connective evaluation remains in `ConditionTree.evalVerdict`. -/
@[simp] def FlatConditionLeaf.evalSelected (context : FlatContext)
    (isRelevant : FlatRelevance := fun _ => true) : FlatConditionLeaf → Verdict
  | .compare comparison =>
      if comparison.allRelevant isRelevant then comparison.eval context else .unknown
  | .tokenValueList quantifier operands values _ =>
      quantifier.evalClassified
        (selectedFlatTokenValueListSide operands context isRelevant)
        (values.resolveSelected context isRelevant)
  | .numberValueList quantifier operands values _ =>
      quantifier.evalClassified
        (selectedFlatNumberValueListSide operands context isRelevant)
        (values.resolveSelected context isRelevant)
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
