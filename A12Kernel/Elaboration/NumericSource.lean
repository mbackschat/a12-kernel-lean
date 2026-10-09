import A12Kernel.Semantics.DateDifferenceSource
import A12Kernel.Semantics.NumericAggregate
import A12Kernel.Elaboration.TemporalNumericInput
import A12Kernel.Elaboration.NumericExpression
import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Elaboration.StaticDiagnostic
import A12Kernel.Semantics.DateDifference
import A12Kernel.Semantics.DateTimeDifference
import A12Kernel.Semantics.String
import A12Kernel.Semantics.NumericConversion

/-! # Shared checked numeric-expression sources

Validation and computation both consume Number-field references, numeric `BaseYear`, direct numeric date-component extraction from a Base-Year date source, direct Date/Time/DateTime field-component sources, checked ordinary String/Enumeration/category conversion, Date-only month/year differences, exact-instant DateTime field/`Now` hour/minute/second differences, and direct resolved Number field-list aggregates through the same authored expression tree. Consumer-specific field resolution, model coherence, explicit-world injection, and runtime reads remain with each checked owner.
-/

namespace A12Kernel

inductive FieldValueAsNumberSourceError where
  | notConvertible
  | unsupportedSource
  | enumeration (error : EnumerationOperandError)
  | incoherentEnumeration
  deriving Repr, DecidableEq

/-- Project the covered conversion gate only; category resolution and local projection limits do not establish this class ([kernel lock index](../../docs/sources/kernel-locks.md#src-kernel-lock-index)). -/
def FieldValueAsNumberSourceError.diagnostic? :
    FieldValueAsNumberSourceError → Option KernelStaticDiagnostic
  | .notConvertible => some .noConvertInNumber
  | _ => none

/-- Admit one exact bounded value-validating String or ordinary closed Enumeration/category source after field/path resolution. -/
def FlatFieldDecl.resolveFieldValueAsNumberSource
    (declaration : FlatFieldDecl) (projectionRef : EnumerationProjectionRef) :
    Except FieldValueAsNumberSourceError ResolvedFieldValueAsNumberSource :=
  match declaration.customType, declaration.policy.kind,
      declaration.enumeration, projectionRef with
  | none, .string, none, .stored =>
      match declaration.toStringValueField?, declaration.stringPatternSource,
          declaration.stringPolicy.maxLength with
      | some field, some pattern, some maximum =>
          if pattern == asciiDigitsPatternSource &&
              maximum ≤ maxFieldValueAsNumberDigits then
            .ok { operand := .string field, scale := 0 }
          else
            .error .notConvertible
      | none, _, _ => .error .unsupportedSource
      | some _, _, _ => .error .notConvertible
  | none, .enumeration, some source, _ =>
      match elaborateEnumeration source with
      | .error _ => .error .incoherentEnumeration
      | .ok checked =>
          match checkEnumerationProjection checked projectionRef with
          | .error error => .error (.enumeration error)
          | .ok projection =>
              match projection.numericScale? with
              | none => .error .notConvertible
              | some scale => .ok {
                  operand := .enumeration {
                    field := { id := declaration.id }
                    projectionRef := projection.projectionRef
                    projection := projection.projection }
                  scale }
  | _, _, _, _ => .error .unsupportedSource

/-- Recover the exact model declaration only when it re-derives the complete resolved conversion source. This keeps forged projections, nonnumeric domains, and scale summaries outside every checked consumer. -/
def FlatModel.certifiedFieldValueAsNumberDeclaration?
    (model : FlatModel) (source : ResolvedFieldValueAsNumberSource) :
    Option FlatFieldDecl :=
  match model.lookupUniqueId source.fieldId with
  | .error _ => none
  | .ok declaration =>
      match declaration.resolveFieldValueAsNumberSource source.projectionRef with
      | .error _ => none
      | .ok resolved =>
          if resolved == source then some declaration else none

/-- Admit a certified conversion source at the existing nonrepeatable scalar boundary. Addressed repeatable consumers retain their separate scope check. -/
def FlatModel.admitsFieldValueAsNumberSource (model : FlatModel)
    (source : ResolvedFieldValueAsNumberSource) : Bool :=
  match model.certifiedFieldValueAsNumberDeclaration? source with
  | some declaration => declaration.repeatableScope.isEmpty
  | none => false

namespace AuthoredDateLiteral

/-- Certify both the authored calendar and the model's completion year at checked entry points. -/
def admittedIn (literal : AuthoredDateLiteral) (model : FlatModel) (anchorYear : Int) : Bool :=
  literal.valid && anchorYear == model.baseYearOrDefault

/-- Literal validity uses the authored common-year rule; runtime completion uses the model's shared anchor (spec/05 §1). Year agreement remains an admission question for the consuming operator. -/
def completedDate? (literal : AuthoredDateLiteral) (model : FlatModel) : Option CivilDate := do
  if !literal.valid then none
  let parts := literal.parts model.baseYearOrDefault
  CivilDate.ofYmd? parts.year parts.month parts.day

def comparisonInstant? (literal : AuthoredDateLiteral) (model : FlatModel) : Option Instant := do
  let civil ← literal.completedDate? model
  let profile ← ModelZone.ConcreteProfile.ofId? model.timeZoneId
  let value ← profile.resolveStoredDate? civil
  pure value.instant

end AuthoredDateLiteral

inductive SurfaceDateDifferenceOperand (Field : Type := SurfaceFieldPath) where
  | literal (source : AuthoredDateLiteral)
  | field (path : Field)
  | baseYear (source : BaseYearDateSource)
  | now
  | today
  deriving Repr, DecidableEq

def SurfaceDateDifferenceOperand.fields : SurfaceDateDifferenceOperand Field → List Field
  | .field source => [source]
  | .literal _ | .baseYear _ | .now | .today => []

namespace ResolvedDateDifferenceOperand

def isField : ResolvedDateDifferenceOperand → Bool
  | .literal _ _ => false
  | .field _ => true
  | .baseYear _ _ | .today _ => false

def components : ResolvedDateDifferenceOperand → TemporalComponents :=
  componentsWith (·.components)

def references (field : FieldId) : ResolvedDateDifferenceOperand → Bool
  | .literal _ _ => false
  | .field source => source.id == field
  | .baseYear _ _ | .today _ => false

def validationOperand (context : FlatContext) :
    ResolvedDateDifferenceOperand → DateDifferenceOperand
  | .literal source year => .value (source.parts year)
  | .field source => DateDifferenceOperand.ofObservation
      (context.observeValidationAt source.id)
  | .baseYear year source => .value (source.parts year)
  | .today profile => match todayParts? profile context.world with
      | some parts => .value parts
      | none => .unavailable .malformed

def calendarDayValidationOperand (profile : ModelZone.ConcreteProfile)
    (context : FlatContext) :
    ResolvedDateDifferenceOperand → CalendarDayDifferenceOperand
  | .literal source year => CalendarDayDifferenceOperand.ofParts profile (source.parts year)
  | .field source => CalendarDayDifferenceOperand.ofObservation
      (context.observeValidationAt source.id)
  | .baseYear year source =>
      CalendarDayDifferenceOperand.ofBaseYear profile year source
  | .today sourceProfile => match todayParts? sourceProfile context.world with
      | some parts => CalendarDayDifferenceOperand.ofParts sourceProfile parts
      | none => .unavailable .malformed

end ResolvedDateDifferenceOperand

namespace FlatTemporalOperand

/-- The static component identity of an admitted sub-day operand. Other temporal comparison operands remain outside the checked difference route. -/
def dateTimeDifferenceComponents? : FlatTemporalOperand → Option TemporalComponents :=
  dateTimeDifferenceComponentsWith? (·.components)

/-- Whether an admitted sub-day operand reads one exact document field. -/
def dateTimeDifferenceReferences
    (operand : FlatTemporalOperand) (field : FieldId) : Bool :=
  operand.fields.any (·.id == field)

end FlatTemporalOperand

/-- A parser-independent direct Number aggregate field list. Checked direct-list admission requires at least two entries; starred/group operands expand through separate owners. -/
structure SurfaceNumericAggregateFields where
  first : SurfaceFieldPath
  rest : List SurfaceFieldPath
  deriving Repr, DecidableEq

/-- One nonempty resolved Number aggregate source in authored encounter order. -/
structure ResolvedNumericAggregateFields where
  first : FlatNumberField
  rest : List FlatNumberField
  deriving Repr, DecidableEq

namespace ResolvedNumericAggregateFields

def fields (source : ResolvedNumericAggregateFields) : List FlatNumberField :=
  source.first :: source.rest

def hasMultipleFields (source : ResolvedNumericAggregateFields) : Bool :=
  !source.rest.isEmpty

def firstDuplicateFieldId? : List FieldId → Option FieldId :=
  FieldId.firstDuplicate?

def firstDuplicate? (source : ResolvedNumericAggregateFields) : Option FieldId :=
  firstDuplicateFieldId? (source.fields.map (·.id))

def hasUniqueFields (source : ResolvedNumericAggregateFields) : Bool :=
  source.firstDuplicate?.isNone

/-- Field-list aggregates derive the maximum contributing declaration scale and never gain literal expansion capability. -/
def scaleSummary (source : ResolvedNumericAggregateFields) :
    NumericScaleSummary :=
  source.rest.foldl
    (fun summary field => summary.union (NumericScaleSummary.field field.info.scale))
    (NumericScaleSummary.field source.first.info.scale)

end ResolvedNumericAggregateFields

namespace NumericAggregateOp

/-- Ordinary value aggregates retain the union of contributing declaration scales; a distinct count is an integral result independently of operand scale. -/
def scaleSummary (op : NumericAggregateOp)
    (source : ResolvedNumericAggregateFields) : NumericScaleSummary :=
  match op with
  | .sum | .minimum | .maximum => source.scaleSummary
  | .distinctCount => NumericScaleSummary.field 0

end NumericAggregateOp

/-- Scalar repetition operands retain group identity for checked re-elaboration; fixed value alone
    does not establish the binding boundary in `spec/07` §3. -/
def ResolvedGroupReference.scalarRepetitionWellFormedBool
    (reference : ResolvedGroupReference) (model : FlatModel) : Bool :=
  reference.origin == .path && reference.boundRepeatableScope.isEmpty &&
    reference.fixedWellFormedBool model reference.path

def BoundCurrentRepetitionSource.wellFormedIn
    (source : BoundCurrentRepetitionSource) (model : FlatModel)
    (available : List RepeatableLevel) : Bool :=
  model.hasGroupPath source.path && !source.scope.isEmpty &&
    source.scope == model.repeatableScopeForGroupPath source.path &&
    source.scope.isPrefixOf available &&
    source.level == (model.repeatableGroups.find? (·.path == source.path)).map (·.level)

inductive SurfaceNumericAtom
    (Aggregate : Type := SurfaceNumericAggregateFields) where
  | field (path : SurfaceFieldPath)
  | currentRepetition (path : SurfaceGroupPath)
  | baseYear
  | baseYearDatePart (source : BaseYearDateSource) (part : DateNumericPart)
  | temporalFieldPart (path : SurfaceFieldPath) (part : TemporalNumericPart)
  /-- One numeric date component of a DateRange field's selected endpoint. The endpoint selection
  and the component are one authored operand, because the endpoint alone is not a numeric value. -/
  | dateRangeBoundPart (path : SurfaceFieldPath) (bound : DateRangeBound)
      (part : DateNumericPart)
  | stringLength (path : SurfaceFieldPath)
  | stringRange (path : SurfaceFieldPath) (start finish : Nat)
  | fieldValueAsNumber (source : SurfaceTextFieldOperand)
  | dateDifference (unit : DateDifferenceUnit)
      (left right : SurfaceDateDifferenceOperand)
  | dateTimeDifference (unit : DateTimeSubdayUnit)
      (left right : SurfaceDateDifferenceOperand)
  | dayDifference (left right : SurfaceDateDifferenceOperand)
  | aggregate (op : NumericAggregateOp) (source : Aggregate)
  | filledGroupCount (operands : List SurfaceGroupCountOperand)
  deriving Repr, DecidableEq

inductive ResolvedNumericAtom (Field : Type)
    (Aggregate : Type := ResolvedNumericAggregateFields) where
  | field (source : Field)
  | fixedCurrentRepetition (reference : ResolvedGroupReference)
  | boundCurrentRepetition (source : BoundCurrentRepetitionSource)
  | baseYear (year : Int)
  | baseYearDatePart (year : Int) (source : BaseYearDateSource)
      (part : DateNumericPart)
  | temporalFieldPart (source : FlatTemporalField) (part : TemporalNumericPart)
      (partialFormat : Option FullDateTargetFormat := none)
  | dateRangeBoundPart (source : FlatDateRangeField) (bound : DateRangeBound)
      (part : DateNumericPart)
  | stringLength (source : FlatStringField)
  | stringRange (source : FlatStringField) (start finish : Nat)
  | fieldValueAsNumber (source : ResolvedFieldValueAsNumberSource)
  | dateDifference (unit : DateDifferenceUnit)
      (left right : ResolvedDateDifferenceOperand)
  | dateTimeDifference (unit : DateTimeSubdayUnit)
      (left right : FlatTemporalOperand)
  | dayDifference (profile : ModelZone.ConcreteProfile)
      (left right : ResolvedDateDifferenceOperand)
  | aggregate (op : NumericAggregateOp) (source : Aggregate)
  | filledGroupCount (groups : List ResolvedGroupReference)
  deriving Repr, DecidableEq

/-- The group and field path of a `CurrentRepetition` operand that names a field rather than a
    group. Its group answers first: from a root rule the field of an uniterated repeatable group
    draws that group's missing star and the field of a fixed group the field class
    ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-current-repetition)). -/
def FlatModel.currentRepetitionNamedField? (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceGroupPath) : Option (SurfaceGroupPath × List String) := do
  let path ← (reference.resolveAgainst declaringGroup).toOption
  if model.hasGroupPath path || !model.fields.any (·.path == path) then none
  else some ({ reference with groups := reference.groups.dropLast }, path)

private def FlatModel.resolveNumericCurrentRepetitionGroup (model : FlatModel)
    (declaringGroup : GroupPath) (available : List RepeatableLevel)
    (reference : SurfaceGroupPath) :
    Except FixedGroupReferenceError (ResolvedNumericAtom Field Aggregate) := do
  let path ← reference.resolveAgainst declaringGroup |>.mapError .reference
  if !model.hasGroupPath path then throw (model.unknownGroupError path)
  let scope := model.repeatableScopeForGroupPath path
  if scope.isEmpty then
    return .fixedCurrentRepetition
      (← model.resolveFixedGroupReference declaringGroup (.path reference))
  let source : BoundCurrentRepetitionSource :=
    { path, scope, level := (model.repeatableGroups.find? (·.path == path)).map (·.level) }
  if source.wellFormedIn model available then
    pure (.boundCurrentRepetition source)
  else
    throw (.repeatableGroupRequiresAddress path)

/-- Resolve structural identity against an explicit binding scope. Validation supplies its host
    scope; computation supplies its target scope, retaining that carrier choice at the call site. -/
def FlatModel.resolveNumericCurrentRepetition (model : FlatModel)
    (declaringGroup : GroupPath) (available : List RepeatableLevel)
    (reference : SurfaceGroupPath) :
    Except FixedGroupReferenceError (ResolvedNumericAtom Field Aggregate) :=
  match model.currentRepetitionNamedField? declaringGroup reference with
  | some (group, fieldPath) => do
      let _ : ResolvedNumericAtom Field Aggregate ←
        model.resolveNumericCurrentRepetitionGroup declaringGroup available group
      throw (.fieldNamedAsGroup fieldPath)
  | none => model.resolveNumericCurrentRepetitionGroup declaringGroup available reference

namespace ResolvedNumericAtom

def summaryWith (fieldSummary : Field → NumericScaleSummary)
    (aggregateSummary : NumericAggregateOp → Aggregate → NumericScaleSummary) :
    ResolvedNumericAtom Field Aggregate → NumericScaleSummary
  | .field source => fieldSummary source
  | .fixedCurrentRepetition _ => NumericScaleSummary.field 0
  | .boundCurrentRepetition _ => NumericScaleSummary.field 0
  | .baseYear _ => NumericScaleSummary.field 0
  | .baseYearDatePart _ _ _ => NumericScaleSummary.field 0
  | .temporalFieldPart _ _ _ => NumericScaleSummary.field 0
  | .dateRangeBoundPart _ _ _ => NumericScaleSummary.field 0
  | .stringLength _ => NumericScaleSummary.field 0
  | .stringRange _ _ _ => NumericScaleSummary.field 0
  | .fieldValueAsNumber source => NumericScaleSummary.field source.scale
  | .dateDifference _ _ _ => NumericScaleSummary.field 0
  | .dateTimeDifference _ _ _ => NumericScaleSummary.field 0
  | .dayDifference _ _ _ => NumericScaleSummary.field 0
  | .aggregate op source => aggregateSummary op source
  | .filledGroupCount _ => NumericScaleSummary.field 0

def summary (fieldSummary : Field → NumericScaleSummary) :
    ResolvedNumericAtom Field → NumericScaleSummary :=
  summaryWith fieldSummary NumericAggregateOp.scaleSummary

end ResolvedNumericAtom


end A12Kernel
