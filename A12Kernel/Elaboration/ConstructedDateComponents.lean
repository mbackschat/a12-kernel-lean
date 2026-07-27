import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Semantics.DateNumeric
import A12Kernel.Semantics.ModelZone
import A12Kernel.Semantics.String

/-! # Checked direct constructed Dates

This capsule certifies direct nonrepeatable `Date` components backed by ordinary Number fields, pattern-backed String fields, the complete-Year `yyyy` Date field, admitted quoted constants, or matching Date/DateTime field extractors, plus the two-argument Base-Year specialization, for model-owned UTC or GMT. Each field position keeps the kernel checker's exact stored-width, numeric-maximum, or Year-only format gate; each constant keeps the pinned Java host's decimal-digit profile and its positional width and range gate; each extractor reuses the shared temporal component admission; the omitted year is the fixed model Base Year; and the split year is `century * 100 + shortYear`.

The extensible-enumeration String alternative, recursive extractor operands, other model zones, repeatable placement, targets, and a general temporal-expression tree remain outside.
-/

namespace A12Kernel

/-- The declaration gate selected by a direct Number-field Date component position. -/
inductive ConstructedDateComponentPosition where
  | day
  | month
  | year
  | century
  | shortYear
  deriving Repr, DecidableEq

namespace ConstructedDateComponentPosition

/-- Complete stored width accepted as an alternative to the positional numeric maximum. -/
def storedWidth : ConstructedDateComponentPosition → Nat
  | .day | .month | .century | .shortYear => 2
  | .year => 4

/-- Whether one explicit maximum satisfies the position-specific checker branch. Complete years deliberately accept the kernel's flexible 1000–9999 range. -/
def admitsMaximum (position : ConstructedDateComponentPosition) :
    Option Rat → Bool
  | some maximum =>
      match position with
      | .day => maximum == 31
      | .month => maximum == 12
      | .year => decide (1000 ≤ maximum ∧ maximum ≤ 9999)
      | .century => decide (10 ≤ maximum ∧ maximum ≤ 99)
      | .shortYear => maximum == 99
  | none => false

/-- Exact parser boundary for one quoted constant under the pinned Java 21 host profile. Day and Month have no width gate; every year form does. -/
def decodeConstant? (position : ConstructedDateComponentPosition)
    (source : String) : Option Int := do
  let value ← parseJava21BmpNatural? source
  let widthAccepted := match position with
    | .day | .month => true
    | .year => utf16CodeUnitLength source == 4
    | .century | .shortYear => utf16CodeUnitLength source == 2
  let rangeAccepted := match position with
    | .day => 1 ≤ value && value < 32
    | .month => 1 ≤ value && value < 13
    | .year => 1800 ≤ value && value < 2200
    | .century => 18 ≤ value && value < 22
    | .shortYear => value < 100
  if widthAccepted && rangeAccepted then
    some value
  else
    none

/-- The only direct Date extractor that may occupy this constructor position. Split-year positions support no extractor. -/
def extractor? : ConstructedDateComponentPosition → Option DateNumericPart
  | .day => some .day
  | .month => some .month
  | .year => some .year
  | .century | .shortYear => none

end ConstructedDateComponentPosition

/-- One grammar-valid direct component source before model-relative checking. -/
inductive SurfaceConstructedDateSource where
  | numberField (field : FieldId)
  | stringField (field : FieldId)
  | dateYearField (field : FieldId)
  | constant (source : String)
  | extractor (part : DateNumericPart) (field : FieldId)
  deriving Repr, DecidableEq

/-- The three legal authored year shapes before model-relative checking. -/
inductive SurfaceConstructedDateYear where
  | complete (source : SurfaceConstructedDateSource)
  | baseYear
  | centuryAndShortYear
      (century shortYear : SurfaceConstructedDateSource)
  deriving Repr, DecidableEq

/-- One complete direct Date source in generated component order. -/
structure SurfaceConstructedDateComponents where
  day : SurfaceConstructedDateSource
  month : SurfaceConstructedDateSource
  year : SurfaceConstructedDateYear
  deriving Repr, DecidableEq

/-- Exact Number declaration gate for one direct three-field Date component. -/
def FlatModel.admitsConstructedDateNumberField (model : FlatModel)
    (position : ConstructedDateComponentPosition)
    (source : FlatNumberField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      let constraints := declaration.numericTargetConstraints
      declaration.repeatableScope.isEmpty &&
        declaration.toNumberField? == some source &&
        source.info.scale == 0 &&
        constraints.minFractionalDigits == 0 &&
        (constraints.maxStoredLength == some position.storedWidth ||
          position.admitsMaximum constraints.maximum) &&
        declaration.numberDomainNonnegative source

/-- One ordinary Number field carrying its exact Date-component certificate. -/
structure CheckedConstructedDateNumberField (model : FlatModel) where
  position : ConstructedDateComponentPosition
  source : FlatNumberField
  admitted : model.admitsConstructedDateNumberField position source = true

/-- Exact pattern-backed String declaration gate for one direct Date component. Extensible-enumeration admission is deliberately not represented here. -/
def FlatModel.admitsConstructedDateStringField (model : FlatModel)
    (position : ConstructedDateComponentPosition)
    (source : FlatStringField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.toStringValueField? == some source &&
        declaration.customType.isNone &&
        declaration.enumeration.isNone &&
        declaration.stringPolicy.maxLength == some position.storedWidth &&
        declaration.stringPatternSource.any
          (isTemporalComponentDigitPattern position.storedWidth)

/-- One ordinary checked String field under the position's exact digit-pattern and stored-width gate. -/
structure CheckedConstructedDateStringField (model : FlatModel) where
  position : ConstructedDateComponentPosition
  source : FlatStringField
  admitted :
    model.admitsConstructedDateStringField position source = true

/-- Exact direct Date-field gate used only by the complete-Year constructor position. The retained policy is part of the certificate because component flags do not imply the literal `yyyy` format. -/
def FlatModel.admitsConstructedDateYearField (model : FlatModel)
    (position : ConstructedDateComponentPosition)
    (source : FlatTemporalField) (policy : TemporalTargetPolicy) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.toTemporalField? == some source &&
        declaration.toTemporalTargetPolicy? == some policy &&
        position == .year &&
        source.kind == .date &&
        policy.format == "yyyy"

/-- One complete-Year Date field with the exact model-owned `yyyy` declaration policy. -/
structure CheckedConstructedDateYearField (model : FlatModel) where
  position : ConstructedDateComponentPosition
  source : FlatTemporalField
  policy : TemporalTargetPolicy
  admitted :
    model.admitsConstructedDateYearField position source policy = true

/-- Exact direct Date/DateTime field gate for one matching Date-component extractor. -/
def FlatModel.admitsConstructedDateExtractorField (model : FlatModel)
    (position : ConstructedDateComponentPosition) (part : DateNumericPart)
    (source : FlatTemporalField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.toTemporalField? == some source &&
        source.kind != .time &&
        position.extractor? == some part &&
        part.admittedBy model.hasBaseYear source.components

/-- One ordinary Date or DateTime field carrying the matching component-extractor certificate. -/
structure CheckedConstructedDateExtractorField (model : FlatModel) where
  position : ConstructedDateComponentPosition
  part : DateNumericPart
  source : FlatTemporalField
  admitted :
    model.admitsConstructedDateExtractorField position part source = true

/-- One checked field-backed, extractor-backed, or fixed constant component. -/
inductive CheckedConstructedDateSource (model : FlatModel) where
  | numberField (source : CheckedConstructedDateNumberField model)
  | stringField (source : CheckedConstructedDateStringField model)
  | dateYearField (source : CheckedConstructedDateYearField model)
  | constant (value : Int)
  | extractor (source : CheckedConstructedDateExtractorField model)

/-- A checked complete Year source, fixed model Base Year, or authored Century/Short-Year pair. -/
inductive CheckedConstructedDateYear (model : FlatModel) where
  | complete (source : CheckedConstructedDateSource model)
  | baseYear (year : Int)
  | centuryAndShortYear
      (century shortYear : CheckedConstructedDateSource model)

/-- The checked direct constructor plus its bounded model-zone certificate. -/
structure CheckedConstructedDateComponents (model : FlatModel) where
  day : CheckedConstructedDateSource model
  month : CheckedConstructedDateSource model
  year : CheckedConstructedDateYear model
  profileIsUtc :
    ModelZone.ConcreteProfile.ofId? model.timeZoneId =
      some .utc

/-- Static rejection before any component is read. -/
inductive ConstructedDateComponentsElabError where
  | field (position : ConstructedDateComponentPosition) (error : ResolveError)
  | sourceKind (position : ConstructedDateComponentPosition) (field : FieldId)
  | declarationNotAdmitted (position : ConstructedDateComponentPosition)
      (field : FieldId)
  | stringSourceKind
      (position : ConstructedDateComponentPosition) (field : FieldId)
  | stringDeclarationNotAdmitted
      (position : ConstructedDateComponentPosition) (field : FieldId)
  | dateYearSourceKind
      (position : ConstructedDateComponentPosition) (field : FieldId)
  | dateYearPolicyUnavailable
      (position : ConstructedDateComponentPosition) (field : FieldId)
  | dateYearDeclarationNotAdmitted
      (position : ConstructedDateComponentPosition) (field : FieldId)
  | constantNotAdmitted
      (position : ConstructedDateComponentPosition) (source : String)
  | extractorMismatch
      (position : ConstructedDateComponentPosition) (part : DateNumericPart)
  | extractorSourceKind
      (position : ConstructedDateComponentPosition) (field : FieldId)
  | extractorDeclarationNotAdmitted
      (position : ConstructedDateComponentPosition)
      (part : DateNumericPart) (field : FieldId)
  | missingBaseYear
  | unsupportedZone (zoneId : String)
  deriving Repr, DecidableEq

/-- Resolve one direct Number field and retain the position-specific declaration proof. -/
def elaborateConstructedDateNumberField
    (model : FlatModel) (position : ConstructedDateComponentPosition)
    (field : FieldId) :
    Except ConstructedDateComponentsElabError
      (CheckedConstructedDateNumberField model) := do
  let declaration ←
    model.resolveNonrepeatableDeclarationById field |>.mapError (.field position)
  let source ← match declaration.toNumberField? with
    | some source => pure source
    | none => throw (.sourceKind position field)
  if admitted :
      model.admitsConstructedDateNumberField position source = true then
    pure { position, source, admitted }
  else
    throw (.declarationNotAdmitted position field)

/-- Resolve one ordinary String field and retain the position-specific pattern and stored-width certificate. -/
def elaborateConstructedDateStringField
    (model : FlatModel) (position : ConstructedDateComponentPosition)
    (field : FieldId) :
    Except ConstructedDateComponentsElabError
      (CheckedConstructedDateStringField model) := do
  let declaration ←
    model.resolveNonrepeatableDeclarationById field |>.mapError (.field position)
  let source ← match declaration.toStringValueField? with
    | some source => pure source
    | none => throw (.stringSourceKind position field)
  if admitted :
      model.admitsConstructedDateStringField position source = true then
    pure { position, source, admitted }
  else
    throw (.stringDeclarationNotAdmitted position field)

/-- Resolve one Date field and retain the exact complete-Year `yyyy` certificate. -/
def elaborateConstructedDateYearField
    (model : FlatModel) (position : ConstructedDateComponentPosition)
    (field : FieldId) :
    Except ConstructedDateComponentsElabError
      (CheckedConstructedDateYearField model) := do
  let declaration ←
    model.resolveNonrepeatableDeclarationById field |>.mapError (.field position)
  let source ← match declaration.toTemporalField? with
    | some source => pure source
    | none => throw (.dateYearSourceKind position field)
  let policy ← match declaration.toTemporalTargetPolicy? with
    | some policy => pure policy
    | none => throw (.dateYearPolicyUnavailable position field)
  if admitted :
      model.admitsConstructedDateYearField position source policy = true then
    pure { position, source, policy, admitted }
  else
    throw (.dateYearDeclarationNotAdmitted position field)

/-- Resolve one direct Date/DateTime field and retain the matching component-extractor certificate. -/
def elaborateConstructedDateExtractorField
    (model : FlatModel) (position : ConstructedDateComponentPosition)
    (part : DateNumericPart) (field : FieldId) :
    Except ConstructedDateComponentsElabError
      (CheckedConstructedDateExtractorField model) := do
  if position.extractor? != some part then
    throw (.extractorMismatch position part)
  let declaration ←
    model.resolveNonrepeatableDeclarationById field |>.mapError (.field position)
  let source ← match declaration.toTemporalField? with
    | some source => pure source
    | none => throw (.extractorSourceKind position field)
  if admitted :
      model.admitsConstructedDateExtractorField position part source = true then
    pure { position, part, source, admitted }
  else
    throw (.extractorDeclarationNotAdmitted position part field)

/-- Check one direct field or quoted constant at its authored position. -/
def elaborateConstructedDateSource
    (model : FlatModel) (position : ConstructedDateComponentPosition) :
    SurfaceConstructedDateSource →
      Except ConstructedDateComponentsElabError
        (CheckedConstructedDateSource model)
  | .numberField field =>
      .numberField <$> elaborateConstructedDateNumberField model position field
  | .stringField field =>
      .stringField <$> elaborateConstructedDateStringField
        model position field
  | .dateYearField field =>
      .dateYearField <$> elaborateConstructedDateYearField
        model position field
  | .constant source =>
      match position.decodeConstant? source with
      | some value => pure (.constant value)
      | none => throw (.constantNotAdmitted position source)
  | .extractor part field =>
      .extractor <$> elaborateConstructedDateExtractorField
        model position part field

/-- Check one two-, three-, or four-part direct Date through a common ordered source seam. -/
def elaborateConstructedDateSources
    (model : FlatModel) (sources : SurfaceConstructedDateComponents) :
    Except ConstructedDateComponentsElabError
      (CheckedConstructedDateComponents model) := do
  match hProfile : ModelZone.ConcreteProfile.ofId? model.timeZoneId with
  | some .utc =>
      let day ← elaborateConstructedDateSource model .day sources.day
      let month ← elaborateConstructedDateSource model .month sources.month
      let year ← match sources.year with
        | .complete source =>
            CheckedConstructedDateYear.complete <$>
              elaborateConstructedDateSource model .year source
        | .baseYear =>
            match model.baseYear with
            | some year => pure (.baseYear year)
            | none => throw .missingBaseYear
        | .centuryAndShortYear century shortYear =>
            pure (.centuryAndShortYear
              (← elaborateConstructedDateSource model .century century)
              (← elaborateConstructedDateSource model .shortYear shortYear))
      pure { day, month, year, profileIsUtc := hProfile }
  | _ => throw (.unsupportedZone model.timeZoneId)

/-- Check the direct Day/Month/Year form and reject unsupported zone behavior before execution. -/
def elaborateConstructedDateComponents
    (model : FlatModel) (day month year : FieldId) :
    Except ConstructedDateComponentsElabError
      (CheckedConstructedDateComponents model) :=
  elaborateConstructedDateSources model {
    day := .numberField day
    month := .numberField month
    year := .complete (.numberField year) }

/-- Check the two-argument Day/Month form and retain the required model Base Year as its fixed third component. -/
def elaborateConstructedDateBaseYearComponents
    (model : FlatModel) (day month : FieldId) :
    Except ConstructedDateComponentsElabError
      (CheckedConstructedDateComponents model) :=
  elaborateConstructedDateSources model {
    day := .numberField day
    month := .numberField month
    year := .baseYear }

/-- Check the four-argument Day/Month/Century/Short-Year form in source-check order. -/
def elaborateConstructedDateCenturyComponents
    (model : FlatModel) (day month century shortYear : FieldId) :
    Except ConstructedDateComponentsElabError
      (CheckedConstructedDateComponents model) :=
  elaborateConstructedDateSources model {
    day := .numberField day
    month := .numberField month
    year := .centuryAndShortYear
      (.numberField century) (.numberField shortYear) }

end A12Kernel
