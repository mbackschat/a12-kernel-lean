import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Semantics.ModelZone

/-! # Checked three-Number-field constructed Dates

This capsule certifies the direct nonrepeatable `Date(day, month, year)` Number-field form for model-owned UTC or GMT. Each position keeps the kernel checker's exact stored-width-or-maximum declaration gate.

Execution, other model zones, String and extractor components, Base-Year and four-component forms, numeric expression amounts, repeatable placement, targets, and a general temporal-expression tree remain outside.
-/

namespace A12Kernel

/-- The declaration gate selected by a direct three-field Date component position. -/
inductive ConstructedDateComponentPosition where
  | day
  | month
  | year
  deriving Repr, DecidableEq

namespace ConstructedDateComponentPosition

/-- Complete stored width accepted as an alternative to the positional numeric maximum. -/
def storedWidth : ConstructedDateComponentPosition → Nat
  | .day | .month => 2
  | .year => 4

/-- Whether one explicit maximum satisfies the position-specific checker branch. Complete years deliberately accept the kernel's flexible 1000–9999 range. -/
def admitsMaximum (position : ConstructedDateComponentPosition) :
    Option Rat → Bool
  | some maximum =>
      match position with
      | .day => maximum == 31
      | .month => maximum == 12
      | .year => decide (1000 ≤ maximum ∧ maximum ≤ 9999)
  | none => false

end ConstructedDateComponentPosition

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

/-- The checked direct three-field constructor plus its bounded model-zone certificate. -/
structure CheckedConstructedDateComponents (model : FlatModel) where
  day : CheckedConstructedDateNumberField model
  month : CheckedConstructedDateNumberField model
  year : CheckedConstructedDateNumberField model
  profileIsUtc :
    ModelZone.ConcreteProfile.ofId? model.timeZoneId =
      some .utc

/-- Static rejection before any component is read. -/
inductive ConstructedDateComponentsElabError where
  | field (position : ConstructedDateComponentPosition) (error : ResolveError)
  | sourceKind (position : ConstructedDateComponentPosition) (field : FieldId)
  | declarationNotAdmitted (position : ConstructedDateComponentPosition)
      (field : FieldId)
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

/-- Check the direct Day/Month/Year form and reject unsupported zone behavior before execution. -/
def elaborateConstructedDateComponents
    (model : FlatModel) (day month year : FieldId) :
    Except ConstructedDateComponentsElabError
      (CheckedConstructedDateComponents model) := do
  match hProfile : ModelZone.ConcreteProfile.ofId? model.timeZoneId with
  | some .utc =>
      let checkedDay ←
        elaborateConstructedDateNumberField model .day day
      let checkedMonth ←
        elaborateConstructedDateNumberField model .month month
      let checkedYear ←
        elaborateConstructedDateNumberField model .year year
      pure {
        day := checkedDay
        month := checkedMonth
        year := checkedYear
        profileIsUtc := hProfile }
  | _ => throw (.unsupportedZone model.timeZoneId)

end A12Kernel
