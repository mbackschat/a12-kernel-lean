import A12Kernel.Elaboration.Flat.Model
import A12Kernel.Semantics.TimeConstructionInputs

namespace A12Kernel

/-- Exact Number declaration gate shared by scalar and addressed `Time(...)` component positions. Placement is certified separately, so this predicate owns only kind and numeric policy. The two-character alternative is the declaration's complete stored-length bound, not its integer-digit cap. -/
def FlatModel.admitsTimeNumberComponentField (model : FlatModel)
    (position : TimeComponentPosition) (source : FlatNumberField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      let constraints := declaration.numericTargetConstraints
      declaration.toNumberField? == some source &&
        source.info.scale == 0 &&
        constraints.minFractionalDigits == 0 &&
        (constraints.maxStoredLength == some 2 ||
          constraints.maximum == some position.maximum) &&
        declaration.numberDomainNonnegative source

/-- Scope-bound specialization of the shared Number-component policy gate. -/
def FlatModel.admitsTimeNumberField (model : FlatModel)
    (position : TimeComponentPosition) (source : FlatNumberField) (scope : List RepeatableLevel := []) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      declaration.repetitionBoundBy scope &&
        model.admitsTimeNumberComponentField position source

/-- Whether the exact declared source is one of the six digit patterns the construction
    checker recognizes without interpreting general regular-expression equivalence. -/
def isTimeComponentDigitPattern (source : String) : Bool :=
  isTemporalComponentDigitPattern 2 source

/-- Placement-neutral pattern-backed String declaration gate shared by scalar and addressed `Time(...)` components. The client-SPI extensible-String alternative bypasses only the pattern gate. -/
def FlatModel.admitsTimeStringComponentField (model : FlatModel)
    (source : FlatStringField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      declaration.toStringValueField? == some source &&
        declaration.customType.isNone &&
        declaration.enumeration.isNone &&
        declaration.stringPolicy.maxLength == some 2 &&
        (declaration.stringExtensibleEnum || declaration.stringPatternSource.any isTimeComponentDigitPattern)

/-- Scope-bound specialization of the shared String-component policy gate. -/
def FlatModel.admitsTimeStringField (model : FlatModel)
    (source : FlatStringField) (scope : List RepeatableLevel := []) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      declaration.repetitionBoundBy scope &&
        model.admitsTimeStringComponentField source

/-- Placement-neutral field-backed extractor admission. The selected temporal half and constructor position are static obligations; placement is certified separately. -/
def FlatModel.admitsTimeExtractorComponentField (model : FlatModel)
    (position : TimeComponentPosition) (part : TimeNumericPart)
    (source : FlatTemporalField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      declaration.toTemporalField? == some source &&
        part.admittedBy source.components &&
        position.extractor == part

/-- Scope-bound specialization of the shared extractor-component policy gate. -/
def FlatModel.admitsTimeExtractorField (model : FlatModel)
    (position : TimeComponentPosition) (part : TimeNumericPart)
    (source : FlatTemporalField) (scope : List RepeatableLevel := []) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      declaration.repetitionBoundBy scope &&
        model.admitsTimeExtractorComponentField position part source

end A12Kernel
