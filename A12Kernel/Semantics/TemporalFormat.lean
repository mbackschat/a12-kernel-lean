import A12Kernel.Semantics.DateComparison

/-! # Temporal format-component admission

This capsule owns the static component facts shared by direct temporal comparisons and temporal extrema. Direct comparisons use the kernel's coarse year/date-class test and require matching time presence only for equality/inequality. Aggregate admission is stricter: after an optional Base Year supplies `YEAR`, the complete component sets must match. Text parsing, format spelling, operand classification, and resolved value evaluation remain separate.
-/

namespace A12Kernel

/-- Presence of the six semantic components exposed by an admitted temporal format. -/
structure TemporalComponents where
  year : Bool
  month : Bool
  day : Bool
  hour : Bool
  minute : Bool
  second : Bool
  deriving Repr, DecidableEq

/-- Whether a format exposes at least one calendar-date component. -/
def TemporalComponents.hasDate (components : TemporalComponents) : Bool :=
  components.year || components.month || components.day

/-- Whether a format exposes at least one wall-time component. -/
def TemporalComponents.hasTime (components : TemporalComponents) : Bool :=
  components.hour || components.minute || components.second

/-- Supply `YEAR` from the model-wide Base Year when one exists. -/
def TemporalComponents.withBaseYear (components : TemporalComponents)
    (hasBaseYear : Bool) : TemporalComponents :=
  if hasBaseYear then { components with year := true } else components

/-- Full DateTime aggregate formats expose every date and time component. -/
def TemporalComponents.isFullDateTime (components : TemporalComponents) : Bool :=
  components.year && components.month && components.day &&
    components.hour && components.minute && components.second

/-- Equality and inequality, unlike directional comparisons, require both formats to agree on whether they expose a time component. -/
def TemporalComparisonOp.requiresSameTimePresence : TemporalComparisonOp → Bool
  | .equal | .notEqual => true
  | .before | .beforeOrEqual | .after | .afterOrEqual => false

/-- Static admission for a direct temporal comparison. This intentionally does not require equal component sets. -/
def TemporalComparisonOp.admitsFormats (op : TemporalComparisonOp)
    (hasBaseYear : Bool) (left right : TemporalComponents) : Bool :=
  let left := left.withBaseYear hasBaseYear
  let right := right.withBaseYear hasBaseYear
  (left.year == right.year) &&
    (left.hasDate == right.hasDate) &&
    (!op.requiresSameTimePresence || (left.hasTime == right.hasTime))

/-- Static admission shared by temporal operand-list and field-list extrema: component sets must agree exactly after Base Year supplementation. -/
def temporalAggregateFormatsCompatible (hasBaseYear : Bool)
    (left right : TemporalComponents) : Bool :=
  left.withBaseYear hasBaseYear == right.withBaseYear hasBaseYear

end A12Kernel
