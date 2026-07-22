import A12Kernel.Semantics.DateTimeComparison

/-! # Temporal format-component admission

This capsule owns the static component facts shared by direct temporal comparisons and temporal extrema. Direct comparisons use the kernel's coarse year/date-class test and require matching time presence only for equality/inequality. Aggregate admission is stricter: after an optional Base Year supplies `YEAR`, the complete component sets must match. Text parsing, format spelling, operand classification, and resolved value evaluation remain separate.
-/

namespace A12Kernel

/-- Parser-independent component shape of the two legal Date constants: `DD.MM.YYYY` and the Base-Year-dependent `DD.MM.` form. Lexical spelling and decoding are earlier responsibilities. -/
def TemporalComponents.isDateLiteral (components : TemporalComponents) : Bool :=
  components.month && components.day && !components.hasTime

/-- Static component identity carried by `Now`: a full date and time, independent of its exact millisecond runtime value. -/
def TemporalComponents.now : TemporalComponents :=
  { year := true, month := true, day := true,
    hour := true, minute := true, second := true }

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

/-- `Now` obeys ordinary direct-comparison compatibility and the additional generated-code restriction that the other operand expose a time component. -/
def TemporalComparisonOp.admitsNow (op : TemporalComparisonOp)
    (hasBaseYear : Bool) (other : TemporalComponents) : Bool :=
  other.hasTime && op.admitsFormats hasBaseYear other TemporalComponents.now

/-- Static admission shared by temporal operand-list and field-list extrema: component sets must agree exactly after Base Year supplementation. -/
def temporalAggregateFormatsCompatible (hasBaseYear : Bool)
    (left right : TemporalComponents) : Bool :=
  left.withBaseYear hasBaseYear == right.withBaseYear hasBaseYear

end A12Kernel
