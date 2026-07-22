import A12Kernel.Semantics.DateTimeComparison

/-! # Temporal format-component admission

This capsule owns the static component facts shared by direct temporal comparisons and temporal extrema. Direct comparisons preserve the original date-versus-time class, compare year presence after optional Base Year supplementation, and require matching time presence only for equality/inequality. Aggregate admission preserves that original class and additionally requires the complete supplemented component sets to match. Text parsing, format spelling, operand classification, and resolved value evaluation remain separate.
-/

namespace A12Kernel

/-- Parser-independent component shape of the two legal Date constants: `DD.MM.YYYY` and the Base-Year-dependent `DD.MM.` form. Lexical spelling and decoding are earlier responsibilities. -/
def TemporalComponents.isDateLiteral (components : TemporalComponents) : Bool :=
  components.month && components.day && !components.hasTime

/-- Static component identity carried by `Now`: a full date and time, independent of its exact millisecond runtime value. -/
def TemporalComponents.now : TemporalComponents :=
  { year := true, month := true, day := true,
    hour := true, minute := true, second := true }

/-- Static identity of a complete calendar date with no time component. -/
def TemporalComponents.fullDate : TemporalComponents :=
  { year := true, month := true, day := true,
    hour := false, minute := false, second := false }

/-- Static component identity carried by `Today`. -/
def TemporalComponents.today : TemporalComponents := TemporalComponents.fullDate

def TemporalComponents.baseYear : TemporalComponents := TemporalComponents.fullDate

/-- Equality and inequality, unlike directional comparisons, require both formats to agree on whether they expose a time component. -/
def TemporalComparisonOp.requiresSameTimePresence : TemporalComparisonOp → Bool
  | .equal | .notEqual => true
  | .before | .beforeOrEqual | .after | .afterOrEqual => false

/-- Static admission for a direct temporal comparison. This intentionally does not require equal component sets. -/
def TemporalComparisonOp.admitsFormats (op : TemporalComparisonOp)
    (hasBaseYear : Bool) (left right : TemporalComponents) : Bool :=
  let leftWithYear := left.withBaseYear hasBaseYear
  let rightWithYear := right.withBaseYear hasBaseYear
  (leftWithYear.year == rightWithYear.year) &&
    (left.hasDate == right.hasDate) &&
    (!op.requiresSameTimePresence || (left.hasTime == right.hasTime))

/-- `Now` obeys ordinary direct-comparison compatibility and the additional generated-code restriction that the other operand expose a time component. -/
def TemporalComparisonOp.admitsNow (op : TemporalComparisonOp)
    (hasBaseYear : Bool) (other : TemporalComponents) : Bool :=
  other.hasTime && op.admitsFormats hasBaseYear other TemporalComponents.now

/-- `Today` is admitted exactly as a complete date-shaped operand through the ordinary direct-comparison gate. -/
def TemporalComparisonOp.admitsToday (op : TemporalComparisonOp)
    (hasBaseYear : Bool) (other : TemporalComponents) : Bool :=
  op.admitsFormats hasBaseYear other TemporalComponents.today

/-- Base Year is already known to exist here, so it supplies the year component while otherwise following the ordinary date-shaped format gate. -/
def TemporalComparisonOp.admitsBaseYear (op : TemporalComparisonOp)
    (other : TemporalComponents) : Bool :=
  other.hasDate && op.admitsFormats true other TemporalComponents.baseYear

/-- Static admission shared by temporal operand-list and field-list extrema: the original date class must agree and component sets must agree exactly after Base Year supplementation. -/
def temporalAggregateFormatsCompatible (hasBaseYear : Bool)
    (left right : TemporalComponents) : Bool :=
  (left.hasDate == right.hasDate) &&
    (left.withBaseYear hasBaseYear == right.withBaseYear hasBaseYear)

end A12Kernel
