import A12Kernel.Semantics.Observation
import A12Kernel.Semantics.ValueList

namespace A12Kernel

/-- The set this gate actually compares: the declared one with YEAR supplied when the model declares
    a **Base Year**.

    Measured on this operator at `baseYear: "2024"`: a yearless `MM` operand is admitted beside
    `yyyy-MM`, and `MM-dd` beside a complete date, while `MM-dd` beside `yyyy-MM` stays refused and
    both mixed pairs stay refused with no Base Year declared
    ([checkpoint](../../docs/sources/temporal-runtime-fold-probes.md#src-distinct-count-component-omitting-fold)).
    Supplement-then-require-equality reproduces all four rows; plain equality refuses the first two,
    which are legal models. The Base Year supplies only the year, so a set that disagrees on any
    other component is refused exactly as before. -/
def TemporalComponents.supplementedByBaseYear
    (components : TemporalComponents) (hasBaseYear : Bool) : TemporalComponents :=
  if hasBaseYear then { components with year := true } else components

/-- The declared components select the identity. A yearless list retains the calendar position it
    spells; completing it against an invented year would change the comparison domain. -/
inductive TemporalDistinctCountFoldArm where
  | dated
  | yearless
  | clock
  | instant
  deriving Repr, DecidableEq

/-- The value-list kind each arm folds over. -/
def TemporalDistinctCountFoldArm.kind : TemporalDistinctCountFoldArm → ValueListKind
  | .dated => .date
  | .yearless => .yearlessDate
  | .clock => .timeOfDay
  | .instant => .instant

/-- The arm a shared component set folds at, given whether the model declares a Base Year.

    Keyed on the declared **component set** and never on the declared kind, which is measured: a TIME
    and a DATETIME declared the degenerate `HH:mm:ss` count one value for one clock reading, so they
    must land in the same arm
    ([checkpoint](../../docs/sources/temporal-runtime-fold-probes.md#src-distinct-count-time-bearing-fold)).
    Among the date arms a year is available when the set names one or the Base Year supplies it,
    which is the same supplementation the admission gate applies. -/
def temporalDistinctCountFoldArm
    (components : TemporalComponents) (hasBaseYear : Bool) :
    TemporalDistinctCountFoldArm :=
  if components.hasTime then
    if components.hasDate then .instant else .clock
  else if components.year || hasBaseYear then .dated
  else .yearless

/-- Project one addressed temporal cell to the identity this list compares: the **decoded** date
    reduced to the operand's declared component set, with a yearless declaration's year taken from
    the model's Base Year. The stored text is deliberately discarded, which is the exact inverse of
    the neighbouring uniqueness operator's projection over the same cells.

    **The omitted components are replaced by the set's canonical representative rather than read off
    the cell**, and that is load-bearing. `RawCell.parsed` carries whatever value the classifier that
    admitted the text produced, and the document's coherence check re-derives boolean, confirm, and
    DateRange values from their stored text but not temporal ones — so for a `yyyy-MM` declaration
    nothing pins which day the producer chose. A fold that trusted the day would answer differently
    for two producers spelling the same value, which is not a semantics. Masking makes the count the
    declaration's.

    Measured: the count compares at the shared set's precision after Base Year supplementation
    ([checkpoint](../../docs/sources/temporal-runtime-fold-probes.md#src-distinct-count-component-omitting-fold)). -/
def temporalDistinctCountCell
    (phase : Phase) (components : TemporalComponents) (baseYear : Option Int) :
    (arm : TemporalDistinctCountFoldArm) → CheckedCell →
      ValueListCell arm.kind
  | .dated, cell =>
      match observeCell phase cell with
      | .value (.temporal (.date dateValue)) =>
          let (year, month, day) :=
            maskedDateComponents components baseYear dateValue.parts
          match FullDate.ofYmd? year month day with
          | some date => .present date
          | none => .unknown .malformed
      | .value _ => .unknown .malformed
      | .empty => .empty
      | .unknown cause | .poison cause => .unknown cause
  | .yearless, cell =>
      match observeCell phase cell with
      | .value (.temporal (.date dateValue)) =>
          let (_, month, day) :=
            maskedDateComponents components baseYear dateValue.parts
          .present { month, day }
      | .value _ => .unknown .malformed
      | .empty => .empty
      | .unknown cause | .poison cause => .unknown cause
  | .clock, cell =>
      match observeCell phase cell with
      -- **One case covers both temporal kinds that can declare a clock set, because the cell's value
      -- shape follows the declared component set and not the declared kind.** A DATETIME declared the
      -- degenerate `HH:mm:ss` holds a `.time` here — `formalCheck` marks a `.dateTime` value under
      -- that declaration malformed — which is why the measured cross-kind identity needs no second
      -- case: a TIME and such a DATETIME arrive as the same value shape and compare on the decoded
      -- reading. Comparing instants instead would answer 2 to the pair the Kernel counts as one,
      -- since neither operand's transport date is meaningful.
      | .value (.temporal (.time _ parts)) => .present parts
      | .value _ => .unknown .malformed
      | .empty => .empty
      | .unknown cause | .poison cause => .unknown cause
  | .instant, cell =>
      match observeCell phase cell with
      -- Exact instants preserve the distinction needed by in-flight temporal consumers. For this
      -- field-list consumer, computed cells also store text, and injective fresh-label resolution
      -- on the concrete profiles makes label and instant identity agree
      -- ([store checkpoint](../../docs/sources/computation-placement-and-constant-probes.md#src-computed-value-is-not-retained-past-its-store),
      -- `concreteProfile_resolveLocal_injective`).
      | .value (.temporal (.dateTime instant _ _ _)) => .present instant
      | .value _ => .unknown .malformed
      | .empty => .empty
      | .unknown cause | .poison cause => .unknown cause

/-- Whether the fold's atom for a time-bearing set holds exactly the components that set names.

    The date arms need no such condition: each omitted component is masked to the set's canonical
    representative. The time atoms cannot be masked — `TimeOfDay` and `Instant` carry every component
    they have — so a set omitting one would be folded at a precision it does not declare. No format
    in the admitted domain spells such a set: the twelve admitted date/time formats are the ten date
    sets, the complete clock, and the complete instant
    ([checkpoint](../../docs/sources/temporal-runtime-fold-probes.md#src-distinct-count-time-bearing-fold)).
    So this is a representable shape with no known witness rather than a measured gap, which is
    exactly why it stays a certificate instead of an invented projection. -/
def timeBearingSetIsComplete (components : TemporalComponents) : Bool :=
  !components.hasTime ||
    (components.hour && components.minute && components.second &&
      (!components.hasDate ||
        (components.year && components.month && components.day)))

end A12Kernel
