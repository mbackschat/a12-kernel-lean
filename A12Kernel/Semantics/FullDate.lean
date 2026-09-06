import A12Kernel.Core

/-! # Full civil Date semantics

This is the post-parse value boundary for a fully known calendar Date. It keeps decoded parts, calendar reality, and the kernel's always-on value floor as three separate stages, then exposes one strict chronological comparison. Declared formats, empty/formal cells, `Date(...)`, partial dates, DateTime, zones, and arithmetic belong to later capsules.

The definitions are original clean-room semantics for the decoded chronology, calendar-reality, and value-floor clauses of `spec/05` §§1, 3–4. They use an unbounded positive-era Gregorian account; kernel correspondence is claimed only for the separately documented reachable fragment.
-/

namespace A12Kernel

namespace DateParts

/-- Gregorian leap-year classification. -/
def isLeapYear (year : Int) : Bool :=
  decide (year % 4 = 0 ∧ (year % 100 ≠ 0 ∨ year % 400 = 0))

/-- The Gregorian length of a month, or `none` for a non-month number. -/
def daysInMonth? (year : Int) : Nat → Option Nat
  | 1 => some 31
  | 2 => some (if isLeapYear year then 29 else 28)
  | 3 => some 31
  | 4 => some 30
  | 5 => some 31
  | 6 => some 30
  | 7 => some 31
  | 8 => some 31
  | 9 => some 30
  | 10 => some 31
  | 11 => some 30
  | 12 => some 31
  | _ => none

/-- Executable calendar reality for fully known positive-era parts. -/
def isReal (parts : DateParts) : Bool :=
  decide (0 < parts.year) &&
    match daysInMonth? parts.year parts.month with
    | some lastDay => decide (0 < parts.day ∧ parts.day ≤ lastDay)
    | none => false

/-- Proposition exposed by the executable reality check. -/
def Real (parts : DateParts) : Prop :=
  parts.isReal = true

instance (parts : DateParts) : Decidable parts.Real := by
  unfold Real
  infer_instance

/-- Strict lexicographic order over decoded civil components. -/
def Before (left right : DateParts) : Prop :=
  left.year < right.year ∨
    left.year = right.year ∧
      (left.month < right.month ∨
        left.month = right.month ∧ left.day < right.day)

instance (left right : DateParts) : Decidable (Before left right) := by
  unfold Before
  infer_instance

end DateParts

/-- A fully known date whose parts denote a real proleptic-Gregorian calendar day. -/
structure CivilDate where
  parts : DateParts
  real : parts.Real
  deriving Repr, DecidableEq

namespace CivilDate

/-- Construct a civil date exactly when its decoded parts denote a real day. -/
def ofParts? (parts : DateParts) : Option CivilDate :=
  if real : parts.Real then
    some { parts, real }
  else
    none

/-- Decode-independent convenience constructor for already-separated components. -/
def ofYmd? (year : Int) (month day : Nat) : Option CivilDate :=
  ofParts? { year, month, day }

/-- Strict civil chronology. -/
def Before (left right : CivilDate) : Prop :=
  left.parts.Before right.parts

instance (left right : CivilDate) : Decidable (Before left right) := by
  unfold Before
  infer_instance

/-- The inclusive lower bound for stored and computed Date values. -/
def gregorianFloor : CivilDate :=
  {
    parts := { year := 1583, month := 10, day := 16 }
    real := by decide
  }

end CivilDate

/-- A fully known, Gregorian-real A12 Date value on or after 1583-10-16. -/
structure FullDate where
  civil : CivilDate
  admissible : ¬civil.Before CivilDate.gregorianFloor
  deriving Repr, DecidableEq

namespace FullDate

/-- Admit a real civil date exactly when it meets the A12 value floor. -/
def ofCivil? (civil : CivilDate) : Option FullDate :=
  if admissible : ¬civil.Before CivilDate.gregorianFloor then
    some { civil, admissible }
  else
    none

/-- Construct an admitted full Date through both calendar-reality and value-floor checks. -/
def ofYmd? (year : Int) (month day : Nat) : Option FullDate :=
  (CivilDate.ofYmd? year month day).bind ofCivil?

/-- Strict chronological comparison over admitted full-Date values. -/
def before (left right : FullDate) : Bool :=
  decide (left.civil.Before right.civil)

end FullDate

/-- The component triple a temporal aggregate compares for one operand: the cell's decoded parts
reduced to the operand's **declared** component set, with a yearless declaration's year taken from
the model's Base Year. Each component the set omits takes the set's canonical representative and
never the cell's value.

**Why masking rather than reading the cell.** `RawCell.parsed` carries whatever value the classifier
that admitted the stored text produced, and the document's coherence check re-derives boolean,
confirm and DateRange values from their stored text but not temporal ones — so for a `yyyy-MM`
declaration nothing pins which day the producer chose. A fold that trusted the omitted components
would answer differently for two producers spelling the same value, which is not a semantics.

**Why it lives here.** Two completed consumers compare at the shared set and mean the same thing by
it: `NumberOfDifferentValues` folds distinct values at that precision, and `MinValue`/`MaxValue` order
at it — both measured, on the same declarations
([distinct count](../../docs/sources/evaluation-and-application-routes.md#src-distinct-count-component-omitting-fold),
[extrema](../../docs/sources/evaluation-and-application-routes.md#src-extrema-component-omitting-fold)).
Their modules share only this projection, which is the reason `toFullDate?` sits here too.

A caller reaching the year-bearing arm has a year available from the set or the Base Year, so the
`0` fallback is unreachable there; it is written as a total function rather than gated on that
reachability, because a partial one would put the arm's precondition into every caller. -/
def maskedDateComponents (components : TemporalComponents) (baseYear : Option Int)
    (parts : DateParts) : Int × Nat × Nat :=
  (if components.year then parts.year else baseYear.getD 0,
    if components.month then parts.month else 1,
    if components.day then parts.day else 1)

namespace DateValue

/-- Project one universal Date endpoint into the established real, floor-admitted full-Date domain. Exact instant and calendar provenance remain available on the source value.

    It sits here rather than beside its first caller because the temporal extrema need the identical projection, and the two consumers' modules share only this one. -/
def toFullDate? (value : DateValue) : Option FullDate :=
  FullDate.ofYmd? value.parts.year value.parts.month value.parts.day

end DateValue

end A12Kernel
