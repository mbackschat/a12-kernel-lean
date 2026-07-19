/-! # Full civil Date semantics

This is the post-parse value boundary for a fully known calendar Date. It keeps decoded parts, calendar reality, and the kernel's always-on value floor as three separate stages, then exposes one strict chronological comparison. Declared formats, empty/formal cells, `Date(...)`, partial dates, DateTime, zones, and arithmetic belong to later capsules.

The definitions are original clean-room semantics for the decoded chronology, calendar-reality, and value-floor clauses of `spec/05` §§1, 3–4. They use an unbounded positive-era Gregorian account; kernel correspondence is claimed only for the separately documented reachable fragment.
-/

namespace A12Kernel

/-- Decoded year/month/day components before calendar and A12 value admission. -/
structure DateParts where
  year : Int
  month : Nat
  day : Nat
  deriving Repr, DecidableEq

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

end A12Kernel
