/-! # A12Kernel.Core — the truth/polarity algebra and the value domain

The foundational types every operator clause hangs off. Refines
`spec/13-lean-encoding-guide.md` §1 and `spec/SEMANTICS-MAP.md` §6, taking the verdict
algebra in the unified 4-state form (rationale + the full decision record in
[`docs/ARCHITECTURE.md`](../docs/ARCHITECTURE.md)).

Nothing here transcribes engine source — see `CLAUDE.md` for the clean-room rule. -/

namespace A12Kernel

/-! ## Kleene truth -/

/-- **Kleene truth.** `unknown` arises from an unavailable validation operand, including
    a formally invalid cell or a partial-validation reference outside the relevant set.
    The binary `And`/`Or` connectives use the strong-Kleene tables. There is deliberately
    **no negation combinator** — the language has no generic `Not`. (`spec/02`, §1/§3;
    `spec/10`, §5) -/
inductive K where
  | tru
  | fls
  | unknown
  deriving Repr, DecidableEq

namespace K

/-- Strong-Kleene conjunction: `fls` dominates; `unknown` only when no operand is `fls`
    and they are not both `tru`. -/
def and : K → K → K
  | .fls, _    => .fls
  | _,    .fls => .fls
  | .tru, .tru => .tru
  | _,    _    => .unknown

/-- Strong-Kleene disjunction: `tru` dominates; `unknown` only when no operand is `tru`
    and they are not both `fls`. -/
def or : K → K → K
  | .tru, _    => .tru
  | _,    .tru => .tru
  | .fls, .fls => .fls
  | _,    _    => .unknown

end K

/-! ## Message polarity and the verdict algebra -/

/-- A fired message's **polarity** (the kernel's message *type*): `value` = "what you
    entered is wrong" (no fill helps); `omission` = "something is missing" (a fill could
    clear it). Derived from directional fillability. (`spec/10`, §12) -/
inductive Polarity where
  | value
  | omission
  deriving Repr, DecidableEq

/-- A condition's **verdict** — truth and polarity in one lattice. `fired p` is the
    Kleene-`tru` case tagged with the polarity a fired message carries; `notFired` is
    `fls`; `unknown` is the suppressed/invalid case. Unified deliberately: a condition
    result always has a defined truth, so `unknown` *must* be representable — which a bare
    `firedValue | firedOmission | notFired` outcome cannot express. -/
inductive Verdict where
  | notFired
  | fired (p : Polarity)
  | unknown
  deriving Repr, DecidableEq

namespace Verdict

/-- Conjunction (`And`): strong-Kleene on truth, and **omission wins** among fired
    operands. `notFired` (Kleene-false) dominates; `fired ∧ unknown = unknown`. -/
def conj : Verdict → Verdict → Verdict
  | .notFired,       _              => .notFired
  | _,               .notFired      => .notFired
  | .unknown,        _              => .unknown
  | _,               .unknown       => .unknown
  | .fired .omission, _             => .fired .omission
  | _,               .fired .omission => .fired .omission
  | .fired .value,   .fired .value  => .fired .value

/-- Disjunction (`Or`): strong-Kleene on truth, and **value wins** among fired operands.
    `fired` (Kleene-true) dominates; `notFired ∨ unknown = unknown`. -/
def disj : Verdict → Verdict → Verdict
  | .fired .value,   _              => .fired .value
  | _,               .fired .value  => .fired .value
  | .fired .omission, _             => .fired .omission
  | _,               .fired .omission => .fired .omission
  | .unknown,        _              => .unknown
  | _,               .unknown       => .unknown
  | .notFired,       .notFired      => .notFired

end Verdict

/-! ## Number scale and the value domain -/

/-- The statically derived decimal scale of a numeric expression. Exact scales are signed because stripping trailing zeros from an integer constant can produce a negative scale; runtime values do not carry this authoring summary. (`spec/04`) -/
inductive ScaleInfo where
  | exact (digits : Int)
  | unknown
  deriving Repr, DecidableEq

/-- A Number *field*'s static configuration. `scale` gates `==`/`!=` at parse time (ordering
    is scale-exempt); `signed` drives fillability, not a min bound. (`spec/04`) -/
structure NumField where
  scale  : Nat
  signed : Bool
  deriving Repr, DecidableEq

/-- Decoded year/month/day components carried by admitted temporal values before consumer-specific calendar proofs. -/
structure DateParts where
  year : Int
  month : Nat
  day : Nat
  deriving Repr, DecidableEq

/-- A decoded whole-second wall-clock time. -/
structure TimeOfDay where
  hour : Nat
  minute : Nat
  second : Nat
  valid : hour < 24 ∧ minute < 60 ∧ second < 60
  deriving Repr, DecidableEq

namespace TimeOfDay

/-- Construct a whole-second time exactly when every component is in range. -/
def ofHms? (hour minute second : Nat) : Option TimeOfDay :=
  if valid : hour < 24 ∧ minute < 60 ∧ second < 60 then
    some { hour, minute, second, valid }
  else
    none

/-- Elapsed whole seconds since local midnight. -/
def secondsSinceMidnight (time : TimeOfDay) : Nat :=
  time.hour * 3600 + time.minute * 60 + time.second

end TimeOfDay

/-- Exact runtime instant identity in epoch milliseconds. Authored Date, Time, and DateTime values are whole-second, but the injected `Now` clock may retain a sub-second remainder. Calendar and zone resolution live in the temporal semantics. -/
structure Instant where
  epochMillis : Int
  deriving Repr, DecidableEq

namespace Instant

/-- Embed a whole-second temporal value into the exact runtime coordinate. -/
def ofEpochSecond (epochSecond : Int) : Instant :=
  { epochMillis := epochSecond * 1000 }

end Instant

/-- Runtime tag for the three scalar temporal field families. Their static format/component declarations remain model policy, while their admitted runtime payload shares exact instant identity. -/
inductive TemporalKind where
  | date
  | time
  | dateTime
  deriving Repr, DecidableEq

/-- Calendar provenance retained by date-bearing expression values. Stored parsed values use the proleptic Gregorian basis; constructed `Date(...)` descendants retain the legacy hybrid basis. -/
inductive DateCalendarBasis where
  | storedGregorian
  | legacyHybrid
  deriving Repr, DecidableEq

/-- One admitted scalar temporal payload. Exact runtime identity remains separate from decoded local components, and the closed constructors make each kind's available component halves explicit. -/
inductive TemporalValue where
  | date (instant : Instant) (parts : DateParts) (basis : DateCalendarBasis)
  | time (instant : Instant) (parts : TimeOfDay)
  | dateTime (instant : Instant) (date : DateParts) (time : TimeOfDay)
      (basis : DateCalendarBasis)
  deriving Repr, DecidableEq

namespace TemporalValue

/-- Derive the runtime temporal kind from the closed payload shape. -/
def kind : TemporalValue → TemporalKind
  | .date _ _ _ => .date
  | .time _ _ => .time
  | .dateTime _ _ _ _ => .dateTime

/-- Exact scalar instant identity used by direct comparison and instant arithmetic. -/
def instant : TemporalValue → Instant
  | .date instant _ _ => instant
  | .time instant _ => instant
  | .dateTime instant _ _ _ => instant

/-- Decoded date components when the payload is Date or DateTime. -/
def dateParts? : TemporalValue → Option DateParts
  | .date _ parts _ => some parts
  | .time _ _ => none
  | .dateTime _ parts _ _ => some parts

/-- Decoded clock components when the payload is Time or DateTime. -/
def time? : TemporalValue → Option TimeOfDay
  | .date _ _ _ => none
  | .time _ clock => some clock
  | .dateTime _ _ clock _ => some clock

/-- Date calendar provenance when the payload has a date component. -/
def calendarBasis? : TemporalValue → Option DateCalendarBasis
  | .date _ _ basis => some basis
  | .time _ _ => none
  | .dateTime _ _ _ basis => some basis

end TemporalValue

/-- Presence of the six semantic components exposed by an admitted temporal field format. Concrete format spelling and parsing remain upstream. -/
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

/-- The **value domain** (expanded per kind in later stages). Numbers are exact rationals;
    the field's `scale` lives in `NumField`, and *stored-form / representation* equality
    (`7` vs `7.00`) is a separate rendered-string concern, not carried here. Arithmetic
    applies explicit rounding (scale-19 `HALF_UP` for compares, `MathContext(50)` for
    intermediates) at the `spec/04` points, so exactness never silently diverges from the
    engine. Date, Time, and DateTime retain one closed payload with exact instant identity,
    decoded component halves, and date calendar provenance; declared format and
    partial-value admission remain upstream. (`spec/13` §1) -/
inductive Value where
  | num  (d : Rat)
  | str  (s : String)
  | bool (b : Bool)
  | conf (b : Bool)         -- Stored Confirm values are `true`; `false` is comparison-local substitution.
  | enum (stored : String)  -- compared by the stored token, never the display text
  | temporal (value : TemporalValue)
  deriving Repr, DecidableEq

/-! ## Sanity checks (double as regression guards) -/

-- strong-Kleene
example : K.and .fls .unknown = .fls     := rfl
example : K.and .tru .unknown = .unknown := rfl
example : K.or  .tru .unknown = .tru     := rfl
example : K.or  .fls .unknown = .unknown := rfl

-- verdict algebra — the spec's `healthy Or / And broken` cases
example : Verdict.disj (.fired .value) .unknown = .fired .value := rfl  -- fired Or unknown fires
example : Verdict.conj .notFired       .unknown = .notFired     := rfl  -- notFired And unknown suppressed
example : Verdict.conj (.fired .value) .unknown = .unknown      := rfl  -- fired And unknown = unknown
example : Verdict.disj .notFired       .unknown = .unknown      := rfl
-- polarity precedence
example : Verdict.conj (.fired .value) (.fired .omission) = .fired .omission := rfl  -- omission wins under And
example : Verdict.disj (.fired .value) (.fired .omission) = .fired .value    := rfl  -- value wins under Or

end A12Kernel
