import A12Kernel.Semantics.FullDate
import A12Kernel.Semantics.TemporalFormat

/-! # The partially known Date value domain

A Date declaration may allow **literal zero components in a monotone suffix**: an omitted day, an
omitted month with the day also omitted, or an omitted year with both also omitted. This module owns
the resulting value shapes, their two interval boundaries, and which shapes one declared precision
allows — nothing else. It sits below both the stored-input classifier that produces such a value and
the `ValueAsDate` operation that resolves one, because a value's identity cannot depend on either.

An omitted year carries no synthetic replacement: the runtime suppresses it before any completion, so
there is no year to store. -/

namespace A12Kernel

/-- Which boundary of a partially known Date the authored operation selects. -/
inductive ValueAsDateEndpoint where
  | firstDay
  | lastDay
  deriving Repr, DecidableEq

/-- The two full-Date boundaries denoted by one admitted literal omitted-day value. The private constructor prevents callers from pairing unrelated dates. -/
structure OmittedDayDate where
  private mk ::
  first : FullDate
  last : FullDate
  deriving Repr, DecidableEq

namespace OmittedDayDate

/-- Construct an omitted day only when both endpoint completions are real and satisfy the universal Date floor. Checking the first endpoint before execution preserves the kernel's completion-before-floor order. -/
def ofYearMonth? (year : Int) (month : Nat) : Option OmittedDayDate := do
  let first ← FullDate.ofYmd? year month 1
  let lastDay ← DateParts.daysInMonth? year month
  let last ← FullDate.ofYmd? year month lastDay
  pure { first, last }

/-- Select the authored interval boundary. -/
def resolve (date : OmittedDayDate) : ValueAsDateEndpoint → FullDate
  | .firstDay => date.first
  | .lastDay => date.last

end OmittedDayDate

/-- The two full-Date boundaries denoted by one admitted literal omitted-month value. The private constructor prevents callers from pairing unrelated years. -/
structure OmittedMonthDate where
  private mk ::
  first : FullDate
  last : FullDate
  deriving Repr, DecidableEq

namespace OmittedMonthDate

/-- Construct an omitted month only when the formal checker’s earliest completion and the corresponding latest completion are admitted Dates. -/
def ofYear? (year : Int) : Option OmittedMonthDate := do
  let first ← FullDate.ofYmd? year 1 1
  let last ← FullDate.ofYmd? year 12 31
  pure { first, last }

/-- Select the authored complete-year boundary. -/
def resolve (date : OmittedMonthDate) : ValueAsDateEndpoint → FullDate
  | .firstDay => date.first
  | .lastDay => date.last

end OmittedMonthDate

/-- One structurally legal stored shape before the declaration’s partial-precision policy is applied. An omitted year carries no synthetic replacement because the runtime suppresses it before interval completion. -/
inductive PartiallyKnownDateValue where
  | full (date : FullDate)
  | omittedDay (date : OmittedDayDate)
  | omittedMonth (date : OmittedMonthDate)
  | omittedYear
  deriving Repr, DecidableEq

namespace TemporalPartialMode

/-- Whether one legal stored shape is admitted by this declaration precision. Unknown components form a suffix: month omission entails day omission, and year omission entails both. -/
def admitsPartiallyKnownValue :
    TemporalPartialMode → PartiallyKnownDateValue → Bool
  | .full, _ => false
  | .dayOptional, .full _ | .dayOptional, .omittedDay _ => true
  | .dayOptional, .omittedMonth _ | .dayOptional, .omittedYear => false
  | .monthOptional, .full _
  | .monthOptional, .omittedDay _
  | .monthOptional, .omittedMonth _ => true
  | .monthOptional, .omittedYear => false
  | .yearOptional, _ => true

end TemporalPartialMode

/-- A stored partial-Date value certified against its exact declaration precision. -/
structure AdmittedPartiallyKnownDate (mode : TemporalPartialMode) where
  value : PartiallyKnownDateValue
  admitted : mode.admitsPartiallyKnownValue value = true
  deriving Repr, DecidableEq

end A12Kernel
