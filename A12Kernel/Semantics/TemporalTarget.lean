import A12Kernel.Semantics.ModelZone

/-! # Bounded full-Date computation targets

This capsule owns the first executable temporal target result domain. It admits two exact full-Date formats, renders a resolved model-zone date with two-digit day and month, and retains an invalid pre-1900 attempt. DateTime, partial dates, arbitrary `SimpleDateFormat` syntax, and document application remain separate.
-/

namespace A12Kernel

/-- Exact declared formats admitted by the first full-Date target renderer. This is a bounded source-checked subset, not a general date-format parser. -/
inductive FullDateTargetFormat where
  | dayMonthYearDots
  | yearMonthDayDashes
  deriving Repr, DecidableEq

namespace FullDateTargetFormat

/-- Admit only the two exact declaration sources implemented by this renderer. -/
def ofSource? : String → Option FullDateTargetFormat
  | "dd.MM.yyyy" => some .dayMonthYearDots
  | "yyyy-MM-dd" => some .yearMonthDayDashes
  | _ => none

private def twoDigits (value : Nat) : String :=
  if value < 10 then "0" ++ toString value else toString value

/-- Render one admitted local Date. The year is untruncated; day and month are always two digits, matching the kernel's computed-Date store. -/
def renderText (format : FullDateTargetFormat) (date : FullDate) : String :=
  let parts := date.civil.parts
  match format with
  | .dayMonthYearDots =>
      twoDigits parts.day ++ "." ++ twoDigits parts.month ++ "." ++
        toString parts.year
  | .yearMonthDayDashes =>
      toString parts.year ++ "-" ++ twoDigits parts.month ++ "-" ++
        twoDigits parts.day

end FullDateTargetFormat

/-- A nonempty rendered Date attempt. Target rejection retains this exact stored form. -/
structure StoredDate where
  text : String
  nonempty : text ≠ ""
  deriving Repr, DecidableEq

namespace FullDateTargetFormat

/-- Render an admitted Date into a nonempty target attempt. -/
def render (format : FullDateTargetFormat) (date : FullDate) : StoredDate :=
  {
    text := format.renderText date
    nonempty := by
      cases format <;>
        simp [renderText, twoDigits]
  }

end FullDateTargetFormat

/-- Root result before a full-Date target consumes it. -/
inductive FullDateComputationResult where
  | noValue
  | value (instant : Instant)
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

/-- Reachable basic target-check cause in the admitted post-floor full-Date fragment. -/
inductive FullDateTargetError where
  | before1900
  deriving Repr, DecidableEq

/-- Rich full-Date target result before delta classification or application. -/
inductive FullDateTargetOutcome where
  | noValue
  | accepted (stored : StoredDate)
  | errored (attempted : StoredDate) (cause : FullDateTargetError)
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

namespace FullDate

/-- Inclusive lower bound used only when a Date declaration opts into the additional pre-1900 check. -/
def year1900Start : FullDate :=
  {
    civil := {
      parts := { year := 1900, month := 1, day := 1 }
      real := by decide
    }
    admissible := by decide
  }

/-- Whether this already-admitted Date fails the optional pre-1900 target check. -/
def before1900 (date : FullDate) : Bool :=
  date.before year1900Start

end FullDate

end A12Kernel
