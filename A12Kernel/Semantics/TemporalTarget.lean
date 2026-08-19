import A12Kernel.Semantics.ModelZone
import A12Kernel.Semantics.DateRangeOverlap
import A12Kernel.Semantics.TemporalFormat

/-! # Bounded temporal computation targets

This capsule owns bounded Time, full-Date, DateTime, and DateRange target result domains. Time admits the kernel's exact whole-second format and remains a zone-free clock rather than acquiring the runtime transport date. Full Date admits two exact formats, the universal Date floor, and the optional pre-1900 check; the checked declaration layer admits only FULL precision for computation. DateTime admits the bounded standard whole-second formats and deliberately separates its rendered local wall label from the exact source instant, including any millisecond remainder. DateRange admits the exact ISO/slash and dotted-day/dash target profiles and renders through resolved full-Date endpoints while remaining outside scalar temporal indexing. Partially known input values, wider `SimpleDateFormat` syntax, and document application remain separate.
-/

namespace A12Kernel

namespace TemporalTargetText

/-- Render a bounded date/time component with at least two decimal digits. -/
def twoDigits (value : Nat) : String :=
  if value < 10 then "0" ++ toString value else toString value

end TemporalTargetText

/-- The only authorable Time target format in the bounded kernel profile. -/
inductive TimeTargetFormat where
  | wholeSecond
  deriving Repr, DecidableEq

namespace TimeTargetFormat

/-- Admit exactly the kernel's complete Time storage format. -/
def ofSource? : String → Option TimeTargetFormat
  | "HH:mm:ss" => some .wholeSecond
  | _ => none

/-- Render a whole-second clock without introducing a date or zone. -/
def renderText (_ : TimeTargetFormat) (time : TimeOfDay) : String :=
  let seconds := time.secondsSinceMidnight
  TemporalTargetText.twoDigits (seconds / 3600) ++ ":" ++
    TemporalTargetText.twoDigits ((seconds % 3600) / 60) ++ ":" ++
    TemporalTargetText.twoDigits (seconds % 60)

end TimeTargetFormat

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

/-- Render one real civil Date. The year is untruncated; day and month are always two digits, matching the kernel's computed-Date store before its later target checks. -/
def renderCivilText (format : FullDateTargetFormat) (date : CivilDate) : String :=
  let parts := date.parts
  match format with
  | .dayMonthYearDots =>
      TemporalTargetText.twoDigits parts.day ++ "." ++
        TemporalTargetText.twoDigits parts.month ++ "." ++
        toString parts.year
  | .yearMonthDayDashes =>
      toString parts.year ++ "-" ++
        TemporalTargetText.twoDigits parts.month ++ "-" ++
        TemporalTargetText.twoDigits parts.day

/-- Compatibility renderer for an already floor-admitted full Date. -/
def renderText (format : FullDateTargetFormat) (date : FullDate) : String :=
  format.renderCivilText date.civil

end FullDateTargetFormat

/-- A nonempty rendered temporal attempt indexed by its declared scalar kind. The phantom index prevents Date and DateTime target values from mixing while sharing their exact stored-text invariant. -/
structure StoredTemporalText (kind : TemporalKind) where
  text : String
  nonempty : text ≠ ""
  deriving Repr, DecidableEq

/-- Stored text for one checked Time target. -/
abbrev StoredTime := StoredTemporalText .time

namespace TimeTargetFormat

/-- Render a clock into the exact nonempty attempt consumed by the target basic check. -/
def render (format : TimeTargetFormat) (time : TimeOfDay) : StoredTime :=
  {
    text := format.renderText time
    nonempty := by
      cases format
      simp [renderText, TemporalTargetText.twoDigits]
  }

end TimeTargetFormat

/-- Root result before a checked Time target consumes it. Time has clock identity but no exact instant identity. -/
inductive TimeComputationResult where
  | noValue
  | value (time : TimeOfDay)
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

/-- Rich Time target result before source-relative classification or application. Every admitted clock passes the exact target basic check. -/
inductive TimeTargetOutcome where
  | noValue
  | accepted (stored : StoredTime)
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

/-- Stored text for one checked Date target. -/
abbrev StoredDate := StoredTemporalText .date

namespace FullDateTargetFormat

/-- Render one real civil Date into the exact nonempty attempt that the target basic check will consume. -/
def renderCivil (format : FullDateTargetFormat) (date : CivilDate) : StoredDate :=
  {
    text := format.renderCivilText date
    nonempty := by
      cases format <;>
        simp [renderCivilText, TemporalTargetText.twoDigits]
  }

/-- Render an admitted Date into a nonempty target attempt. -/
def render (format : FullDateTargetFormat) (date : FullDate) : StoredDate :=
  format.renderCivil date.civil

end FullDateTargetFormat

/-- Root result before a checked temporal target consumes it. Exact instant identity is retained until the target-specific renderer runs. -/
inductive TemporalComputationResult where
  | noValue
  | value (instant : Instant)
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

/-- Reachable basic target-check causes in the bounded computed-Date fragment. -/
inductive FullDateTargetError where
  | beforeGregorianFloor
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

/-- Exact whole-second DateTime declaration formats admitted by the executable target renderer. -/
inductive DateTimeTargetFormat where
  | dayMonthYearTime
  | yearMonthDayTime
  deriving Repr, DecidableEq

namespace DateTimeTargetFormat

/-- Admit only the bounded standard whole-second DateTime formats. -/
def ofSource? : String → Option DateTimeTargetFormat
  | "dd.MM.yyyy'T'HH:mm:ss" => some .dayMonthYearTime
  | "yyyy-MM-dd'T'HH:mm:ss" => some .yearMonthDayTime
  | _ => none

/-- Render one admitted local DateTime wall label. The exact source instant may retain finer precision than this text. -/
def renderText (format : DateTimeTargetFormat)
    (dateTime : LocalDateTime) : String :=
  let date := dateTime.date.civil.parts
  let seconds := dateTime.time.secondsSinceMidnight
  let hour := seconds / 3600
  let minute := (seconds % 3600) / 60
  let second := seconds % 60
  let timeText :=
    TemporalTargetText.twoDigits hour ++ ":" ++
      TemporalTargetText.twoDigits minute ++ ":" ++
      TemporalTargetText.twoDigits second
  match format with
  | .dayMonthYearTime =>
      TemporalTargetText.twoDigits date.day ++ "." ++
        TemporalTargetText.twoDigits date.month ++ "." ++
        toString date.year ++ "T" ++ timeText
  | .yearMonthDayTime =>
      toString date.year ++ "-" ++
        TemporalTargetText.twoDigits date.month ++ "-" ++
        TemporalTargetText.twoDigits date.day ++ "T" ++ timeText

end DateTimeTargetFormat

/-- Stored text for one checked DateTime target. -/
abbrev StoredDateTime := StoredTemporalText .dateTime

namespace DateTimeTargetFormat

/-- Render an admitted local DateTime into a nonempty target value. -/
def render (format : DateTimeTargetFormat)
    (dateTime : LocalDateTime) : StoredDateTime :=
  {
    text := format.renderText dateTime
    nonempty := by
      cases format
      · simp [renderText, TemporalTargetText.twoDigits]
      · intro empty
        have emptyLength := congrArg String.length empty
        simp [renderText] at emptyLength
  }

end DateTimeTargetFormat

/-- Rich DateTime target result before source-relative classification or application. This bounded fragment has no target-local rejection branch. -/
inductive DateTimeTargetOutcome where
  | noValue
  | accepted (stored : StoredDateTime)
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

namespace DateRangeFormat

/-- Render both resolved full-Date endpoints through the target policy's exact presentation. -/
def renderText (format : DateRangeFormat) (range : ResolvedDateRange) : String :=
  match format with
  | .isoSlash =>
      FullDateTargetFormat.renderText .yearMonthDayDashes range.start ++ "/" ++
        FullDateTargetFormat.renderText .yearMonthDayDashes range.finish
  | .dayMonthYearDash =>
      FullDateTargetFormat.renderText .dayMonthYearDots range.start ++ "-" ++
        FullDateTargetFormat.renderText .dayMonthYearDots range.finish

end DateRangeFormat

/-- A nonempty rendered DateRange target value kept separate from scalar temporal stored text. -/
structure StoredDateRange where
  text : String
  nonempty : text ≠ ""
  deriving Repr, DecidableEq

namespace DateRangeFormat

/-- Render one resolved DateRange into its exact nonempty target value. -/
def render (format : DateRangeFormat)
    (range : ResolvedDateRange) : StoredDateRange := {
  text := format.renderText range
  nonempty := by
    cases format <;>
    simp [renderText, FullDateTargetFormat.renderText,
      FullDateTargetFormat.renderCivilText, TemporalTargetText.twoDigits]
}

end DateRangeFormat

/-- Root result before a checked DateRange target consumes the selected typed interval. -/
inductive DateRangeComputationResult where
  | noValue
  | value (range : DateRangeValue)
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

/-- Target-owned rejection after a typed DateRange value has been rendered. -/
inductive DateRangeTargetError where
  | inverted
  deriving Repr, DecidableEq

/-- Rich DateRange target result before delta classification or application. -/
inductive DateRangeTargetOutcome where
  | noValue
  | accepted (stored : StoredDateRange)
  | errored (attempted : StoredDateRange) (cause : DateRangeTargetError)
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

/-- Structural failure while projecting a typed DateRange result into one exact target presentation. -/
inductive DateRangeTargetEvaluationFault where
  | unresolvedEndpoint (range : DateRangeValue)
  deriving Repr, DecidableEq

namespace DateRangeFormat

/-- Consume one typed DateRange computation result through the exact target renderer shared by every checked producer. -/
def evaluateComputationResult (format : DateRangeFormat) :
    DateRangeComputationResult →
      Except DateRangeTargetEvaluationFault DateRangeTargetOutcome
  | .noValue => .ok .noValue
  | .poison cause => .ok (.poison cause)
  | .value range =>
      match range.toResolvedDateRange? with
      | none => .error (.unresolvedEndpoint range)
      | some resolved =>
          let attempted := format.render resolved
          match resolved.direction with
          | .ordered => .ok (.accepted attempted)
          | .inverted => .ok (.errored attempted .inverted)

end DateRangeFormat

end A12Kernel
