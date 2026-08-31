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

/-- The only format this bounded Time computation target owns. -/
inductive TimeTargetFormat where
  | wholeSecond
  deriving Repr, DecidableEq

namespace TimeTargetFormat

/-- Admit exactly this target profile's complete clock format. -/
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

/-- The year-leading component-omitting Date declaration formats, as **target renderings only**.

    This is deliberately a separate type from `FullDateTargetFormat` rather than three more of its
    constructors. That one carries `parseComponents?`, which reads a *stored* cell back into a date;
    widening it would force an answer to how a stored `2024` parses, and that has never been
    measured. Rendering into such a target has been
    ([checkpoint](../../docs/SOURCES.md#src-component-omitting-date-formats)), so the two questions
    are kept apart and only the measured one is modeled.

    The yearless `MM` and `MM-dd` are **excluded**: the Kernel refuses a date constant for them
    unless the model declares a Base Year, and what such a target then stores is unmeasured. -/
inductive OmittedComponentDateFormat where
  | yearOnly
  | yearMonthDashes
  | yearMonthCompact
  | monthOnly
  | monthDayDashes
  deriving Repr, DecidableEq

namespace OmittedComponentDateFormat

/-- Admit only the three exact declaration sources this renderer implements. -/
def ofSource? : String → Option OmittedComponentDateFormat
  | "yyyy" => some .yearOnly
  | "yyyy-MM" => some .yearMonthDashes
  | "yyyyMM" => some .yearMonthCompact
  | "MM" => some .monthOnly
  | "MM-dd" => some .monthDayDashes
  | _ => none

/-- Whether the declaration is **yearless**, which is the Kernel's own gate: such a target refuses a
Date constant unless the model declares a Base Year, and admits it once one is declared. The Base
Year reaches admission only and contributes no component to the rendering below
([checkpoint](../../docs/SOURCES.md#src-base-year-yearless-store)). -/
def needsBaseYear : OmittedComponentDateFormat → Bool
  | .yearOnly | .yearMonthDashes | .yearMonthCompact => false
  | .monthOnly | .monthDayDashes => true

/-- Render one real civil Date, keeping exactly the components the format names and its own
separator. Measured: `2024`, `2024-03`, `202403`, `03`, and `03-05` for the same 5 March 2024, with
the omitted components discarded and nothing reported. A yearless format writes **no year** even
where the model declares a Base Year, so nothing here reads one. -/
def renderCivilText (format : OmittedComponentDateFormat) (date : CivilDate) : String :=
  let parts := date.parts
  match format with
  | .yearOnly => toString parts.year
  | .yearMonthDashes =>
      toString parts.year ++ "-" ++ TemporalTargetText.twoDigits parts.month
  | .yearMonthCompact =>
      toString parts.year ++ TemporalTargetText.twoDigits parts.month
  | .monthOnly => TemporalTargetText.twoDigits parts.month
  | .monthDayDashes =>
      TemporalTargetText.twoDigits parts.month ++ "-" ++
        TemporalTargetText.twoDigits parts.day

/-- A rendered year is at least one character. The two-component formats get their nonemptiness from
their trailing month digits, but a year-only rendering has no literal to lean on, so the digit
expansion has to be shown nonempty directly. -/
private theorem toDigitsCore_ne_nil (base : Nat) :
    ∀ (fuel n : Nat) (acc : List Char), acc ≠ [] →
      Nat.toDigitsCore base fuel n acc ≠ []
  | 0, _, acc, h => by simpa [Nat.toDigitsCore] using h
  | fuel + 1, n, acc, h => by
      unfold Nat.toDigitsCore
      dsimp only
      split
      · simp
      · exact toDigitsCore_ne_nil base fuel (n / base) _ (by simp)

private theorem toDigits_ne_nil (n : Nat) : Nat.toDigits 10 n ≠ [] := by
  unfold Nat.toDigits Nat.toDigitsCore
  dsimp only
  split
  · simp
  · exact toDigitsCore_ne_nil 10 n (n / 10) _ (by simp)

private theorem intRepr_ne_empty (i : Int) : Int.repr i ≠ "" := by
  cases i with
  | ofNat n =>
      simp only [Int.repr]
      intro contra
      have := congrArg String.toList contra
      simp [Nat.repr] at this
  | negSucc n => simp [Int.repr]

/-- A two-digit rendering is nonempty on both branches. The padded branch has its own literal; the
unpadded one needs the same digit-expansion fact the year uses. -/
private theorem twoDigits_ne_empty (value : Nat) :
    TemporalTargetText.twoDigits value ≠ "" := by
  unfold TemporalTargetText.twoDigits
  split
  · simp
  · intro contra
    have := congrArg String.toList contra
    simp [Nat.repr] at this

/-- Render into the exact nonempty attempt a component-omitting target stores. -/
def renderCivil (format : OmittedComponentDateFormat) (date : CivilDate) : StoredDate :=
  {
    text := format.renderCivilText date
    nonempty := by
      cases format
      case monthOnly =>
        simpa [renderCivilText] using twoDigits_ne_empty date.parts.month
      all_goals
        simp [renderCivilText, TemporalTargetText.twoDigits,
          intRepr_ne_empty date.parts.year]
  }

end OmittedComponentDateFormat

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
  | yearMonthDayTime
  deriving Repr, DecidableEq

namespace DateTimeTargetFormat

/-- Admit this bounded target's ISO whole-second DateTime profile. The model gate refuses the day-first
`dd.MM.yyyy'T'HH:mm:ss` spelling outright: that string tags DateTime-valued expressions rather than a
declaration format. Other legal vocabulary formats on a DateTime declaration remain outside this target
renderer rather than being rejected as model-level authoring. -/
def ofSource? : String → Option DateTimeTargetFormat
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
      intro empty
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

/-- Root result before a checked DateRange target consumes one exact or yearless typed interval. -/
inductive DateRangeComputationResult where
  | noValue
  | value (range : DateRangeCellValue)
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

/-- Structural failure while projecting one exact typed DateRange value into a checked target presentation. -/
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
  | .value (.exact range) =>
      match range.toResolvedDateRange? with
      | none => .error (.unresolvedEndpoint range)
      | some resolved =>
          let attempted := format.render resolved
          match resolved.direction with
          | .ordered => .ok (.accepted attempted)
          | .inverted => .ok (.errored attempted .inverted)
  | .value _ => .ok (.poison .malformed)

end DateRangeFormat

end A12Kernel
