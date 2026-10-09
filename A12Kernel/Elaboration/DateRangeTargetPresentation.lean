import A12Kernel.Elaboration.DateRangeInput
import A12Kernel.Semantics.TemporalTarget

/-! # Shared checked DateRange target presentation -/

namespace A12Kernel.DateRangeInputFormat

/-- Render an ordered yearless month range without manufacturing a calendar year. -/
def renderYearlessMonth (start finish : Nat) : StoredDateRange := {
  text := TemporalTargetText.twoDigits start ++ "/" ++
    TemporalTargetText.twoDigits finish
  nonempty := by simp
}

/-- Render an ordered yearless month/day range without manufacturing a calendar year. -/
def renderYearlessMonthDay (start finish : MonthDayValue) : StoredDateRange := {
  text := TemporalTargetText.twoDigits start.month ++ "-" ++
    TemporalTargetText.twoDigits start.day ++ "/" ++
    TemporalTargetText.twoDigits finish.month ++ "-" ++
    TemporalTargetText.twoDigits finish.day
  nonempty := by simp
}

/-- Render an ordered yearless month range whose declaration carries no separator, concatenating the two months. -/
def renderYearlessMonthConcatenated (start finish : Nat) : StoredDateRange := {
  text := TemporalTargetText.twoDigits start ++ TemporalTargetText.twoDigits finish
  -- No literal separator anchors this text, so nonemptiness comes from both rendered components.
  nonempty := by
    simp only [TemporalTargetText.twoDigits]
    split <;> split <;> simp
}

/-- Render an ordered yearless day-and-month range under the dotted endpoint spelling and dash separator. -/
def renderYearlessDayMonthDotted (start finish : MonthDayValue) : StoredDateRange := {
  text := TemporalTargetText.twoDigits start.day ++ "." ++
    TemporalTargetText.twoDigits start.month ++ "-" ++
    TemporalTargetText.twoDigits finish.day ++ "." ++
    TemporalTargetText.twoDigits finish.month
  nonempty := by simp
}

/-- Render decoded endpoint components through a range profile. Input conversion and computed targets share this presentation (spec/05 §8). -/
def renderParts : DateRangeInputFormat → DateParts → DateParts → StoredDateRange
  | .exact .isoSlash, start, finish => {
      text := FullDateTargetFormat.yearMonthDayDashes.renderPartsText start ++ "/" ++
        FullDateTargetFormat.yearMonthDayDashes.renderPartsText finish
      nonempty := by simp }
  | .exact .dayMonthYearDash, start, finish => {
      text := FullDateTargetFormat.dayMonthYearDots.renderPartsText start ++ "-" ++
        FullDateTargetFormat.dayMonthYearDots.renderPartsText finish
      nonempty := by simp }
  | .yearFragment, start, finish => {
      text := toString start.year ++ "/" ++
        toString finish.year
      nonempty := by simp
    }
  | .yearMonthFragment, start, finish => {
      text := toString start.year ++ "-" ++
        TemporalTargetText.twoDigits start.month ++ "/" ++
        toString finish.year ++ "-" ++
        TemporalTargetText.twoDigits finish.month
      nonempty := by simp
    }
  | .yearlessMonth, start, finish =>
      renderYearlessMonth start.month
        finish.month
  | .yearlessMonthDay, start, finish =>
      renderYearlessMonthDay
        { month := start.month
          day := start.day }
        { month := finish.month
          day := finish.day }
  | .yearlessMonthConcatenated, start, finish =>
      renderYearlessMonthConcatenated start.month
        finish.month
  | .yearlessDayMonthDotted, start, finish =>
      renderYearlessDayMonthDotted
        { month := start.month
          day := start.day }
        { month := finish.month
          day := finish.day }

/-- Render a resolved computation result through the same stored presentation as input conversion. -/
def renderResolved (format : DateRangeInputFormat) (range : ResolvedDateRange) : StoredDateRange :=
  format.renderParts range.start.civil.parts range.finish.civil.parts

/-- Render one exact typed range through a checked DateRange declaration profile. -/
def evaluateExactValue (format : DateRangeInputFormat) (range : DateRangeValue) :
    Except DateRangeTargetEvaluationFault DateRangeTargetOutcome :=
  match format with
  | .exact exactFormat => exactFormat.evaluateComputationResult (.value range)
  | fragment =>
      match range.toResolvedDateRange? with
      | none => .error (.unresolvedEndpoint range)
      | some resolved =>
          let attempted := fragment.renderResolved resolved
          match resolved.direction with
          | .ordered => .ok (.accepted attempted)
          | .inverted => .ok (.errored attempted .inverted)

/-- Select the stored spelling of a month pair, or refuse a profile that retains different components. Every profile listed here shares one order rule. -/
def monthSpelling? :
    DateRangeInputFormat → Option (Nat → Nat → StoredDateRange)
  | .yearlessMonth => some renderYearlessMonth
  | .yearlessMonthConcatenated => some renderYearlessMonthConcatenated
  | _ => none

/-- Select the stored spelling of a month/day pair under the same rule. -/
def monthDaySpelling? :
    DateRangeInputFormat → Option (MonthDayValue → MonthDayValue → StoredDateRange)
  | .yearlessMonthDay => some renderYearlessMonthDay
  | .yearlessDayMonthDotted => some renderYearlessDayMonthDotted
  | _ => none

/-- Consume one exact or yearless typed result through a checked DateRange declaration profile that retains the same components. A profile retaining different components poisons the target rather than inventing a spelling. -/
def evaluateComputationResult (format : DateRangeInputFormat) :
    DateRangeComputationResult →
      Except DateRangeTargetEvaluationFault DateRangeTargetOutcome
  | .noValue => .ok .noValue
  | .poison cause => .ok (.poison cause)
  | .value (.exact range) => format.evaluateExactValue range
  | .value (.yearlessMonth start finish) =>
      match monthSpelling? format with
      | none => .ok (.poison .malformed)
      | some spelling =>
          let attempted := spelling start finish
          if finish < start then .ok (.errored attempted .inverted)
          else .ok (.accepted attempted)
  | .value (.yearlessMonthDay start finish) =>
      match monthDaySpelling? format with
      | none => .ok (.poison .malformed)
      | some spelling =>
          let attempted := spelling start finish
          if finish.before start then
            .ok (.errored attempted .inverted)
          else .ok (.accepted attempted)

end A12Kernel.DateRangeInputFormat
