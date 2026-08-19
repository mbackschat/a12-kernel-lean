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

/-- Render one resolved range through the declaration profile retained by a checked DateRange target. -/
def renderResolved : DateRangeInputFormat → ResolvedDateRange → StoredDateRange
  | .exact format, range => format.render range
  | .yearFragment, range => {
      text := toString range.start.civil.parts.year ++ "/" ++
        toString range.finish.civil.parts.year
      nonempty := by simp
    }
  | .yearMonthFragment, range => {
      text := toString range.start.civil.parts.year ++ "-" ++
        TemporalTargetText.twoDigits range.start.civil.parts.month ++ "/" ++
        toString range.finish.civil.parts.year ++ "-" ++
        TemporalTargetText.twoDigits range.finish.civil.parts.month
      nonempty := by simp
    }
  | .yearlessMonth, range =>
      renderYearlessMonth range.start.civil.parts.month
        range.finish.civil.parts.month
  | .yearlessMonthDay, range =>
      renderYearlessMonthDay
        { month := range.start.civil.parts.month
          day := range.start.civil.parts.day }
        { month := range.finish.civil.parts.month
          day := range.finish.civil.parts.day }

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

/-- Consume one exact or yearless typed result through its matching checked DateRange declaration profile. -/
def evaluateComputationResult (format : DateRangeInputFormat) :
    DateRangeComputationResult →
      Except DateRangeTargetEvaluationFault DateRangeTargetOutcome
  | .noValue => .ok .noValue
  | .poison cause => .ok (.poison cause)
  | .value (.exact range) => format.evaluateExactValue range
  | .value (.yearlessMonth start finish) =>
      match format with
      | .yearlessMonth =>
          let attempted := renderYearlessMonth start finish
          if finish < start then .ok (.errored attempted .inverted)
          else .ok (.accepted attempted)
      | _ => .ok (.poison .malformed)
  | .value (.yearlessMonthDay start finish) =>
      match format with
      | .yearlessMonthDay =>
          let attempted := renderYearlessMonthDay start finish
          if monthDayBefore finish start then
            .ok (.errored attempted .inverted)
          else .ok (.accepted attempted)
      | _ => .ok (.poison .malformed)

end A12Kernel.DateRangeInputFormat
