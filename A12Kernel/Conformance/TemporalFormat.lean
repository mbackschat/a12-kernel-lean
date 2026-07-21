import A12Kernel.Semantics.TemporalFormat

/-! # Temporal format-admission executable locks -/

namespace A12Kernel.Conformance.TemporalFormat

open A12Kernel

private def yearMonth : TemporalComponents :=
  { year := true, month := true, day := false, hour := false, minute := false, second := false }

private def fullDate : TemporalComponents :=
  { year := true, month := true, day := true, hour := false, minute := false, second := false }

private def monthDay : TemporalComponents :=
  { year := false, month := true, day := true, hour := false, minute := false, second := false }

private def fullDateTime : TemporalComponents :=
  { year := true, month := true, day := true, hour := true, minute := true, second := true }

private def hoursMinutes : TemporalComponents :=
  { year := false, month := false, day := false, hour := true, minute := true, second := false }

private def hoursMinutesSeconds : TemporalComponents :=
  { year := false, month := false, day := false, hour := true, minute := true, second := true }

/- Direct ordering admits unequal date component sets; aggregate admission does not. -/
example :
    TemporalComparisonOp.before.admitsFormats false yearMonth fullDate = true ∧
      temporalAggregateFormatsCompatible false yearMonth fullDate = false := by
  decide

/- Date and DateTime may be ordered, but equality requires matching time presence. -/
example :
    TemporalComparisonOp.before.admitsFormats false fullDate fullDateTime = true ∧
      TemporalComparisonOp.equal.admitsFormats false fullDate fullDateTime = false := by
  decide

/- Time comparison ignores a seconds-display mismatch; aggregate admission retains it. -/
example :
    TemporalComparisonOp.equal.admitsFormats false hoursMinutes hoursMinutesSeconds = true ∧
      temporalAggregateFormatsCompatible false hoursMinutes hoursMinutesSeconds = false := by
  decide

/- Base Year supplies the only otherwise-missing year component. -/
example :
    TemporalComparisonOp.before.admitsFormats false monthDay fullDate = false ∧
      TemporalComparisonOp.before.admitsFormats true monthDay fullDate = true ∧
      temporalAggregateFormatsCompatible true monthDay fullDate = true := by
  decide

/- Time-only and date-containing formats remain different comparison classes. -/
example : TemporalComparisonOp.before.admitsFormats false fullDate hoursMinutes = false := by
  decide

/- Full DateTime aggregate admission requires all six components. -/
example :
    fullDateTime.isFullDateTime = true ∧
      hoursMinutesSeconds.isFullDateTime = false := by
  decide

end A12Kernel.Conformance.TemporalFormat
