import A12Kernel.Semantics.FlatValidation

/-! # Admitted temporal value payload locks -/

namespace A12Kernel.Conformance.TemporalValue

open A12Kernel

private def instant : Instant := { epochMillis := 1719292867000 }

private def dateParts : DateParts :=
  { year := 2024, month := 6, day := 25 }

private def clock : TimeOfDay :=
  (TimeOfDay.ofHms? 5 21 7).get (by native_decide)

private def datePayload : TemporalValue :=
  .date instant dateParts .storedGregorian

private def dateTimePayload : TemporalValue :=
  .dateTime instant dateParts clock .storedGregorian

private def dateField : FlatTemporalField :=
  { id := 1, kind := .date
    components :=
      { year := true, month := true, day := true
        hour := false, minute := false, second := false } }

private def dateTimeField : FlatTemporalField :=
  { id := 2, kind := .dateTime
    components :=
      { year := true, month := true, day := true
        hour := true, minute := true, second := true } }

private def context : FlatContext where
  read id :=
    if id = dateField.id then
      { rawPresent := true, parsed := some (.temporal datePayload), findings := [] }
    else if id = dateTimeField.id then
      { rawPresent := true, parsed := some (.temporal dateTimePayload), findings := [] }
    else
      { rawPresent := false, parsed := none, findings := [] }

/- Exact comparison identity and decoded numeric components are two projections of the same checked Date payload. -/
example :
    context.resolveTemporalComparisonOperand dateField =
        .value instant true ∧
      context.resolveDateNumericOperand dateField .day =
        .value 25 .fixed ∧
      context.resolveDateNumericOperand dateField .quarter =
        .value 2 .fixed := by
  native_decide

/- One checked DateTime payload serves instant comparison plus both component families. -/
example :
    context.resolveTemporalComparisonOperand dateTimeField =
        .value instant true ∧
      context.resolveDateNumericOperand dateTimeField .year =
        .value 2024 .fixed ∧
      context.resolveTimeNumericOperand dateTimeField .minute =
        .value 21 .fixed := by
  native_decide

/- Low-level cross-family component reads fail closed even when a malformed caller bypasses authored admission. -/
example :
    context.resolveTimeNumericOperand dateField .hour =
      .unknown .malformed := by
  native_decide

/- The closed constructors derive kind, retain the available component halves and calendar basis, and exclude unavailable projections. -/
example :
    (TemporalValue.date instant dateParts .storedGregorian).kind = .date ∧
      (TemporalValue.time instant clock).kind = .time ∧
      (TemporalValue.dateTime instant dateParts clock .legacyHybrid).kind =
        .dateTime ∧
      (TemporalValue.dateTime instant dateParts clock .legacyHybrid).instant =
        instant ∧
      (TemporalValue.dateTime instant dateParts clock .legacyHybrid).dateParts? =
        some dateParts ∧
      (TemporalValue.dateTime instant dateParts clock .legacyHybrid).time? =
        some clock ∧
      (TemporalValue.dateTime instant dateParts clock .legacyHybrid).calendarBasis? =
        some .legacyHybrid ∧
      (TemporalValue.time instant clock).dateParts? = none ∧
      (TemporalValue.time instant clock).calendarBasis? = none ∧
      (TemporalValue.date instant dateParts .storedGregorian).time? = none := by
  native_decide

end A12Kernel.Conformance.TemporalValue
