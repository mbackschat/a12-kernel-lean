import A12Kernel.Elaboration.DateFromDateTime
import A12Kernel.Elaboration.ValueAsDateTimeExtraction

/-! # `DateFromDateTime` locks

The Date-valued half of the DateTime component extractors, and the sibling of `TimeFromDateTime`.

**What the Kernel decided, measured at 30.8.1 on both codegen strategies.** The extraction reports the
stored DateTime label's **own** date components: a wall label of `2024-06-15T00:30:00` extracts to
`2024-06-15`, where a conversion to UTC under the recorded `+0200` model zone would have produced
`2024-06-14` and fired the rival rule instead. The time is dropped. Static admission is measured too:
the result is a **Date**, comparable to a Date field, to `Today`, and to another extraction, and admitted
as a Date-addition operand, while `Now` and a `TimeFromDateTime` result are refused
`MVK_INVALID_COMPARE_TO_DATE`. A degenerate time-only DateTime source and a plain Date source are both
refused `MVK_WRONG_DATE_FORMAT_FOR_OP` at the operator.

The retained instant is this project's account rather than a measured fact: validation output carries no
instant, so the extracted Date's own midnight is constructed the way every other stored Date in this
theory is, and the two-zone case below locks that choice instead of a correspondence. -/

namespace A12Kernel.Conformance.DateFromDateTime

open A12Kernel

private def berlin : ModelZone.ConcreteProfile := .europeBerlin

private def label (year : Int) (month day hour minute second : Nat) :
    Option LocalDateTime :=
  LocalDateTime.ofYmdHms? year month day hour minute second

/-- One complete DateTime runtime value at a wall label, resolved in the model zone. -/
private def momentAt (profile : ModelZone.ConcreteProfile)
    (year : Int) (month day hour minute second : Nat) : Option TemporalValue := do
  let wall ← label year month day hour minute second
  let instant ← profile.resolveLocal? wall
  pure (.dateTime instant wall.date.civil.parts wall.time .storedGregorian)

/-- The extracted date's components, which is what a comparison against a Date field reads. -/
private def extractedParts? (profile : ModelZone.ConcreteProfile)
    (value : Option TemporalValue) : Option (Int × Nat × Nat) := do
  let moment ← value
  let extracted ← dateFromDateTime? profile moment
  pure (extracted.parts.year, extracted.parts.month, extracted.parts.day)

/- **The measured separator.** A wall label just after midnight keeps its own date. Converting the
retained instant to UTC first would give the previous day under this zone, which is the account the
Kernel refused. -/
example :
    extractedParts? berlin (momentAt berlin 2024 6 15 0 30 0) = some (2024, 6, 15) ∧
      extractedParts? berlin (momentAt berlin 2024 6 15 13 45 0) = some (2024, 6, 15) ∧
      extractedParts? berlin (momentAt berlin 2024 6 15 23 30 0) = some (2024, 6, 15) := by
  native_decide

/- That the label's date survives is not an artifact of one offset: the same wall label extracts to the
same date under the UTC profile, where no conversion could shift it either way. -/
example :
    extractedParts? .utc (momentAt .utc 2024 6 15 0 30 0) = some (2024, 6, 15) := by
  native_decide

/- The time is dropped rather than retained, and the calendar provenance travels with the date. -/
example :
    (do
      let moment ← momentAt berlin 2024 6 15 13 45 30
      let extracted ← dateFromDateTime? berlin moment
      pure extracted.basis) = some .storedGregorian := by
  native_decide

/- **Internal, not measured.** The extracted Date's own instant is that date's *midnight* in the model
zone, not the source instant, so the value is indistinguishable from a stored Date carrying the same
text. Under Europe/Berlin the two differ by the label's own time of day plus the midnight offset, which
is what makes this a choice rather than a projection. -/
example :
    (do
      let moment ← momentAt berlin 2024 6 15 13 45 0
      let extracted ← dateFromDateTime? berlin moment
      let midnightLabel ← label 2024 6 15 0 0 0
      let midnight ← berlin.resolveLocal? midnightLabel
      pure (extracted.instant == midnight,
        extracted.instant == moment.instant)) = some (true, false) := by
  native_decide

/- A Date, a Time, and an absent value are not this operator's source: only a DateTime payload extracts,
which is the runtime half of the measured `MVK_WRONG_DATE_FORMAT_FOR_OP` refusal. -/
example :
    (do
      let moment ← momentAt berlin 2024 6 15 13 45 0
      let extracted ← dateFromDateTime? berlin moment
      pure (dateFromDateTime? berlin (.date extracted)).isNone) = some true := by
  native_decide

/- A label the model zone cannot resolve has no extraction rather than a fabricated one. Reachable only
for a forged payload, since a checked DateTime cell carries a resolved instant by construction. -/
example :
    dateFromDateTime? berlin
        (.dateTime { epochMillis := 0 } { year := 1943, month := 2, day := 30 }
          ⟨0, 0, 0, by decide⟩ .storedGregorian) = none := by
  native_decide

/-! ## Static admission

Every row is `KERNEL_CONFIRMED` at 30.8.1 through `rule add --dry-run`. The Kernel reports one class,
`MVK_WRONG_DATE_FORMAT_FOR_OP`, for each refused source; the arms below are finer so a consumer can say
which requirement failed. -/

private def momentField : FlatFieldDecl := {
  id := 1
  groupPath := ["Order"]
  name := "Moment"
  policy := { kind := .temporal .dateTime TemporalComponents.now }
  temporalTargetPolicy := some {
    format := "yyyy-MM-dd'T'HH:mm:ss", partialMode := .full } }

/-- The degenerate time-only DateTime: a legal declaration the Kernel refuses at this operator. -/
private def clockField : FlatFieldDecl :=
  { momentField with
    id := 2
    name := "Clock"
    policy := { kind := .temporal .dateTime TemporalComponents.time }
    temporalTargetPolicy := some { format := "HH:mm:ss", partialMode := .full } }

private def dateField : FlatFieldDecl :=
  { momentField with
    id := 3
    name := "WallDate"
    policy := { kind := .temporal .date TemporalComponents.fullDate }
    temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .full } }

private def model (zoneId : String := "Europe/Berlin") : FlatModel := {
  fields := [momentField, clockField, dateField]
  timeZoneId := zoneId }

private def elabError? (field : FieldId) (zoneId : String := "Europe/Berlin") :
    Option DateFromDateTimeElabError :=
  match elaborateDateFromDateTime (model zoneId) field with
  | .ok _ => none
  | .error error => some error

/- The complete DateTime source is admitted; the degenerate time-only declaration and a plain Date field
are refused, which is the pair the Kernel reports under one code at the operator. The two refusals stay
distinguishable here: an incomplete component set is not a wrong kind. -/
example :
    (elaborateDateFromDateTime (model) 1).isOk = true ∧
      elabError? 2 = some (.sourceComponents 2 TemporalComponents.time) ∧
      elabError? 3 = some (.sourceKind 3 .date) := by
  native_decide

/- A source the model does not declare is a resolution failure rather than a format one. -/
example :
    elabError? 9 = some (.source (.unknownFieldId 9)) := by
  native_decide

/- The extracted Date's midnight needs a zone this theory implements, so an unsupported model zone is
explicit insufficient context rather than a silent UTC fallback. -/
example :
    elabError? 1 "Pacific/Auckland" = some (.unsupportedZone "Pacific/Auckland") ∧
      (elaborateDateFromDateTime (model "UTC") 1).isOk = true := by
  native_decide

/- The certificate carries the zone it resolved, so a consumer reads the same profile the extraction
used rather than re-deriving one. Both profiles extract the label's own date; they differ only in the
retained midnight. -/
example :
    (do
      let checked ← (elaborateDateFromDateTime (model) 1).toOption
      let utcChecked ← (elaborateDateFromDateTime (model "UTC") 1).toOption
      let moment ← momentAt berlin 2024 6 15 13 45 0
      let berlinDate ← checked.extract? moment
      let utcDate ← utcChecked.extract? moment
      pure (berlinDate.parts == utcDate.parts,
        berlinDate.instant == utcDate.instant)) = some (true, false) := by
  native_decide

/- `TimeFromDateTime` imposes the **same** source requirement, which is measured rather than inherited:
one predicate now answers for both extractors. -/
example :
    ((model).admitsCompleteDateTimeSource
        (momentField.toTemporalField?.get (by native_decide))) = true ∧
      ((model).admitsValueAsDateTimeExtractionSource
        (momentField.toTemporalField?.get (by native_decide))) = true ∧
      ((model).admitsCompleteDateTimeSource
        (clockField.toTemporalField?.get (by native_decide))) = false := by
  native_decide

end A12Kernel.Conformance.DateFromDateTime
