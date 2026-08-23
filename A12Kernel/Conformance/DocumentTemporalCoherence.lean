import A12Kernel.Elaboration.CheckedDocument

/-! # Placed-temporal-cell coherence locks

`CheckedDocument.temporallyCoherent` reports whether every placed Date or DateTime cell agrees with the
value its own classifier derives from its stored text. It is a property a consumer asks for, never a
construction gate, and these cases fix both halves of that boundary: what it detects, and what it
deliberately does not.

**Internal, not measured.** Nothing here reads a kernel output. Each case pins this project's own
representation decision, which is why the deliberately incoherent documents below are *asserted*
incoherent rather than left as an unexamined accident of a fixture. -/

namespace A12Kernel.Conformance.DocumentTemporalCoherence

open A12Kernel

private def dateField : FlatFieldDecl := {
  id := 1
  groupPath := ["Policy"]
  name := "EffectiveOn"
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .full } }

private def momentField : FlatFieldDecl := {
  id := 2
  groupPath := ["Policy"]
  name := "SignedAt"
  policy := { kind := .temporal .dateTime TemporalComponents.now }
  temporalTargetPolicy := some {
    format := "yyyy-MM-dd'T'HH:mm:ss", partialMode := .full } }

/-- A partial Date: admitted by the model, outside every input classifier's ownership. -/
private def fragmentField : FlatFieldDecl := {
  id := 3
  groupPath := ["Policy"]
  name := "KnownMonth"
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some {
    format := "yyyy-MM-dd", partialMode := .dayOptional } }

private def clockField : FlatFieldDecl := {
  id := 4
  groupPath := ["Policy"]
  name := "PickupAt"
  policy := { kind := .temporal .time TemporalComponents.time }
  temporalTargetPolicy := some { format := "HH:mm:ss", partialMode := .full } }

/-- A Date declaration whose format is not a storable one, so no classifier certifies it. -/
private def uncertifiedField : FlatFieldDecl := {
  id := 5
  groupPath := ["Policy"]
  name := "LooseDate"
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some { format := "HH:mm:ss", partialMode := .full } }

private def model : FlatModel := {
  fields := [dateField, momentField, fragmentField, clockField, uncertifiedField]
  timeZoneId := "Europe/Berlin" }

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

/-- The value a certified Date declaration derives from `text`, so a coherent fixture is built the way a
real document is rather than by transcribing an instant. -/
private def canonicalDate (text : String) : RawCell :=
  match certifyFullDateInputField dateField with
  | .error _ => .rejected .dateFormat
  | .ok owner =>
      match owner.classifyStoredForModel model.timeZoneId text with
      | .ok raw => raw
      | .error _ => .rejected .dateFormat

private def canonicalMoment (text : String) : RawCell :=
  match certifyDateTimeInputField momentField with
  | .error _ => .rejected .dateFormat
  | .ok owner =>
      match owner.classifyStoredForModel model.timeZoneId text with
      | .ok raw => raw
      | .error _ => .rejected .dateFormat

private def coherent? (cells : List ClassifiedCellInput) : Option Bool := do
  let checked ←
    (checkDocument prepared "en_US" { instantiatedRows := [], cells }).toOption
  pure checked.temporallyCoherent

private def cell (field : FieldId) (stored : String) (raw : RawCell) :
    ClassifiedCellInput :=
  { address := { field, path := [] }, stored, raw }

/-- The same wall label as `momentField` carries, shifted by an exact millisecond remainder. -/
private def momentWithMillis (text : String) (remainder : Int) : RawCell :=
  match canonicalMoment text with
  | .parsed (.temporal (.dateTime instant parts clock basis)) =>
      .parsed (.temporal (.dateTime
        { epochMillis := instant.epochMillis + remainder } parts clock basis))
  | other => other

/- A document built the way a real one is: every placed value derived from its own stored text. Empty
and present-empty placements are coherent too, since emptiness is not a contradicted value. -/
example :
    coherent? [cell 1 "2024-02-29" (canonicalDate "2024-02-29"),
        cell 2 "2024-06-15T14:30:00" (canonicalMoment "2024-06-15T14:30:00")] =
      some true ∧
    coherent? [cell 1 "" .presentEmpty] = some true ∧
    coherent? [] = some true := by
  native_decide

/- A **formal rejection** is coherent when the stored text is the one that earns it, and incoherent when
the cell claims a different cause than the text produces. This is the arm that keeps a rejected cell from
being treated as unconstrained. -/
example :
    coherent? [cell 1 "2024-02-30" (canonicalDate "2024-02-30")] = some true ∧
    coherent? [cell 1 "2024-02-30" (.rejected .dateInvalid)] = some false ∧
    coherent? [cell 1 "2024-02-30" (.rejected .dateFormat)] = some true := by
  native_decide

/- **The separator the duplicate-value clause needs.** Two temporal cells may carry the same decoded date
under distinct stored texts, and equal stored text with different decoded values; both documents are
constructible, and both are reported incoherent. That is the whole point of a property rather than a
gate: the clause under `SPEC-2026-08-05-03` compares the stored text, so the disagreeing pair has to
remain expressible while still being recognisable as unreachable. -/
example :
    coherent? [cell 1 "2024-06-15" (canonicalDate "2024-01-01")] = some false ∧
    coherent? [cell 2 "2024-06-15T14:30:00"
      (canonicalMoment "2001-02-03T04:05:06")] = some false := by
  native_decide

/- **A sub-second remainder is coherent; a whole-hour disagreement is not.** Stored text cannot express
milliseconds, and this project already locks milliseconds surviving an exact shift, so a retained
remainder below one second is not a contradiction. An instant an hour away — a UTC-resolved label under
this non-UTC model zone — is one, so the tolerance does not quietly swallow a zone error. -/
example :
    coherent? [cell 2 "2024-06-15T14:30:00"
      (momentWithMillis "2024-06-15T14:30:00" 999)] = some true ∧
    coherent? [cell 2 "2024-06-15T14:30:00"
      (momentWithMillis "2024-06-15T14:30:00" (-999))] = some true ∧
    coherent? [cell 2 "2024-06-15T14:30:00"
      (momentWithMillis "2024-06-15T14:30:00" 1000)] = some false ∧
    coherent? [cell 2 "2024-06-15T14:30:00"
      (momentWithMillis "2024-06-15T14:30:00" 7200000)] = some false := by
  native_decide

/- **The declared coverage limit, asserted rather than assumed.** A partial Date, a Time, and a Date
whose declared format no classifier certifies are all reported coherent no matter what value they carry,
because none of them has an owner able to derive one. A consumer reading `true` must not conclude that
these three kinds were checked. -/
example :
    coherent? [cell 3 "2024-06" (canonicalDate "1999-01-01")] = some true ∧
    coherent? [cell 4 "14:30:00" (canonicalDate "1999-01-01")] = some true ∧
    coherent? [cell 5 "nonsense" (canonicalDate "1999-01-01")] = some true := by
  native_decide

end A12Kernel.Conformance.DocumentTemporalCoherence
