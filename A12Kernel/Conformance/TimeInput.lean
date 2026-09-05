import A12Kernel.Elaboration.TimeInput

/-! # Time stored-input conformance locks

Every admission and cause is read off the kernel's own `validateFull` on both codegen strategies at the
Time-input checkpoint in [`SOURCES.md`](../../docs/SOURCES.md). -/

namespace A12Kernel.Conformance.TimeInput

open A12Kernel

private def fullClock : TemporalComponents :=
  { year := false, month := false, day := false
    hour := true, minute := true, second := true }

private def declaration (format : String := "HH:mm:ss")
    (kind : TemporalKind := .time) : FlatFieldDecl := {
  id := 0
  groupPath := ["Order"]
  name := "Pickup"
  policy := { kind := .temporal kind fullClock }
  temporalTargetPolicy := some { format, partialMode := .full }
}

private inductive Outcome where
  | absent
  | presentEmpty
  | rejected (cause : FormalCause)
  | clock (hour minute second : Nat)
  deriving Repr, DecidableEq

private def classify? (text : String) : Option Outcome := do
  let checked ← (certifyTimeInputField (declaration)).toOption
  let cell := checked.checkStored (.parsed text)
  pure <|
    match cell.parsed, cell.findings with
    | some clock, _ => .clock clock.hour clock.minute clock.second
    | none, cause :: _ => .rejected cause
    | none, [] => if cell.rawPresent then .presentEmpty else .absent

/- The admitted clock is decoded, not merely accepted: both boundary times and one ordinary one carry
their exact components through. -/
example :
    classify? "14:30:00" = some (.clock 14 30 0) ∧
      classify? "00:00:00" = some (.clock 0 0 0) ∧
      classify? "23:59:59" = some (.clock 23 59 59) := by
  native_decide

/- **One cause covers every failure in the certified clock profile.** A wrong component width and three
out-of-range components all report the date-format finding, and none reports the date finding because
this declared format carries no position in time. -/
example :
    classify? "14:5:0" = some (.rejected .dateFormat) ∧
      classify? "25:00:00" = some (.rejected .dateFormat) ∧
      classify? "12:60:00" = some (.rejected .dateFormat) ∧
      classify? "12:30:60" = some (.rejected .dateFormat) := by
  native_decide

/- Hour `24` is **not** an end-of-day spelling: it is refused exactly like hour `25`, so a consumer
must not admit it as midnight of the following day. This is the row a reader is most likely to get
wrong, because several other date-time vocabularies do accept it. -/
example :
    classify? "24:00:00" = some (.rejected .dateFormat) ∧
      classify? "23:00:00" = some (.clock 23 0 0) := by
  native_decide

/- Empty stored text is present and value-free rather than invalid, and physical absence is neither. -/
example :
    classify? "" = some .presentEmpty ∧
      ((certifyTimeInputField (declaration)).toOption.map
        (fun checked => (checked.checkStored .empty).rawPresent)) = some false := by
  native_decide

/- Certification is decided by the declared **format** and refuses only what that format does not
name. The refusal is reachable rather than defensive: the model gate checks a temporal format against
a kind-independent vocabulary, so a Time field may legally declare a date format, and such a
declaration belongs to the date classifier rather than to this one. -/
example :
    (certifyTimeInputField (declaration (format := "yyyy-MM-dd"))).toOption = none ∧
      (certifyTimeInputField (declaration)).toOption.isSome = true := by
  native_decide

/- **The declared kind is not read**, and every kind that may carry the clock format is certified by
it. This row read `none` for the two cross-kind declarations until the kind conjunct was removed, and
that refusal was the divergence: the Kernel classifies such a cell's text exactly as it classifies a
TIME field's, over the complete twelve-format vocabulary on all three date-bearing kinds
([inbound](../../docs/SOURCES.md#inbound-2026-09-05b)). A conjunct here left the cell classified by
**no** classifier at all, so its text could not be classified rather than being classified wrongly. -/
example :
    (certifyTimeInputField (declaration (kind := .date))).toOption.isSome = true ∧
      (certifyTimeInputField (declaration (kind := .dateTime))).toOption.isSome =
        true := by
  native_decide

/- And they classify **identically**, which is the claim rather than mere admission: one ordinary
value, one out-of-range component, and empty, read back through all three kinds. Admission alone
would leave a classifier free to decode a DATE-declared clock differently. -/
example :
    let byKind (kind : TemporalKind) (text : String) : Option Outcome := do
      let checked ← (certifyTimeInputField (declaration (kind := kind))).toOption
      let cell := checked.checkStored (.parsed text)
      pure <|
        match cell.parsed, cell.findings with
        | some clock, _ => .clock clock.hour clock.minute clock.second
        | none, cause :: _ => .rejected cause
        | none, [] => if cell.rawPresent then .presentEmpty else .absent
    ["14:30:00", "25:00:00", ""].all fun text =>
      byKind .date text == byKind .time text &&
        byKind .dateTime text == byKind .time text := by
  native_decide

/- The phase read is where one formal invalidity becomes two consumer-visible states, which is the
invariant every input classifier in this project shares. -/
example :
    ((certifyTimeInputField (declaration)).toOption.map
        (fun checked => checked.observe .validation (.parsed "25:00:00"))) =
        some (.unknown .dateFormat) ∧
      ((certifyTimeInputField (declaration)).toOption.map
        (fun checked => checked.observe .computation (.parsed "25:00:00"))) =
        some (.poison .dateFormat) := by
  native_decide

end A12Kernel.Conformance.TimeInput
