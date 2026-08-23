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

/- **One cause covers every failure.** A wrong component width and three out-of-range components all
report the date-format finding, and none reports the date finding — a clock has no position in time to
fall below a floor, which is the whole difference from Date and DateTime input. -/
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

/- Certification is refused for a declaration this classifier does not own, and both refusals are
**reachable** rather than defensive: the model gate checks a temporal format against a kind-independent
vocabulary, so a Time field may legally declare a date format and a Date field may legally declare the
clock format. Neither is silently read as a clock here. -/
example :
    (certifyTimeInputField (declaration (format := "yyyy-MM-dd"))).toOption = none ∧
      (certifyTimeInputField (declaration (kind := .date))).toOption = none ∧
      (certifyTimeInputField (declaration)).toOption.isSome = true := by
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
