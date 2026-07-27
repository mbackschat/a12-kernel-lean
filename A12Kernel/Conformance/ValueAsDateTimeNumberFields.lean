import A12Kernel.Elaboration.ValueAsDateTimeNumberFields

/-! # Partial-Date and Number-field `Time(...)` locks -/

namespace A12Kernel.Conformance.ValueAsDateTimeNumberFields

open A12Kernel

private def componentField
    (id : FieldId) (constraints : NumericTargetConstraints)
    (info : NumField := { scale := 0, signed := false }) : FlatFieldDecl := {
  id
  groupPath := ["Order"]
  name := s!"Component{id}"
  policy := { kind := .number info }
  numericTargetConstraints := constraints
}

private def partialDate : FlatFieldDecl := {
  id := 0
  groupPath := ["Order"]
  name := "ApproxDate"
  policy := {
    kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some {
    format := "dd.MM.yyyy"
    partialMode := .yearOptional
    youngerThan1900Check := false } }

private def timeModel : FlatModel := {
  fields := [
    partialDate,
    componentField 1 { maxStoredLength := some 2 },
    componentField 2 { maxStoredLength := some 2 },
    componentField 3 { maxStoredLength := some 2 }]
  timeZoneId := "Europe/Berlin"
}

private def prepared? (model : FlatModel) :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption

private def document? (model : FlatModel)
    (cells : List ClassifiedCellInput) : Option (CheckedDocument model) := do
  let prepared ← prepared? model
  checkDocument prepared "en_US" {
    instantiatedRows := []
    cells
  } |>.toOption

private def numberCell (field : FieldId) (stored : String)
    (raw : RawCell) : ClassifiedCellInput := {
  address := { field, path := [] }
  stored
  raw
}

/- `Time(...)` checks the Number declaration's stored-length or exact-value bound; an
   integer-digit cap with the same numeral is not a substitute. -/
example :
    let storedLengthModel : FlatModel := {
      fields := [componentField 1 { maxStoredLength := some 2 }]
    }
    let integerDigitsModel : FlatModel := {
      fields := [componentField 1 { maxIntegerDigits := some 2 }]
    }
    (elaborateTimeNumberFields storedLengthModel
        (.hour 1)).isOk = true ∧
      (elaborateTimeNumberFields integerDigitsModel
        (.hour 1)).isOk = false := by
  native_decide

/- Fractional declarations and a position-specific maximum copied to the wrong slot are
   rejected before the document is read. -/
example :
    let fractional : FlatModel := {
      fields := [componentField 1 { maxStoredLength := some 2 }
        { scale := 1, signed := false }]
    }
    let hourBoundAtMinute : FlatModel := {
      fields := [componentField 1 { maximum := some 23 }]
    }
    (elaborateTimeNumberFields fractional (.hour 1)).isOk = false ∧
      (elaborateTimeNumberFields hourBoundAtMinute (.minute 1 1)).isOk = false := by
  native_decide

/- A signed declaration needs an explicit nonnegative minimum; the exact position maximum
   then remains a legal alternative to the stored-length bound. -/
example :
    let signedWithoutMinimum : FlatModel := {
      fields := [componentField 1 { maximum := some 23 }
        { scale := 0, signed := true }]
    }
    let signedWithMinimum : FlatModel := {
      fields := [componentField 1 { minimum := some 0, maximum := some 23 }
        { scale := 0, signed := true }]
    }
    (elaborateTimeNumberFields signedWithoutMinimum (.hour 1)).isOk = false ∧
      (elaborateTimeNumberFields signedWithMinimum (.hour 1)).isOk = true := by
  native_decide

/- A one-field prefix delegates trailing zeroes to the resolved constructor. A
   length-bounded field can still contain `24`, which is unreal rather than clamped. -/
example :
    let result (stored : String) (value : Rat) := do
      let checked ← (elaborateTimeNumberFields timeModel (.hour 1)).toOption
      let input ← document? timeModel [
        numberCell 1 stored (.parsed (.num value))]
      checked.evaluate .validation input |>.toOption
    result "10" 10 = some (.value
        ((TimeOfDay.ofHms? 10 0 0).get (by native_decide))) ∧
      result "24" 24 = some .unreal := by
  native_decide

/- Empty and formal inputs retain distinct construction reasons, and the first formal
   component wins in authored order. -/
example :
    let result (cells : List ClassifiedCellInput) := do
      let checked ←
        (elaborateTimeNumberFields timeModel (.second 1 2 3)).toOption
      let input ← document? timeModel cells
      checked.evaluate .computation input |>.toOption
    result [numberCell 1 "10" (.parsed (.num 10))] =
        some .incomplete ∧
      result [
        numberCell 1 "bad" (.rejected .malformed),
        numberCell 2 "100" (.rejected .declaredConstraint)] =
          some (.unavailable .malformed) := by
  native_decide

/- The checked payload classifier rejects a forged fractional Number instead of applying
   truncation that belongs only to other numeric operations. -/
example :
    let checked : CheckedTimeNumberField timeModel := {
      position := .hour
      source := { id := 1, info := { scale := 0, signed := false } }
      admitted := by native_decide
    }
    (match checked.classify (.value (.num (1 / 2))) with
    | .error (.nonIntegralPayload field value) =>
        field == 1 && value == (1 / 2)
    | _ => false) = true := by
  native_decide

/- A full checked prefix reaches the existing partial-Date DateTime constructor without
   reconstructing either document values or zone policy. -/
example :
    let expectedLocal := (LocalDateTime.ofYmdHms?
      2024 2 29 10 30 45).get (by native_decide)
    let expectedInstant :=
      (ModelZone.ConcreteProfile.europeBerlin.resolveLocal?
        expectedLocal).get (by native_decide)
    let result := do
      let time ←
        (elaborateTimeNumberFields timeModel (.second 1 2 3)).toOption
      let construction ←
        (elaborateValueAsDateTime timeModel 0 .lastDay).toOption
      let input ← document? timeModel [
        numberCell 1 "10" (.parsed (.num 10)),
        numberCell 2 "30" (.parsed (.num 30)),
        numberCell 3 "45" (.parsed (.num 45))]
      construction.evaluateNumberFieldsRaw time .validation input
        (.parsed "00.02.2024") |>.toOption
    result = some (.value expectedLocal expectedInstant) := by
  native_decide

end A12Kernel.Conformance.ValueAsDateTimeNumberFields
