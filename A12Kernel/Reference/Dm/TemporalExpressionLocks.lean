import A12Kernel.Reference.Dm.LowerDocument
import A12Kernel.Reference.Dm.LowerValidation
import A12Kernel.Reference.Dm.Parser

namespace A12Kernel.Dm.TemporalExpressionLocks

open A12Kernel A12Kernel.Dm

private def model : FlatModel := {
  fields := [
    {
      id := 5
      groupPath := ["Order"]
      name := "Due1"
      policy := { kind := .temporal .date TemporalComponents.fullDate }
      temporalTargetPolicy := some { format := "yyyy-MM-dd" }
    }, {
      id := 6
      groupPath := ["Order"]
      name := "Clock"
      policy := { kind := .temporal .time TemporalComponents.time }
      temporalTargetPolicy := some { format := "HH:mm:ss" }
    }, {
      id := 7
      groupPath := ["Order"]
      name := "Stamp"
      policy := { kind := .temporal .dateTime TemporalComponents.now }
      temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" }
    }, {
      id := 8
      groupPath := ["Order"]
      name := "Stamp2"
      policy := { kind := .temporal .dateTime TemporalComponents.now }
      temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" }
    }]
}

private def admitted (text : String) : Bool :=
  match parseText .english text with
  | .ok parsed => (lowerCondition model ["Order"] false parsed.body).toOption.isSome
  | .error _ => false

private def operationAdmitted (text : String) : Bool :=
  match parseText .english text, model.lookupUniqueId 7 with
  | .ok parsed, .ok target =>
      (lowerDocumentStep model ["Order"] target parsed.body).toOption.isSome
  | _, _ => false

example :
    !admitted "Stamp == Now" ∧
      !admitted "{Stamp} == Now" ∧
      !admitted "Min(Stamp, Stamp2) == Now" ∧
      !operationAdmitted "Stamp2" ∧
      admitted "[Stamp] == Now" ∧
      admitted "{[Stamp]} == Now" ∧
      admitted "Min([Stamp], [Stamp2]) == Now" ∧
      operationAdmitted "[Stamp2]" := by native_decide

example :
    !admitted "AddHours(Min(Now, [Stamp]), 1) == Now" ∧
      !admitted "TimeFromDateTime(MinValue(Stamp, Stamp2)) == [Clock]" ∧
      !admitted "TimeFromDateTime([Stamp]) == [Clock]" ∧
      admitted "TimeFromDateTime(Stamp) == [Clock]" ∧
      admitted "Min(Now, [Stamp]) == Now" := by native_decide

private def stored (targetField : FieldId) (text : String) : Option String := do
  let parsed ← (parseText .english text).toOption
  let target ← (model.lookupUniqueId targetField).toOption
  let step ← (lowerDocumentStep model ["Order"] target parsed.body).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" { instantiatedRows := [], cells := [] }).toOption
  let (outcome, _) ← (step.run { now := { epochMillis := 0 } } (fun _ => none) document).toOption
  pure (match outcome with
    | .fullDate (.accepted value) => value.text
    | .time (.accepted value) => value.text
    | .dateTime (.accepted value) => value.text
    | _ => "unavailable")

example :
    admitted "DateFromDateTime(AddHours(Now, 25)) == Today" ∧
      admitted "TimeFromDateTime(AddMinutes(Now, 90)) == \"01:30:00\"" ∧
      !admitted "\"01:30:00\" == \"01:30:00\"" ∧
      admitted "{Now} == Now" ∧
      !admitted "{Now} == {Now}" ∧
      !admitted "AddHours(\"01:30:00\", 1) == Now" := by native_decide

example :
    stored 5 "DateFromDateTime(AddHours(Now, 25))" = some "1970-01-02" ∧
      stored 6 "Time(\"1\", \"30\")" = some "01:30:00" ∧
      stored 7 "AddSeconds(Now, 61)" = some "1970-01-01T00:01:01" ∧
      stored 7 "AddHours(Stamp, 1)" = none := by native_decide

example :
    admitted "MinValue(Stamp, Stamp2) == [Stamp]" ∧
      !admitted "DateFromDateTime(MinValue(Stamp, Stamp2)) == Today" ∧
      !admitted "AddHours(MinValue(Stamp, Stamp2), 1) == Now" ∧
      !admitted "AddHours({Now}, 1) == Now" ∧
      !admitted "AddHours([Stamp], 1) == Now" ∧
      admitted "AddHours(Stamp, 1) == Now" ∧
      admitted "DateFromDateTime(AddHours(Now, 25)) == Today" ∧
      admitted "AddHours(AddSeconds(Now, 1), 1) == Now" := by native_decide

private def gapResult (targetField : FieldId) (text : String) :
    Option (DocumentTargetOutcome × CheckedCell) := do
  let berlin := { model with timeZoneId := "Europe/Berlin" }
  let parsed ← (parseText .english text).toOption
  let target ← (berlin.lookupUniqueId targetField).toOption
  let step ← (lowerDocumentStep berlin ["Order"] target parsed.body).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler berlin).toOption
  let document ← (checkDocument prepared "en_US" { instantiatedRows := [], cells := [] }).toOption
  (step.run world (fun _ => none) document).toOption

example :
    gapResult 7 "\"31.03.2024T02:30:00\"" =
        some (.valueError .dateTime, DocumentComputationReadBack.empty) ∧
      gapResult 7 "AddSeconds(\"31.03.2024T02:30:00\", 1)" =
        some (.valueError .dateTime, DocumentComputationReadBack.empty) ∧
      gapResult 5 "DateFromDateTime(\"31.03.2024T02:30:00\")" =
        some (.valueError .fullDate, DocumentComputationReadBack.empty) ∧
      gapResult 6 "TimeFromDateTime(\"31.03.2024T02:30:00\")" =
        some (.valueError .time, DocumentComputationReadBack.empty) := by native_decide

example :
    (DocumentTargetOutcome.valueError .dateTime).storedText? = none ∧
      (DocumentTargetOutcome.valueError .dateTime).formalValueMessage?
          (MessagePointer.ofCellAddr { field := 7, path := [] }) =
        some {
          pointer := MessagePointer.ofCellAddr { field := 7, path := [] }
          errorCode := berechnungsWertFehler
          messageType := .value
          payload := () } ∧
      (DocumentTargetOutcome.dateTime .noValue).formalValueMessage?
          (MessagePointer.ofCellAddr { field := 8, path := [] }) = none := by native_decide

end A12Kernel.Dm.TemporalExpressionLocks
