import A12Kernel.Elaboration.DateRangeConstructionComparison

/-! # DateRange construction-operand refusal locks

These cases isolate which operand shapes a `DateRange(start, finish)` construction refuses and
which Kernel diagnostic each refusal reports. The verdicts are the Kernel rows in the
operand-grid checkpoint, decided through the real consistency oracle. The value paths, target
admission, and rendering keep their own module.
-/

namespace A12Kernel.Conformance.DateRangeConstructionOperand

open A12Kernel

private def dateField (id : FieldId) (name : String) : FlatFieldDecl := {
  id
  groupPath := ["Order"]
  name
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .full }
}

private def start := dateField 1 "Start"
private def finish := dateField 2 "Finish"

private def monthFragment : FlatFieldDecl := {
  dateField 3 "MonthFragment" with
  temporalTargetPolicy := some { format := "MM", partialMode := .yearOptional }
}

private def numberEndpoint : FlatFieldDecl := {
  id := 4
  groupPath := ["Order"]
  name := "Count"
  policy := { kind := .number { scale := 0, signed := false } }
}

private def stringEndpoint : FlatFieldDecl := {
  id := 5
  groupPath := ["Order"]
  name := "Note"
  policy := { kind := .string }
}

private def dateTimeEndpoint : FlatFieldDecl := {
  dateField 6 "Stamp" with
  policy := { kind := .temporal .dateTime TemporalComponents.now }
  temporalTargetPolicy := some {
    format := "yyyy-MM-dd'T'HH:mm:ss"
    partialMode := .full
  }
}

private def rangeEndpoint : FlatFieldDecl := {
  id := 7
  groupPath := ["Order"]
  name := "OtherWindow"
  policy := { kind := .dateRange }
  dateRangePolicy := some { format := "dd.MM.yyyy", separator := "-" }
}

private def repeatableEndpoint : FlatFieldDecl := {
  dateField 8 "RowDate" with
  groupPath := ["Order", "Rows"]
  repeatableScope := [10]
}

private def model : FlatModel := {
  fields := [start, finish, monthFragment, numberEndpoint, stringEndpoint,
    dateTimeEndpoint, rangeEndpoint, repeatableEndpoint]
  repeatableGroups := [
    { level := 10, path := ["Order", "Rows"], repeatability := some 5 }]
  timeZoneId := "UTC"
}

private def diagnostic? (startField finishField : FieldId) :
    Option KernelStaticDiagnostic :=
  match elaborateDateRangeConstruction model startField finishField with
  | .ok _ => none
  | .error cause => cause.diagnostic?

/- Every operand whose declared kind is not a Date-shaped temporal field reports the one
wrong-format class, so a Number, a String, a DateTime, and a DateRange operand are
indistinguishable by code, and a pair whose component sets disagree joins them in either
authored order. A repeatable operand reached from outside its group reports the missing-wildcard
class instead, which is the one operand refusal this boundary separates. -/
example :
    [diagnostic? numberEndpoint.id finish.id,
      diagnostic? stringEndpoint.id finish.id,
      diagnostic? dateTimeEndpoint.id finish.id,
      diagnostic? rangeEndpoint.id finish.id,
      diagnostic? start.id numberEndpoint.id,
      diagnostic? monthFragment.id finish.id,
      diagnostic? start.id monthFragment.id] =
      List.replicate 7 (some .wrongDateFormatForOp) ∧
    diagnostic? repeatableEndpoint.id finish.id = some .noWildcard ∧
    diagnostic? finish.id repeatableEndpoint.id = some .noWildcard ∧
    diagnostic? start.id finish.id = none := by
  native_decide

/- The two reported codes are the Kernel's own, and they are distinct classes rather than one
refusal with two names. -/
example :
    KernelStaticDiagnostic.wrongDateFormatForOp.kernelCode =
        "MVK_WRONG_DATE_FORMAT_FOR_OP" ∧
      KernelStaticDiagnostic.noWildcard.kernelCode = "MVK_NO_WILDCARD" := by
  decide

end A12Kernel.Conformance.DateRangeConstructionOperand
