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

/-- A TIME declaration carrying the endpoint's own date format. The declared kind and the declared
component set both disagree with the format here, which is what makes it the separating cell. -/
private def timeDeclaredEndpoint : FlatFieldDecl := {
  dateField 9 "TimeDeclared" with
  policy := { kind := .temporal .time TemporalComponents.time }
}

/-- A DATETIME declaration carrying that same date format, so the cross-kind cell is measured on
both of the kinds the endpoint used to refuse rather than on one of them. -/
private def stampDeclaredEndpoint : FlatFieldDecl := {
  dateField 10 "StampDeclared" with
  policy := { kind := .temporal .dateTime TemporalComponents.now }
}

private def model : FlatModel := {
  fields := [start, finish, monthFragment, numberEndpoint, stringEndpoint,
    dateTimeEndpoint, rangeEndpoint, repeatableEndpoint,
    timeDeclaredEndpoint, stampDeclaredEndpoint]
  repeatableGroups := [
    { level := 10, path := ["Order", "Rows"], repeatability := some 5 }]
  timeZoneId := "UTC"
}

private def diagnostic? (startField finishField : FieldId) :
    Option KernelStaticDiagnostic :=
  match elaborateDateRangeConstruction model startField finishField with
  | .ok _ => none
  | .error cause => cause.diagnostic?

/- Every operand whose declared **format** is not a Date-shaped one reports the one wrong-format
class, so a Number, a String, a stamp-formatted DateTime, and a DateRange operand are
indistinguishable by code, and a pair whose component sets disagree joins them in either
authored order. A repeatable operand reached from outside its group reports the missing-wildcard
class instead, which is the one operand refusal this boundary separates.

Read the DateTime row precisely: it is refused for its stamp **format**, not for its kind. The
cross-kind case below carries the same declared kind on the endpoint's own date format and is
admitted, which is why the two rows do not contradict each other. -/
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

/- **An endpoint is admitted by its declared format alone, on all three declared kinds.** A TIME and
a DATETIME declaration carrying the endpoint's date format pair with the DATE-declared endpoint and
with each other, so the declared kind reaches neither side of the construction gate — the operand
rule this position follows ([checkpoint](../../docs/sources/computation-placement-and-constant-probes.md#src-temporal-difference-gates-read-the-format)).
Both cells also disagree with their format about the component set, so nothing here is the gate
reading a component set that happens to match. -/
example :
    [diagnostic? timeDeclaredEndpoint.id finish.id,
      diagnostic? stampDeclaredEndpoint.id finish.id,
      diagnostic? timeDeclaredEndpoint.id stampDeclaredEndpoint.id,
      diagnostic? start.id timeDeclaredEndpoint.id] =
      List.replicate 4 none := by
  native_decide

/- The two reported codes are the Kernel's own, and they are distinct classes rather than one
refusal with two names. -/
example :
    KernelStaticDiagnostic.wrongDateFormatForOp.kernelCode =
        "MVK_WRONG_DATE_FORMAT_FOR_OP" ∧
      KernelStaticDiagnostic.noWildcard.kernelCode = "MVK_NO_WILDCARD" := by
  decide

end A12Kernel.Conformance.DateRangeConstructionOperand
