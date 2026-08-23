import A12Kernel.Elaboration.ValueAsDate

/-! # `ValueAsDate` reading-locus locks

Where a partial-Date operand may be read, as opposed to what it means once read. Measured at kernel
30.8.1 through `rule add --dry-run`, which runs the real consistency oracle on a candidate rule.

Three loci separate. A partial-Date operand **inside a repeatable group is admitted** when the reading
rule's own iteration scope binds that group. An outer rule naming the same row path without an asterisk
is refused, the Kernel demanding the asterisk. A **starred** operand is refused
`MVK_NO_WILDCARDS_ALLOWED` at `ValueAsDate` itself, so no scope admits one and this project's signature
cannot express it. A fourth, already recorded in the spec, is the group-scope operand's own refusal.

Only the direct-comparison carrier was measured; the shift and difference carriers keep the
nonrepeatable locus, because in this family a locus verdict does not transfer between carriers. What a
bound operand's per-row *cell read* does is not modelled anywhere yet: the family consumes stored text
directly, so no route resolves a row's cell for it. -/

namespace A12Kernel.Conformance.ValueAsDateLocus

open A12Kernel

private def date? (year : Int) (month day : Nat) : Option FullDate :=
  FullDate.ofYmd? year month day

private def dayOptionalSource
    (partialMode : TemporalPartialMode := .dayOptional)
    (format : String := "dd.MM.yyyy") : FlatFieldDecl := {
  id := 0
  groupPath := ["Order"]
  name := "ApproxDate"
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some { format, partialMode } }

private def modelWith
    (source : FlatFieldDecl := dayOptionalSource) : FlatModel := {
  fields := [source]
  timeZoneId := "Europe/Berlin" }

private def rowSource : FlatFieldDecl :=
  { dayOptionalSource with
    groupPath := ["Order", "Rows"]
    repeatableScope := [10] }

private def rowModel : FlatModel := {
  fields := [rowSource]
  repeatableGroups := [{ level := 10, path := ["Order", "Rows"] }]
  timeZoneId := "Europe/Berlin" }

/- The operand is admitted exactly when the reading scope binds its repeatable level, and the
nonrepeatable entry point stays the `scope = []` case of the same gate rather than a second rule. -/
example :
    (elaborateValueAsDateSourceIn rowModel [10] 0 .firstDay).isOk = true ∧
      (elaborateValueAsDateSourceIn rowModel [] 0 .firstDay).isOk = false ∧
      (elaborateValueAsDateSource rowModel 0 .firstDay).isOk = false ∧
      (elaborateValueAsDateSourceIn (modelWith dayOptionalSource) [] 0
        .firstDay).isOk = true := by
  native_decide

/- An unbound level is a resolution refusal naming the operand's own path, which is the channel the
kernel's asterisk demand maps onto: the operand is legal, the reading locus is not. -/
example :
    (elaborateValueAsDateSourceIn rowModel [] 0 .firstDay
        |>.toOption.isNone) = true ∧
      (match elaborateValueAsDateSourceIn rowModel [] 0 .firstDay with
        | .error error => error
        | .ok _ => .unsupportedFormat 0 "unreachable") =
        .sourcePolicy (.resolve
          (.repeatableReference ["Order", "Rows", "ApproxDate"])) := by
  native_decide

/- The comparison carrier inherits the same gate, so its admitted locus is the source's and not a
second decision. Precision and kind gates still run inside the bound scope. -/
example :
    let expected := (date? 2024 6 15).get (by native_decide)
    (elaborateValueAsDateComparisonIn rowModel [10] 0 .firstDay .before
        expected).isOk = true ∧
      (elaborateValueAsDateComparisonIn rowModel [] 0 .firstDay .before
        expected).isOk = false ∧
      (elaborateValueAsDateComparisonIn
        { rowModel with fields := [{ rowSource with
            temporalTargetPolicy := some {
              format := "dd.MM.yyyy", partialMode := .full } }] }
        [10] 0 .firstDay .before expected).isOk = false := by
  native_decide

/- A bound operand still evaluates through the one existing raw route: admission changed, meaning did
not. The per-row *read* is not modelled here — the family takes stored text directly, so nothing yet
resolves a row's cell for it. -/
example :
    let expected := (date? 2024 6 15).get (by native_decide)
    let checked := (elaborateValueAsDateComparisonIn rowModel [10] 0 .firstDay
      .before expected).toOption.get (by native_decide)
    checked.evaluateRaw (.parsed "00.06.2024") = .fired .value := by
  native_decide

end A12Kernel.Conformance.ValueAsDateLocus
