import A12Kernel.Elaboration.RepeatableDateConstantComputation
import A12Kernel.Elaboration.CheckedDocument

/-! # Repeatable Date constant locks

The Kernel rows behind these cases are the [cross-group carrier](../../docs/SOURCES.md#src-cross-group-repeatable-constant-target)
and the [Date-constant target-formatting](../../docs/SOURCES.md#src-date-constant-target-formatting)
checkpoints. The second is what this family exists to lock: the target's declared format is a
**rendering** of one literal date and never an admission gate.
-/

namespace A12Kernel.Conformance.RepeatableDateConstantComputation

open A12Kernel

private def dateField (id : FieldId) (name : String) (groupPath : GroupPath)
    (scope : List RepeatableLevel) (format : String := "yyyy-MM-dd")
    (youngerThan1900Check : Bool := false) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some { format, partialMode := .full, youngerThan1900Check }
}

private def iso := dateField 1 "DIso" ["Probe", "Rows"] [10]
private def ger := dateField 2 "DGer" ["Probe", "Rows"] [10] "dd.MM.yyyy"

private def year := dateField 3 "DYear" ["Probe", "Rows"] [10] "yyyy"
private def yearMonth := dateField 6 "DYearMonth" ["Probe", "Rows"] [10] "yyyy-MM"
private def compact := dateField 7 "DCompact" ["Probe", "Rows"] [10] "yyyyMM"

/-- The two **yearless** formats: admitted only where the model declares a Base Year. -/
private def monthOnly := dateField 8 "DMonth" ["Probe", "Rows"] [10] "MM"
private def monthDay := dateField 9 "DMonthDay" ["Probe", "Rows"] [10] "MM-dd"

private def note := dateField 4 "Note" ["Probe", "Store"] []

/-- A target that opts into the additional pre-1900 check, for the delegation case below. -/
private def guarded := dateField 5 "DGuarded" ["Probe", "Rows"] [10] "yyyy-MM-dd" true

private def model : FlatModel := {
  fields := [iso, ger, year, yearMonth, compact, monthOnly, monthDay, note, guarded]
  repeatableGroups := [
    { level := 10, path := ["Probe", "Rows"], repeatability := some 3 }]
  timeZoneId := "UTC"
}

/-- The same model with a declared Base Year and **nothing else changed**, so a difference between
the two is attributable to that declaration alone. -/
private def baseYearModel : FlatModel := { model with baseYear := some 2024 }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def rows (count : Nat) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows :=
      (List.range count).map fun index => { group := 10, path := [index + 1] }
    cells := [] }).toOption

private def march5 : CivilDate :=
  { parts := { year := 2024, month := 3, day := 5 }, real := by decide }

private def old : CivilDate :=
  { parts := { year := 1899, month := 12, day := 31 }, real := by decide }

/-- The same month and day a century earlier, so a yearless rendering cannot distinguish it. -/
private def march5Old : CivilDate :=
  { parts := { year := 1899, month := 3, day := 5 }, real := by decide }

private def outcome? (declaringGroup : GroupPath) (target : FieldId)
    (constant : CivilDate := march5) : Option FullDateTargetOutcome :=
  (checkRepeatableDateConstantComputation model declaringGroup target constant).toOption.map
    (·.outcome)

private def outcomes? (declaringGroup : GroupPath) (target : FieldId) (count : Nat) :
    Option (List RepeatableDateConstantComputationOutcome) :=
  (checkRepeatableDateConstantComputation model declaringGroup target march5).toOption.bind
    fun operation => (rows count).bind fun input => (operation.execute input).toOption

private def stored (text : String) (nonempty : text ≠ "" := by decide) : StoredDate :=
  { text, nonempty }

/-- The same query against the Base-Year model, so a yearless target can be reached at all. -/
private def baseYearOutcome? (target : FieldId)
    (constant : CivilDate := march5) : Option FullDateTargetOutcome :=
  (checkRepeatableDateConstantComputation baseYearModel ["Probe"] target constant).toOption.map
    (·.outcome)

/- **One constant stores two different texts.** The declared format is a rendering of the literal
   date, not a gate on it: the same `05.03.2024` reaches an ISO-declared target as `2024-03-05` and a
   dotted one as `05.03.2024`, both accepted. Measured on kernel 30.8.1 across both codegen
   strategies, where one authored constant produced exactly these two stored values with nothing
   cleared and nothing errored. This is the case that separates a rendering from an admission gate;
   a carrier storing the authored text would pass every same-format fixture and fail here. -/
example : (outcome? ["Probe"] iso.id, outcome? ["Probe"] ger.id) =
    (some (.accepted (stored "2024-03-05")), some (.accepted (stored "05.03.2024"))) := by
  native_decide

/- The constant reaches every in-capacity target row and no more, from an ancestor exactly as from
   the target's own group. Two rows, two outcomes; no rows, none at all rather than one implicit
   instance. -/
example : (outcomes? ["Probe"] iso.id 2, outcomes? ["Probe", "Rows"] iso.id 2,
    outcomes? ["Probe"] iso.id 0) =
    (some [{ targetField := { field := iso.id, path := [1] }
             outcome := .accepted (stored "2024-03-05") },
           { targetField := { field := iso.id, path := [2] }
             outcome := .accepted (stored "2024-03-05") }],
     some [{ targetField := { field := iso.id, path := [1] }
             outcome := .accepted (stored "2024-03-05") },
           { targetField := { field := iso.id, path := [2] }
             outcome := .accepted (stored "2024-03-05") }],
     some []) := by
  native_decide

/- **An over-limit row gets a clear, not the constant.** Declared capacity is three: at four and five
   instantiated rows the first three take the constant and every further row takes `.noValue`, which
   the application projection turns into a clear. Measured on kernel 30.8.1 across both codegen
   strategies: unseeded excess rows report no outcome under the changed-subset projection, and a
   **seeded** one reports `cleared` with no value in the same run where its in-capacity siblings
   compute ([checkpoint](../../docs/SOURCES.md#src-over-limit-computation-target)). Dropping the row
   instead would pass every unseeded fixture and leave a stale value the Kernel removes. -/
example :
    ((outcomes? ["Probe"] iso.id 3).map (·.map (·.outcome)),
      (outcomes? ["Probe"] iso.id 5).map (·.map (·.outcome))) =
    (some [.accepted (stored "2024-03-05"), .accepted (stored "2024-03-05"),
           .accepted (stored "2024-03-05")],
     some [.accepted (stored "2024-03-05"), .accepted (stored "2024-03-05"),
           .accepted (stored "2024-03-05"), .noValue, .noValue]) := by
  native_decide

/- **The component-omitting store, measured.** One literal reaches three declared component subsets
   and keeps exactly what each names, with its own separator: `yyyy` stores `2024`, `yyyy-MM` stores
   `2024-03`, and `yyyyMM` stores `202403`. The discarded day and month are reported nowhere — every
   row is accepted. Together with the two complete formats above, one constant now produces five
   different stored texts, which is what makes the declared format a rendering rather than a gate. -/
example : (outcome? ["Probe"] year.id, outcome? ["Probe"] yearMonth.id,
    outcome? ["Probe"] compact.id) =
    (some (.accepted (stored "2024")), some (.accepted (stored "2024-03")),
     some (.accepted (stored "202403"))) := by
  native_decide

/- **A yearless target needs a declared Base Year, and the Base Year reaches admission only.** The
   two models differ in that one declaration and nothing else. Without it both yearless targets are
   refused, with the Kernel's own `MVK_INVALID_COMPARE_TO_DATE`; with it both are accepted and store
   **no year at all** — `03` and `03-05` — although the model declares 2024 and the constant supplies
   it. Measured on kernel 30.8.1 across both codegen strategies, where the same constant into `MM`,
   `MM-dd`, `yyyy-MM`, `yyyy`, and a complete target stored those five different texts in one run
   ([checkpoint](../../docs/SOURCES.md#src-base-year-yearless-store)). A carrier completing the store
   from the Base Year would pass every year-leading row above and fail exactly here. -/
example : (outcome? ["Probe"] monthOnly.id, outcome? ["Probe"] monthDay.id,
    baseYearOutcome? monthOnly.id, baseYearOutcome? monthDay.id) =
    (none, none,
     some (.accepted (stored "03")), some (.accepted (stored "03-05"))) := by
  native_decide

/- The refusal without a Base Year carries the Kernel identity it was measured with, on both yearless
   formats. Its admitted control is the same target on the Base-Year model above, so this is a gate
   that opens rather than a declaration the carrier never supported. -/
example : ([monthOnly.id, monthDay.id].map fun target =>
      match checkRepeatableDateConstantComputation model ["Probe"] target march5 with
      | .error cause => cause.diagnostic?.map KernelStaticDiagnostic.kernelCode
      | .ok _ => none) =
    [some "MVK_INVALID_COMPARE_TO_DATE", some "MVK_INVALID_COMPARE_TO_DATE"] := by
  native_decide

/- **The stored text of a yearless target does not depend on the year**, which is the whole content
   of "the Base Year gates admission and renders nothing". Two constants a century apart store the
   same two texts, while the year-leading sibling on the same model separates them. -/
example : ([baseYearOutcome? monthOnly.id march5, baseYearOutcome? monthOnly.id march5Old,
      baseYearOutcome? yearMonth.id march5, baseYearOutcome? yearMonth.id march5Old]) =
    [some (.accepted (stored "03")), some (.accepted (stored "03")),
     some (.accepted (stored "2024-03")), some (.accepted (stored "1899-03"))] := by
  native_decide

/- Placement is containment: the target's own group and every ancestor admit it, and only a group the
   target does not lie below is refused — with the Kernel identity that refusal actually carries. -/
example : ([["Probe", "Rows"], ["Probe"]].map fun group =>
      (checkRepeatableDateConstantComputation model group iso.id march5).toOption.isSome,
    match checkRepeatableDateConstantComputation model ["Probe", "Store"] iso.id march5 with
    | .error cause => cause.diagnostic?.map KernelStaticDiagnostic.kernelCode
    | .ok _ => none) =
    ([true, true], some "MVK_ERROR_FIELD_NOT_IN_RULEGROUP") := by
  native_decide

/- A nonrepeatable target belongs to no carrier here and is declined by the shared certificate rather
   than by a second local gate, so it claims no Kernel class. -/
example : (match checkRepeatableDateConstantComputation model ["Probe"] note.id march5 with
    | .error cause => (cause.diagnostic?.isSome, true)
    | .ok _ => (false, false)) = (false, true) := by
  native_decide

/- The declaration's own additional check is **delegated, not restated**: a target opting into the
   pre-1900 check errors on a 1899 constant while retaining the exact attempted text, and the same
   constant is accepted by the unguarded target beside it. Kernel correspondence for this branch is
   the shared computed-Date target check's, not this family's — the constant rows measured no
   pre-1900 target — so what this case locks is that the carrier reaches that check rather than
   carrying a copy of it. -/
example : (outcome? ["Probe"] guarded.id old, outcome? ["Probe"] iso.id old) =
    (some (.errored (stored "1899-12-31") .before1900),
     some (.accepted (stored "1899-12-31"))) := by
  native_decide

end A12Kernel.Conformance.RepeatableDateConstantComputation
