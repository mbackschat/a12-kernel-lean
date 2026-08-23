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

/-! ## The per-row read

A bound operand is read at the row the environment binds, and its whole input is the cell's **stored
text**: a partially known Date denotes an interval, so it has no `Value` form and the Date kind accepts
no `Value` that could stand for one. The placement therefore carries text and no parsed value by
construction, and the classifier that owns the text is the only thing that decides its meaning.

**Internal, not measured.** The admission above is Kernel-measured; what a bound operand *evaluates* to
per row is this project's account, built from the already-measured classifier plus the shared addressed
read. -/

private def rowsModel : FlatModel := {
  fields := [rowSource]
  repeatableGroups := [{ level := 10, path := ["Order", "Rows"], repeatability := some 2 }]
  timeZoneId := "Europe/Berlin" }

private def prepared :
    PreparedFlatStringContext rowsModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler rowsModel).toOption.get (by native_decide)

/-- The fault of a bound read, projected so a case can name it exactly. -/
private def faultOf (result : Except ValueAsDateReadFault Verdict) :
    Option ValueAsDateReadFault :=
  match result with
  | .ok _ => none
  | .error fault => some fault

private def rowCell (row : Nat) (stored : String)
    (raw : RawCell := .presentEmpty) : ClassifiedCellInput :=
  { address := { field := 0, path := [row] }, stored, raw }

private def documentOf (cells : List ClassifiedCellInput)
    (rows : List RowAddr :=
      [{ group := 10, path := [1] }, { group := 10, path := [2] }]) :
    Option (CheckedDocument rowsModel) :=
  (checkDocument prepared "en_US"
    { instantiatedRows := rows, cells }).toOption

private def comparison? : Option (CheckedValueAsDateComparison rowsModel) := do
  let expected ← date? 2024 6 15
  (elaborateValueAsDateComparisonIn rowsModel [10] 0 .firstDay .before
    expected).toOption

private def verdictAt? (cells : List ClassifiedCellInput) (row : Nat)
    (rows : List RowAddr :=
      [{ group := 10, path := [1] }, { group := 10, path := [2] }]) :
    Option Verdict := do
  let checked ← comparison?
  let document ← documentOf cells rows
  (checked.evaluateAt [(10, row)] document).toOption

/- Each row is read at its own coordinate: the same operation gives opposite verdicts on two rows whose
stored texts straddle the compared date, which is the whole point of a per-row read. -/
example :
    let cells := [rowCell 1 "00.01.2024", rowCell 2 "00.09.2024"]
    verdictAt? cells 1 = some (.fired .value) ∧
      verdictAt? cells 2 = some .notFired := by
  native_decide

/- Absence and a present-but-empty text are both ordinary non-firing emptiness, and they stay distinct
in the read even though this comparison treats them alike. -/
example :
    verdictAt? [rowCell 1 "00.01.2024"] 2 = some .notFired ∧
      verdictAt? [rowCell 1 "", rowCell 2 "00.01.2024"] 1 = some .notFired := by
  native_decide

/- An earlier stage's formal rejection reaches the verdict as UNKNOWN rather than as emptiness, and the
classifier's own refusal does the same at the row that carries it while a sibling row is unaffected. -/
example :
    let mixed := [rowCell 1 "bad" (.rejected .dateFormat), rowCell 2 "00.01.2024"]
    verdictAt? mixed 1 = some .unknown ∧
      verdictAt? mixed 2 = some (.fired .value) ∧
      verdictAt? [rowCell 1 "00.00.00"] 1 = some .unknown := by
  native_decide

/- Two different failures at a row that is not an ordinary one, and they must not be conflated. A row
**instantiated beyond** the declared repetition reads as unavailable, so its verdict is UNKNOWN rather
than quietly non-firing. A row that was never instantiated at all is a structural addressing fault and
produces no verdict, because the document cannot say what it does not contain. -/
example :
    verdictAt? [rowCell 1 "00.01.2024"] 3
        [{ group := 10, path := [1] }, { group := 10, path := [2] },
          { group := 10, path := [3] }] = some .unknown ∧
      verdictAt? [rowCell 1 "00.01.2024"] 3 = none := by
  native_decide

/- That fault names the missing row rather than degrading to emptiness. -/
example :
    let checked := comparison?.get (by native_decide)
    let document := (documentOf [rowCell 1 "00.01.2024"]).get (by native_decide)
    faultOf (checked.evaluateAt [(10, 3)] document) =
      some (.document (.missingRow { group := 10, path := [3] })) := by
  native_decide

/- An environment that does not bind the operand's level is a structural fault, not a verdict. It is
reachable only for a bound source, which is why the root read needs no such channel. -/
example :
    let expected := (date? 2024 6 15).get (by native_decide)
    let checked := (elaborateValueAsDateComparisonIn rowsModel [10] 0 .firstDay
      .before expected).toOption.get (by native_decide)
    let document := (documentOf [rowCell 1 "00.01.2024"]).get (by native_decide)
    faultOf (checked.evaluateAt [] document) =
      some (.environment (.missingBinding 10)) := by
  native_decide

/- The stored-text read is refused for a declaration whose text is not its whole input, so a full Date
cannot be reached by a route that skips its own classifier. -/
example :
    let fullSource : FlatFieldDecl :=
      { rowSource with
        temporalTargetPolicy := some {
          format := "dd.MM.yyyy", partialMode := .full } }
    let fullModel : FlatModel := { rowsModel with fields := [fullSource] }
    let fullPrepared := (prepareFlatStringContext { now := { epochMillis := 0 } }
      builtinStringPatternCompiler fullModel).toOption.get (by native_decide)
    let document := (checkDocument fullPrepared "en_US"
      { instantiatedRows := [{ group := 10, path := [1] }]
        cells := [] }).toOption.get (by native_decide)
    (match document.readStoredText { field := 0, path := [1] } with
        | .ok _ => none
        | .error error => some error) =
      some (.nonPartialDateField { field := 0, path := [1] }) := by
  native_decide

/- A partial-precision Date declaration admits **two** encodings, because it still holds ordinary fully
known values alongside partial ones. A partially known value has no `Value` form, so its cell carries a
stored text and no parsed value; a value that does have one still places ordinarily. The stored-text read
is the same either way, which is what lets the classifier stay the only thing that decides meaning.

An *empty* text with a rejection is refused under both rules, so the widening does not reach it. -/
example :
    (documentOf [rowCell 1 "00.01.2024"]).isSome = true ∧
      (documentOf [rowCell 1 "00.01.2024"
        (.parsed (.str "00.01.2024"))]).isSome = true ∧
      (documentOf [rowCell 1 "" (.rejected .dateFormat)]).isNone = true := by
  native_decide

/- Both encodings hand the classifier the same text, and an absent cell hands it none. -/
example :
    let read (cells : List ClassifiedCellInput) : Option (Option String) := do
      let document ← documentOf cells
      (document.readStoredText { field := 0, path := [1] }).toOption.map
        (fun cell => cell.parsed)
    read [rowCell 1 "00.01.2024"] = some (some "00.01.2024") ∧
      read [rowCell 1 "00.01.2024" (.parsed (.str "00.01.2024"))] =
        some (some "00.01.2024") ∧
      read [] = some none := by
  native_decide

end A12Kernel.Conformance.ValueAsDateLocus
