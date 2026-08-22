import A12Kernel.Elaboration.AtLeastOneDateRangeOverlap
import A12Kernel.Semantics.DateRangeOverlapOperators

/-! # Resolved Date-range overlap operator locks

These cases start after authored operands have been expanded and filtered into ordered slots. They separate the any-pair and scalar-versus-list scans, including their different filter-derived polarity rules.
-/

namespace A12Kernel.Conformance.DateRangeOverlapOperators

open A12Kernel

/-! ## Checked `DateRangesOverlap` source admission -/

private def rangeField (id : FieldId) (groupPath : GroupPath) (name : String)
    (scope : List RepeatableLevel := []) (format : String := "yyyy-MM-dd")
    (separator : String := "/") : FlatFieldDecl := {
  id, groupPath, name, repeatableScope := scope
  policy := { kind := .dateRange }
  dateRangePolicy := some { format, separator }
}

private def admissionModel : FlatModel := {
  fields := [
    rangeField 1 ["Form"] "Start",
    rangeField 2 ["Form"] "Finish" [] "dd.MM.yyyy" "-",
    rangeField 3 ["Form", "Rows"] "Window" [10],
    rangeField 4 ["Form"] "Unsupported" [] "dd.MM" "-",
    { id := 5, groupPath := ["Form"], name := "Code",
      policy := { kind := .string },
      stringPolicy := { lineBreaksPermitted := true } },
    { id := 6, groupPath := ["Form", "Rows"], name := "Guard",
      repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := false } } },
    rangeField 7 ["Form", "Fixed"] "Left",
    rangeField 8 ["Form", "Fixed"] "Right",
    rangeField 9 ["Form", "Periods"] "Window" [11],
    rangeField 10 ["Form", "Periods"] "Grace" [11],
    { id := 11, groupPath := ["Form"], name := "Quantity",
      policy := { kind := .number { scale := 0, signed := false } } },
    { id := 12, groupPath := ["Form"], name := "BackorderQuantity",
      policy := { kind := .number { scale := 0, signed := false } } }]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 4 },
    { level := 11, path := ["Form", "Periods"], repeatability := some 3 }]
}

private def direct (field : String) : SurfaceFieldEntityOperand :=
  .field { base := .relative 0, groups := [], field }

private def star (field : String) : SurfaceStarFieldPath := {
  base := .absolute
  groups := [{ name := "Form" }, { name := "Rows", starred := true }]
  field
}

private def periodsStar (field : String) : SurfaceStarFieldPath := {
  base := .absolute
  groups := [{ name := "Form" }, { name := "Periods", starred := true }]
  field
}

private def projected (field : String) : SurfaceFieldEntityOperand :=
  .field { base := .relative 0, groups := [], field } (.projected "Band")

private def selfFilter : SurfaceCorrelatedHaving :=
  .compareNumbers .equal
    { origin := .inner,
      field := { base := .absolute, groups := ["Form", "Rows"], field := "Guard" } }
    { origin := .inner,
      field := { base := .absolute, groups := ["Form", "Rows"], field := "Guard" } }

private def starredRowsGroup : SurfaceFieldEntityOperand :=
  .starredGroup {
    base := .absolute
    groups := [{ name := "Form" }, { name := "Rows", starred := true }]
  }

private def starredPeriodsGroup : SurfaceFieldEntityOperand :=
  .starredGroup {
    base := .absolute
    groups := [{ name := "Form" }, { name := "Periods", starred := true }]
  }

private def checkedSource? (first : SurfaceFieldEntityOperand)
    (rest : List SurfaceFieldEntityOperand := []) :
    Option (CheckedDateRangesOverlapSource admissionModel) :=
  (elaborateDateRangesOverlapSource admissionModel ["Form"] { first, rest }).toOption

private def admissionError? (first : SurfaceFieldEntityOperand)
    (rest : List SurfaceFieldEntityOperand := []) :
    Option DateRangesOverlapElabError :=
  match elaborateDateRangesOverlapSource admissionModel ["Form"] { first, rest } with
  | .ok _ => none
  | .error error => some error

/- The operator accepts both canonical full-year policies in one list; it does not require one presentation. -/
example : (checkedSource? (direct "Start") [direct "Finish"]).isSome = true := by
  native_decide

/- A sole star satisfies multiplicity, and a filter stays attached to its exact authored slot. -/
example :
    (checkedSource? (.star (star "Window"))).map (·.hasHaving) = some false ∧
      (checkedSource? (.starHaving (star "Window") selfFilter)).map
        (·.hasHaving) = some true := by
  native_decide

/- Authored groups are an operator-specific refusal even when their whole expansion is DateRange. -/
example :
    (admissionError? (.group (.path {
      base := .absolute, groups := ["Form", "Fixed"] }))).bind
        DateRangesOverlapElabError.diagnostic? = some .noGroupsAllowed ∧
      admissionError? starredRowsGroup =
        some (.groupsNotAllowed ["Form", "Rows"]) := by
  native_decide

/- Shared arity and duplicate gates remain earlier than DateRange certification. -/
example :
    (admissionError? (direct "Start")).bind DateRangesOverlapElabError.diagnostic? =
        some .paramSizeInvalidN ∧
      (admissionError? (direct "Start") [direct "Start"]).bind
        DateRangesOverlapElabError.diagnostic? = some .duplicateParam1 := by
  native_decide

/- Wrong-kind and wrong-read-form sources fail explicitly instead of becoming empty operands.
A yearless declaration beside a year-bearing one meets the earlier uniform-year gate, so this
route's policy refusal is reachable only from a uniformly yearless list and is locked with its
payload in `Conformance.DateRangeFragmentOverlap`. -/
example :
    admissionError? (direct "Start") [direct "Code"] =
        some (.sourceNotDateRange ["Form", "Code"] .string) ∧
      (admissionError? (direct "Start") [direct "Unsupported"]).bind
        DateRangesOverlapElabError.diagnostic? = some .dateWithAndWithoutYear ∧
      admissionError? (.field { base := .relative 0, groups := [], field := "Start" }
        (.projected "Band")) [direct "Finish"] =
        some (.unsupportedReadForm ["Form", "Start"] (.projected "Band")) := by
  native_decide

/-! ## Checked `AtLeastOneDateRangeOverlaps` source admission -/

private def checkedPluralSource? (scalar first : SurfaceFieldEntityOperand)
    (rest : List SurfaceFieldEntityOperand := []) :
    Option (CheckedAtLeastOneDateRangeOverlapsSource admissionModel) :=
  (elaborateAtLeastOneDateRangeOverlapsSource admissionModel ["Form"] {
    scalar
    list := { first, rest }
  }).toOption

private def pluralAdmissionError? (scalar first : SurfaceFieldEntityOperand)
    (rest : List SurfaceFieldEntityOperand := []) :
    Option AtLeastOneDateRangeOverlapsElabError :=
  match elaborateAtLeastOneDateRangeOverlapsSource admissionModel ["Form"] {
      scalar
      list := { first, rest }
    } with
  | .ok _ => none
  | .error error => some error

private def pluralGroupSummary? :
    CheckedAtLeastOneDateRangeOverlapsListOperand admissionModel →
      Option (GroupPath × Bool × List FieldId)
  | .field _ => none
  | .group source => some (
      source.source.groupPath,
      source.source.isStarred,
      (source.first :: source.rest).map (·.declaration.id))

/- A single direct list field is legal: list nonemptiness is distinct from the singular aggregate's multiplicity gate. -/
example :
    (checkedPluralSource? (direct "Start") (direct "Finish")).isSome = true := by
  native_decide

/- The public certificate keeps the scalar outside the ordered list and preserves field identity. -/
example :
    (checkedPluralSource? (direct "Start") (direct "Finish")
      [.star (star "Window")]).map (fun checked =>
        (checked.scalar.declaration.id,
          checked.operands.map fun operand =>
            operand.fields.map (·.declaration.id))) =
      some (1, [[2], [3]]) := by
  native_decide

/- Plain and filtered stars retain their exact filter slot on the list side. -/
example :
    (checkedPluralSource? (direct "Start") (.star (star "Window"))).map
        (·.hasHaving) = some false ∧
      (checkedPluralSource? (direct "Start")
        (.starHaving (star "Window") selfFilter)).map (·.hasHaving) = some true := by
  native_decide

/- Both measured group spellings are admitted in the list slot and retain one authored operand. -/
example :
    (checkedPluralSource? (direct "Start")
      (.group (.path {
        base := .absolute, groups := ["Form", "Fixed"] }))).map
        (·.operands.length) = some 1 ∧
      (checkedPluralSource? (direct "Start") starredPeriodsGroup).map
        (·.operands.length) = some 1 := by
  native_decide

/- Group certificates keep authored group identity and complete declaration order. -/
example :
    (checkedPluralSource? (direct "Start")
      (.group (.path {
        base := .absolute, groups := ["Form", "Fixed"] }))).bind
        (pluralGroupSummary? ·.first) =
          some (["Form", "Fixed"], false, [7, 8]) ∧
      (checkedPluralSource? (direct "Start") starredPeriodsGroup).bind
        (pluralGroupSummary? ·.first) =
          some (["Form", "Periods"], true, [9, 10]) := by
  native_decide

/- The measured scalar/list reversal gets its exact class; an unmeasured scalar group remains unmapped. -/
example :
    (pluralAdmissionError? (.star (star "Window")) (direct "Start")).bind
        AtLeastOneDateRangeOverlapsElabError.diagnostic? =
          some .invalidParameterForDateRangeComparison ∧
      (pluralAdmissionError?
        (.group (.path { base := .absolute, groups := ["Form", "Fixed"] }))
        (direct "Start")).bind
          AtLeastOneDateRangeOverlapsElabError.diagnostic? = none := by
  native_decide

/- The scalar wildcard gate precedes list overlap checks; the unmeasured filtered spelling stays unmapped. -/
example :
    (pluralAdmissionError? (.star (periodsStar "Window"))
      starredPeriodsGroup).bind
        AtLeastOneDateRangeOverlapsElabError.diagnostic? =
          some .invalidParameterForDateRangeComparison ∧
      (pluralAdmissionError? (.starHaving (star "Window") selfFilter)
        (direct "Start")).bind
          AtLeastOneDateRangeOverlapsElabError.diagnostic? = none := by
  native_decide

/- The exact measured Number/Number pair maps to `MVK_NO_DATE_RANGE`; either isolated kind mismatch stays unmapped. -/
example :
    (pluralAdmissionError? (direct "Quantity")
      (direct "BackorderQuantity")).bind
        AtLeastOneDateRangeOverlapsElabError.diagnostic? = some .noDateRange ∧
      (pluralAdmissionError? (direct "Code") (direct "Start")).bind
        AtLeastOneDateRangeOverlapsElabError.diagnostic? = none ∧
      (pluralAdmissionError? (direct "Start") (direct "Code")).bind
        AtLeastOneDateRangeOverlapsElabError.diagnostic? = none := by
  native_decide

/- Unsupported policy and read-form refusals stay unmapped on either side. -/
example :
    (pluralAdmissionError? (direct "Unsupported") (direct "Finish")).bind
        AtLeastOneDateRangeOverlapsElabError.diagnostic? = none ∧
      (pluralAdmissionError? (direct "Start") (direct "Unsupported")).bind
        AtLeastOneDateRangeOverlapsElabError.diagnostic? = none ∧
      (pluralAdmissionError? (projected "Start") (direct "Finish")).bind
        AtLeastOneDateRangeOverlapsElabError.diagnostic? = none ∧
      (pluralAdmissionError? (direct "Start") (projected "Finish")).bind
        AtLeastOneDateRangeOverlapsElabError.diagnostic? = none := by
  native_decide

/- Exact duplication spans scalar and list, and a group cannot certify by silently dropping its wrong-kind field. -/
example :
    (pluralAdmissionError? (direct "Start") (direct "Start")).bind
        AtLeastOneDateRangeOverlapsElabError.diagnostic? = some .duplicateParam1 ∧
      pluralAdmissionError? (direct "Start") starredRowsGroup =
        some (.groupExpansionNotDateRange ["Form", "Rows"]) := by
  native_decide

/-! ## Checked-document assembly -/

private def prepared :
    PreparedFlatStringContext admissionModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler admissionModel).toOption.get (by native_decide)

private def dateValue (epochMillis : Int) (month day : Nat) : DateValue := {
  instant := { epochMillis }
  parts := { year := 2024, month, day }
  basis := .storedGregorian
}

private def rangeValue (startMillis finishMillis : Int)
    (startMonth startDay finishMonth finishDay : Nat) : DateRangeValue := {
  start := dateValue startMillis startMonth startDay
  finish := dateValue finishMillis finishMonth finishDay
}

private def januaryValue :=
  rangeValue 1704067200000 1706659200000 1 1 1 31
private def lateJanuaryValue :=
  rangeValue 1705276800000 1706659200000 1 15 1 31
private def marchValue :=
  rangeValue 1709251200000 1711843200000 3 1 3 31

private def rangeCell (field : FieldId) (path : List Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := { field, path }, stored, raw }

private def document? (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option (CheckedDocument admissionModel) :=
  (checkDocument prepared "en_US" { instantiatedRows := rows, cells }).toOption

private def evaluated? (first : SurfaceFieldEntityOperand)
    (rest : List SurfaceFieldEntityOperand) (rows : List RowAddr)
    (cells : List ClassifiedCellInput) :
    Option (CheckedDateRangesOverlapResult admissionModel) := do
  let source ← checkedSource? first rest
  let document ← document? rows cells
  (source.evaluateCheckedDocument document []).toOption

private def verdict? (first : SurfaceFieldEntityOperand)
    (rest : List SurfaceFieldEntityOperand) (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option Verdict :=
  (evaluated? first rest rows cells).map (·.verdict)

private def evaluatedPlural? (scalar first : SurfaceFieldEntityOperand)
    (rest : List SurfaceFieldEntityOperand) (rows : List RowAddr)
    (cells : List ClassifiedCellInput) :
    Option (CheckedAtLeastOneDateRangeOverlapsResult admissionModel) := do
  let source ← checkedPluralSource? scalar first rest
  let document ← document? rows cells
  (source.evaluateCheckedDocument document []).toOption

private def pluralVerdict? (scalar first : SurfaceFieldEntityOperand)
    (rest : List SurfaceFieldEntityOperand) (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option Verdict :=
  (evaluatedPlural? scalar first rest rows cells).map (·.verdict)

private def pluralListAddresses? (scalar first : SurfaceFieldEntityOperand)
    (rest : List SurfaceFieldEntityOperand) (rows : List RowAddr)
    (cells : List ClassifiedCellInput) :
    Option (List (List (FieldId × List Nat))) :=
  (evaluatedPlural? scalar first rest rows cells).map fun result =>
    result.operands.map fun operand =>
      operand.core.addressedCells.map fun cell =>
        (cell.address.field, cell.address.path)

private def directOverlapCells : List ClassifiedCellInput := [
  rangeCell 1 [] "2024-01-01/2024-01-31" (.parsed (.dateRange januaryValue)),
  rangeCell 2 [] "15.01.2024-31.01.2024" (.parsed (.dateRange lateJanuaryValue))]

/- Direct fields use one checked document and retain their addresses for Explain. -/
example :
    verdict? (direct "Start") [direct "Finish"] [] directOverlapCells =
        some (.fired .value) ∧
      (evaluated? (direct "Start") [direct "Finish"] [] directOverlapCells).map
        (fun result => result.operands.map fun operand =>
          operand.core.addressedCells.map fun cell =>
            (cell.address.field, cell.address.path)) =
        some [[(1, [])], [(2, [])]] := by
  native_decide

private def row1 : RowAddr := { group := 10, path := [1] }

private def rows12 : List RowAddr := [
  row1, { group := 10, path := [2] }]

/- A disjoint direct field cannot hide the star's later internal pair. -/
example :
    verdict? (direct "Start") [.star (star "Window")] rows12 [
      rangeCell 1 [] "2024-03-01/2024-03-31" (.parsed (.dateRange marchValue)),
      rangeCell 3 [1] "2024-01-01/2024-01-31" (.parsed (.dateRange januaryValue)),
      rangeCell 3 [2] "2024-01-15/2024-01-31" (.parsed (.dateRange lateJanuaryValue))] =
        some (.fired .value) := by
  native_decide

/- Repeating one star keeps duplicate occurrences, so one filled row can pair with itself. -/
example :
    verdict? (.star (star "Window")) [.star (star "Window")] [row1] [
      rangeCell 3 [1] "2024-01-01/2024-01-31" (.parsed (.dateRange januaryValue))] =
        some (.fired .value) := by
  native_decide

/- A formally unavailable direct cell is skipped before a later star-internal match. -/
example :
    verdict? (direct "Start") [.star (star "Window")] rows12 [
      rangeCell 1 [] "broken" (.rejected .dateRangeSeparator),
      rangeCell 3 [1] "2024-01-01/2024-01-31" (.parsed (.dateRange januaryValue)),
      rangeCell 3 [2] "2024-01-15/2024-01-31" (.parsed (.dateRange lateJanuaryValue))] =
        some (.fired .value) := by
  native_decide

private def filteredSource : SurfaceFieldEntityOperand :=
  .starHaving (star "Window") selfFilter

/- Only a kept filtered occurrence taints the later direct match; an empty filtered cell or extent is inert. -/
example :
    verdict? filteredSource [direct "Start", direct "Finish"] [row1] (
      directOverlapCells ++ [
        rangeCell 3 [1] "2024-03-01/2024-03-31" (.parsed (.dateRange marchValue)),
        { address := { field := 6, path := [1] }, stored := "1",
          raw := .parsed (.num 1) }]) = some (.fired .omission) ∧
      verdict? filteredSource [direct "Start", direct "Finish"] [row1] (
        directOverlapCells ++ [
          { address := { field := 6, path := [1] }, stored := "1",
            raw := .parsed (.num 1) }]) = some (.fired .value) ∧
      verdict? filteredSource [direct "Start", direct "Finish"] []
        directOverlapCells = some (.fired .value) := by
  native_decide

/-! ## Checked plural-overlap assembly -/

/- A skipped scalar terminates before the internally overlapping list is resolved. -/
example :
    (evaluatedPlural? (direct "Start") (.star (star "Window")) [] rows12 [
      rangeCell 1 [] "broken" (.rejected .dateRangeSeparator),
      rangeCell 3 [1] "2024-01-01/2024-01-31" (.parsed (.dateRange januaryValue)),
      rangeCell 3 [2] "2024-01-15/2024-01-31"
        (.parsed (.dateRange lateJanuaryValue))]).map
          (fun result =>
            (result.verdict, result.source.operands.length,
              result.operands.length)) =
        some (.notFired, 1, 0) := by
  native_decide

/- The first direct match stops before the later filtered star, while the checked source retains both authored operands. -/
example :
    pluralVerdict? (direct "Start") (direct "Finish") [filteredSource]
      [row1] (directOverlapCells ++ [
        rangeCell 3 [1] "2024-01-15/2024-01-31"
          (.parsed (.dateRange lateJanuaryValue)),
        { address := { field := 6, path := [1] }, stored := "1",
          raw := .parsed (.num 1) }]) = some (.fired .value) ∧
      pluralListAddresses? (direct "Start") (direct "Finish")
        [filteredSource] [row1] (directOverlapCells ++ [
          rangeCell 3 [1] "2024-01-15/2024-01-31"
            (.parsed (.dateRange lateJanuaryValue)),
          { address := { field := 6, path := [1] }, stored := "1",
            raw := .parsed (.num 1) }]) =
          some [[(2, [])]] ∧
      (evaluatedPlural? (direct "Start") (direct "Finish")
        [filteredSource] [row1] (directOverlapCells ++ [
          rangeCell 3 [1] "2024-01-15/2024-01-31"
            (.parsed (.dateRange lateJanuaryValue)),
          { address := { field := 6, path := [1] }, stored := "1",
            raw := .parsed (.num 1) }])).map
          (fun result =>
            (result.source.operands.length, result.operands.length)) =
          some (2, 1) ∧
      pluralVerdict? (direct "Start") filteredSource [] [row1] [
        rangeCell 1 [] "2024-01-01/2024-01-31"
          (.parsed (.dateRange januaryValue)),
        rangeCell 3 [1] "2024-01-15/2024-01-31"
          (.parsed (.dateRange lateJanuaryValue)),
        { address := { field := 6, path := [1] }, stored := "1",
          raw := .parsed (.num 1) }] = some (.fired .omission) := by
  native_decide

/- An earlier filtered but disjoint operand does not taint a later direct match. -/
example :
    pluralVerdict? (direct "Start") filteredSource [direct "Finish"] [row1] [
      rangeCell 1 [] "2024-01-01/2024-01-31"
        (.parsed (.dateRange januaryValue)),
      rangeCell 2 [] "15.01.2024-31.01.2024"
        (.parsed (.dateRange lateJanuaryValue)),
      rangeCell 3 [1] "2024-03-01/2024-03-31"
        (.parsed (.dateRange marchValue)),
      { address := { field := 6, path := [1] }, stored := "1",
        raw := .parsed (.num 1) }] = some (.fired .value) := by
  native_decide

private def periodsRows12 : List RowAddr := [
  { group := 11, path := [1] }, { group := 11, path := [2] }]

/- Fixed groups retain declaration order and reach both direct fields. -/
example :
    pluralVerdict? (direct "Start")
      (.group (.path {
        base := .absolute, groups := ["Form", "Fixed"] })) [] [] [
          rangeCell 1 [] "2024-01-01/2024-01-31"
            (.parsed (.dateRange januaryValue)),
          rangeCell 7 [] "2024-03-01/2024-03-31"
            (.parsed (.dateRange marchValue)),
          rangeCell 8 [] "2024-01-15/2024-01-31"
            (.parsed (.dateRange lateJanuaryValue))] = some (.fired .value) ∧
      pluralListAddresses? (direct "Start")
        (.group (.path {
          base := .absolute, groups := ["Form", "Fixed"] })) [] [] [
            rangeCell 1 [] "2024-01-01/2024-01-31"
              (.parsed (.dateRange januaryValue)),
            rangeCell 7 [] "2024-03-01/2024-03-31"
              (.parsed (.dateRange marchValue)),
            rangeCell 8 [] "2024-01-15/2024-01-31"
              (.parsed (.dateRange lateJanuaryValue))] =
          some [[(7, []), (8, [])]] := by
  native_decide

/- A starred group reaches the second declaration in the second row. -/
example :
    pluralVerdict? (direct "Start") starredPeriodsGroup [] periodsRows12 [
      rangeCell 1 [] "2024-01-01/2024-01-31"
        (.parsed (.dateRange januaryValue)),
      rangeCell 9 [1] "2024-03-01/2024-03-31"
        (.parsed (.dateRange marchValue)),
      rangeCell 9 [2] "2024-03-01/2024-03-31"
        (.parsed (.dateRange marchValue)),
      rangeCell 10 [1] "2024-03-01/2024-03-31"
        (.parsed (.dateRange marchValue)),
      rangeCell 10 [2] "2024-01-15/2024-01-31"
        (.parsed (.dateRange lateJanuaryValue))] = some (.fired .value) ∧
      pluralListAddresses? (direct "Start") starredPeriodsGroup []
        periodsRows12 [
          rangeCell 1 [] "2024-01-01/2024-01-31"
            (.parsed (.dateRange januaryValue)),
          rangeCell 9 [1] "2024-03-01/2024-03-31"
            (.parsed (.dateRange marchValue)),
          rangeCell 9 [2] "2024-03-01/2024-03-31"
            (.parsed (.dateRange marchValue)),
          rangeCell 10 [1] "2024-03-01/2024-03-31"
            (.parsed (.dateRange marchValue)),
          rangeCell 10 [2] "2024-01-15/2024-01-31"
            (.parsed (.dateRange lateJanuaryValue))] =
        some [[(9, [1]), (9, [2]), (10, [1]), (10, [2])]] := by
  native_decide

private def date2024 (month day : Nat)
    (admissible : (FullDate.ofYmd? 2024 month day).isSome) : FullDate :=
  (FullDate.ofYmd? 2024 month day).get admissible

private def jan1 := date2024 1 1 (by native_decide)
private def jan15 := date2024 1 15 (by native_decide)
private def jan31 := date2024 1 31 (by native_decide)
private def feb1 := date2024 2 1 (by native_decide)
private def feb15 := date2024 2 15 (by native_decide)
private def feb28 := date2024 2 28 (by native_decide)
private def mar1 := date2024 3 1 (by native_decide)
private def mar31 := date2024 3 31 (by native_decide)

private def january : ResolvedDateRange :=
  { start := jan1, finish := jan31 }

private def lateJanuary : ResolvedDateRange :=
  { start := jan15, finish := jan31 }

private def february : ResolvedDateRange :=
  { start := feb1, finish := feb28 }

private def lateFebruary : ResolvedDateRange :=
  { start := feb15, finish := feb28 }

private def march : ResolvedDateRange :=
  { start := mar1, finish := mar31 }

private def operand (hasFilter : Bool)
    (slots : List ResolvedDateRangeSlot) : ResolvedDateRangeOperand :=
  { slots, hasFilter }

private def plain (ranges : List ResolvedDateRange) : ResolvedDateRangeOperand :=
  operand false (ranges.map .kept)

private def filtered (ranges : List ResolvedDateRange) : ResolvedDateRangeOperand :=
  operand true (ranges.map .kept)

/- A disjoint first operand cannot hide an internal pair in a later operand. -/
example :
    evalDateRangesOverlap [plain [march], plain [january, lateJanuary]] =
      .fired .value := by
  native_decide

/- Equal values arriving through two operand positions remain two occurrences. -/
example :
    evalDateRangesOverlap [plain [january], plain [january]] =
      .fired .value := by
  native_decide

/- A single occurrence cannot form a pair. -/
example : evalDateRangesOverlap [plain [january]] = .notFired := by
  native_decide

/- A filtered operand contributes polarity only after a kept occurrence is reached. -/
example :
    evalDateRangesOverlap
      [operand true [.skipped], plain [january, lateJanuary]] =
      .fired .value := by
  native_decide

/- A kept filtered occurrence taints a later any-pair firing even when it is disjoint. -/
example :
    evalDateRangesOverlap
      [filtered [march], plain [january, lateJanuary]] =
      .fired .omission := by
  native_decide

/- A filtered current occurrence contributes polarity before it is compared with the seen prefix. -/
example :
    evalDateRangesOverlap
      [plain [january], filtered [lateJanuary]] =
      .fired .omission := by
  native_decide

/- A filter after the first match is never reached. -/
example :
    evalDateRangesOverlap
      [plain [january, lateJanuary], filtered [march]] =
      .fired .value := by
  native_decide

/- Reordering can preserve truth while changing the any-pair polarity. -/
example :
    evalDateRangesOverlap
        [filtered [march], plain [january, lateJanuary]] =
          .fired .omission ∧
      evalDateRangesOverlap
        [plain [january, lateJanuary], filtered [march]] =
          .fired .value := by
  native_decide

/- Pairwise-disjoint occurrences do not fire. -/
example :
    evalDateRangesOverlap [plain [january, february, march]] =
      .notFired := by
  native_decide

/- Internal list overlap cannot rescue a skipped scalar. -/
example :
    evalAtLeastOneDateRangeOverlaps .skipped
      [plain [january, lateJanuary]] = .notFired := by
  native_decide

/- Internal list overlap also cannot rescue a kept but disjoint scalar. -/
example :
    evalAtLeastOneDateRangeOverlaps (.kept march)
      [plain [january, lateJanuary]] = .notFired := by
  native_decide

/- A filtered disjoint list operand does not taint a later unfiltered match. -/
example :
    evalAtLeastOneDateRangeOverlaps (.kept january)
      [filtered [march], plain [lateJanuary]] =
        .fired .value := by
  native_decide

/- Polarity comes from the list operand containing the first match. -/
example :
    evalAtLeastOneDateRangeOverlaps (.kept january)
      [plain [march], filtered [lateJanuary]] =
        .fired .omission := by
  native_decide

/- A later filtered match is irrelevant after an earlier unfiltered match. -/
example :
    evalAtLeastOneDateRangeOverlaps (.kept january)
      [plain [lateJanuary], filtered [january]] =
        .fired .value := by
  native_decide

/- A scalar with no matching list occurrence does not fire. -/
example :
    evalAtLeastOneDateRangeOverlaps (.kept january)
      [plain [lateFebruary, march]] = .notFired := by
  native_decide

end A12Kernel.Conformance.DateRangeOverlapOperators
