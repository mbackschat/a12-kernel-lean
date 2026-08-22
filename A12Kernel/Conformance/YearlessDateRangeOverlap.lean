import A12Kernel.Elaboration.YearlessDateRangeOverlap

/-! # Unconfigured yearless DateRange overlap locks

These cases run the whole route for a model with no Base Year: stored text, checked cells,
admission, and the any-pair verdict. Their expected verdicts are the Kernel rows in the
yearless-overlap checkpoint, measured on both codegen strategies.
-/

namespace A12Kernel.Conformance.YearlessDateRangeOverlap

open A12Kernel

private def rangeField (id : FieldId) (name format separator : String)
    (groupPath : GroupPath := ["Form"])
    (scope : List RepeatableLevel := [])
    (interpretationOfYear : Option DateRangeYearInterpretation := none) :
    FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .dateRange }
  dateRangePolicy := some { format, separator, interpretationOfYear }
}

private def model : FlatModel := {
  fields := [
    rangeField 1 "MonthSlash" "MM" "/",
    rangeField 2 "OtherMonthSlash" "MM" "/",
    rangeField 3 "MonthDaySlash" "MM-dd" "/",
    rangeField 4 "MonthEmpty" "MM" "",
    rangeField 5 "ExactIso" "yyyy-MM-dd" "/",
    rangeField 6 "Period" "MM" "/" ["Form", "Rows"] [10],
    { id := 7, name := "Guard", groupPath := ["Form", "Rows"]
      repeatableScope := [10]
      policy := { kind := .number { scale := 0, signed := false } } },
    rangeField 8 "WindowLeft" "MM" "/" ["Form", "Windows"],
    rangeField 9 "WindowRight" "MM-dd" "/" ["Form", "Windows"],
    rangeField 10 "MonthSlashFrom" "MM" "/" ["Form"] [] (some .anchorStart)]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 4 }]
}

private def configured : FlatModel := { model with baseYear := some 2024 }

private def certify? (checkedModel : FlatModel) (id : FieldId) :
    Option (CheckedYearlessDateRangeOverlapField checkedModel) :=
  match checkedModel.lookupUniqueId id with
  | .ok declaration =>
      (certifyYearlessDateRangeOverlapField checkedModel declaration).toOption
  | .error _ => none

/-- Classify one stored token exactly as the checked-document route does, so the fixture cannot disagree with canonical classification. -/
private def storedCell (field : FieldId) (stored : String) : ClassifiedCellInput := {
  address := { field, path := [] }
  stored
  raw :=
    match model.lookupUniqueId field with
    | .ok declaration =>
        match declaration.toDateRangeDeclarationPolicy? with
        | some policy =>
            (classifyStoredDateRangeForModel model.timeZoneId model.baseYear
              policy stored).toOption.getD .empty
        | none => .empty
    | .error _ => .empty
}

private def verdict? (left right : FieldId)
    (leftText rightText : String) : Option Verdict := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let leftSource ← certify? model left
  let rightSource ← certify? model right
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := [storedCell left leftText, storedCell right rightText]
  }).toOption
  (evaluateYearlessDateRangesOverlap [leftSource, rightSource] document).toOption

/- Both yearless spellings are admitted without a Base Year, and a configured model routes to the completed owner instead. -/
example :
    (certify? model 1).isSome = true ∧
      (certify? model 4).isSome = true ∧
      (certify? model 3).isSome = true ∧
      (certify? configured 1).isNone = true ∧
      (certify? model 5).isNone = true := by
  native_decide

/- A month-only pair spans whole months, the interval is closed, and a disjoint pair does not fire. -/
example :
    verdict? 1 2 "01/06" "04/09" = some (.fired .value) ∧
      verdict? 1 2 "01/03" "06/09" = some .notFired ∧
      verdict? 1 2 "01/06" "06/09" = some (.fired .value) := by
  native_decide

/- The halved spelling behaves exactly like its slash sibling on the same components. -/
example :
    verdict? 1 4 "01/06" "0409" = some (.fired .value) ∧
      verdict? 1 4 "01/03" "0609" = some .notFired := by
  native_decide

/- A month-only operand compares against a day-bearing operand of a different component set, reaching inside its month and stopping at the month's edges. -/
example :
    verdict? 1 3 "01/06" "06-15/06-20" = some (.fired .value) ∧
      verdict? 1 3 "07/12" "06-01/06-30" = some .notFired ∧
      verdict? 1 3 "06/12" "05-01/06-01" = some (.fired .value) ∧
      verdict? 1 3 "01/06" "06-30/07-31" = some (.fired .value) := by
  native_decide

/- February reaches day 29 where no year can decide leapness, and the span still stops before March. -/
example :
    verdict? 1 3 "01/02" "02-29/03-05" = some (.fired .value) ∧
      verdict? 1 3 "01/02" "03-01/03-05" = some .notFired := by
  native_decide

/- An empty operand is skipped rather than compared, so no pair remains. -/
example : verdict? 1 2 "" "04/09" = some .notFired := by
  native_decide

private def pluralVerdict? (scalar listed : FieldId)
    (scalarText listedText : String) : Option Verdict := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let scalarSource ← certify? model scalar
  let listedSource ← certify? model listed
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := [storedCell scalar scalarText, storedCell listed listedText]
  }).toOption
  (evaluateYearlessAtLeastOneDateRangeOverlapsOperands (.direct scalarSource)
    [.direct listedSource] document []).toOption

/- The scalar-versus-list scan compares yearless labels exactly as the any-pair scan does, and an
unusable scalar terminates before the list is read. Each row is a measured Kernel outcome. -/
example :
    pluralVerdict? 1 3 "01/06" "06-15/06-20" = some (.fired .value) ∧
      pluralVerdict? 1 3 "01/06" "07-01/07-05" = some .notFired ∧
      pluralVerdict? 1 3 "01/02" "02-29/03-05" = some (.fired .value) ∧
      pluralVerdict? 1 3 "" "06-15/06-20" = some .notFired := by
  native_decide

private def periodStar : SurfaceFieldEntityOperand :=
  .star {
    base := .absolute
    groups := [{ name := "Form" }, { name := "Rows", starred := true }]
    field := "Period"
  }

private def starOperand? (checkedModel : FlatModel)
    (authored : SurfaceFieldEntityOperand) :
    Option (CheckedYearlessDateRangeOverlapOperand checkedModel) :=
  match resolveFieldEntityOperandUnchecked checkedModel ["Form"] authored with
  | .ok resolved =>
      (certifyYearlessDateRangeOverlapOperand checkedModel ["Form"] resolved).toOption
  | .error _ => none

private def rowCell (row : Nat) (stored : String) : ClassifiedCellInput := {
  address := { field := 6, path := [row] }
  stored
  raw :=
    match model.lookupUniqueId 6 with
    | .ok declaration =>
        match declaration.toDateRangeDeclarationPolicy? with
        | some policy =>
            (classifyStoredDateRangeForModel model.timeZoneId model.baseYear
              policy stored).toOption.getD .empty
        | none => .empty
    | .error _ => .empty
}

private def guardFilter : SurfaceCorrelatedHaving :=
  .compareNumbers .equal
    { origin := .inner,
      field := { base := .absolute, groups := ["Form", "Rows"], field := "Guard" } }
    { origin := .inner,
      field := { base := .absolute, groups := ["Form", "Rows"], field := "Guard" } }

private def filteredPeriodStar : SurfaceFieldEntityOperand :=
  .starHaving {
    base := .absolute
    groups := [{ name := "Form" }, { name := "Rows", starred := true }]
    field := "Period"
  } guardFilter

/-- One filled per-row guard so a self-comparing filter keeps its row. -/
private def guardCell (row : Nat) : ClassifiedCellInput := {
  address := { field := 7, path := [row] }
  stored := "1"
  raw := .parsed (.num 1)
}

private def verdictFor? (authored : SurfaceFieldEntityOperand)
    (rows : List (Nat × String)) : Option Verdict := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let operand ← starOperand? model authored
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows :=
      (List.range 4).map fun index => { group := 10, path := [index + 1] }
    cells := (rows.map fun (row, stored) => rowCell row stored) ++
      rows.map fun (row, _) => guardCell row
  }).toOption
  (evaluateYearlessDateRangeOverlapOperands [operand] document []).toOption

private def filteredStarVerdict? (rows : List (Nat × String)) : Option Verdict :=
  verdictFor? filteredPeriodStar rows

private def starVerdict? (rows : List (Nat × String)) : Option Verdict :=
  verdictFor? periodStar rows

/- A plain starred yearless operand is admitted without a Base Year, and its flattened rows
compare as yearless labels: an internal overlapping pair fires, a disjoint list does not, and
February still reaches day 29. Empty rows are skipped rather than compared. -/
example :
    (starOperand? model periodStar).isSome = true ∧
      starVerdict? [(1, "01/06"), (2, "04/09")] = some (.fired .value) ∧
      starVerdict? [(1, "01/03"), (2, "06/09")] = some .notFired ∧
      starVerdict? [(1, "01/06"), (2, "06/09")] = some (.fired .value) ∧
      starVerdict? [(1, "01/02"), (2, "02/02")] = some (.fired .value) ∧
      starVerdict? [(1, "01/06")] = some .notFired ∧
      starVerdict? [(1, "01/06"), (2, "")] = some .notFired := by
  native_decide

/- A filtered yearless star is admitted, and a firing that reached a filter-bearing operand is
OMISSION rather than VALUE. The filter itself is self-comparing here, so it keeps every row and
isolates the polarity rule from the selection rule. -/
example :
    (starOperand? model filteredPeriodStar).isSome = true ∧
      filteredStarVerdict? [(1, "01/06"), (2, "04/09")] =
        some (.fired .omission) ∧
      filteredStarVerdict? [(1, "01/03"), (2, "06/09")] = some .notFired := by
  native_decide

private def windowsGroup : SurfaceFieldEntityOperand :=
  .group (.path { base := .absolute, groups := ["Form", "Windows"] })

private def groupCarrierVerdict? (scalarText leftText rightText : String) :
    Option Verdict := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let scalar ← starOperand? model (.field {
    base := .relative 0, groups := [], field := "MonthSlash" })
  let listed ← starOperand? model windowsGroup
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := [storedCell 1 scalarText, storedCell 8 leftText,
      storedCell 9 rightText]
  }).toOption
  (evaluateYearlessAtLeastOneDateRangeOverlapsOperands scalar [listed] document
    []).toOption

/- A group carrier on the plural list side contributes every yearless declaration in its subtree,
so either member can be the match, and an unusable scalar still terminates first. The singular
operator's refusal of every group carrier is measured too, and stays locked with its exact
diagnostic in `Conformance.DateRangeOverlapOperators`. -/
example :
    groupCarrierVerdict? "01/06" "04/09" "10-01/12-31" = some (.fired .value) ∧
      groupCarrierVerdict? "01/06" "08/09" "05-01/07-31" = some (.fired .value) ∧
      groupCarrierVerdict? "01/03" "06/09" "10-01/12-31" = some .notFired ∧
      groupCarrierVerdict? "" "04/09" "10-01/12-31" = some .notFired := by
  native_decide

/- The unconfigured route refuses an interpretation-bearing declaration on the same terms as the completed one. The interpretation has no anchor year to act on here, so the refusal is a property of the declaration rather than of its completion, and it carries the Kernel's format diagnostic through the shared singular cause. -/
example :
    (match model.lookupUniqueId 10 with
      | .ok declaration =>
          certifyYearlessDateRangeOverlapField model declaration
            |>.toOption.isNone
      | .error _ => false) = true ∧
    (match model.lookupUniqueId 10 with
      | .ok declaration =>
          match certifyYearlessDateRangeOverlapField model declaration with
          | .error (.source cause) => cause.diagnostic?
          | _ => none
      | .error _ => none) = some .invalidDateRangeFormat ∧
    (certify? model 1).isSome = true := by
  native_decide

end A12Kernel.Conformance.YearlessDateRangeOverlap
