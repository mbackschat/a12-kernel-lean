import A12Kernel.Reference.Dm.Compute

namespace A12Kernel.Dm.OverlapAgreementLocks

private def model (baseYear : Option Int := none) (yearless : Bool := false) : FlatModel :=
  let first := if yearless then "MM-dd" else "yyyy-MM-dd"
  let second := if yearless then "dd.MM" else "dd.MM.yyyy"
  let range (id : FieldId) (name : String) (group : GroupPath) (format separator : String)
      (scope : List RepeatableLevel := []) : FlatFieldDecl := {
    id, name, groupPath := group, repeatableScope := scope, policy := { kind := .dateRange }
    dateRangePolicy := some { format, separator } }
  { baseYear
    fields := [range 1 "Scalar" ["Form"] first "/",
      range 2 "A" ["Form", "Fixed"] first "/", range 3 "B" ["Form", "Fixed"] second "-",
      range 4 "A" ["Form", "Rows", "Ranges"] first "/" [10],
      range 5 "B" ["Form", "Rows", "Ranges"] second "-" [10],
      { id := 6, name := "Key", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } },
      { id := 7, name := "Out", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } }]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2, indexField := some 6 }] }

private def admission (condition : String) (source : FlatModel) : Option (Bool × Bool) := do
  let parsed ← (parseText .english condition).toOption
  pure ((lowerCondition source ["Form"] false parsed.body).isOk,
    (lowerComputation source .english {
      name := "Consumer", group := ["Form"], targetRelPath := "../Out"
      commonPrecondition := some condition, alternatives := [{ precondition := none, operation := "1" }]
      errorCodesToSuppress := [] }).isOk)

example : model.validate.isOk = true ∧ (model (some 2024)).validate.isOk = true ∧
    admission "AtLeastOneDateRangeOverlaps(Scalar In Fixed/A,Fixed/B)" model == some (true, true) ∧
    admission "AtLeastOneDateRangeOverlaps(Scalar In Fixed)" (model (some 2024)) == some (true, true) := by native_decide

example : [false, true].all (fun yearless =>
    ["Fixed", "Rows*/Ranges", "Rows/Ranges For \"k\""].all (fun operand =>
      admission ("AtLeastOneDateRangeOverlaps(Scalar In " ++ operand ++ ")") (model none yearless) == some (false, false))) = true := by native_decide

private def uniform (source : FlatModel) : FlatModel := {
  source with fields := source.fields.map fun field =>
    if field.id == 3 || field.id == 5 then { field with dateRangePolicy := (source.fields[0]?).bind (·.dateRangePolicy) }
    else field }

private def diagnostic (condition : String) (source : FlatModel) : Option String := do
  let parsed ← (parseText .english condition).toOption
  match lowerCondition source ["Form"] false parsed.body with
  | .ok _ => none
  | .error error => some error.detail

example : [false, true].all (fun yearless =>
    ["Fixed", "Rows*/Ranges", "Rows/Ranges For \"k\""].all (fun operand =>
      let condition := "AtLeastOneDateRangeOverlaps(Scalar In " ++ operand ++ ")"
      admission condition (uniform (model none yearless)) == some (true, true) &&
      diagnostic condition (model none yearless) == some "MVK_DATE_WITH_AND_WITHOUT_YEAR") &&
    admission "AtLeastOneDateRangeOverlaps(Scalar In Fixed/A,Fixed/B)" (model none yearless) == some (true, true) &&
    admission "DateRangesOverlap(Fixed/A,Fixed/B)" (model none yearless) == some (true, true)) = true := by native_decide

example : ["Fixed", "Rows*/Ranges", "Rows/Ranges For \"k\""].all (fun operand =>
    admission ("AtLeastOneDateRangeOverlaps(Scalar In " ++ operand ++ ")") (model (some 2024)) == some (true, true)) = true := by native_decide

private def interpreted (baseYear : Option Int) : FlatModel := {
  model baseYear with fields := (model baseYear).fields.map fun field =>
    if field.id == 3 then { field with dateRangePolicy := field.dateRangePolicy.map fun policy =>
      { policy with interpretationOfYear := some .anchorStart } } else field }

example : [none, some 2024].all (fun year =>
    diagnostic "AtLeastOneDateRangeOverlaps(Scalar In Fixed)" (interpreted year) ==
      some "MVK_INVALID_DATE_RANGE_FORMAT") = true := by native_decide

example : [false, true].all (fun yearless => [none, some 2024].all fun year =>
    let source := model year yearless
    let expanded := source.fields.filter (fun field => [1, 2, 3].contains field.id)
    (checkHavingOverlapDeclarations source [expanded]).isOk == year.isSome &&
    (checkHavingOverlapDeclarations source (expanded.map (fun field => [field]))).isOk) = true := by native_decide

end A12Kernel.Dm.OverlapAgreementLocks
