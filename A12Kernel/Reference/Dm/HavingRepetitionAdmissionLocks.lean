import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingRepetitionAdmissionLocks
open A12Kernel

private def diagnostic (filter : String) :=
  HavingFixture.filterDiagnostic? HavingFixture.model filter

example : ["RepetitionNotUnique(Rows/N)", "RepetitionNotUnique(Rows/N, Rows/Tag)",
    "RepetitionNotUnique(Rows/N @From Rows)"].all (fun filter =>
    diagnostic filter == some .disallowedConstructInFilterCondition &&
    HavingFixture.admissions HavingFixture.model filter == (false, false)) = true := by native_decide

example : diagnostic "RepetitionNotUnique(Expected)" = some .repeatableGroupMissing ∧
    diagnostic "RepetitionNotUnique(Rows/N, Rows/N)" = some .duplicateParam1 ∧
    diagnostic "RepetitionNotUnique(Rows, Rows/N)" = some .duplicateParam2 ∧
    diagnostic "RepetitionNotUnique(Rows)" = some .noGroupsAllowed ∧
    diagnostic "RepetitionNotUnique(Rows*/N)" = some .noWildcardsAllowed ∧
    diagnostic "RepetitionNotUnique(Rows/N @From Rows/N)" = some .noFieldsAllowed ∧
    diagnostic "RepetitionNotUnique(Rows/N @From /Form)" = some .groupNotRepeatable ∧
    diagnostic "RepetitionNotUnique(Rows/N @From Rows*)" = some .noWildcardsAllowed := by native_decide

example : ["And", "Or"].all (fun op => [false, true].all fun reverse =>
    let join := fun left right => if reverse then right ++ " " ++ op ++ " " ++ left else left ++ " " ++ op ++ " " ++ right
    diagnostic (join "RepetitionNotUnique(Rows/N)" "[Rows/Tag] > \"keep\"") == some .invalidTypeForComparison &&
    diagnostic (join "RepetitionNotUnique(Rows/N)" "FieldFilled($Rows/N)") == some .noWildcard) = true := by native_decide

example : HavingFixture.run "FieldFilled(Rows/N) And [Rows/Tag] == \"keep\"" =
    some (.fired .omission, ["value 9"]) := by native_decide

private def domain : EnumerationDeclaration := {
  storedTokens := ["keep", "drop"], categories := [{ name := "Label", tokens := ["K", "D"] }] }

private def typedModel (kind : FieldKind) : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields.map fun field => if field.id == 3 then { field with
    policy := { kind }, enumeration := if kind == .enumeration then some domain else none
    dateRangePolicy := if kind == .dateRange then some { format := "yyyy-MM-dd", separator := "/" } else none } else field }

example : [.boolean, .confirm, .enumeration, .dateRange,
    .temporal .date TemporalComponents.fullDate,
    .temporal .time (TemporalComponents.ofFormat "HH:mm:ss")].all (fun kind =>
    (typedModel kind).validate.isOk &&
    HavingFixture.filterDiagnostic? (typedModel kind) "RepetitionNotUnique(Rows/Tag)" ==
      some .disallowedConstructInFilterCondition) = true := by native_decide

example : HavingFixture.filterDiagnostic? (typedModel .enumeration)
    "RepetitionNotUnique(Rows, Rows/Tag->Label)" = some .categoryNotAllowed ∧
    HavingFixture.filterDiagnostic? (typedModel .enumeration)
    "RepetitionNotUnique(Rows/Tag->Label, Rows)" = some .categoryNotAllowed ∧
    HavingFixture.filterDiagnostic? (typedModel .enumeration)
    "RepetitionNotUnique(Rows/Tag->Label, Rows/Tag->Label)" = some .duplicateParam1 := by native_decide

private def rawModel : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields.map fun field => if field.id == 3 then
    { field with stringValueMode := .raw, stringPolicy := { lineBreaksPermitted := true } } else field }

example : rawModel.validate.isOk = true ∧
    HavingFixture.filterDiagnostic? rawModel "RepetitionNotUnique(Rows/Tag)" = some .rawTypeOperandInvalid ∧
    HavingFixture.filterDiagnostic? rawModel "RepetitionNotUnique(Rows/Tag, Rows*/N)" = some .noWildcardsAllowed ∧
    HavingFixture.filterDiagnostic? rawModel "RepetitionNotUnique(Rows/Tag, Rows)" = some .duplicateParam2 := by native_decide

example : HavingFixture.filterDiagnostic? HavingFixture.model "RepetitionNotUnique($Rows/N @From $Rows)"
      (bindingGroup := ["Form", "Rows"]) = some .noIterationForWildcard ∧
    HavingFixture.filterDiagnostic? HavingFixture.model "RepetitionNotUnique($Rows/N @From Rows)"
      (bindingGroup := ["Form", "Rows"]) = some .disallowedConstructInFilterCondition ∧
    HavingFixture.filterDiagnostic? HavingFixture.model "RepetitionNotUnique($Rows/N, Rows/N)"
      (bindingGroup := ["Form", "Rows"]) = some .disallowedConstructInFilterCondition ∧
    HavingFixture.filterDiagnostic? HavingFixture.model "WiederholungNichtEindeutig(Rows/N @Von Rows)" .german =
      some .disallowedConstructInFilterCondition := by native_decide

private def branchedModel : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields ++ [
    { id := 6, groupPath := ["Form", "Other"], name := "N", repeatableScope := [20],
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 7, groupPath := ["Form", "Rows", "A"], name := "N", repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 8, groupPath := ["Form", "Rows", "B"], name := "N", repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := HavingFixture.model.repeatableGroups ++ [{ level := 20, path := ["Form", "Other"], repeatability := some 3 }] }

example : branchedModel.validate.isOk = true ∧
    HavingFixture.filterDiagnostic? branchedModel "RepetitionNotUnique(Rows/N, Other/N)" = some .notInSamePath ∧
    HavingFixture.filterDiagnostic? branchedModel "RepetitionNotUnique(Other/N @From Rows)" = some .entityNotInGroup ∧
    HavingFixture.filterDiagnostic? branchedModel "RepetitionNotUnique(Other/N)" = some .invalidIterationInFilterCondition ∧
    HavingFixture.filterDiagnostic? branchedModel "RepetitionNotUnique(Rows/A/N, Rows/B/N)" = some .disallowedConstructInFilterCondition ∧
    HavingFixture.filterDiagnostic? branchedModel "RepetitionNotUnique(Rows/A/N, Rows/B/N @From Rows)" = some .disallowedConstructInFilterCondition := by native_decide

example : diagnostic "RepetitionNotUnique(Rows->Label)" = some .noGroupsAllowed ∧
    diagnostic "RepetitionNotUnique(Rows/N, Rows/N, Rows->Label)" = some .noGroupsAllowed := by native_decide

private def projectedGroupModel : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields ++ [{
    id := 6, groupPath := ["Form", "Rows", "Labels"], name := "E", repeatableScope := [10]
    policy := { kind := .enumeration }, enumeration := some {
      storedTokens := ["keep", "drop"], categories := [{ name := "Label", tokens := ["drop", "keep"] }] } }] }

private def projectedGroupRows : Array Lean.Json := #["2", "5", "7"].map fun n => Lean.Json.mkObj [
  ("N", Lean.Json.str n), ("Tag", Lean.Json.str "keep"),
  ("Labels", Lean.Json.mkObj [("E", Lean.Json.str "keep")])]

private def projectedRun (filter : String) :=
  HavingFixture.runModel projectedGroupModel filter false "keep" "keep" "drop"
    (ruleExpected := "14") (rowsOverride := some projectedGroupRows)

example : projectedGroupModel.validate.isOk = true ∧
    projectedRun "FirstFilledValue(Rows/Labels, Rows/Labels/E->Label) == \"keep\"" =
      some (.fired .omission, ["value 14"]) ∧
    projectedRun "NumberOfValueInFields(\"keep\" In Rows/Labels, Rows/Labels/E->Label) == 1" =
      some (.fired .omission, ["value 14"]) := by native_decide

example : HavingFixture.filterDiagnostic? projectedGroupModel
    "FirstFilledValue(Rows/Labels, Rows/Labels/E) == \"keep\"" = some .duplicateParam2 ∧
    HavingFixture.filterDiagnostic? projectedGroupModel
    "NumberOfValueInFields(\"keep\" In Rows/Labels/E, Rows/Labels) == 1" = some .duplicateParam2 := by native_decide

example : projectedRun "NoFieldValueIncludedInValueList(Rows/Labels In Rows/Labels/E->Label)" =
      some (.fired .omission, ["value 14"]) ∧
    projectedRun "FirstFilledValue(Rows/Labels/E->Label, Rows/Labels) == \"drop\"" =
      some (.fired .omission, ["value 14"]) ∧
    HavingFixture.filterDiagnostic? projectedGroupModel
      "NoFieldValueIncludedInValueList(Rows/Labels In Rows/Labels/E)" = some .duplicateParam2 := by native_decide

example : diagnostic "RepetitionNotUnique(Rows, Rows, Missing)" = some .invalidEntity ∧
    diagnostic "RepetitionNotUnique(Rows/N, Rows/N @From Missing)" = some .invalidEntity := by native_decide

end A12Kernel.Dm.HavingRepetitionAdmissionLocks
