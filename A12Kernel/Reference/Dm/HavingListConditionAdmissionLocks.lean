import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingListConditionAdmissionLocks
open A12Kernel

private def model : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields ++ [
    { id := 6, name := "RowOut", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 7, name := "A", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .dateRange }, dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } },
    { id := 8, name := "B", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .dateRange }, dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } },
    { id := 9, name := "Day", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .temporal .date .fullDate }, temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
    { id := 10, name := "OtherDay", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .temporal .date .fullDate }, temporalTargetPolicy := some { format := "dd.MM.yyyy" } },
    { id := 11, name := "Raw", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .string }, stringValueMode := .raw, stringPolicy := { lineBreaksPermitted := true } },
    { id := 12, name := "Choice", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .enumeration }, enumeration := some {
        storedTokens := ["a"], categories := [{ name := "Label", tokens := ["b"] }] } },
    { id := 13, name := "X", groupPath := ["Form", "Pool"],
      policy := { kind := .dateRange }, dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } },
    { id := 14, name := "Y", groupPath := ["Form", "Pool"],
      policy := { kind := .dateRange }, dateRangePolicy := some { format := "dd.MM.yyyy", separator := "-" } },
    { id := 15, name := "Other", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 3 }] }

private def result (body : String) (row : Bool) (fixture : FlatModel := model) : String × String :=
  HavingFixture.readerResults ("Sum(Rows*/N Having " ++ body ++ ")") fixture row

example : model.validate.isOk = true ∧ [false, true].all (fun row =>
    ["FieldValuesNotUnique(Rows/N,Rows/Other)", "DateRangesOverlap(Rows/A,Rows/B)",
      "AtLeastOneDateRangeOverlaps(Rows/A In Rows/B)",
      "DateRangesOverlap(Pool/X,Pool/Y) And FieldFilled(Rows/N)"].all fun body => result body row == ("admitted", "admitted")) = true := by native_decide

private def indexedCases : List (String × String) := [
  ("FieldValuesNotUnique(Rows/N For \"keep\",Rows/Other)", "MVK_SEMANTIC_INDEX_NOT_ALLOWED"),
  ("DateRangesOverlap(Rows/A For \"keep\",Rows/B)", "MVK_SEMANTIC_INDEX_NOT_ALLOWED"),
  ("AtLeastOneDateRangeOverlaps(Rows/A For \"keep\" In Rows/B)", "MVK_SEMANTIC_INDEX_NOT_ALLOWED"),
  ("AtLeastOneDateRangeOverlaps(Rows/A In Rows/B For \"keep\")", "MVK_SEMANTIC_INDEX_NOT_ALLOWED"),
  ("FieldValuesNotUnique(Rows/N For \"keep\",Rows/N For \"keep\")", "MVK_DUPLICATE_PARAM1"),
  ("DateRangesOverlap(Rows/A For \"keep\",Rows/A For \"drop\")", "MVK_SEMANTIC_INDEX_NOT_ALLOWED"),
  ("AtLeastOneDateRangeOverlaps(Rows/A For \"keep\" In Rows/A For \"keep\")", "MVK_DUPLICATE_PARAM1"),
  ("FieldValuesNotUnique(Rows/N For \"keep\",Rows/Day,Rows/OtherDay)", "MVK_ONLY_STRING_ENUM_NUMBER_DATE_ALLOWED"),
  ("FieldValuesNotUnique(Rows/N For \"keep\",Rows/Raw)", "MVK_VARYING_TYPES_NOT_ALLOWED"),
  ("FieldValuesNotUnique(Rows/Tag For \"keep\",Rows/Raw)", "MVK_INVALID_RAW_TYPE"),
  ("DateRangesOverlap(Rows/A For \"keep\",Rows/N)", "MVK_NO_DATE_RANGE"),
  ("AtLeastOneDateRangeOverlaps(Rows/A For \"keep\" In Rows/N,Rows/A For \"keep\")", "MVK_VARYING_TYPES_NOT_ALLOWED"),
  ("DateRangesOverlap(Rows For \"keep\")", "MVK_NO_GROUPS_ALLOWED"),
  ("AtLeastOneDateRangeOverlaps(Rows For \"keep\" In Rows/A)", "MVK_VARYING_TYPES_NOT_ALLOWED"),
  ("AtLeastOneDateRangeOverlaps(Pool In Rows/A For \"keep\")", "MVK_INVALID_PARAMETER_FOR_DATE_RANGE_COMPARISON"),
  ("FieldValuesNotUnique(Rows/Choice->Label For \"keep\",Rows/N)", "MVK_CATEGORY_NOT_ALLOWED"),
  ("DateRangesOverlap(Rows/Choice->Label For \"keep\",Rows/A)", "MVK_CATEGORY_NOT_ALLOWED")]

example : [false, true].all (fun row => indexedCases.all fun (body, diagnostic) =>
    result body row == (diagnostic, diagnostic)) = true := by native_decide

private def plainCases : List (String × String) := [
  ("FieldValuesNotUnique(Rows/N,Rows/Day,Rows/OtherDay)", "MVK_ONLY_STRING_ENUM_NUMBER_DATE_ALLOWED"),
  ("FieldValuesNotUnique(Rows/N,Rows/Raw)", "MVK_VARYING_TYPES_NOT_ALLOWED"),
  ("FieldValuesNotUnique(Rows/Tag,Rows/Raw)", "MVK_INVALID_RAW_TYPE"),
  ("DateRangesOverlap(Rows/A)", "MVK_PARAMSIZE_INVALIDFN"),
  ("DateRangesOverlap(Pool)", "MVK_NO_GROUPS_ALLOWED"),
  ("AtLeastOneDateRangeOverlaps(Rows/A In Rows/N,Rows/A)", "MVK_VARYING_TYPES_NOT_ALLOWED"),
  ("AtLeastOneDateRangeOverlaps(Pool In Rows/A)", "MVK_INVALID_PARAMETER_FOR_DATE_RANGE_COMPARISON"),
  ("AtLeastOneDateRangeOverlaps(Rows/A In Pool)", "MVK_DATE_WITH_AND_WITHOUT_YEAR"),
  ("AtLeastOneDateRangeOverlaps(Rows/A In \"x\")", "MVK_NO_CONST")]

example : [false, true].all (fun row => plainCases.all fun (body, diagnostic) =>
    result body row == (diagnostic, diagnostic)) = true := by native_decide

example : [false, true].all (fun row =>
    ["FieldValuesNotUnique(Rows/N For \"keep\",Rows/N For \"keep\",Missing)",
      "DateRangesOverlap(Rows/N For \"keep\",Missing)",
      "AtLeastOneDateRangeOverlaps(Pool In Missing)"].all fun body =>
        result body row == ("MVK_INVALID_ENTITY", "MVK_INVALID_ENTITY")) = true := by native_decide

example : [false, true].all (fun row =>
    ["FieldValuesNotUnique(Rows/N For \"keep\",Rows/Other)",
      "DateRangesOverlap(Rows/A For \"keep\",Rows/B)",
      "AtLeastOneDateRangeOverlaps(Rows/A For \"keep\" In Rows/B)"].all fun body =>
        result (body ++ " And FieldFilled(Missing)") row == ("MVK_INVALID_ENTITY", "MVK_INVALID_ENTITY")) = true := by native_decide

private def typedResult (body : String) : String :=
  match parseText .english body with
  | .error _ => "parse refusal"
  | .ok parsed => match lowerHaving parsed.body (some (model, ["Form"])) with
    | .error refusal => refusal.detail
    | .ok source => match elaborateHavingBodyAtLevels model ["Form"] [10] [10] source with
      | .ok _ => "admitted"
      | .error error => error.diagnostic?.map (·.kernelCode) |>.getD "unclassified"

example : (plainCases.take 8).all (fun (body, diagnostic) => typedResult body == diagnostic) = true := by native_decide

example : [false, true].all (fun row =>
    let preceding := "AtLeastOneFieldFilled(Rows*/N Having FieldFilled(Rows/N)) And "
    ["FieldValuesNotUnique(Rows/N,Rows/Other)", "DateRangesOverlap(Rows/A,Rows/B)",
      "AtLeastOneDateRangeOverlaps(Rows/A In Rows/B)"].all (fun body =>
        result (preceding ++ body) row ==
          (if row then ("MVK_DISALLOWED_CONSTRUCT_IN_FILTER_CONDITION", "MVK_DISALLOWED_CONSTRUCT_IN_FILTER_CONDITION")
           else ("MVK_NO_WILDCARD", "MVK_NO_WILDCARD"))) &&
    ["FieldValuesNotUnique($Rows/N,Rows/Other)", "DateRangesOverlap($Rows/A,Rows/B)",
      "AtLeastOneDateRangeOverlaps($Rows/A In Rows/B)"].all (fun body =>
        result (preceding ++ body) row == ("MVK_INVALID_OUTER_ITERATION", "MVK_INVALID_OUTER_ITERATION"))) = true := by native_decide

example : [false, true].all (fun row =>
    ["FieldValuesNotUnique(Rows*/N Having FieldFilled(Rows/N),Rows/Other)",
      "DateRangesOverlap(Rows*/A Having FieldFilled(Rows/N),Rows/B)",
      "AtLeastOneDateRangeOverlaps(Rows/A In Rows*/B Having FieldFilled(Rows/N),Rows/B)"].all fun body =>
        result body row ==
          (if row then ("MVK_DISALLOWED_CONSTRUCT_IN_FILTER_CONDITION", "MVK_DISALLOWED_CONSTRUCT_IN_FILTER_CONDITION")
           else ("MVK_NO_WILDCARD", "MVK_NO_WILDCARD"))) = true := by native_decide

private def yearlessModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 8 then { field with dateRangePolicy := some { format := "MM-dd", separator := "/" } } else field }

private def interpretedModel : FlatModel := { yearlessModel with fields := yearlessModel.fields.map fun field =>
  if field.id == 8 then { field with dateRangePolicy := some {
    format := "MM-dd", separator := "/", interpretationOfYear := some .anchorStart } } else field }

example : yearlessModel.validate.isOk = true ∧ interpretedModel.validate.isOk = true ∧
    [false, true].all (fun row =>
      ["DateRangesOverlap(Rows/A For \"keep\",Rows/B)",
       "AtLeastOneDateRangeOverlaps(Rows/A For \"keep\" In Rows/B)"].all fun body =>
        result body row yearlessModel == ("MVK_DATE_WITH_AND_WITHOUT_YEAR", "MVK_DATE_WITH_AND_WITHOUT_YEAR") &&
        result body row { yearlessModel with baseYear := some 2024 } ==
          ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED") &&
        result body row { interpretedModel with baseYear := some 2024 } ==
          ("MVK_INVALID_DATE_RANGE_FORMAT", "MVK_INVALID_DATE_RANGE_FORMAT")) = true := by native_decide

example : [false, true].all (fun row =>
    result "AtLeastOneDateRangeOverlaps(Rows/A For \"keep\" In Pool)" row ==
      ("MVK_DATE_WITH_AND_WITHOUT_YEAR", "MVK_DATE_WITH_AND_WITHOUT_YEAR") &&
    result "AtLeastOneDateRangeOverlaps(Rows/A For \"keep\" In Pool)" row { model with baseYear := some 2024 } ==
      ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED") &&
    result "AtLeastOneDateRangeOverlaps(Rows/A In Pool)" row { model with baseYear := some 2024 } ==
      ("admitted", "admitted")) = true := by native_decide

end A12Kernel.Dm.HavingListConditionAdmissionLocks
