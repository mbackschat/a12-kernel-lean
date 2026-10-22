import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingGlobalAdmissionLocks
open A12Kernel

private def model : FlatModel := { HavingFixture.model with
  baseYear := some 2024
  fields := HavingFixture.model.fields ++ [
    { id := 6, name := "RowOut", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 7, name := "Tag", groupPath := ["Form", "Parties"], repeatableScope := [20], policy := { kind := .string } },
    { id := 8, name := "N", groupPath := ["Form", "Parties"], repeatableScope := [20], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 9, name := "Qty", groupPath := ["Form", "Parties", "Lines"], repeatableScope := [20, 30],
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 10, name := "Raw", groupPath := ["Form"], repeatableScope := [], policy := { kind := .string },
      stringValueMode := .raw, stringPolicy := { lineBreaksPermitted := true } }]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 3 },
    { level := 20, path := ["Form", "Parties"], repeatability := some 3, indexField := some 7 },
    { level := 30, path := ["Form", "Parties", "Lines"], repeatability := some 3 }] }

private def marked : String := "FieldFilled($Rows/N For \"keep\")"
private def ordinary : String := "Sum(Rows*/N Having " ++ marked ++ " And FieldFilled(Rows/N)) == 9"
private def parallelBody : String := "Sum(Rows*/N Having FieldFilled($Parties/N) And " ++ marked ++ " And FieldFilled(Rows/N)) == 9"
private def parallelOwner : String := "Sum(Parties/Lines*/Qty Having " ++ marked ++ " And FieldFilled(Parties/Lines/Qty)) == 9"

private def result (condition : String) (row : Bool := true) : String × String :=
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let report {α : Type} : Lowering α → String
    | .ok _ => "admitted"
    | .error refusal => refusal.detail
  (report (checkRule dm .english {
    group := ["Form"], name := "Selected", errorCode := "SELECTED", errorEntityRelPath := if row then "../Rows/RowOut" else "../Error"
    condition := (if row then "FieldFilled(Rows/RowOut) And " else "FieldFilled(Error) And ") ++ condition, severity := "ERROR" }),
   report (lowerComputation model .english {
    group := ["Form"], name := "Selected", targetRelPath := if row then "../Rows/RowOut" else "../Out", commonPrecondition := some condition
    alternatives := [{ precondition := none, operation := "9" }], errorCodesToSuppress := [] }))

example : model.validate.isOk = true := by native_decide

example : result ordinary == ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED") ∧
    result (ordinary.replace marked "FieldFilled(Rows/N)") == ("admitted", "admitted") ∧
    result ("RepetitionNotUnique(Rows/N) And " ++ ordinary) ==
      ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED") ∧
    result (parallelOwner.replace "Parties/Lines*" "Parties*/Lines*") ==
      ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED") := by native_decide

example : result parallelBody == ("MVK_PARALLEL_ITERATION_NOT_ALLOWED", "MVK_PARALLEL_ITERATION_NOT_ALLOWED") ∧
    result parallelOwner == ("MVK_PARALLEL_ITERATION_FOR_FILTERED_ENTITY_NOT_ALLOWED", "MVK_PARALLEL_ITERATION_FOR_FILTERED_ENTITY_NOT_ALLOWED") ∧
    result ("RepetitionNotUnique(Rows/N) And FieldFilled(Parties/N) And " ++ ordinary) ==
      ("MVK_PARALLEL_ITERATION_NOT_ALLOWED", "MVK_PARALLEL_ITERATION_NOT_ALLOWED") ∧
    result ("RepetitionNotUnique(Rows/N) And " ++ parallelOwner) ==
      ("MVK_PARALLEL_ITERATION_NOT_ALLOWED", "MVK_PARALLEL_ITERATION_NOT_ALLOWED") := by native_decide

example : [parallelBody, parallelOwner].all (fun condition =>
    result (condition ++ " And FieldFilled(Missing)") == ("MVK_INVALID_ENTITY", "MVK_INVALID_ENTITY")) = true := by native_decide

example : [parallelBody, parallelBody.replace "FieldFilled($Parties/N)" "GroupFilled($Parties)",
    parallelBody.replace "FieldFilled($Parties/N)" "FieldValueIncludedInValueList($Parties/Tag, \"keep\")",
    parallelBody.replace "FieldFilled($Parties/N)" "AtLeastOneFieldFilled($Parties/N)",
    parallelBody.replace "FieldFilled($Parties/N)" "[$Parties/Tag] PatternMatched \"[0-9]+\""].all
    (fun condition => result condition == ("MVK_PARALLEL_ITERATION_NOT_ALLOWED", "MVK_PARALLEL_ITERATION_NOT_ALLOWED") &&
      result (condition.replace marked "FieldFilled(Rows/N)") ==
        ("MVK_PARALLEL_ITERATION_NOT_ALLOWED", "MVK_PARALLEL_ITERATION_NOT_ALLOWED")) = true := by native_decide

example : result (parallelOwner.replace marked "FieldFilled(Parties/Lines/Qty)") ==
    ("MVK_PARALLEL_ITERATION_FOR_FILTERED_ENTITY_NOT_ALLOWED", "MVK_PARALLEL_ITERATION_FOR_FILTERED_ENTITY_NOT_ALLOWED") := by native_decide

private def computationResult (common own operation : String) : String :=
  match lowerComputation model .english {
    group := ["Form"], name := "Selected", targetRelPath := "../Rows/RowOut", commonPrecondition := some common
    alternatives := [{ precondition := some own, operation }], errorCodesToSuppress := [] } with
  | .ok _ => "admitted"
  | .error refusal => refusal.detail

example : computationResult ("RepetitionNotUnique(Rows/N) And " ++ ordinary) "FieldFilled(Parties/N)" "9" ==
    "MVK_PARALLEL_ITERATION_NOT_ALLOWED" ∧
    computationResult ordinary "RepetitionNotUnique(Rows/N) And FieldFilled(Parties/N)" "9" ==
      "MVK_PARALLEL_ITERATION_NOT_ALLOWED" ∧
    computationResult parallelOwner "FieldFilled(Rows/N)" "[Expected] - 1" == "MVK_NO_NUMBER_FOR_CALC" := by native_decide

private def plain : String := ordinary.replace marked "FieldFilled(Rows/N)"

example : result (plain ++ " And Length(Raw) > 2") ==
    ("MVK_INVALID_LENGTH_OF_RAW_TYPE", "MVK_INVALID_LENGTH_OF_RAW_TYPE") ∧
    result (plain.replace "FieldFilled(Rows/N)" "Length(Raw) > 2 And FieldFilled(Rows/N)") ==
      ("MVK_INVALID_LENGTH_OF_RAW_TYPE", "MVK_INVALID_LENGTH_OF_RAW_TYPE") ∧
    result (plain ++ " And Length(Expected) > 2") == ("admitted", "admitted") := by native_decide

example : result (ordinary ++ " And Length(Raw) > 2") ==
    ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED") ∧
    result (parallelOwner ++ " And Length(Raw) > 2") ==
      ("MVK_PARALLEL_ITERATION_FOR_FILTERED_ENTITY_NOT_ALLOWED", "MVK_PARALLEL_ITERATION_FOR_FILTERED_ENTITY_NOT_ALLOWED") ∧
    result (plain ++ " And Length(Raw) > 2 And FieldFilled(Missing)") ==
      ("MVK_INVALID_ENTITY", "MVK_INVALID_ENTITY") := by native_decide

example : computationResult plain "Length(Raw) > 2" "9" == "MVK_INVALID_LENGTH_OF_RAW_TYPE" ∧
    computationResult plain "FieldFilled(Rows/N)" "Length(Raw)" == "MVK_INVALID_LENGTH_OF_RAW_TYPE" ∧
    computationResult ordinary "Length(Raw) > 2" "9" == "MVK_SEMANTIC_INDEX_NOT_ALLOWED" ∧
    computationResult plain "Length(Raw) > 2" "[Expected] - 1" == "MVK_NO_NUMBER_FOR_CALC" := by native_decide

private def repeated : String := "RepetitionNotUnique(Rows/N) And RepetitionNotUnique(Rows/Tag) And "

example : result (repeated ++ plain) ==
    ("MVK_INVALID_COMBINATION_OF_REPETITON_NOT_UNIQUE", "MVK_INVALID_COMBINATION_OF_REPETITON_NOT_UNIQUE") ∧
    result (repeated ++ plain ++ " And Length(Raw) > 2") ==
      ("MVK_INVALID_COMBINATION_OF_REPETITON_NOT_UNIQUE", "MVK_INVALID_COMBINATION_OF_REPETITON_NOT_UNIQUE") := by native_decide

example : result (repeated ++ ordinary) == ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED") ∧
    result (repeated ++ parallelOwner) == ("MVK_PARALLEL_ITERATION_NOT_ALLOWED", "MVK_PARALLEL_ITERATION_NOT_ALLOWED") ∧
    result (repeated ++ plain ++ " And FieldFilled(Missing)") == ("MVK_INVALID_ENTITY", "MVK_INVALID_ENTITY") := by native_decide

example : computationResult ("RepetitionNotUnique(Rows/N) And " ++ plain) "RepetitionNotUnique(Rows/Tag)" "9" ==
    "MVK_INVALID_COMBINATION_OF_REPETITON_NOT_UNIQUE" ∧
    computationResult ("RepetitionNotUnique(Rows/N) And " ++ plain) "RepetitionNotUnique(Rows/Tag)" "[Expected] - 1" ==
      "MVK_NO_NUMBER_FOR_CALC" := by native_decide

private def staticAdmission (condition : String) : Bool :=
  match parseText .english condition with
  | .error _ => false
  | .ok text => (checkOrderedAdmission model ["Form"] ["Form", "Rows"] text.body).isOk

example : staticAdmission ("RepetitionNotUnique(Rows/N) And " ++ plain) = true := by native_decide

example : result plain false == ("admitted", "admitted") ∧
    result (plain ++ " And Length(Raw) > 2") false ==
      ("MVK_INVALID_LENGTH_OF_RAW_TYPE", "MVK_INVALID_LENGTH_OF_RAW_TYPE") ∧
    result (ordinary ++ " And Length(Raw) > 2") false ==
      ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED") := by native_decide

private def bareRuleResult (condition : String) (row : Bool := false) : String :=
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  match checkRule dm .english {
    group := ["Form"], name := "Selected", errorCode := "SELECTED", errorEntityRelPath := if row then "../Rows/RowOut" else "../Error"
    condition, severity := "ERROR" } with
  | .ok _ => "admitted"
  | .error refusal => refusal.detail

example : bareRuleResult plain == "MVK_ERROR_FIELD_NOT_REFERENCED A12Kernel.FlatRuleAssemblyError.errorFieldNotReferenced 1" ∧
    bareRuleResult (plain ++ " And Length(Raw) > 2") == "MVK_INVALID_LENGTH_OF_RAW_TYPE" ∧
    bareRuleResult ordinary == "MVK_SEMANTIC_INDEX_NOT_ALLOWED" := by native_decide

private def negative : String :=
  "FieldNotFilled(Rows/RowOut) And NoFieldFilled(Rows*/N Having FieldFilled(Rows/N))"

example : bareRuleResult negative true == "MVK_NEG_CONDITION_IN_ITERATION A12Kernel.FlatRuleAssemblyError.negativeConditionInIteration 10" ∧
    bareRuleResult (negative.replace "FieldNotFilled(Rows/RowOut)" "FieldFilled(Rows/RowOut)") true == "admitted" ∧
    bareRuleResult (negative.replace "FieldFilled(Rows/N)" (marked ++ " And FieldFilled(Rows/N)")) true ==
      "MVK_SEMANTIC_INDEX_NOT_ALLOWED" ∧
    bareRuleResult (negative.replace "FieldFilled(Rows/N)" "FieldFilled(Rows/N) And Length(Raw) > 2") true ==
      "MVK_INVALID_LENGTH_OF_RAW_TYPE" := by native_decide

private def filterResult (body : String) (row : Bool) : String × String :=
  result ("Sum(Rows*/N Having " ++ body ++ ") == 9") row

example : [false, true].all (fun row =>
    filterResult "CurrentRepetition(Rows) == [Rows/N For \"keep\"]" row ==
      ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED") &&
    filterResult "CurrentRepetition(Rows) == [Rows/N]" row == ("admitted", "admitted")) = true ∧
    result ("CurrentRepetition(Rows) == 1 And " ++ plain) == ("admitted", "admitted") := by native_decide

example : [false, true].all (fun row =>
    [("RoundUpValue(Missing,15) > 0", "MVK_INVALID_ENTITY"),
     ("RoundUpValue(Rows/Tag,15) > 0", "MVK_NO_NUMBER"),
     ("RoundUpValue(Rows/N,15) > 0", "MVK_INVALID_DIGIT_FOR_ROUNDING"),
     ("RoundUpValue(Raw,15) > 0", "MVK_NO_NUMBER"),
     ("Abs(1) + [Missing] > 0", "MVK_NO_CONST"),
     ("Abs(\"bad\") + [Missing] > 0", "MVK_NO_CONST"),
     ("RoundUp(1,0) + [Missing] > 0", "MVK_NO_CONST"),
     ("RoundUp(1,15) > 0", "MVK_NO_CONST"),
     ("RoundUp([Rows/Tag],15) > 0", "MVK_NO_NUMBER"),
     ("RoundUp([Rows/Tag],0) > 0", "MVK_NO_NUMBER")].all fun (body, diagnostic) =>
      filterResult body row == (diagnostic, diagnostic)) = true := by native_decide

example : [false, true].all (fun row =>
    ["Abs([Rows/N]) > 0", "RoundUp([Rows/N],0) > 0", "RoundUpValue(Rows/N,0) > 0"].all fun body =>
      filterResult body row == ("admitted", "admitted")) = true := by native_decide

example : [false, true].all (fun row =>
    ["BaseYear == BaseYear", "BaseYear < {BaseYear}", "Abs(BaseYear) == BaseYear"].all fun comparison =>
      filterResult (marked ++ " And FieldFilled(Rows/N) And " ++ comparison) row ==
        ("MVK_INCONSISTENT_TYPES_COMPARED", "MVK_INCONSISTENT_TYPES_COMPARED")) = true ∧
    filterResult (marked ++ " And FieldFilled(Rows/N) And BaseYear == BaseYear + 0") true ==
      ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED") := by native_decide

example : bareRuleResult ("FieldFilled(Error) And CustomCondition 'True' And " ++ plain) == "admitted" ∧
    bareRuleResult ("FieldFilled(Error) And " ++ plain ++ " And CustomCondition 'True'") == "admitted" := by native_decide

example : [false, true].all (fun row => ["Min", "Max"].all fun op =>
    [(s!"{op}(1,2) + [Missing] > 0", "MVK_TOO_MANY_CONST_FOR_CALC_OP"),
     (s!"{op}(\"a\",\"b\") > 0", "MVK_TOO_MANY_CONST_FOR_CALC_OP"),
     (s!"{op}(True,1) > 0", "MVK_TOO_MANY_CONST_FOR_CALC_OP"),
     (s!"{op}(1,2,[Missing]) > 0", "MVK_INVALID_ENTITY")].all fun (body, diagnostic) =>
      filterResult body row == (diagnostic, diagnostic)) = true ∧
    [false, true].all (fun row => ["Min", "Max"].all fun op =>
      filterResult s!"{op}([Rows/N],1) > 0" row == ("admitted", "admitted")) = true := by native_decide

example : [false, true].all (fun row =>
    [("Abs(Today) + [Missing] > 0", "MVK_NO_CONST"),
     ("RoundUp({Now},15) > 0", "MVK_NO_CONST"),
     ("Min(Today,Today) + [Missing] > 0", "MVK_TOO_MANY_CONST_FOR_CALC_OP"),
     ("Max({Now},Now) > 0", "MVK_TOO_MANY_CONST_FOR_CALC_OP")].all fun (body, diagnostic) =>
      filterResult body row == (diagnostic, diagnostic)) = true := by native_decide

example : [false, true].all (fun row =>
    ["BaseYear DiffersWithToleranceRange1 BaseYear",
     "Abs(BaseYear) DiffersWithToleranceRange2 BaseYear"].all fun comparison =>
      filterResult (marked ++ " And FieldFilled(Rows/N) And " ++ comparison) row ==
        ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED")) = true := by native_decide


private def referenceModel : FlatModel := {
  fields := [
    { id := 11, name := "Output", groupPath := ["Probe", "Rows"], repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 1, name := "SkuText", groupPath := ["Probe"], policy := { kind := .string } },
    { id := 2, name := "Amount", groupPath := ["Probe"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 3, name := "RowVal", groupPath := ["Probe", "Rows"], repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 4, name := "RowText", groupPath := ["Probe", "Rows"], repeatableScope := [10], policy := { kind := .string } },
    { id := 5, name := "RowFlag", groupPath := ["Probe", "Rows"], repeatableScope := [10], policy := { kind := .boolean } },
    { id := 6, name := "RowDate", groupPath := ["Probe", "Rows"], repeatableScope := [10], policy := { kind := .temporal .date .fullDate }, temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
    { id := 7, name := "RowSpan", groupPath := ["Probe", "Rows"], repeatableScope := [10], policy := { kind := .dateRange }, dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } },
    { id := 8, name := "RowScaled", groupPath := ["Probe", "Rows"], repeatableScope := [10], policy := { kind := .number { scale := 2, signed := true } } },
    { id := 9, name := "Leaf", groupPath := ["Probe", "Rows", "Sub"], repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 10, name := "R", groupPath := ["Probe", "Rows", "Ranges"], repeatableScope := [10], policy := { kind := .dateRange }, dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } }]
  repeatableGroups := [{ level := 10, path := ["Probe", "Rows"], repeatability := some 3 }] }

private def referenceResult (errorField condition : String)
    (target : String := "../Rows/RowScaled") : String × String :=
  let dm : DmModel := { flat := referenceModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let report {α : Type} : Lowering α → String
    | .ok _ => "admitted"
    | .error refusal =>
        if refusal.detail.startsWith "MVK_ERROR_FIELD_NOT_REFERENCED A12Kernel.FlatRuleAssemblyError.errorFieldNotReferenced" then "MVK_ERROR_FIELD_NOT_REFERENCED"
        else if refusal.detail.startsWith "MVK_NEG_CONDITION_IN_ITERATION A12Kernel.FlatRuleAssemblyError.negativeConditionInIteration" then "MVK_NEG_CONDITION_IN_ITERATION"
        else if refusal.detail.startsWith "MVK_ERROR_FIELD_AND_ITERATION_INVALID A12Kernel.FlatRuleAssemblyError.errorFieldIterationInvalid" then "MVK_ERROR_FIELD_AND_ITERATION_INVALID"
        else refusal.detail
  (report (checkRule dm .english {
    group := ["Probe"], name := "Selected", errorCode := "SELECTED", errorEntityRelPath := "../" ++ errorField,
    condition, severity := "ERROR" }),
   report (lowerComputation referenceModel .english {
    group := ["Probe"], name := "Selected", targetRelPath := target, commonPrecondition := some condition,
    alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] }))

private def referenceCases : List (String × String × String × String × String) := [
  ("Sumplain", "Rows/RowVal", "Sum(Rows*/RowVal) > 0", "admitted", "admitted"),
  ("Sumpayload", "Rows/RowVal", "Sum(Rows*/RowVal Having (CurrentRepetition(Rows) > 0)) > 0", "admitted", "admitted"),
  ("Sumcandidate", "Rows/Sub/Leaf", "Sum(Rows*/RowVal Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) > 0", "MVK_ERROR_FIELD_NOT_REFERENCED", "admitted"),
  ("Summarked", "Rows/Sub/Leaf", "Sum(Rows*/RowVal Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) > 0", "admitted", "admitted"),
  ("Sumguard", "Rows/Sub/Leaf", "FieldFilled(Rows/Sub/Leaf) And Sum(Rows*/RowVal Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) > 0", "admitted", "admitted"),
  ("Sumunrelated", "SkuText", "Sum(Rows*/RowVal Having (CurrentRepetition(Rows) > 0)) > 0", "MVK_ERROR_FIELD_NOT_REFERENCED", "admitted"),
  ("Sumallmarked", "Rows/Sub/Leaf", "Sum(Rows*/RowVal Having (FieldFilled($Rows/Sub/Leaf))) > 0", "MVK_NO_ITERATION_FOR_WILDCARD", "MVK_NO_ITERATION_FOR_WILDCARD"),
  ("Maxplain", "Rows/RowVal", "MaxValue(Rows*/RowVal) > 0", "admitted", "admitted"),
  ("Maxpayload", "Rows/RowVal", "MaxValue(Rows*/RowVal Having (CurrentRepetition(Rows) > 0)) > 0", "admitted", "admitted"),
  ("Maxcandidate", "Rows/Sub/Leaf", "MaxValue(Rows*/RowVal Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) > 0", "MVK_ERROR_FIELD_NOT_REFERENCED", "admitted"),
  ("Maxmarked", "Rows/Sub/Leaf", "MaxValue(Rows*/RowVal Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) > 0", "admitted", "admitted"),
  ("Maxguard", "Rows/Sub/Leaf", "FieldFilled(Rows/Sub/Leaf) And MaxValue(Rows*/RowVal Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) > 0", "admitted", "admitted"),
  ("Maxunrelated", "SkuText", "MaxValue(Rows*/RowVal Having (CurrentRepetition(Rows) > 0)) > 0", "MVK_ERROR_FIELD_NOT_REFERENCED", "admitted"),
  ("Maxallmarked", "Rows/Sub/Leaf", "MaxValue(Rows*/RowVal Having (FieldFilled($Rows/Sub/Leaf))) > 0", "MVK_NO_ITERATION_FOR_WILDCARD", "MVK_NO_ITERATION_FOR_WILDCARD"),
  ("Filledplain", "Rows/RowVal", "NumberOfFilledFields(Rows*/RowVal) > 0", "admitted", "admitted"),
  ("Filledpayload", "Rows/RowVal", "NumberOfFilledFields(Rows*/RowVal Having (CurrentRepetition(Rows) > 0)) > 0", "admitted", "admitted"),
  ("Filledcandidate", "Rows/Sub/Leaf", "NumberOfFilledFields(Rows*/RowVal Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) > 0", "MVK_ERROR_FIELD_NOT_REFERENCED", "admitted"),
  ("Filledmarked", "Rows/Sub/Leaf", "NumberOfFilledFields(Rows*/RowVal Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) > 0", "admitted", "admitted"),
  ("Filledguard", "Rows/Sub/Leaf", "FieldFilled(Rows/Sub/Leaf) And NumberOfFilledFields(Rows*/RowVal Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) > 0", "admitted", "admitted"),
  ("Filledunrelated", "SkuText", "NumberOfFilledFields(Rows*/RowVal Having (CurrentRepetition(Rows) > 0)) > 0", "MVK_ERROR_FIELD_NOT_REFERENCED", "admitted"),
  ("Filledallmarked", "Rows/Sub/Leaf", "NumberOfFilledFields(Rows*/RowVal Having (FieldFilled($Rows/Sub/Leaf))) > 0", "MVK_NO_ITERATION_FOR_WILDCARD", "MVK_NO_ITERATION_FOR_WILDCARD"),
  ("Distinctplain", "Rows/RowText", "NumberOfDifferentValues(Rows*/RowText) > 0", "admitted", "admitted"),
  ("Distinctpayload", "Rows/RowText", "NumberOfDifferentValues(Rows*/RowText Having (CurrentRepetition(Rows) > 0)) > 0", "admitted", "admitted"),
  ("Distinctcandidate", "Rows/Sub/Leaf", "NumberOfDifferentValues(Rows*/RowText Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) > 0", "MVK_ERROR_FIELD_NOT_REFERENCED", "admitted"),
  ("Distinctmarked", "Rows/Sub/Leaf", "NumberOfDifferentValues(Rows*/RowText Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) > 0", "admitted", "admitted"),
  ("Distinctguard", "Rows/Sub/Leaf", "FieldFilled(Rows/Sub/Leaf) And NumberOfDifferentValues(Rows*/RowText Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) > 0", "admitted", "admitted"),
  ("Distinctunrelated", "SkuText", "NumberOfDifferentValues(Rows*/RowText Having (CurrentRepetition(Rows) > 0)) > 0", "MVK_ERROR_FIELD_NOT_REFERENCED", "admitted"),
  ("Distinctallmarked", "Rows/Sub/Leaf", "NumberOfDifferentValues(Rows*/RowText Having (FieldFilled($Rows/Sub/Leaf))) > 0", "MVK_NO_ITERATION_FOR_WILDCARD", "MVK_NO_ITERATION_FOR_WILDCARD"),
  ("NumberCountplain", "Rows/RowVal", "NumberOfValueInFields(1 In Rows*/RowVal) > 0", "admitted", "admitted"),
  ("NumberCountpayload", "Rows/RowVal", "NumberOfValueInFields(1 In Rows*/RowVal Having (CurrentRepetition(Rows) > 0)) > 0", "admitted", "admitted"),
  ("NumberCountcandidate", "Rows/Sub/Leaf", "NumberOfValueInFields(1 In Rows*/RowVal Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) > 0", "MVK_ERROR_FIELD_NOT_REFERENCED", "admitted"),
  ("NumberCountmarked", "Rows/Sub/Leaf", "NumberOfValueInFields(1 In Rows*/RowVal Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) > 0", "admitted", "admitted"),
  ("NumberCountguard", "Rows/Sub/Leaf", "FieldFilled(Rows/Sub/Leaf) And NumberOfValueInFields(1 In Rows*/RowVal Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) > 0", "admitted", "admitted"),
  ("NumberCountunrelated", "SkuText", "NumberOfValueInFields(1 In Rows*/RowVal Having (CurrentRepetition(Rows) > 0)) > 0", "MVK_ERROR_FIELD_NOT_REFERENCED", "admitted"),
  ("NumberCountallmarked", "Rows/Sub/Leaf", "NumberOfValueInFields(1 In Rows*/RowVal Having (FieldFilled($Rows/Sub/Leaf))) > 0", "MVK_NO_ITERATION_FOR_WILDCARD", "MVK_NO_ITERATION_FOR_WILDCARD"),
  ("TokenCountplain", "Rows/RowText", "NumberOfValueInFields(\"a\" In Rows*/RowText) > 0", "admitted", "admitted"),
  ("TokenCountpayload", "Rows/RowText", "NumberOfValueInFields(\"a\" In Rows*/RowText Having (CurrentRepetition(Rows) > 0)) > 0", "admitted", "admitted"),
  ("TokenCountcandidate", "Rows/Sub/Leaf", "NumberOfValueInFields(\"a\" In Rows*/RowText Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) > 0", "MVK_ERROR_FIELD_NOT_REFERENCED", "admitted"),
  ("TokenCountmarked", "Rows/Sub/Leaf", "NumberOfValueInFields(\"a\" In Rows*/RowText Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) > 0", "admitted", "admitted"),
  ("TokenCountguard", "Rows/Sub/Leaf", "FieldFilled(Rows/Sub/Leaf) And NumberOfValueInFields(\"a\" In Rows*/RowText Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) > 0", "admitted", "admitted"),
  ("TokenCountunrelated", "SkuText", "NumberOfValueInFields(\"a\" In Rows*/RowText Having (CurrentRepetition(Rows) > 0)) > 0", "MVK_ERROR_FIELD_NOT_REFERENCED", "admitted"),
  ("TokenCountallmarked", "Rows/Sub/Leaf", "NumberOfValueInFields(\"a\" In Rows*/RowText Having (FieldFilled($Rows/Sub/Leaf))) > 0", "MVK_NO_ITERATION_FOR_WILDCARD", "MVK_NO_ITERATION_FOR_WILDCARD"),
  ("BoolCountplain", "Rows/RowFlag", "NumberOfValueInFields(True In Rows*/RowFlag) > 0", "admitted", "admitted"),
  ("BoolCountpayload", "Rows/RowFlag", "NumberOfValueInFields(True In Rows*/RowFlag Having (CurrentRepetition(Rows) > 0)) > 0", "admitted", "admitted"),
  ("BoolCountcandidate", "Rows/Sub/Leaf", "NumberOfValueInFields(True In Rows*/RowFlag Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) > 0", "MVK_ERROR_FIELD_NOT_REFERENCED", "admitted"),
  ("BoolCountmarked", "Rows/Sub/Leaf", "NumberOfValueInFields(True In Rows*/RowFlag Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) > 0", "admitted", "admitted"),
  ("BoolCountguard", "Rows/Sub/Leaf", "FieldFilled(Rows/Sub/Leaf) And NumberOfValueInFields(True In Rows*/RowFlag Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) > 0", "admitted", "admitted"),
  ("BoolCountunrelated", "SkuText", "NumberOfValueInFields(True In Rows*/RowFlag Having (CurrentRepetition(Rows) > 0)) > 0", "MVK_ERROR_FIELD_NOT_REFERENCED", "admitted"),
  ("BoolCountallmarked", "Rows/Sub/Leaf", "NumberOfValueInFields(True In Rows*/RowFlag Having (FieldFilled($Rows/Sub/Leaf))) > 0", "MVK_NO_ITERATION_FOR_WILDCARD", "MVK_NO_ITERATION_FOR_WILDCARD"),
  ("Firstplain", "Rows/RowText", "FirstFilledValue(Rows*/RowText) == \"a\"", "admitted", "admitted"),
  ("Firstpayload", "Rows/RowText", "FirstFilledValue(Rows*/RowText Having (CurrentRepetition(Rows) > 0)) == \"a\"", "admitted", "admitted"),
  ("Firstcandidate", "Rows/Sub/Leaf", "FirstFilledValue(Rows*/RowText Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) == \"a\"", "MVK_ERROR_FIELD_NOT_REFERENCED", "admitted"),
  ("Firstmarked", "Rows/Sub/Leaf", "FirstFilledValue(Rows*/RowText Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) == \"a\"", "admitted", "admitted"),
  ("Firstguard", "Rows/Sub/Leaf", "FieldFilled(Rows/Sub/Leaf) And FirstFilledValue(Rows*/RowText Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) == \"a\"", "admitted", "admitted"),
  ("Firstunrelated", "SkuText", "FirstFilledValue(Rows*/RowText Having (CurrentRepetition(Rows) > 0)) == \"a\"", "MVK_ERROR_FIELD_NOT_REFERENCED", "admitted"),
  ("Firstallmarked", "Rows/Sub/Leaf", "FirstFilledValue(Rows*/RowText Having (FieldFilled($Rows/Sub/Leaf))) == \"a\"", "MVK_NO_ITERATION_FOR_WILDCARD", "MVK_NO_ITERATION_FOR_WILDCARD"),
  ("DateMinplain", "Rows/RowDate", "MinValue(Rows*/RowDate) == \"01.01.2024\"", "admitted", "admitted"),
  ("DateMinpayload", "Rows/RowDate", "MinValue(Rows*/RowDate Having (CurrentRepetition(Rows) > 0)) == \"01.01.2024\"", "admitted", "admitted"),
  ("DateMincandidate", "Rows/Sub/Leaf", "MinValue(Rows*/RowDate Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) == \"01.01.2024\"", "MVK_ERROR_FIELD_NOT_REFERENCED", "admitted"),
  ("DateMinmarked", "Rows/Sub/Leaf", "MinValue(Rows*/RowDate Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) == \"01.01.2024\"", "admitted", "admitted"),
  ("DateMinguard", "Rows/Sub/Leaf", "FieldFilled(Rows/Sub/Leaf) And MinValue(Rows*/RowDate Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) == \"01.01.2024\"", "admitted", "admitted"),
  ("DateMinunrelated", "SkuText", "MinValue(Rows*/RowDate Having (CurrentRepetition(Rows) > 0)) == \"01.01.2024\"", "MVK_ERROR_FIELD_NOT_REFERENCED", "admitted"),
  ("DateMinallmarked", "Rows/Sub/Leaf", "MinValue(Rows*/RowDate Having (FieldFilled($Rows/Sub/Leaf))) == \"01.01.2024\"", "MVK_NO_ITERATION_FOR_WILDCARD", "MVK_NO_ITERATION_FOR_WILDCARD"),
  ("Rangeplain", "Rows/RowSpan", "DateRangesOverlap(Rows*/RowSpan)", "admitted", "admitted"),
  ("Rangepayload", "Rows/RowSpan", "DateRangesOverlap(Rows*/RowSpan Having (CurrentRepetition(Rows) > 0))", "admitted", "admitted"),
  ("Rangecandidate", "Rows/Sub/Leaf", "DateRangesOverlap(Rows*/RowSpan Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "MVK_ERROR_FIELD_NOT_REFERENCED", "admitted"),
  ("Rangemarked", "Rows/Sub/Leaf", "DateRangesOverlap(Rows*/RowSpan Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "admitted", "admitted"),
  ("Rangeguard", "Rows/Sub/Leaf", "FieldFilled(Rows/Sub/Leaf) And DateRangesOverlap(Rows*/RowSpan Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "admitted", "admitted"),
  ("Rangeunrelated", "SkuText", "DateRangesOverlap(Rows*/RowSpan Having (CurrentRepetition(Rows) > 0))", "MVK_ERROR_FIELD_NOT_REFERENCED", "admitted"),
  ("Rangeallmarked", "Rows/Sub/Leaf", "DateRangesOverlap(Rows*/RowSpan Having (FieldFilled($Rows/Sub/Leaf)))", "MVK_NO_ITERATION_FOR_WILDCARD", "MVK_NO_ITERATION_FOR_WILDCARD"),
  ("GroupRangeplain", "Rows/Ranges/R", "DateRangesOverlap(Rows*/Ranges)", "MVK_NO_GROUPS_ALLOWED", "MVK_NO_GROUPS_ALLOWED"),
  ("GroupRangepayload", "Rows/Ranges/R", "DateRangesOverlap(Rows*/Ranges Having (CurrentRepetition(Rows) > 0))", "MVK_NO_GROUPS_ALLOWED", "MVK_NO_GROUPS_ALLOWED"),
  ("GroupRangecandidate", "Rows/Sub/Leaf", "DateRangesOverlap(Rows*/Ranges Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "MVK_NO_GROUPS_ALLOWED", "MVK_NO_GROUPS_ALLOWED"),
  ("GroupRangemarked", "Rows/Sub/Leaf", "DateRangesOverlap(Rows*/Ranges Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "MVK_NO_GROUPS_ALLOWED", "MVK_NO_GROUPS_ALLOWED"),
  ("GroupRangeguard", "Rows/Sub/Leaf", "FieldFilled(Rows/Sub/Leaf) And DateRangesOverlap(Rows*/Ranges Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "MVK_NO_GROUPS_ALLOWED", "MVK_NO_GROUPS_ALLOWED"),
  ("GroupRangeunrelated", "SkuText", "DateRangesOverlap(Rows*/Ranges Having (CurrentRepetition(Rows) > 0))", "MVK_NO_GROUPS_ALLOWED", "MVK_NO_GROUPS_ALLOWED"),
  ("GroupRangeallmarked", "Rows/Sub/Leaf", "DateRangesOverlap(Rows*/Ranges Having (FieldFilled($Rows/Sub/Leaf)))", "MVK_NO_GROUPS_ALLOWED", "MVK_NO_GROUPS_ALLOWED"),
  ("GroupSumplain", "Rows/Sub/Leaf", "Sum(Rows*/Sub) > 0", "admitted", "admitted"),
  ("GroupSumpayload", "Rows/Sub/Leaf", "Sum(Rows*/Sub Having (CurrentRepetition(Rows) > 0)) > 0", "MVK_NO_GROUPS_ALLOWED", "MVK_NO_GROUPS_ALLOWED"),
  ("GroupSumcandidate", "Rows/Sub/Leaf", "Sum(Rows*/Sub Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) > 0", "MVK_NO_GROUPS_ALLOWED", "MVK_NO_GROUPS_ALLOWED"),
  ("GroupSummarked", "Rows/Sub/Leaf", "Sum(Rows*/Sub Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) > 0", "MVK_NO_GROUPS_ALLOWED", "MVK_NO_GROUPS_ALLOWED"),
  ("GroupSumguard", "Rows/Sub/Leaf", "FieldFilled(Rows/Sub/Leaf) And Sum(Rows*/Sub Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0)) > 0", "MVK_NO_GROUPS_ALLOWED", "MVK_NO_GROUPS_ALLOWED"),
  ("GroupSumunrelated", "SkuText", "Sum(Rows*/Sub Having (CurrentRepetition(Rows) > 0)) > 0", "MVK_NO_GROUPS_ALLOWED", "MVK_NO_GROUPS_ALLOWED"),
  ("GroupSumallmarked", "Rows/Sub/Leaf", "Sum(Rows*/Sub Having (FieldFilled($Rows/Sub/Leaf))) > 0", "MVK_NO_GROUPS_ALLOWED", "MVK_NO_GROUPS_ALLOWED"),
  ("Fillplain", "Rows/RowText", "AtLeastOneFieldFilled(Rows*/RowText)", "admitted", "admitted"),
  ("Fillpayload", "Rows/RowText", "AtLeastOneFieldFilled(Rows*/RowText Having (CurrentRepetition(Rows) > 0))", "admitted", "admitted"),
  ("Fillcandidate", "Rows/Sub/Leaf", "AtLeastOneFieldFilled(Rows*/RowText Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "MVK_ERROR_FIELD_NOT_REFERENCED", "admitted"),
  ("Fillmarked", "Rows/Sub/Leaf", "AtLeastOneFieldFilled(Rows*/RowText Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "MVK_NEG_CONDITION_IN_ITERATION", "admitted"),
  ("Fillguard", "Rows/Sub/Leaf", "FieldFilled(Rows/Sub/Leaf) And AtLeastOneFieldFilled(Rows*/RowText Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "admitted", "admitted"),
  ("Fillunrelated", "SkuText", "AtLeastOneFieldFilled(Rows*/RowText Having (CurrentRepetition(Rows) > 0))", "MVK_ERROR_FIELD_NOT_REFERENCED", "admitted"),
  ("Fillallmarked", "Rows/Sub/Leaf", "AtLeastOneFieldFilled(Rows*/RowText Having (FieldFilled($Rows/Sub/Leaf)))", "MVK_NO_ITERATION_FOR_WILDCARD", "MVK_NO_ITERATION_FOR_WILDCARD"),
  ("Uniqueplain", "Rows/RowText", "FieldValuesNotUnique(Rows*/RowText)", "admitted", "admitted"),
  ("Uniquepayload", "Rows/RowText", "FieldValuesNotUnique(Rows*/RowText Having (CurrentRepetition(Rows) > 0))", "admitted", "admitted"),
  ("Uniquecandidate", "Rows/Sub/Leaf", "FieldValuesNotUnique(Rows*/RowText Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "MVK_ERROR_FIELD_NOT_REFERENCED", "admitted"),
  ("Uniquemarked", "Rows/Sub/Leaf", "FieldValuesNotUnique(Rows*/RowText Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "MVK_NEG_CONDITION_IN_ITERATION", "admitted"),
  ("Uniqueguard", "Rows/Sub/Leaf", "FieldFilled(Rows/Sub/Leaf) And FieldValuesNotUnique(Rows*/RowText Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "admitted", "admitted"),
  ("Uniqueunrelated", "SkuText", "FieldValuesNotUnique(Rows*/RowText Having (CurrentRepetition(Rows) > 0))", "MVK_ERROR_FIELD_NOT_REFERENCED", "admitted"),
  ("Uniqueallmarked", "Rows/Sub/Leaf", "FieldValuesNotUnique(Rows*/RowText Having (FieldFilled($Rows/Sub/Leaf)))", "MVK_NO_ITERATION_FOR_WILDCARD", "MVK_NO_ITERATION_FOR_WILDCARD"),
  ("PluralGroup", "Rows/Ranges/R", "AtLeastOneDateRangeOverlaps(Rows/RowSpan In Rows*/Ranges)", "MVK_ERROR_FIELD_AND_ITERATION_INVALID", "admitted"),
  ("PluralGroupGuard", "Rows/Ranges/R", "FieldFilled(Rows/Ranges/R) And AtLeastOneDateRangeOverlaps(Rows/RowSpan In Rows*/Ranges)", "admitted", "admitted"),
  ("OutsideCandidate0", "Rows/RowVal", "Sum(Rows*/RowVal Having ([ Amount ] > 0 And CurrentRepetition(Rows) > 0)) > 0", "admitted", "admitted"),
  ("OutsideCandidate1", "Rows/RowVal", "Sum(Rows*/RowVal Having (CurrentRepetition(Rows) > 0 And [ Amount ] > 0)) > 0", "admitted", "admitted"),
  ("OutsideCaptured0", "Rows/RowVal", "Sum(Rows*/RowVal Having ([ $Amount ] > 0 And CurrentRepetition(Rows) > 0)) > 0", "admitted", "admitted"),
  ("OutsideCaptured1", "Rows/RowVal", "Sum(Rows*/RowVal Having (CurrentRepetition(Rows) > 0 And [ $Amount ] > 0)) > 0", "admitted", "admitted"),
  ("DayMinplain", "Rows/RowDate", "DayFromDate(MinValue(Rows*/RowDate)) > 0", "MVK_UNEXPECTED_TOKEN", "MVK_UNEXPECTED_TOKEN"),
  ("DayMinpayload", "Rows/RowDate", "DayFromDate(MinValue(Rows*/RowDate Having (CurrentRepetition(Rows) > 0))) > 0", "MVK_UNEXPECTED_TOKEN", "MVK_UNEXPECTED_TOKEN"),
  ("DayMincandidate", "Rows/Sub/Leaf", "DayFromDate(MinValue(Rows*/RowDate Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))) > 0", "MVK_UNEXPECTED_TOKEN", "MVK_UNEXPECTED_TOKEN"),
  ("DayMinmarked", "Rows/Sub/Leaf", "DayFromDate(MinValue(Rows*/RowDate Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))) > 0", "MVK_UNEXPECTED_TOKEN", "MVK_UNEXPECTED_TOKEN"),
  ("DayMinguard", "Rows/Sub/Leaf", "FieldFilled(Rows/Sub/Leaf) And DayFromDate(MinValue(Rows*/RowDate Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))) > 0", "MVK_UNEXPECTED_TOKEN", "MVK_UNEXPECTED_TOKEN"),
  ("DayMinunrelated", "SkuText", "DayFromDate(MinValue(Rows*/RowDate Having (CurrentRepetition(Rows) > 0))) > 0", "MVK_UNEXPECTED_TOKEN", "MVK_UNEXPECTED_TOKEN"),
  ("DayMinallmarked", "Rows/Sub/Leaf", "DayFromDate(MinValue(Rows*/RowDate Having (FieldFilled($Rows/Sub/Leaf)))) > 0", "MVK_UNEXPECTED_TOKEN", "MVK_UNEXPECTED_TOKEN")]

private def referenceMismatches : List (String × String × String) :=
  referenceCases.filterMap fun (name, errorField, condition, validation, computation) =>
    let actual := referenceResult errorField condition
    if actual == (validation, computation) then none else some (name, actual.1, actual.2)

example : referenceModel.validate.isOk = true := by native_decide
example : referenceMismatches = [] := by native_decide

private def iterationGuardCases : List (String × String × String × String) := [
  ("AllFieldsFilledrowPair", "Rows/RowVal", "AllFieldsFilled(Rows/RowVal, Rows/RowScaled)", "admitted"),
  ("AllFieldsFilledmixedPair", "Rows/RowVal", "AllFieldsFilled(Rows/RowVal, Amount)", "admitted"),
  ("AllFieldsFilledstarAndRow", "Rows/RowScaled", "AllFieldsFilled(Rows*/RowVal, Rows/RowScaled)", "admitted"),
  ("AllFieldsFilledmarked", "Rows/Sub/Leaf", "AllFieldsFilled(Rows*/RowVal Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "admitted"),
  ("AllFieldsFilledguard", "Rows/Sub/Leaf", "FieldFilled(Rows/Sub/Leaf) And AllFieldsFilled(Rows*/RowVal Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "admitted"),
  ("AllFieldsFilledcandidate", "Rows/RowVal", "AllFieldsFilled(Rows*/RowVal Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "admitted"),
  ("AllFieldsFilledplain", "Rows/RowVal", "AllFieldsFilled(Rows*/RowVal)", "admitted"),
  ("NoFieldFilledrowPair", "Rows/RowVal", "NoFieldFilled(Rows/RowVal, Rows/RowScaled)", "MVK_NEG_CONDITION_IN_ITERATION"),
  ("NoFieldFilledmixedPair", "Rows/RowVal", "NoFieldFilled(Rows/RowVal, Amount)", "MVK_NEG_CONDITION_IN_ITERATION"),
  ("NoFieldFilledstarAndRow", "Rows/RowScaled", "NoFieldFilled(Rows*/RowVal, Rows/RowScaled)", "MVK_NEG_CONDITION_IN_ITERATION"),
  ("NoFieldFilledmarked", "Rows/Sub/Leaf", "NoFieldFilled(Rows*/RowVal Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "admitted"),
  ("NoFieldFilledguard", "Rows/Sub/Leaf", "FieldFilled(Rows/Sub/Leaf) And NoFieldFilled(Rows*/RowVal Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "admitted"),
  ("NoFieldFilledcandidate", "Rows/RowVal", "NoFieldFilled(Rows*/RowVal Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "admitted"),
  ("NoFieldFilledplain", "Rows/RowVal", "NoFieldFilled(Rows*/RowVal)", "admitted"),
  ("AtLeastOneFieldFilledrowPair", "Rows/RowVal", "AtLeastOneFieldFilled(Rows/RowVal, Rows/RowScaled)", "admitted"),
  ("AtLeastOneFieldFilledmixedPair", "Rows/RowVal", "AtLeastOneFieldFilled(Rows/RowVal, Amount)", "MVK_NEG_CONDITION_IN_ITERATION"),
  ("AtLeastOneFieldFilledstarAndRow", "Rows/RowScaled", "AtLeastOneFieldFilled(Rows*/RowVal, Rows/RowScaled)", "MVK_NEG_CONDITION_IN_ITERATION"),
  ("AtLeastOneFieldFilledmarked", "Rows/Sub/Leaf", "AtLeastOneFieldFilled(Rows*/RowVal Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "MVK_NEG_CONDITION_IN_ITERATION"),
  ("AtLeastOneFieldFilledguard", "Rows/Sub/Leaf", "FieldFilled(Rows/Sub/Leaf) And AtLeastOneFieldFilled(Rows*/RowVal Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "admitted"),
  ("AtLeastOneFieldFilledcandidate", "Rows/RowVal", "AtLeastOneFieldFilled(Rows*/RowVal Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "admitted"),
  ("AtLeastOneFieldFilledplain", "Rows/RowVal", "AtLeastOneFieldFilled(Rows*/RowVal)", "admitted"),
  ("MoreThanOneFieldFilledrowPair", "Rows/RowVal", "MoreThanOneFieldFilled(Rows/RowVal, Rows/RowScaled)", "admitted"),
  ("MoreThanOneFieldFilledmixedPair", "Rows/RowVal", "MoreThanOneFieldFilled(Rows/RowVal, Amount)", "admitted"),
  ("MoreThanOneFieldFilledstarAndRow", "Rows/RowScaled", "MoreThanOneFieldFilled(Rows*/RowVal, Rows/RowScaled)", "MVK_NEG_CONDITION_IN_ITERATION"),
  ("MoreThanOneFieldFilledmarked", "Rows/Sub/Leaf", "MoreThanOneFieldFilled(Rows*/RowVal Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "MVK_NEG_CONDITION_IN_ITERATION"),
  ("MoreThanOneFieldFilledguard", "Rows/Sub/Leaf", "FieldFilled(Rows/Sub/Leaf) And MoreThanOneFieldFilled(Rows*/RowVal Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "admitted"),
  ("MoreThanOneFieldFilledcandidate", "Rows/RowVal", "MoreThanOneFieldFilled(Rows*/RowVal Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "admitted"),
  ("MoreThanOneFieldFilledplain", "Rows/RowVal", "MoreThanOneFieldFilled(Rows*/RowVal)", "admitted"),
  ("NotAllFieldsFilledrowPair", "Rows/RowVal", "NotAllFieldsFilled(Rows/RowVal, Rows/RowScaled)", "MVK_NEG_CONDITION_IN_ITERATION"),
  ("NotAllFieldsFilledmixedPair", "Rows/RowVal", "NotAllFieldsFilled(Rows/RowVal, Amount)", "MVK_NEG_CONDITION_IN_ITERATION"),
  ("NotAllFieldsFilledstarAndRow", "Rows/RowScaled", "NotAllFieldsFilled(Rows*/RowVal, Rows/RowScaled)", "MVK_NEG_CONDITION_IN_ITERATION"),
  ("NotAllFieldsFilledmarked", "Rows/Sub/Leaf", "NotAllFieldsFilled(Rows*/RowVal Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "admitted"),
  ("NotAllFieldsFilledguard", "Rows/Sub/Leaf", "FieldFilled(Rows/Sub/Leaf) And NotAllFieldsFilled(Rows*/RowVal Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "admitted"),
  ("NotAllFieldsFilledcandidate", "Rows/RowVal", "NotAllFieldsFilled(Rows*/RowVal Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "admitted"),
  ("NotAllFieldsFilledplain", "Rows/RowVal", "NotAllFieldsFilled(Rows*/RowVal)", "admitted"),
  ("NotExactlyOneFieldFilledrowPair", "Rows/RowVal", "NotExactlyOneFieldFilled(Rows/RowVal, Rows/RowScaled)", "MVK_NEG_CONDITION_IN_ITERATION"),
  ("NotExactlyOneFieldFilledmixedPair", "Rows/RowVal", "NotExactlyOneFieldFilled(Rows/RowVal, Amount)", "MVK_NEG_CONDITION_IN_ITERATION"),
  ("NotExactlyOneFieldFilledstarAndRow", "Rows/RowScaled", "NotExactlyOneFieldFilled(Rows*/RowVal, Rows/RowScaled)", "MVK_NEG_CONDITION_IN_ITERATION"),
  ("NotExactlyOneFieldFilledmarked", "Rows/Sub/Leaf", "NotExactlyOneFieldFilled(Rows*/RowVal Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "admitted"),
  ("NotExactlyOneFieldFilledguard", "Rows/Sub/Leaf", "FieldFilled(Rows/Sub/Leaf) And NotExactlyOneFieldFilled(Rows*/RowVal Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "admitted"),
  ("NotExactlyOneFieldFilledcandidate", "Rows/RowVal", "NotExactlyOneFieldFilled(Rows*/RowVal Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "admitted"),
  ("NotExactlyOneFieldFilledplain", "Rows/RowVal", "NotExactlyOneFieldFilled(Rows*/RowVal)", "admitted"),
  ("FieldsNotCollectivelyFilledrowPair", "Rows/RowVal", "FieldsNotCollectivelyFilled(Rows/RowVal, Rows/RowScaled)", "admitted"),
  ("FieldsNotCollectivelyFilledmixedPair", "Rows/RowVal", "FieldsNotCollectivelyFilled(Rows/RowVal, Amount)", "MVK_NEG_CONDITION_IN_ITERATION"),
  ("FieldsNotCollectivelyFilledstarAndRow", "Rows/RowScaled", "FieldsNotCollectivelyFilled(Rows*/RowVal, Rows/RowScaled)", "MVK_NEG_CONDITION_IN_ITERATION"),
  ("FieldsNotCollectivelyFilledmarked", "Rows/Sub/Leaf", "FieldsNotCollectivelyFilled(Rows*/RowVal Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "MVK_NEG_CONDITION_IN_ITERATION"),
  ("FieldsNotCollectivelyFilledguard", "Rows/Sub/Leaf", "FieldFilled(Rows/Sub/Leaf) And FieldsNotCollectivelyFilled(Rows*/RowVal Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "admitted"),
  ("FieldsNotCollectivelyFilledcandidate", "Rows/RowVal", "FieldsNotCollectivelyFilled(Rows*/RowVal Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "admitted"),
  ("FieldsNotCollectivelyFilledplain", "Rows/RowVal", "FieldsNotCollectivelyFilled(Rows*/RowVal)", "admitted"),
  ("FieldValuesNotUniquerowPair", "Rows/RowVal", "FieldValuesNotUnique(Rows/RowVal, Rows/RowScaled)", "admitted"),
  ("FieldValuesNotUniquemixedPair", "Rows/RowVal", "FieldValuesNotUnique(Rows/RowVal, Amount)", "admitted"),
  ("FieldValuesNotUniquestarAndRow", "Rows/RowScaled", "FieldValuesNotUnique(Rows*/RowVal, Rows/RowScaled)", "MVK_NEG_CONDITION_IN_ITERATION"),
  ("FieldValuesNotUniquemarked", "Rows/Sub/Leaf", "FieldValuesNotUnique(Rows*/RowVal Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "MVK_NEG_CONDITION_IN_ITERATION"),
  ("FieldValuesNotUniqueguard", "Rows/Sub/Leaf", "FieldFilled(Rows/Sub/Leaf) And FieldValuesNotUnique(Rows*/RowVal Having (FieldFilled($Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "admitted"),
  ("FieldValuesNotUniquecandidate", "Rows/RowVal", "FieldValuesNotUnique(Rows*/RowVal Having (FieldFilled(Rows/Sub/Leaf) And CurrentRepetition(Rows) > 0))", "admitted"),
  ("FieldValuesNotUniqueplain", "Rows/RowVal", "FieldValuesNotUnique(Rows*/RowVal)", "admitted")]

private def iterationGuardMismatches : List (String × String × String) :=
  iterationGuardCases.filterMap fun (name, errorField, condition, expected) =>
    let actual := referenceResult errorField condition "../Rows/Output"
    if actual == (expected, "admitted") then none else some (name, actual.1, actual.2)

example : iterationGuardMismatches = [] := by native_decide

private def referenceScopeCases : List (String × String × String × String) := [
  ("Sumplain", "Rows/RowVal", "Sum(Rows*/RowVal) > 0", "admitted"),
  ("Sumsibling", "Rows/RowVal", "FieldFilled(Rows/RowScaled) And Sum(Rows*/RowVal) > 0", "MVK_ERROR_FIELD_AND_ITERATION_INVALID"),
  ("Sumown", "Rows/RowVal", "FieldFilled(Rows/RowVal) And Sum(Rows*/RowVal) > 0", "admitted"),
  ("Filledplain", "Rows/RowVal", "NumberOfFilledFields(Rows*/RowVal) > 0", "admitted"),
  ("Filledsibling", "Rows/RowVal", "FieldFilled(Rows/RowScaled) And NumberOfFilledFields(Rows*/RowVal) > 0", "MVK_ERROR_FIELD_AND_ITERATION_INVALID"),
  ("Filledown", "Rows/RowVal", "FieldFilled(Rows/RowVal) And NumberOfFilledFields(Rows*/RowVal) > 0", "admitted"),
  ("Distinctplain", "Rows/RowText", "NumberOfDifferentValues(Rows*/RowText) > 0", "admitted"),
  ("Distinctsibling", "Rows/RowText", "FieldFilled(Rows/RowScaled) And NumberOfDifferentValues(Rows*/RowText) > 0", "MVK_ERROR_FIELD_AND_ITERATION_INVALID"),
  ("Distinctown", "Rows/RowText", "FieldFilled(Rows/RowText) And NumberOfDifferentValues(Rows*/RowText) > 0", "admitted"),
  ("Firstplain", "Rows/RowText", "FirstFilledValue(Rows*/RowText) == \"a\"", "admitted"),
  ("Firstsibling", "Rows/RowText", "FieldFilled(Rows/RowScaled) And FirstFilledValue(Rows*/RowText) == \"a\"", "MVK_ERROR_FIELD_AND_ITERATION_INVALID"),
  ("Firstown", "Rows/RowText", "FieldFilled(Rows/RowText) And FirstFilledValue(Rows*/RowText) == \"a\"", "admitted"),
  ("Dateplain", "Rows/RowDate", "MinValue(Rows*/RowDate) == \"01.01.2024\"", "admitted"),
  ("Datesibling", "Rows/RowDate", "FieldFilled(Rows/RowScaled) And MinValue(Rows*/RowDate) == \"01.01.2024\"", "MVK_ERROR_FIELD_AND_ITERATION_INVALID"),
  ("Dateown", "Rows/RowDate", "FieldFilled(Rows/RowDate) And MinValue(Rows*/RowDate) == \"01.01.2024\"", "admitted"),
  ("Fillplain", "Rows/RowText", "AtLeastOneFieldFilled(Rows*/RowText)", "admitted"),
  ("Fillsibling", "Rows/RowText", "FieldFilled(Rows/RowScaled) And AtLeastOneFieldFilled(Rows*/RowText)", "MVK_ERROR_FIELD_AND_ITERATION_INVALID"),
  ("Fillown", "Rows/RowText", "FieldFilled(Rows/RowText) And AtLeastOneFieldFilled(Rows*/RowText)", "admitted"),
  ("Uniqueplain", "Rows/RowText", "FieldValuesNotUnique(Rows*/RowText)", "admitted"),
  ("Uniquesibling", "Rows/RowText", "FieldFilled(Rows/RowScaled) And FieldValuesNotUnique(Rows*/RowText)", "MVK_ERROR_FIELD_AND_ITERATION_INVALID"),
  ("Uniqueown", "Rows/RowText", "FieldFilled(Rows/RowText) And FieldValuesNotUnique(Rows*/RowText)", "admitted"),
  ("Rangeplain", "Rows/RowSpan", "DateRangesOverlap(Rows*/RowSpan)", "admitted"),
  ("Rangesibling", "Rows/RowSpan", "FieldFilled(Rows/RowScaled) And DateRangesOverlap(Rows*/RowSpan)", "MVK_ERROR_FIELD_AND_ITERATION_INVALID"),
  ("Rangeown", "Rows/RowSpan", "FieldFilled(Rows/RowSpan) And DateRangesOverlap(Rows*/RowSpan)", "admitted"),
  ("GroupSumplain", "Rows/Sub/Leaf", "Sum(Rows*/Sub) > 0", "admitted"),
  ("GroupSumsibling", "Rows/Sub/Leaf", "FieldFilled(Rows/RowScaled) And Sum(Rows*/Sub) > 0", "MVK_ERROR_FIELD_AND_ITERATION_INVALID"),
  ("GroupSumown", "Rows/Sub/Leaf", "FieldFilled(Rows/Sub/Leaf) And Sum(Rows*/Sub) > 0", "admitted"),
  ("GroupRangeplain", "Rows/Ranges/R", "AtLeastOneDateRangeOverlaps(Rows/RowSpan In Rows*/Ranges)", "MVK_ERROR_FIELD_AND_ITERATION_INVALID"),
  ("GroupRangesibling", "Rows/Ranges/R", "FieldFilled(Rows/RowScaled) And AtLeastOneDateRangeOverlaps(Rows/RowSpan In Rows*/Ranges)", "MVK_ERROR_FIELD_AND_ITERATION_INVALID"),
  ("GroupRangeown", "Rows/Ranges/R", "FieldFilled(Rows/Ranges/R) And AtLeastOneDateRangeOverlaps(Rows/RowSpan In Rows*/Ranges)", "admitted")]

private def referenceScopeMismatches : List (String × String × String) :=
  referenceScopeCases.filterMap fun (name, errorField, condition, expected) =>
    let actual := referenceResult errorField condition "../Rows/Output"
    if actual == (expected, "admitted") then none else some (name, actual.1, actual.2)

example : referenceScopeMismatches = [] := by native_decide

private def markedGroupCases : List (String × String × String) := [
  ("Rows/RowVal", "FieldFilled(Rows/RowScaled) And Sum(Rows*/RowVal Having (GroupFilled($/Probe) And CurrentRepetition(Rows) > 0)) > 0", "MVK_ERROR_FIELD_AND_ITERATION_INVALID"),
  ("Rows/RowVal", "FieldFilled(Rows/RowVal) And Sum(Rows*/RowVal Having (GroupFilled($/Probe) And CurrentRepetition(Rows) > 0)) > 0", "admitted"),
  ("Rows/RowText", "FieldFilled(Rows/RowScaled) And FirstFilledValue(Rows*/RowText Having (GroupFilled($/Probe) And CurrentRepetition(Rows) > 0)) == \"a\"", "MVK_ERROR_FIELD_AND_ITERATION_INVALID"),
  ("Rows/RowText", "FieldFilled(Rows/RowText) And FirstFilledValue(Rows*/RowText Having (GroupFilled($/Probe) And CurrentRepetition(Rows) > 0)) == \"a\"", "admitted"),
  ("Rows/RowDate", "FieldFilled(Rows/RowScaled) And MinValue(Rows*/RowDate Having (GroupFilled($/Probe) And CurrentRepetition(Rows) > 0)) == \"01.01.2024\"", "MVK_ERROR_FIELD_AND_ITERATION_INVALID"),
  ("Rows/RowDate", "FieldFilled(Rows/RowDate) And MinValue(Rows*/RowDate Having (GroupFilled($/Probe) And CurrentRepetition(Rows) > 0)) == \"01.01.2024\"", "admitted"),
  ("Rows/RowSpan", "FieldFilled(Rows/RowScaled) And DateRangesOverlap(Rows*/RowSpan Having (GroupFilled($/Probe) And CurrentRepetition(Rows) > 0))", "MVK_ERROR_FIELD_AND_ITERATION_INVALID"),
  ("Rows/RowSpan", "FieldFilled(Rows/RowSpan) And DateRangesOverlap(Rows*/RowSpan Having (GroupFilled($/Probe) And CurrentRepetition(Rows) > 0))", "admitted")]

example : markedGroupCases.all (fun (field, condition, expected) =>
    (referenceResult field condition "../Rows/Output").1 == expected) = true := by native_decide

private def nestedReferenceModel : FlatModel := { referenceModel with
  fields := referenceModel.fields ++ [
    { id := 12, name := "N", groupPath := ["Probe", "Rows", "Deep"], repeatableScope := [10, 20],
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 13, name := "Other", groupPath := ["Probe", "Rows", "Deep"], repeatableScope := [10, 20],
      policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := referenceModel.repeatableGroups ++ [
    { level := 20, path := ["Probe", "Rows", "Deep"], repeatability := some 2 }] }

private def markedGroupResult (nested own : Bool) : String :=
  let fixture := if nested then nestedReferenceModel else referenceModel
  let error := if nested then "Rows/Deep/N" else "Rows/RowVal"
  let sibling := if nested then "Rows/Deep/Other" else "Rows/RowScaled"
  let selected := if nested then "Rows*/Deep*/N" else "Rows*/RowVal"
  let group := if nested then "$/Probe/Rows" else "$/Probe"
  let repetition := if nested then "Rows/Deep" else "Rows"
  let condition := "FieldFilled(" ++ (if own then error else sibling) ++ ") And Sum(" ++ selected ++
    " Having (GroupFilled(" ++ group ++ ") And CurrentRepetition(" ++ repetition ++ ") > 0)) > 0"
  let dm : DmModel := { flat := fixture, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let rule : DmRule := {
    group := ["Probe"], name := "MarkedGroup", errorCode := "GROUP"
    errorEntityRelPath := "../" ++ error, condition, severity := "ERROR" }
  match checkRule dm .english rule with
  | .ok _ => "admitted"
  | .error refusal => refusal.detail

example : nestedReferenceModel.validate.isOk = true ∧
    markedGroupResult false false = "MVK_ERROR_FIELD_AND_ITERATION_INVALID A12Kernel.FlatRuleAssemblyError.errorFieldIterationInvalid 3 10" ∧
    markedGroupResult true false = "MVK_ERROR_FIELD_AND_ITERATION_INVALID A12Kernel.FlatRuleAssemblyError.errorFieldIterationInvalid 12 20" ∧
    [false, true].all (fun nested => markedGroupResult nested true == "admitted") = true := by native_decide

private def firstFieldComparisons : List String :=
  [false, true].flatMap fun filtered =>
    let first := "FirstFilledValue(Rows*/RowText" ++
      (if filtered then " Having [Rows/RowVal] > 0" else "") ++ ")"
    ["==", "!="].flatMap fun op =>
      [first ++ " " ++ op ++ " [SkuText]", "[SkuText] " ++ op ++ " " ++ first]

example : firstFieldComparisons.all (fun condition =>
    referenceResult "Rows/RowText" condition "../Rows/Output" ==
      ("admitted", "admitted")) = true := by native_decide

example : [false, true].all (fun filtered =>
    let first := "FirstFilledValue(Rows*/RowText" ++
      (if filtered then " Having [Rows/RowVal] > 0" else "") ++ ")"
    let refused := referenceResult "Rows/RowText" (first ++ " == SkuText") "../Rows/Output"
    refused.1 != "admitted" && refused.2 != "admitted") = true := by native_decide

private def runCaller (condition : String) (range : Bool := false)
    (rows : Array Lean.Json := #[]) (expected : String := "a") : Option (Verdict × List String) :=
  let fixture := if range then { HavingFixture.model with
      fields := HavingFixture.model.fields.map fun field =>
        if field.id == 2 || field.id == 3 then { field with
          policy := { kind := .dateRange }
          dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } }
        else field } else HavingFixture.model
  HavingFixture.runModel fixture "" false expected "" ""
    (operationOverride := some "9")
    (ruleCondition := some ("FieldFilled(Error) And " ++ condition))
    (computationPrecondition := some condition) (rowsOverride := some rows)
    (extra := [("Out", .str "99")]) (zoneRules := ModelZone.concreteRules)

private def callerRow (value gate : String) : Lean.Json :=
  Lean.Json.mkObj [("Tag", .str value), ("N", .str gate)]

example : runCaller "FirstFilledValue(Rows*/Tag Having [Rows/N] > 0) == \"a\""
      false #[callerRow "drop" "0", callerRow "a" "1", callerRow "b" "1"] =
      some (.fired .omission, ["value 9"]) ∧
    runCaller "FirstFilledValue(Rows*/Tag Having [Rows/N] > 0) == \"a\""
      false #[callerRow "a" "0", callerRow "b" "1"] =
      some (.notFired, ["cleared"]) := by native_decide

example : [false, true].all (fun reverse =>
    let selected := "FirstFilledValue(Rows*/Tag Having [Rows/N] > 0)"
    let condition := if reverse then "[Expected] == " ++ selected else selected ++ " == [Expected]"
    runCaller condition false #[callerRow "drop" "0", callerRow "a" "1", callerRow "b" "1"] ==
      some (.fired .omission, ["value 9"]) &&
    runCaller condition false #[callerRow "a" "0", callerRow "b" "1"] ==
      some (.notFired, ["cleared"])) = true := by native_decide

example : runCaller "DateRangesOverlap(Rows*/Tag Having [Rows/N] > 0)"
      true #[callerRow "bad" "0", callerRow "2024-01-01/2024-01-10" "1",
        callerRow "2024-01-10/2024-01-20" "1"] "2024-03-01/2024-03-10" =
      some (.fired .omission, ["value 9"]) ∧
    runCaller "DateRangesOverlap(Rows*/Tag Having [Rows/N] > 0)"
      true #[callerRow "2024-01-01/2024-01-10" "1", callerRow "2024-03-01/2024-03-10" "1"]
        "2024-01-10/2024-01-20" = some (.notFired, ["cleared"]) ∧
    runCaller "AtLeastOneDateRangeOverlaps(Expected In Rows*/Tag Having [Rows/N] > 0)"
      true #[callerRow "bad" "0", callerRow "2024-01-10/2024-01-20" "1"]
        "2024-01-01/2024-01-10" = some (.fired .omission, ["value 9"]) ∧
    runCaller "AtLeastOneDateRangeOverlaps(Expected In Rows*/Tag Having [Rows/N] > 0)"
      true #[callerRow "2024-03-01/2024-03-10" "1"]
        "2024-01-01/2024-01-10" = some (.notFired, ["cleared"]) := by native_decide

end A12Kernel.Dm.HavingGlobalAdmissionLocks
