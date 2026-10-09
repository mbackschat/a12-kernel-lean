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
  | .ok text => (checkLateFilterIndex model ["Form"] ["Form", "Rows"] text.body).isOk

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

example : bareRuleResult plain == "A12Kernel.FlatRuleAssemblyError.errorFieldNotReferenced 1" ∧
    bareRuleResult (plain ++ " And Length(Raw) > 2") == "MVK_INVALID_LENGTH_OF_RAW_TYPE" ∧
    bareRuleResult ordinary == "MVK_SEMANTIC_INDEX_NOT_ALLOWED" := by native_decide

private def negative : String :=
  "FieldNotFilled(Rows/RowOut) And NoFieldFilled(Rows*/N Having FieldFilled(Rows/N))"

example : bareRuleResult negative true == "A12Kernel.FlatRuleAssemblyError.negativeConditionInIteration 10" ∧
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

end A12Kernel.Dm.HavingGlobalAdmissionLocks
