import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingValueCountAdmissionLocks
open A12Kernel

private def model : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields ++ [
    { id := 6, name := "RowOut", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 7, name := "Flag", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .boolean } },
    { id := 8, name := "Yes", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .confirm } },
    { id := 9, name := "Choice", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .enumeration },
      enumeration := some { storedTokens := ["a", "b"], categories := [{ name := "Label", tokens := ["cat", "other"] }] } },
    { id := 10, name := "OtherChoice", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .enumeration },
      enumeration := some { storedTokens := ["a", "c"], categories := [{ name := "Label", tokens := ["cat", "extra"] }] } },
    { id := 11, name := "Raw", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string },
      stringValueMode := .raw, stringPolicy := { lineBreaksPermitted := true } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 3 }] }

private def filter (indexed : Bool) : String :=
  (if indexed then "FieldFilled($Rows/N For \"keep\") And " else "") ++ "FieldFilled(Rows/N)"

private def result (expected field : String) (indexed row : Bool) : String × String :=
  HavingFixture.readerResults ("NumberOfValueInFields(" ++ expected ++ " In Rows*/" ++ field ++
    " Having " ++ filter indexed ++ ")") model row

example : model.validate.isOk = true := by native_decide

example : [false, true].all (fun row =>
    [("1", "N"), ("\"keep\"", "Tag"), ("\"a\"", "Choice"),
      ("True", "Flag"), ("False", "Flag"), ("True", "Yes")].all fun (literal, field) =>
      result literal field false row == ("admitted", "admitted") &&
      result literal field true row == ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED")) = true := by native_decide

example : [false, true].all (fun row => [false, true].all fun indexed =>
    [("False", "Yes", "MVK_NO_TYPEYESNO"), ("True", "Tag", "MVK_NO_TYPE_YES_OR_YESNO"),
      ("1", "Tag", "MVK_NO_NUMBER"), ("\"keep\"", "N", "MVK_NO_STRING_OR_ENUM"),
      ("\"missing\"", "Choice", "MVK_INVALID_STRING_CONSTANT_FOR_ENUMERATION"),
      ("\"a\"", "Choice->Label", "MVK_INVALID_STRING_CONSTANT_FOR_ENUMERATION_CATEGORY"),
      ("\"keep\"", "Raw", "MVK_INVALID_RAW_TYPE"),
      ("\"01.03.2024\"", "Tag", "MVK_NO_DATE_CONSTANT")].all fun (literal, field, diagnostic) =>
        result literal field indexed row == (diagnostic, diagnostic)) = true := by native_decide

private def bodyResult (body : String) (row : Bool) (indexed : Bool := true) : String × String :=
  HavingFixture.readerResults ("Sum(Rows*/N Having " ++ filter indexed ++ " And " ++ body ++ ")") model row

example : [false, true].all (fun row =>
    [("NumberOfValueInFields(1 In Rows/Tag,Rows/Tag) > 0", "MVK_DUPLICATE_PARAM1"),
      ("NumberOfValueInFields(False In Rows/Yes) > 0", "MVK_PARAMSIZE_INVALIDN"),
      ("NumberOfValueInFields(\"missing\" In Rows/Tag,Rows/Choice) > 0", "MVK_INVALID_STRING_CONSTANT_FOR_ENUMERATION"),
      ("NumberOfValueInFields(\"b\" In Rows/Choice,Rows/OtherChoice) > 0", "MVK_INVALID_STRING_CONSTANT_FOR_ENUMERATION"),
      ("NumberOfValueInFields(1 In Missing) > 0", "MVK_INVALID_ENTITY")].all fun (body, diagnostic) =>
        bodyResult body row == (diagnostic, diagnostic)) = true := by native_decide

example : [false, true].all (fun row =>
    ["NumberOfValueInFields(\"a\" In Rows/Tag,Rows/Choice) > 0",
     "NumberOfValueInFields(\"a\" In Rows/Choice,Rows/OtherChoice) > 0"].all fun body =>
       bodyResult body row == ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED")) = true := by native_decide

example : [false, true].all (fun row =>
    let body := "NumberOfValueInFields(\"cat\" In Rows/Choice->Label,Rows/OtherChoice->Label) > 0"
    bodyResult body row false == ("admitted", "admitted") &&
    bodyResult body row true == ("MVK_SEMANTIC_INDEX_NOT_ALLOWED", "MVK_SEMANTIC_INDEX_NOT_ALLOWED")) = true := by native_decide

private def projectedStarAdmission (literal : String) : String :=
  match parseText .english ("NumberOfValueInFields(\"" ++ literal ++
      "\" In Rows*/Choice->Label Having FieldFilled(Rows/N)) > 0") with
  | .error _ => "syntax"
  | .ok parsed => match checkRawConditionBeforeGlobals model ["Form"] ["Form"] parsed.body false with
    | .error refusal => refusal.detail
    | .ok facts => facts.refusal?.map (·.kernelCode) |>.getD "admitted"

example : projectedStarAdmission "cat" == "admitted" ∧
    projectedStarAdmission "a" == "MVK_INVALID_STRING_CONSTANT_FOR_ENUMERATION_CATEGORY" := by native_decide

end A12Kernel.Dm.HavingValueCountAdmissionLocks
