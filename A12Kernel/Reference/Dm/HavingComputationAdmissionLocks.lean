import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingComputationAdmissionLocks
open A12Kernel

private def targets : List (FlatFieldDecl × String) := [
  ({ id := 6, name := "Target", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } }, "9"),
  ({ id := 6, name := "Target", groupPath := ["Form"], policy := { kind := .string } }, "\"a\""),
  ({ id := 6, name := "Target", groupPath := ["Form"], policy := { kind := .boolean } }, "True"),
  ({ id := 6, name := "Target", groupPath := ["Form"], policy := { kind := .confirm } }, "True"),
  ({ id := 6, name := "Target", groupPath := ["Form"], policy := { kind := .enumeration },
      enumeration := some { storedTokens := ["a", "b"] } }, "\"a\""),
  ({ id := 6, name := "Target", groupPath := ["Form"], policy := { kind := .temporal .date .fullDate },
      temporalTargetPolicy := some { format := "yyyy-MM-dd" } }, "Today"),
  ({ id := 6, name := "Target", groupPath := ["Form"], policy := { kind := .temporal .time .time },
      temporalTargetPolicy := some { format := "HH:mm:ss" } }, "\"12:30:00\""),
  ({ id := 6, name := "Target", groupPath := ["Form"], policy := { kind := .temporal .dateTime .now },
      temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } }, "Now"),
  ({ id := 6, name := "Target", groupPath := ["Form"], policy := { kind := .dateRange },
      dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } }, "DateRange(Start,Finish)")]

private def model (target : FlatFieldDecl) (row : Bool) : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields ++ [
    { target with groupPath := if row then ["Form", "Rows"] else ["Form"], repeatableScope := if row then [10] else [] },
    { id := 7, name := "Span", groupPath := ["Form"], policy := { kind := .dateRange },
      dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } },
    { id := 8, name := "Start", groupPath := ["Form"], policy := { kind := .temporal .date .fullDate },
      temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
    { id := 9, name := "Finish", groupPath := ["Form"], policy := { kind := .temporal .date .fullDate },
      temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
    { id := 10, name := "Choice", groupPath := ["Form"], policy := { kind := .enumeration }, enumeration := some { storedTokens := ["a", "b"] } },
    { id := 11, name := "OtherChoice", groupPath := ["Form"], policy := { kind := .enumeration }, enumeration := some { storedTokens := ["a", "b"] } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 3 }] }

private def guard (indexed : Bool) : String :=
  "Sum(Rows*/N Having FieldFilled(" ++ (if indexed then "$Rows/N For \"keep\"" else "Rows/N") ++
    ") And FieldFilled(Rows/N)) == 9"

private def result (target : FlatFieldDecl) (row : Bool) (common : Option String)
    (alternatives : List DmAlternative) (suppressed : List String := []) (roundingMode : String := "Exact") : String :=
  match lowerComputation (model target row) .english {
    group := ["Form"], name := "Selected", targetRelPath := if row then "../Rows/Target" else "../Target"
    commonPrecondition := common, alternatives, errorCodesToSuppress := suppressed, roundingMode } with
  | .ok _ => "admitted"
  | .error refusal => refusal.detail

example : [false, true].all (fun row => targets.all fun (target, _) => (model target row).validate.isOk) = true := by native_decide

private def operationFor (target : FlatFieldDecl) (row : Bool) (operation : String) : String :=
  if !row && target.policy.kind == .enumeration then "FirstFilledValue(Choice,OtherChoice)" else operation

example : [false, true].all (fun row => targets.all fun (target, operation) =>
    let operation := operationFor target row operation
    result target row (some (guard false)) [{ precondition := none, operation }] == "admitted" &&
    result target row none [{ precondition := some (guard false), operation }] == "admitted") = true := by native_decide

example : [false, true].all (fun row => targets.all fun (target, operation) =>
    let operation := operationFor target row operation
    let expected := "MVK_SEMANTIC_INDEX_NOT_ALLOWED"
    result target row (some (guard true)) [{ precondition := none, operation }] == expected &&
    result target row none [{ precondition := some (guard true), operation }] == expected) = true := by native_decide

private def numberTarget : FlatFieldDecl := {
  id := 6, name := "Target", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } }

example : [false, true].all (fun row =>
    result numberTarget row (some (guard true)) [{ precondition := none, operation := "[Missing]" }] == "MVK_INVALID_ENTITY" &&
    result numberTarget row none [
      { precondition := some (guard true), operation := "[Expected] - 1" }] == "MVK_NO_NUMBER_FOR_CALC" &&
    result numberTarget row none [
      { precondition := some "FieldFilled(Error)", operation := "[Expected] - 1" },
      { precondition := some (guard true), operation := "9" }] == "MVK_NO_NUMBER_FOR_CALC" &&
    result numberTarget row (some "FieldFilled(Missing)") [
      { precondition := some (guard true), operation := "9" }] == "MVK_INVALID_ENTITY") = true := by native_decide

example : [false, true].all (fun row =>
    result numberTarget row (some (guard true)) [{ precondition := none, operation := "1.25" }] == "MVK_INVALID_COMPARE_DEC_PLACES" &&
    result numberTarget row (some (guard true)) [{ precondition := none, operation := "1.25" }]
      ["MVK_INVALID_COMPARE_DEC_PLACES"] == "MVK_SEMANTIC_INDEX_NOT_ALLOWED" &&
    result numberTarget row none [
      { precondition := some (guard true), operation := "1.25" },
      { precondition := some "FieldFilled(Missing)", operation := "9" }] == "MVK_INVALID_COMPARE_DEC_PLACES") = true := by native_decide

private def partialTarget : FlatFieldDecl := {
  id := 6, name := "Target", groupPath := ["Form"], policy := { kind := .temporal .date .fullDate }
  temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .dayOptional } }

example : [false, true].all (fun row => (model partialTarget row).validate.isOk &&
    result partialTarget row (some (guard true)) [{ precondition := none, operation := "[Missing]" }] == "MVK_INVALID_DATE_TYPE" &&
    result partialTarget row (some (guard true)) [{ precondition := none, operation := "[" }] == "MVK_INVALID_DATE_TYPE" &&
    result numberTarget row none [
      { precondition := some (guard true), operation := "[Expected] - 1" },
      { precondition := some "FieldFilled(", operation := "9" }] == "MVK_NO_NUMBER_FOR_CALC") = true := by native_decide

example : [false, true].all (fun row =>
    let nestedScale := (guard true).replace "And FieldFilled(Rows/N)" "And [Rows/N] == 1.25"
    result numberTarget row (some nestedScale) [{ precondition := none, operation := "9" }] == "MVK_INVALID_COMPARE_DEC_PLACES" &&
    result numberTarget row (some nestedScale) [{ precondition := none, operation := "9" }]
      ["MVK_INVALID_COMPARE_DEC_PLACES"] == "MVK_SEMANTIC_INDEX_NOT_ALLOWED") = true := by native_decide

private def stringTarget : FlatFieldDecl := { id := 6, name := "Target", groupPath := ["Form"], policy := { kind := .string } }

example : [false, true].all (fun row =>
    let selected := "FirstFilledValue(Rows*/Tag Having FieldFilled(Rows/Tag))"
    let indexed := "FirstFilledValue(Rows*/Tag Having FieldFilled($Rows/N For \"keep\") And FieldFilled(Rows/Tag))"
    result stringTarget row none [{ precondition := none, operation := selected }] == "admitted" &&
    result stringTarget row none [{ precondition := none, operation := indexed }] == "MVK_SEMANTIC_INDEX_NOT_ALLOWED") = true := by native_decide

example : [false, true].all (fun row =>
    result numberTarget row (some (guard false)) [{ precondition := none, operation := "9" }] [] "RoundUp" == "MVK_ERROR_WRONG_ROUNDING_MODE" &&
    result numberTarget row (some (guard true)) [{ precondition := none, operation := "9" }] [] "RoundUp" == "MVK_SEMANTIC_INDEX_NOT_ALLOWED" &&
    result numberTarget row (some (guard true)) [{ precondition := none, operation := "[Expected] - 1" }] [] "RoundUp" == "MVK_NO_NUMBER_FOR_CALC") = true := by native_decide

example : [false, true].all (fun row =>
    result numberTarget row none [{ precondition := none, operation := "9" }]
      ["UNKNOWN_WARNING"] "RoundUp" == "MVK_ERROR_WRONG_ROUNDING_MODE" &&
    result numberTarget row none [{ precondition := none, operation := "9" }]
      ["UNKNOWN_WARNING"] "Exact" == "UNKNOWN_WARNING" &&
    result numberTarget row (some (guard false)) [{ precondition := none, operation := "9" }]
      ["UNKNOWN_WARNING"] "RoundUp" == "UNKNOWN_WARNING") = true := by native_decide

example : [false, true].all (fun row =>
    let common := some "FieldFilled(Missing)"
    let operations := [{ precondition := none, operation := "9" }]
    let own := [{ precondition := some "FieldFilled(Missing)", operation := "9" }]
    result numberTarget row common operations != "admitted" &&
    result numberTarget row common operations ["UNKNOWN_WARNING"] == result numberTarget row common operations &&
    result numberTarget row none own ["UNKNOWN_WARNING"] == result numberTarget row none own &&
    result numberTarget row (some "FieldFilled(Error)") [{ precondition := none, operation := "[" }]
      ["UNKNOWN_WARNING"] == SyntaxErrorClass.expectedTokenNotFound.code &&
    result numberTarget row (some "FieldFilled(Error)") [{ precondition := none, operation := "9" }]
      ["UNKNOWN_WARNING"] == "UNKNOWN_WARNING") = true := by native_decide

end A12Kernel.Dm.HavingComputationAdmissionLocks
