import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingScalarOperationLocks
open A12Kernel

private def model : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields ++ [
    { id := 6, name := "RowOut", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 7, name := "Text", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .string }, stringPatternSource := some "[0-9]+", stringPolicy := { maxLength := some 4 } },
    { id := 8, name := "Choice", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .enumeration }, enumeration := some {
        storedTokens := ["1.2", "3"], categories := [{ name := "Label", tokens := ["2.40", "5"] }] } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 3 }] }

private def result (body : String) (row : Bool) (fixture : FlatModel := model) : String × String :=
  HavingFixture.readerResults ("Sum(Rows*/N Having " ++ body ++ ")") fixture row
private def operations : List (String × String × String × Bool) := [
  ("Length", "Rows/Text", "", true), ("FieldValueAsNumber", "Rows/Text", "", true),
  ("RangeAsNumber", "Rows/Text", ", 1, 2", true), ("RangeAsString", "Rows/Text", ", 1, 2", false),
  ("FieldValueAsString", "Rows/N", "", false)]
private def comparison (number : Bool) : String := if number then " > 0" else " == \"x\""

example : model.validate.isOk = true ∧ [false, true].all (fun row => operations.all fun (op, field, rest, number) =>
    result (op ++ "(" ++ field ++ rest ++ ")" ++ comparison number) row == ("admitted", "admitted") &&
    result (op ++ "(" ++ field ++ " For \"keep\"" ++ rest ++ ")" ++ comparison number) row ==
      (KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode, KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode)) = true := by native_decide

example : [false, true].all (fun row =>
    let number := KernelStaticDiagnostic.noNumber.kernelCode
    let string := KernelStaticDiagnostic.noString.kernelCode
    let conversion := KernelStaticDiagnostic.noConvertInNumber.kernelCode
    let type := KernelStaticDiagnostic.invalidType.kernelCode
    result "Length(Rows/N For \"keep\") > 0" row == (string, string) &&
    result "FieldValueAsString(Rows/Text For \"keep\") == \"x\"" row == (number, number) &&
    result "FieldValueAsNumber(Rows/N For \"keep\") > 0" row == (conversion, conversion) &&
    result "RangeAsNumber(Rows/N For \"keep\", 1, 2) > 0" row == (type, type) &&
    result "RangeAsString(Rows/N For \"keep\", 1, 2) == \"x\"" row == (type, type)) = true := by native_decide

example : [false, true].all (fun row =>
    let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
    result "RangeAsNumber(Rows/N For \"keep\", 0, 1) > [Missing]" row == ("MVK_INVALID_INTERVAL", "MVK_INVALID_INTERVAL") &&
    result "RangeAsString(Missing, 0, 1) == \"x\"" row == (missing, missing) &&
    result "Length(Missing) > [Rows/N For \"keep\"]" row == (missing, missing) &&
    result "[Rows/Tag For \"keep\"] PatternMatched {RangeAsString(Missing, 1, 2) + \"x\"}" row == (missing, missing)) = true := by native_decide

private def rawModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 7 then
    { field with
      stringValueMode := .raw
      stringPatternSource := none
      stringPolicy := { lineBreaksPermitted := true } }
  else field }

example : rawModel.validate.isOk = true ∧ [false, true].all (fun row =>
    let indexed := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    let raw := KernelStaticDiagnostic.rawTypeOperandInvalid.kernelCode
    let conversion := KernelStaticDiagnostic.noConvertInNumber.kernelCode
    let number := KernelStaticDiagnostic.noNumber.kernelCode
    let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
    result "Length(Rows/Text For \"keep\") > 0" row rawModel == (indexed, indexed) &&
    result "Length(Rows/Text) > 0 And [Missing] > 0" row rawModel == (missing, missing) &&
    result "FieldValueAsNumber(Rows/Text For \"keep\") > 0" row rawModel == (conversion, conversion) &&
    result "RangeAsNumber(Rows/Text For \"keep\", 1, 2) > 0" row rawModel == (raw, raw) &&
    result "RangeAsString(Rows/Text For \"keep\", 1, 2) == \"x\"" row rawModel == (raw, raw) &&
    result "FieldValueAsString(Rows/Text For \"keep\") == \"x\"" row rawModel == (number, number)) = true := by native_decide

example : [false, true].all (fun row =>
    let category := KernelStaticDiagnostic.categoryNotAllowed.kernelCode
    let indexed := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    operations.all (fun (op, _, rest, number) =>
      result (op ++ "(RuleGroup" ++ rest ++ ")" ++ comparison number) row ==
        (KernelStaticDiagnostic.noGroupsAllowed.kernelCode, KernelStaticDiagnostic.noGroupsAllowed.kernelCode) &&
      (op == "FieldValueAsNumber" || result (op ++ "(Rows/Choice->Label For \"keep\"" ++ rest ++ ")" ++ comparison number) row == (category, category))) &&
    result "FieldValueAsNumber(Rows/Choice For \"keep\") > 0" row == (indexed, indexed) &&
    result "FieldValueAsNumber(Rows/Choice->Label For \"keep\") > 0" row == (indexed, indexed) &&
    result "FieldValueAsNumber(Rows/Choice->Label) > 0" row == ("admitted", "admitted")) = true := by native_decide

example : [false, true].all (fun row =>
    let forbidden := KernelStaticDiagnostic.disallowedConstructInFilterCondition.kernelCode
    let unbound := KernelStaticDiagnostic.noWildcard.kernelCode
    let outer := KernelStaticDiagnostic.invalidOuterIteration.kernelCode
    let preceding := "AtLeastOneFieldFilled(Rows*/N Having FieldFilled(Rows/N)) And "
    operations.all (fun (op, field, rest, number) =>
      result (preceding ++ op ++ "(" ++ field ++ rest ++ ")" ++ comparison number) row ==
        (if row then (forbidden, forbidden) else (unbound, unbound)) &&
      result (preceding ++ op ++ "($" ++ field ++ rest ++ ")" ++ comparison number) row == (outer, outer))) = true := by native_decide

example : [false, true].all (fun row =>
    let indexed := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    let addition := KernelStaticDiagnostic.noStringOrNumberForAdd.kernelCode
    let number := KernelStaticDiagnostic.noNumber.kernelCode
    let pattern := KernelStaticDiagnostic.missingConstantInPatternComparison.kernelCode
    result "{RangeAsString(Rows/Text For \"keep\", 1, 2) + FieldValueAsString(Rows/N)} == \"x\"" row == (indexed, indexed) &&
    result "{RangeAsString(Rows/Text For \"keep\", 1, 2) + 1} == [Missing]" row == (addition, addition) &&
    result "FieldValueAsString(Rows/Text For \"keep\") == [Missing]" row == (number, number) &&
    result "[Rows/Tag] PatternMatched RangeAsString(Rows/Text For \"keep\", 1, 2)" row == (pattern, pattern)) = true := by native_decide

private def displayModel (remapped : Bool) : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 8 then
    { field with enumeration := field.enumeration.map fun declaration =>
      { declaration with displayFacts := declaration.storedTokens.map fun stored =>
        { locale := "en_US", stored, display := if remapped && stored == "1.2" then "one" else stored } } }
  else field }

example : [false, true].all (fun row =>
    let fixture := displayModel true
    let indexed := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    let addition := KernelStaticDiagnostic.noStringOrNumberForAdd.kernelCode
    result "{[Rows/Choice For \"keep\"]} + [Rows/Text] == \"x\"" row fixture == (indexed, indexed) &&
    result "[Rows/Text] + {{[Rows/Choice For \"keep\"]}} == \"x\"" row fixture == (indexed, indexed) &&
    result "{[Rows/Choice]} + [Missing] == \"x\"" row fixture == ("MVK_INVALID_ENTITY", "MVK_INVALID_ENTITY") &&
    result "{[Rows/Choice] + [Rows/Text]} == [Missing]" row fixture == (addition, addition) &&
    result "{[Rows/Choice]} + [Rows/N] == \"x\"" row fixture == (addition, addition) &&
    result "FirstFilledValue(Rows/Choice,Rows/Choice For \"keep\") + \"x\" == \"x\"" row fixture ==
      (indexed, indexed)) = true := by native_decide

example : [false, true].all (fun row =>
    let preceding := "AtLeastOneFieldFilled(Rows*/N Having FieldFilled(Rows/N)) And "
    let expected := if row then "MVK_DISALLOWED_CONSTRUCT_IN_FILTER_CONDITION" else "MVK_NO_WILDCARD"
    result (preceding ++ "{[Rows/Choice]} + [Rows/Text] == \"x\"") row (displayModel true) == (expected, expected) &&
    result (preceding ++ "{[$Rows/Choice]} + [Rows/Text] == \"x\"") row (displayModel true) ==
      ("MVK_INVALID_OUTER_ITERATION", "MVK_INVALID_OUTER_ITERATION")) = true := by native_decide

example : [false, true].all (fun row =>
    let addition := KernelStaticDiagnostic.noStringOrNumberForAdd.kernelCode
    result "{[Rows/Choice]} + [Rows/Text] == \"x\"" row (displayModel true) == ("admitted", "admitted") &&
    result "[Rows/Text] + {{[Rows/Choice]}} == \"x\"" row (displayModel true) == ("admitted", "admitted") &&
    result "[Rows/Choice] + [Rows/Text] == \"x\"" row (displayModel true) == (addition, addition) &&
    result "{[Rows/Choice] + [Rows/Text]} == \"x\"" row (displayModel true) == (addition, addition) &&
    result "[Rows/Choice] + [Rows/Text] == \"x\"" row (displayModel false) == ("admitted", "admitted")) = true := by native_decide

example : [false, true].all (fun row =>
    let indexed := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    let addition := KernelStaticDiagnostic.noStringOrNumberForAdd.kernelCode
    let fixture := displayModel true
    result "RangeAsString(Rows/Text For \"keep\", 1, 2) + {[Rows/Choice]} == \"x\"" row fixture == (indexed, indexed) &&
    result "{{[Rows/Choice]}} + RangeAsString(Rows/Text For \"keep\", 1, 2) == \"x\"" row fixture == (indexed, indexed) &&
    result "{RangeAsString(Rows/Text For \"keep\", 1, 2) + [Rows/Choice]} == \"x\"" row fixture == (addition, addition) &&
    result "{[Rows/Choice]} + [Rows/Choice For \"keep\"] == \"x\"" row fixture == (addition, addition)) = true := by native_decide

example : [false, true].all (fun remapped => (displayModel remapped).validate.isOk) = true ∧
    [false, true].all (fun row =>
      let addition := KernelStaticDiagnostic.noStringOrNumberForAdd.kernelCode
      let indexed := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
      result "RangeAsString(Rows/Text, 1, 2) + [Rows/Choice] == \"x\"" row (displayModel false) == ("admitted", "admitted") &&
      result "RangeAsString(Rows/Text For \"keep\", 1, 2) + [Rows/Choice] == \"x\"" row (displayModel false) == (indexed, indexed) &&
      result "RangeAsString(Rows/Text, 1, 2) + [Rows/Choice] == \"x\"" row (displayModel true) == (addition, addition)) = true := by native_decide

example : [false, true].all (fun row =>
    let number := KernelStaticDiagnostic.noNumber.kernelCode
    let string := KernelStaticDiagnostic.noString.kernelCode
    let conversion := KernelStaticDiagnostic.noConvertInNumber.kernelCode
    let type := KernelStaticDiagnostic.invalidType.kernelCode
    result "Length(Rows/N) > 0" row == (string, string) &&
    result "FieldValueAsString(Rows/Text) == \"x\"" row == (number, number) &&
    result "FieldValueAsNumber(Rows/N) > 0" row == (conversion, conversion) &&
    result "RangeAsNumber(Rows/N, 1, 2) > 0" row == (type, type) &&
    result "RangeAsString(Rows/N, 1, 2) == \"x\"" row == (type, type) &&
    result "RangeAsNumber(Rows/Text, 0, 1) > 0" row == ("MVK_INVALID_INTERVAL", "MVK_INVALID_INTERVAL") &&
    result "RangeAsNumber(Rows/Text, 1, 1) > 0" row == ("admitted", "admitted")) = true := by native_decide

end A12Kernel.Dm.HavingScalarOperationLocks
