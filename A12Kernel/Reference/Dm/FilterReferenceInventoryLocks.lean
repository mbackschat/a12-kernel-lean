import A12Kernel.Reference.Dm.HavingFixture
import A12Kernel.Reference.Dm.FilterReferenceInventory
import A12Kernel.Reference.Dm.HavingAdmission

/- The matrices separate the post-read walk, ordered body admission and the wired validation/
computation readers. Nested-filter exit and the late indexed-read gate retain separate failure boundaries. -/

namespace A12Kernel.Dm.FilterReferenceInventoryLocks
open A12Kernel

private def model : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields ++ [
    { id := 6, name := "Qty", groupPath := ["Form", "Rows", "Lines"],
      policy := { kind := .number { scale := 0, signed := true } }, repeatableScope := [10, 20] },
    { id := 7, name := "Tag", groupPath := ["Form", "Parties"],
      policy := { kind := .string }, repeatableScope := [30] }]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 3 },
    { level := 20, path := ["Form", "Rows", "Lines"], repeatability := some 2 },
    { level := 30, path := ["Form", "Parties"], repeatability := some 2 }] }

private def walk (target body : String) : Option (Option KernelStaticDiagnostic) := do
  let source ← (← (parseModelPath .english target).toOption).toStarFieldPath?
  let checked ← (elaborateStarFieldPath model ["Form"] source).toOption
  let expression := (← (parseText .english body).toOption).body
  let (references, forbidden) ← (filterBodyInventory model ["Form"] checked expression).toOption
  pure (filterBodyRefusal references forbidden)

example : model.validate.isOk = true ∧
    walk "Rows*/N" "FieldFilled(Rows/N)" = some none ∧
    walk "Rows*/N" "Sum(Rows*/N) > 0" = some (some .noIterationForWildcard) ∧
    walk "Rows*/N" "Sum(Rows*/Lines*/Qty) > 0 And [Rows/N] > 1" = some none := by native_decide

example : walk "Rows*/N" "Sum(Rows*/Lines/Qty) > 0 And [Rows/N] > 1" =
      some (some .invalidIterationInFilterCondition) ∧
    walk "Rows*/Lines*/Qty" "Sum(Rows*/Lines/Qty) > 0 And [Rows/Lines/Qty] > 1" =
      some (some .noWildcard) := by native_decide

example : walk "Rows*/N" "FieldFilled(Rows/N For \"keep\")" = some (some .semanticIndexNotAllowed) ∧
    walk "Rows*/N" "FieldFilled($Rows/N For \"keep\") And FieldFilled(Rows/N)" = some none ∧
    walk "Rows*/N" "FieldFilled($Rows/N For Parties/Tag) And FieldFilled(Rows/N)" =
      some (some .invalidIterationInFilterCondition) := by native_decide

example : walk "Rows*/N" "Sum(Rows*/N Having [Parties/Tag] == \"keep\") > 0 And [Rows/N] > 1" =
      some (some .invalidIterationInFilterCondition) ∧
    walk "Rows*/N" "Sum(Rows*/N Having [Rows/N] > 0) > 0 And [Rows/N] > 1" =
      some (some .disallowedConstructInFilterCondition) := by native_decide

example : walk "Rows*/N" "RepetitionNotUnique(Rows/N @From Parties)" =
      some (some .invalidIterationInFilterCondition) ∧
    walk "Rows*/N" "RepetitionNotUnique(Rows/N @From Rows)" =
      some (some .disallowedConstructInFilterCondition) := by native_decide

private def admission (body : String) (fixture : FlatModel := model) : Option String := do
  let source ← (elaborateStarFieldPath fixture ["Form"] {
    base := .relative 0, groups := [{ name := "Rows", starred := true }], field := "N" }).toOption
  let expression := (← (parseText .english body).toOption).body
  match elaborateRawStarHaving fixture ["Form"] source expression with
  | .ok _ => pure "admitted"
  | .error refusal => pure refusal.detail

example : admission "FieldFilled(Rows/N)" = some "admitted" ∧
    admission "Sum(Rows*/N) > 0" = some KernelStaticDiagnostic.noIterationForWildcard.kernelCode ∧
    admission "RepetitionNotUnique(Rows/N)" =
      some KernelStaticDiagnostic.disallowedConstructInFilterCondition.kernelCode := by native_decide

example : ["And", "Or"].all (fun connective =>
    admission ("[Rows/Tag] > \"keep\" " ++ connective ++ " FieldFilled(Rows/N For \"keep\")") ==
      some KernelStaticDiagnostic.invalidTypeForComparison.kernelCode &&
    admission ("FieldFilled(Rows/N) " ++ connective ++ " [Rows/Tag] > \"keep\"") ==
      some KernelStaticDiagnostic.invalidTypeForComparison.kernelCode) = true := by native_decide

example : ["And", "Or"].all (fun connective => [false, true].all fun reverse =>
    let first := "RepetitionNotUnique(Rows/N)"
    let second := "[Rows/Tag] > \"keep\""
    admission (if reverse then second ++ " " ++ connective ++ " " ++ first
      else first ++ " " ++ connective ++ " " ++ second) ==
        some KernelStaticDiagnostic.invalidTypeForComparison.kernelCode) = true := by native_decide

example : ["FieldFilled", "FieldNotFilled"].all (fun operator =>
    admission (operator ++ "(Rows/N For \"keep\")") == some KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode &&
    admission (operator ++ "(Rows/N For \"\")") == some KernelStaticDiagnostic.semanticIndexConstantInvalid.kernelCode) = true := by native_decide

example : ["And", "Or"].all (fun connective =>
    admission ("FieldFilled(Rows/N For \"keep\") " ++ connective ++ " [Rows/Tag] > \"keep\"") ==
      some KernelStaticDiagnostic.invalidTypeForComparison.kernelCode &&
    admission ("FieldFilled(Rows/N For \"\") " ++ connective ++ " [Rows/Tag] > \"keep\"") ==
      some KernelStaticDiagnostic.semanticIndexConstantInvalid.kernelCode) = true := by native_decide

example : ["And", "Or"].all (fun connective =>
    admission ("[Parties/Tag] == \"keep\" " ++ connective ++ " FieldFilled(Rows/N For \"keep\")") ==
      some KernelStaticDiagnostic.invalidIterationInFilterCondition.kernelCode &&
    admission ("FieldFilled(Rows/N For \"keep\") " ++ connective ++ " [Parties/Tag] == \"keep\"") ==
      some KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode) = true := by native_decide

example : admission "FieldFilled(Missing For \"keep\")" = some KernelStaticDiagnostic.invalidEntity.kernelCode ∧
    admission "FieldFilled(Rows/N For \"keep\")" HavingFixture.model =
      some KernelStaticDiagnostic.noIndexField.kernelCode ∧
    admission "FieldFilled(Rows/Lines/Qty For \"keep\")" =
      some KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode := by native_decide

private def numberIndexModel : FlatModel := { model with
  fields := model.fields.map fun field => if field.id == 3 then
    { field with policy := { kind := .number { scale := 0, signed := true } } } else field }

example : numberIndexModel.validate.isOk = true ∧
    admission "FieldFilled(Rows/N For \"12\")" numberIndexModel =
      some KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode ∧
    admission "FieldFilled(Rows/N For \"keep\")" numberIndexModel =
      some KernelStaticDiagnostic.semanticIndexConstantInvalid.kernelCode ∧
    admission "FieldFilled(Rows/N)" numberIndexModel = some "admitted" := by native_decide

private def rawExpectedModel : FlatModel := { model with
  fields := model.fields.map fun field => if field.id == 2 then
    { field with stringValueMode := .raw, stringPolicy := { lineBreaksPermitted := true } } else field }

private def rawExpectedNumberIndexModel : FlatModel := { numberIndexModel with
  fields := numberIndexModel.fields.map fun field => if field.id == 2 then
    { field with stringValueMode := .raw, stringPolicy := { lineBreaksPermitted := true } } else field }

example : rawExpectedModel.validate.isOk = true ∧
    rawExpectedNumberIndexModel.validate.isOk = true := by native_decide

example : ["FieldFilled", "FieldNotFilled"].all (fun operator =>
    admission (operator ++ "(Rows/N For Expected)") ==
      some KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode &&
    admission (operator ++ "(Rows/N For Out)") ==
      some KernelStaticDiagnostic.indexTypeInconsistent.kernelCode &&
    admission (operator ++ "(Rows/N For Rows/Tag)") ==
      some KernelStaticDiagnostic.semanticIndexContainedInIndex.kernelCode &&
    admission (operator ++ "(Rows/N For Missing)") ==
      some KernelStaticDiagnostic.invalidEntity.kernelCode) = true := by native_decide

example : ["FieldFilled", "FieldNotFilled"].all (fun operator =>
    admission (operator ++ "(Rows/N For Expected)") rawExpectedModel ==
      some KernelStaticDiagnostic.rawTypeOperandInvalid.kernelCode &&
    admission (operator ++ "(Rows/N For Expected)") rawExpectedNumberIndexModel ==
      some KernelStaticDiagnostic.indexTypeInconsistent.kernelCode &&
    admission (operator ++ "(Rows/N For Missing)") HavingFixture.model ==
      some KernelStaticDiagnostic.invalidEntity.kernelCode &&
    admission (operator ++ "(Rows/N For Expected)") HavingFixture.model ==
      some KernelStaticDiagnostic.noIndexField.kernelCode) = true := by native_decide

example : ["FieldFilled", "FieldNotFilled"].all (fun operator =>
    ["And", "Or"].all fun connective => [false, true].all fun reverse =>
      let indexed := operator ++ "(Rows/N For Expected)"
      let comparison := "[Rows/Tag] > \"keep\""
      admission (if reverse then comparison ++ " " ++ connective ++ " " ++ indexed
        else indexed ++ " " ++ connective ++ " " ++ comparison) ==
          some KernelStaticDiagnostic.invalidTypeForComparison.kernelCode) = true := by native_decide

example : ["FieldFilled", "FieldNotFilled"].all (fun operator =>
    ["And", "Or"].all fun connective =>
      let indexed := operator ++ "(Rows/N For Out)"
      let comparison := "[Rows/Tag] > \"keep\""
      admission (indexed ++ " " ++ connective ++ " " ++ comparison) ==
        some KernelStaticDiagnostic.indexTypeInconsistent.kernelCode &&
      admission (comparison ++ " " ++ connective ++ " " ++ indexed) ==
        some KernelStaticDiagnostic.invalidTypeForComparison.kernelCode) = true := by native_decide

private def categoryKeyModel : FlatModel := { model with
  fields := model.fields.map fun field => if field.id == 2 || field.id == 3 then
    { field with policy := { kind := .enumeration }, enumeration := some {
      storedTokens := ["keep", "drop"], categories := [{ name := "Label", tokens := ["K", "D"] }] } }
    else field }

example : categoryKeyModel.validate.isOk = true ∧
    ((categoryKeyModel.lookupUniqueId 2).toOption.any fun field =>
      (field.checkEntityCategoryRead (.projected "Label")).isOk) = true := by native_decide

example : ["FieldFilled", "FieldNotFilled"].all (fun operator =>
    admission (operator ++ "(Rows/N For Expected->Label)") categoryKeyModel ==
      some KernelStaticDiagnostic.semanticIndexKeyWithCategory.kernelCode &&
    admission (operator ++ "(Rows/N For Expected->Missing)") categoryKeyModel ==
      some KernelStaticDiagnostic.categoryUnknown.kernelCode &&
    admission (operator ++ "(Rows/N For Expected->Label)") ==
      some KernelStaticDiagnostic.noEnumeration.kernelCode &&
    admission (operator ++ "(Rows/N For Rows/Tag->Label)") categoryKeyModel ==
      some KernelStaticDiagnostic.semanticIndexContainedInIndex.kernelCode) = true := by native_decide

example : ["FieldFilled", "FieldNotFilled"].all (fun operator =>
    admission (operator ++ "(Rows/N For Rows/Tag For \"keep\")") ==
      some KernelStaticDiagnostic.semanticIndexOnSemanticIndex.kernelCode &&
    admission (operator ++ "(Rows/N For Rows/Tag For \"keep\")") HavingFixture.model ==
      some KernelStaticDiagnostic.semanticIndexOnSemanticIndex.kernelCode &&
    admission (operator ++ "(Rows/N For Rows/Tag For Missing)") ==
      some KernelStaticDiagnostic.invalidEntity.kernelCode &&
    admission (operator ++ "(Rows/N For Missing For \"keep\")") ==
      some KernelStaticDiagnostic.invalidEntity.kernelCode) = true := by native_decide

example : admission "FieldFilled(Rows/N For Rows/Tag For Expected->Missing)" categoryKeyModel =
    some KernelStaticDiagnostic.categoryUnknown.kernelCode := by native_decide

private def mismatchedCategoryKeyModel : FlatModel := { categoryKeyModel with
  fields := categoryKeyModel.fields.map fun field => if field.id == 3 then
    { field with policy := { kind := .string }, enumeration := none } else field }

example : mismatchedCategoryKeyModel.validate.isOk = true ∧
    ((mismatchedCategoryKeyModel.lookupUniqueId 2).toOption.any fun field =>
      (field.checkEntityCategoryRead (.projected "Label")).isOk) = true ∧
    admission "[Rows/Tag] > \"keep\"" categoryKeyModel =
      some KernelStaticDiagnostic.invalidTypeForComparison.kernelCode := by native_decide

example : ["FieldFilled", "FieldNotFilled"].all (fun operator =>
    admission (operator ++ "(Rows/N For Expected->Label)") mismatchedCategoryKeyModel ==
      some KernelStaticDiagnostic.indexTypeInconsistent.kernelCode &&
    admission (operator ++ "(Rows/N For Rows/Tag For \"\")") ==
      some KernelStaticDiagnostic.semanticIndexOnSemanticIndex.kernelCode &&
    admission (operator ++ "(Rows/N For Rows/Tag->Missing For \"keep\")") categoryKeyModel ==
      some KernelStaticDiagnostic.semanticIndexOnSemanticIndex.kernelCode &&
    admission (operator ++ "(Rows/N For Rows/Tag For Expected->Label)") categoryKeyModel ==
      some KernelStaticDiagnostic.semanticIndexOnSemanticIndex.kernelCode) = true := by native_decide

example : ["FieldFilled", "FieldNotFilled"].all (fun operator =>
    ["And", "Or"].all fun connective =>
      let indexed := operator ++ "(Rows/N For Expected->Label)"
      let comparison := "[Rows/Tag] > \"keep\""
      admission (indexed ++ " " ++ connective ++ " " ++ comparison) categoryKeyModel ==
        some KernelStaticDiagnostic.semanticIndexKeyWithCategory.kernelCode &&
      admission (comparison ++ " " ++ connective ++ " " ++ indexed) categoryKeyModel ==
        some KernelStaticDiagnostic.invalidTypeForComparison.kernelCode) = true := by native_decide

example : ["FieldFilled", "FieldNotFilled"].all (fun operator =>
    ["And", "Or"].all fun connective =>
      let indexed := operator ++ "(Rows/N For Rows/Tag For \"keep\")"
      let comparison := "[Rows/Tag] > \"keep\""
      admission (indexed ++ " " ++ connective ++ " " ++ comparison) ==
        some KernelStaticDiagnostic.semanticIndexOnSemanticIndex.kernelCode &&
      admission (comparison ++ " " ++ connective ++ " " ++ indexed) ==
        some KernelStaticDiagnostic.invalidTypeForComparison.kernelCode) = true := by native_decide

private def readerResults (operation : String) (fixture : FlatModel := model) (rowBound : Bool := false) : String × String :=
  HavingFixture.readerResults operation fixture rowBound

private def bothReaders (operation : String) (expected : String) (fixture : FlatModel := model) : Bool :=
  readerResults operation fixture == (expected, expected)

example : ["FieldFilled", "FieldNotFilled"].all (fun operator =>
    bothReaders ("Sum(Rows*/N Having " ++ operator ++ "(Rows/N For Expected))")
      KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode &&
    bothReaders ("Sum(Rows*/N Having " ++ operator ++ "(Rows/N For Out))")
      KernelStaticDiagnostic.indexTypeInconsistent.kernelCode) = true := by native_decide

example : bothReaders "Sum(Missing, Rows*/N Having FieldFilled(Rows/N For Expected))"
      KernelStaticDiagnostic.invalidEntity.kernelCode = true ∧
    bothReaders "Sum(Rows*/N Having FieldFilled(Rows/N For Expected), Missing)"
      KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode = true := by native_decide

example : bothReaders "Sum(Rows*/N Having FieldFilled(Rows/N) And FieldFilled($Expected))" "admitted" = true ∧
    bothReaders "Sum(Rows*/N Having FieldFilled(Rows/N) And FieldFilled($Rows/N))"
      KernelStaticDiagnostic.noWildcard.kernelCode = true := by native_decide

private def rowBoundModel : FlatModel := { model with fields := model.fields ++ [{
  id := 8, name := "RowOut", groupPath := ["Form", "Rows"], repeatableScope := [10]
  policy := { kind := .number { scale := 0, signed := true } } }] }

example : rowBoundModel.validate.isOk = true ∧
    readerResults "Sum(Rows*/N Having FieldFilled(Rows/N) And FieldFilled($Rows/Tag))" rowBoundModel true =
      ("admitted", "admitted") ∧
    bothReaders "Sum(Expected, Rows*/N Having FieldFilled(Rows/N For Expected))"
      KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode = true := by native_decide

private def guardResults (guard : String) (fixture : FlatModel := model) (rowBound : Bool := false) : String × String :=
  let dm : DmModel := { flat := fixture, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let report {α : Type} : Lowering α → String
    | .ok _ => "admitted"
    | .error refusal => refusal.detail
  (report (checkRule dm .english {
    group := ["Form"], name := "Guard", errorCode := "GUARD", errorEntityRelPath := if rowBound then "../Rows/RowOut" else "../Error"
    condition := (if rowBound then "FieldFilled(Rows/RowOut) And " else "FieldFilled(Error) And ") ++ guard, severity := "ERROR" }),
   report (lowerComputation fixture .english {
    group := ["Form"], name := "Guard", targetRelPath := if rowBound then "../Rows/RowOut" else "../Out", commonPrecondition := none
    alternatives := [{ precondition := some guard, operation := "9" }], errorCodesToSuppress := [] }))

private def fillOperators := ["AllFieldsFilled", "NoFieldFilled", "AtLeastOneFieldFilled", "MoreThanOneFieldFilled",
  "NotAllFieldsFilled", "NotExactlyOneFieldFilled", "FieldsNotCollectivelyFilled"]

example : fillOperators.all (fun operator =>
    guardResults (operator ++ "(Rows*/N Having FieldFilled(Rows/N))") == ("admitted", "admitted")) = true := by native_decide

example : fillOperators.all (fun operator =>
    let diagnostic := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    guardResults (operator ++ "(Rows*/N Having FieldFilled(Rows/N For Expected))") ==
      (diagnostic, diagnostic)) = true := by native_decide

example : guardResults "Sum(Rows*/N Having FieldFilled(Rows/N)) == 14" = ("admitted", "admitted") ∧
    guardResults "Sum(Rows*/N Having FieldFilled(Rows/N For Expected)) == 14" =
      (KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode,
       KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode) := by native_decide

example : fillOperators.all (fun operator => ["FieldFilled", "FieldNotFilled"].all fun presence =>
    let filtered := "Rows*/N Having " ++ presence ++ "(Rows/N For Expected)"
    let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
    let indexed := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    guardResults (operator ++ "(Missing, " ++ filtered ++ ")") == (missing, missing) &&
    guardResults (operator ++ "(" ++ filtered ++ ", Missing)") == (indexed, indexed)) = true := by native_decide

example : fillOperators.all (fun operator => ["FieldFilled", "FieldNotFilled"].all fun presence =>
    let diagnostic := KernelStaticDiagnostic.indexTypeInconsistent.kernelCode
    guardResults (operator ++ "(Rows*/N Having " ++ presence ++ "(Rows/N For Out))") ==
      (diagnostic, diagnostic)) = true := by native_decide

example : fillOperators.all (fun operator => ["FieldFilled", "FieldNotFilled"].all fun presence =>
    ["And", "Or"].all fun connective => [false, true].all fun reverse =>
      let indexed := presence ++ "(Rows/N For Expected)"
      let comparison := "[Rows/Tag] > \"keep\""
      let body := if reverse then comparison ++ " " ++ connective ++ " " ++ indexed
        else indexed ++ " " ++ connective ++ " " ++ comparison
      let diagnostic := KernelStaticDiagnostic.invalidTypeForComparison.kernelCode
      guardResults (operator ++ "(Rows*/N Having " ++ body ++ ")") ==
        (diagnostic, diagnostic)) = true := by native_decide

example : fillOperators.all (fun operator =>
    guardResults (operator ++ "(Rows*/N Having FieldFilled(Rows/N) And FieldFilled($Rows/Tag))") rowBoundModel true ==
      ("admitted", "admitted") &&
    let diagnostic := KernelStaticDiagnostic.noWildcard.kernelCode
    guardResults (operator ++ "(Rows*/N Having FieldFilled(Rows/N) And FieldFilled($Rows/Tag))") ==
      (diagnostic, diagnostic)) = true := by native_decide

example : guardResults "NoFieldValueIncludedInValueList(Expected In Rows*/Tag Having FieldFilled(Rows/N))" =
    ("admitted", "admitted") := by native_decide

example : guardResults "NoFieldValueIncludedInValueList(Missing In Rows*/Tag Having FieldFilled(Rows/N For Expected))" =
      (KernelStaticDiagnostic.invalidEntity.kernelCode, KernelStaticDiagnostic.invalidEntity.kernelCode) ∧
    guardResults "NoFieldValueIncludedInValueList(Rows*/Tag Having FieldFilled(Rows/N For Expected) In Missing)" =
      (KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode,
       KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode) := by native_decide

example : ["[Missing]", "Length(Missing)"].all (fun earlier =>
    bothReaders (earlier ++ " + Sum(Rows*/N Having FieldFilled(Rows/N For Expected))")
      KernelStaticDiagnostic.invalidEntity.kernelCode &&
    bothReaders ("Sum(Rows*/N Having FieldFilled(Rows/N For Expected)) + " ++ earlier)
      KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode) = true := by native_decide

private def keyShapeCases : List (String × KernelStaticDiagnostic) := [
  ("Rows", .semanticIndexKeyNotField), ("Rows*", .semanticIndexKeyNotField),
  ("Rows/Lines", .semanticIndexKeyNotField), ("Rows*/Tag", .semanticIndexKeyStarred),
  ("Rows*/Lines/Qty", .semanticIndexKeyStarred),
  ("Parties*/Tag", .semanticIndexKeyStarred),
  ("Rows/Tag*", .invalidWildcard), ("Expected*/Missing", .invalidWildcard),
  ("Rows*/Missing", .invalidEntity), ("Missing*/Tag", .invalidEntity),
  ("Rows->Label", .noGroupsAllowed), ("Rows*/Tag->Label", .noEnumeration),
  ("Rows For \"keep\"", .semanticIndexOnSemanticIndex),
  ("Rows*/Tag For Expected", .semanticIndexOnSemanticIndex),
  ("Rows/Tag For Rows", .semanticIndexKeyNotField),
  ("Rows/Tag For Rows*/Tag", .semanticIndexKeyStarred)]

example : ["FieldFilled", "FieldNotFilled"].all (fun operator => keyShapeCases.all fun (key, diagnostic) =>
    bothReaders ("Sum(Rows*/N Having " ++ operator ++ "(Rows/N For " ++ key ++ "))")
      diagnostic.kernelCode) = true := by native_decide

example : ["And", "Or"].all (fun connective => keyShapeCases.all fun (key, diagnostic) =>
    let keyed := "FieldFilled(Rows/N For " ++ key ++ ")"
    let comparison := "[Rows/Tag] > \"keep\""
    admission (keyed ++ " " ++ connective ++ " " ++ comparison) == some diagnostic.kernelCode &&
    admission (comparison ++ " " ++ connective ++ " " ++ keyed) ==
      some KernelStaticDiagnostic.invalidTypeForComparison.kernelCode) = true := by native_decide

private def emptyKeyModel : FlatModel := { model with repeatableGroups := model.repeatableGroups ++ [
  { level := 40, path := ["Form", "Empty"], repeatability := some 2 }] }

example : emptyKeyModel.validate.isOk = true ∧
    ["Empty", "Empty*", "Empty->Label"].all (fun key =>
      admission ("FieldFilled(Rows/N For " ++ key ++ ")") emptyKeyModel ==
        some KernelStaticDiagnostic.groupIsEmpty.kernelCode) = true := by native_decide

private def markedKeyCases : List (String × KernelStaticDiagnostic) := [
  ("$Expected", .semanticIndexNotAllowed), ("$Out", .indexTypeInconsistent),
  ("$Rows/Tag", .semanticIndexKeyInvalidIteration), ("$Rows", .semanticIndexKeyInvalidIteration),
  ("$Rows*/Tag", .semanticIndexKeyStarred), ("$Rows*", .semanticIndexKeyNotField),
  ("$Rows*/Lines/Qty", .semanticIndexKeyInvalidIteration),
  ("$Rows/Tag->Missing", .semanticIndexKeyInvalidIteration),
  ("$Rows/Tag For Expected", .semanticIndexOnSemanticIndex),
  ("$Expected->Label", .noEnumeration)]

example : ["FieldFilled", "FieldNotFilled"].all (fun operator => markedKeyCases.all fun (key, diagnostic) =>
    bothReaders ("Sum(Rows*/N Having " ++ operator ++ "(Rows/N For " ++ key ++ "))")
      diagnostic.kernelCode) = true := by native_decide

example : ["FieldFilled", "FieldNotFilled"].all (fun operator =>
    let expression key := "Sum(Rows*/N Having " ++ operator ++ "(Rows/N For " ++ key ++ "))"
    readerResults (expression "$Expected") rowBoundModel true == (KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode, KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode) &&
    readerResults (expression "$Rows/Tag") rowBoundModel true ==
      (KernelStaticDiagnostic.semanticIndexContainedInIndex.kernelCode,
       KernelStaticDiagnostic.semanticIndexContainedInIndex.kernelCode) &&
    readerResults (expression "$Rows") rowBoundModel true ==
      (KernelStaticDiagnostic.semanticIndexKeyNotField.kernelCode,
       KernelStaticDiagnostic.semanticIndexKeyNotField.kernelCode)) = true := by native_decide

private def filteredKeyCases : List (String × KernelStaticDiagnostic) := [
  ("Rows*/Tag Having FieldFilled(Rows/Tag)", .semanticIndexKeyStarred),
  ("Rows*/Tag Having FieldFilled(Rows/Tag For Expected)", .semanticIndexOnSemanticIndex),
  ("Rows*/Tag Having FieldFilled($Rows/Tag)", .semanticIndexKeyInvalidIteration),
  ("Rows*/Tag Having [$Rows/N] > 0", .semanticIndexKeyInvalidIteration),
  ("Rows*/Tag Having [$Rows/Tag] > \"keep\"", .semanticIndexKeyInvalidIteration),
  ("Rows*/Tag Having FieldFilled(Rows/Tag For Missing)", .invalidEntity),
  ("Rows*/Tag Having FieldFilled(Rows/Tag For Rows)", .semanticIndexKeyNotField),
  ("Rows*/Tag Having RepetitionNotUnique(Rows/Tag)", .disallowedConstructInFilterCondition),
  ("$Rows*/Tag Having FieldFilled(Expected)", .invalidOuterIteration),
  ("$Rows*/Tag Having [Rows/Tag] > \"keep\"", .invalidTypeForComparison),
  ("Rows*/Tag Having FieldFilled(Parties/Tag)", .invalidIterationInFilterCondition),
  ("Rows*/Tag Having FieldFilled(Expected)", .noIterationForWildcard),
  ("Rows*/Tag Having [Rows/Tag] > \"keep\"", .invalidTypeForComparison),
  ("Expected Having FieldFilled(Expected)", .wildcardsRequired),
  ("Expected Having [Expected] > \"keep\"", .invalidTypeForComparison),
  ("Rows/Tag Having FieldFilled(Rows/Tag)", .semanticIndexKeyInvalidIteration),
  ("Rows*/Lines/Qty Having FieldFilled(Rows/Lines/Qty)", .semanticIndexKeyInvalidIteration),
  ("Rows*/Tag Having FieldFilled($Expected)", .noIterationForWildcard),
  ("$Rows*/Tag Having FieldFilled(Rows/Tag)", .invalidOuterIteration),
  ("Rows Having [Missing] > 0", .noGroupsAllowed),
  ("Rows*/Tag->Missing Having FieldFilled(Rows/Tag)", .noEnumeration),
  ("Rows*/Tag->Missing Having FieldFilled(Parties/Tag)", .invalidIterationInFilterCondition),
  ("Missing*/Tag Having [Expected] > \"keep\"", .invalidEntity)]

example : ["FieldFilled", "FieldNotFilled"].all (fun operator => filteredKeyCases.all fun (key, diagnostic) =>
    bothReaders ("Sum(Rows*/N Having " ++ operator ++ "(Rows/N For " ++ key ++ "))")
      diagnostic.kernelCode) = true := by native_decide

example : readerResults "Sum(Rows*/N Having FieldFilled(Rows/N For Rows/Tag Having FieldFilled(Rows/Tag)))"
      rowBoundModel true =
    (KernelStaticDiagnostic.wildcardsRequired.kernelCode, KernelStaticDiagnostic.wildcardsRequired.kernelCode) := by native_decide

private def capturedKeyBodyLeaves : List String := [
  "AllFieldsFilled($Rows/N, Out)", "NumberOfFilledFields($Rows/N, Out) > 0",
  "Sum($Rows/N, Out) > 0", "FirstFilledValue($Rows/N, Out) > 0",
  "Length($Rows/Tag) > 0", "GroupFilled($Rows)",
  "FieldValueIncludedInValueList($Rows/Tag, \"keep\")"]

example : capturedKeyBodyLeaves.all (fun leaf =>
    let operation := "Sum(Rows*/N Having FieldFilled(Rows/N For Rows*/Tag Having FieldFilled(Rows/Tag) And " ++ leaf ++ "))"
    bothReaders operation KernelStaticDiagnostic.semanticIndexKeyInvalidIteration.kernelCode &&
    readerResults operation rowBoundModel true ==
      (KernelStaticDiagnostic.semanticIndexKeyStarred.kernelCode, KernelStaticDiagnostic.semanticIndexKeyStarred.kernelCode)) = true := by native_decide

private def productFilterCases : List (String × KernelStaticDiagnostic) := [
  ("Rows*/N Having FieldFilled(Rows/N), Rows*/N", .wildcardAtLowestLevelRequired),
  ("Rows*/N, Rows*/N Having FieldFilled(Rows/N)", .wildcardAtLowestLevelRequired),
  ("Rows*/N Having FieldFilled(Rows/N For Expected), Rows*/N", .semanticIndexNotAllowed),
  ("Rows*/N, Rows*/N Having FieldFilled(Rows/N For Expected)", .semanticIndexNotAllowed),
  ("Missing, Rows*/N Having FieldFilled(Rows/N For Expected)", .invalidEntity),
  ("Rows*/N Having FieldFilled(Rows/N For Expected), Missing", .semanticIndexNotAllowed),
  ("Rows*/Tag, Rows*/N Having FieldFilled(Rows/N For Expected)", .semanticIndexNotAllowed),
  ("Rows/N For \"keep\", Rows*/N Having FieldFilled(Rows/N For Expected)", .semanticIndexNotAllowed),
  ("Rows/N For Expected, Rows*/N Having FieldFilled(Rows/N For Expected)", .semanticIndexNotAllowed),
  ("Rows/N For Rows/Tag, Rows*/N Having FieldFilled(Rows/N For Expected)", .semanticIndexKeyInvalidIteration),
  ("Rows*/N For \"\", Rows*/N Having FieldFilled(Rows/N For Expected)", .semanticIndexConstantInvalid),
  ("Rows*/N For \"keep\", Rows*/N Having FieldFilled(Rows/N For Expected)", .semanticIndexAndWildcard)]

example : bothReaders "SumOfProducts(Rows*/N, Rows*/N)" "admitted" = true ∧
    productFilterCases.all (fun (arguments, diagnostic) =>
      bothReaders ("SumOfProducts(" ++ arguments ++ ")") diagnostic.kernelCode) = true := by native_decide

example : let operation := "SumOfProducts(Rows*/N Having FieldFilled(Rows/N) And FieldFilled($Rows/Tag), Rows*/N)"
    bothReaders operation KernelStaticDiagnostic.noWildcard.kernelCode = true ∧
    readerResults operation rowBoundModel true =
      (KernelStaticDiagnostic.wildcardAtLowestLevelRequired.kernelCode,
       KernelStaticDiagnostic.wildcardAtLowestLevelRequired.kernelCode) := by native_decide

private def selectorModel (kind : FieldKind) : FlatModel :=
  let enum := if kind == .enumeration then
    (categoryKeyModel.lookupUniqueId 3).toOption.bind (·.enumeration) else none
  { model with fields := (model.fields.map fun field =>
      if field.id == 4 || field.id == 5 then { field with policy := { kind }, enumeration := enum } else field) ++ [
    { id := 9, name := "Payload2", groupPath := ["Form"], policy := { kind }, enumeration := enum },
    { id := 8, name := "RowOut", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind }, enumeration := enum }] }

private def selectorResults (kind : FieldKind) (operation : String) (rowBound : Bool := false) : String × String :=
  let fixture := selectorModel kind
  let dm : DmModel := { flat := fixture, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let report {α : Type} : Lowering α → String
    | .ok _ => "admitted" | .error refusal => refusal.detail
  let expected := if kind == .boolean || kind == .confirm then "True" else "\"keep\""
  (report (checkRule dm .english {
    group := ["Form"], name := "Selector", errorCode := "SELECTOR", errorEntityRelPath := if rowBound then "../Rows/RowOut" else "../Error"
    condition := (if rowBound then "FieldFilled(Rows/RowOut) And " else "FieldFilled(Error) And ") ++ operation ++ " == " ++ expected,
    severity := "ERROR" }),
   report (lowerComputation fixture .english {
    group := ["Form"], name := "Selector", targetRelPath := if rowBound then "../Rows/RowOut" else "../Out", commonPrecondition := none
    alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }))

private def selectorKinds : List FieldKind := [.string, .boolean, .enumeration]

example : selectorKinds.all (fun kind => (selectorModel kind).validate.isOk &&
    [false, true].all fun row => selectorResults kind
      "FirstFilledValue(Rows*/N Having FieldFilled(Rows/Tag), Payload2)" row == ("admitted", "admitted")) = true := by native_decide

example : selectorKinds.all (fun kind => [false, true].all fun row =>
    let diagnostic := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    selectorResults kind "FirstFilledValue(Rows*/N Having FieldFilled(Rows/N For Expected), Payload2)" row ==
      (diagnostic, diagnostic)) = true := by native_decide

example : selectorKinds.all (fun kind => [
    "FirstFilledValue(Rows*/N Having FieldFilled(Rows/Tag) And FieldFilled($Rows/Tag), Payload2)",
    "FirstFilledValue(Payload2, Rows*/N Having FieldFilled(Rows/Tag) And FieldFilled($Rows/Tag))"].all fun operation =>
    let diagnostic := KernelStaticDiagnostic.noWildcard.kernelCode
    selectorResults kind operation == (diagnostic, diagnostic) &&
    selectorResults kind operation true == ("admitted", "admitted")) = true := by native_decide

example : selectorKinds.all (fun kind => [false, true].all fun row =>
    let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
    let indexed := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    selectorResults kind "FirstFilledValue(Missing, Rows*/N Having FieldFilled(Rows/N For Expected))" row ==
      (missing, missing) &&
    selectorResults kind "FirstFilledValue(Rows*/N Having FieldFilled(Rows/N For Expected), Missing)" row ==
      (indexed, indexed)) = true := by native_decide

example : [false, true].all (fun row =>
    let category := KernelStaticDiagnostic.categoryUnknown.kernelCode
    let indexed := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    selectorResults .enumeration
      "FirstFilledValue(Payload2->Missing, Rows*/N Having FieldFilled(Rows/N For Expected))" row ==
        (category, category) &&
    selectorResults .enumeration
      "FirstFilledValue(Payload2->Label, Rows*/N Having FieldFilled(Rows/N For Expected))" row ==
        (indexed, indexed) &&
    selectorResults .enumeration
      "FirstFilledValue(Rows*/N Having FieldFilled(Rows/N For Expected), Payload2->Missing)" row ==
        (indexed, indexed)) = true := by native_decide

private def nestedFillOperators : List String := [
  "AllFieldsFilled", "NoFieldFilled", "AtLeastOneFieldFilled", "MoreThanOneFieldFilled",
  "NotAllFieldsFilled", "NotExactlyOneFieldFilled", "FieldsNotCollectivelyFilled"]

private def nestedFillResults (body : String) (row : Bool) : String × String :=
  readerResults ("Sum(Rows*/N Having " ++ body ++ ")") rowBoundModel row

example : nestedFillOperators.all (fun operator => [false, true].all fun row =>
    nestedFillResults (operator ++ "(Rows*/N) And FieldFilled(Rows/N)") row == ("admitted", "admitted")) = true := by native_decide

example : nestedFillOperators.all (fun operator => [false, true].all fun row =>
    let nested := operator ++ "(Rows*/N Having FieldFilled(Rows/N))"
    let forbidden := KernelStaticDiagnostic.disallowedConstructInFilterCondition.kernelCode
    let unbound := KernelStaticDiagnostic.noWildcard.kernelCode
    nestedFillResults ("FieldFilled(Rows/N) And " ++ nested) row == (forbidden, forbidden) &&
    nestedFillResults (nested ++ " And FieldFilled(Rows/N)") row ==
      (if row then (forbidden, forbidden) else (unbound, unbound))) = true := by native_decide

example : nestedFillOperators.all (fun operator => [false, true].all fun row =>
    let nested := operator ++ "(Rows*/N Having FieldFilled(Rows/N))"
    let invalid := KernelStaticDiagnostic.invalidOuterIteration.kernelCode
    nestedFillResults (nested ++ " And FieldFilled($Rows/Tag)") row == (invalid, invalid) &&
    nestedFillResults (operator ++ "(Rows*/N Having FieldFilled(Rows/N), $Rows/Tag)") row == (invalid, invalid)) = true := by native_decide

example : nestedFillOperators.all (fun operator => [false, true].all fun row =>
    let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
    let groups := KernelStaticDiagnostic.noGroupsAllowed.kernelCode
    nestedFillResults (operator ++ "(Rows* Having FieldFilled(Missing))") row == (groups, groups) &&
    nestedFillResults (operator ++ "(Rows*/N Having FieldFilled(Missing))") row == (missing, missing)) = true := by native_decide

private def nestedAggregateOperators : List String := ["Sum", "MinValue", "MaxValue"]

example : nestedAggregateOperators.all (fun operator => [false, true].all fun row =>
    let aggregate := operator ++ "(Rows*/N Having FieldFilled(Rows/N))"
    let forbidden := KernelStaticDiagnostic.disallowedConstructInFilterCondition.kernelCode
    let unbound := KernelStaticDiagnostic.noWildcard.kernelCode
    let invalid := KernelStaticDiagnostic.invalidOuterIteration.kernelCode
    nestedFillResults ("FieldFilled(Rows/N) And " ++ aggregate ++ " > 0") row == (forbidden, forbidden) &&
    nestedFillResults (aggregate ++ " + [Rows/N] > 0") row ==
      (if row then (forbidden, forbidden) else (unbound, unbound)) &&
    nestedFillResults (aggregate ++ " + [$Rows/N] > 0") row == (invalid, invalid)) = true := by native_decide

example : [false, true].all (fun row =>
    let kind := KernelStaticDiagnostic.noNumber.kernelCode
    let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
    nestedFillResults "Sum(Rows*/Tag Having FieldFilled(Rows/N)) + [Missing] > 0" row == (kind, kind) &&
    nestedFillResults "[Missing] + Sum(Rows*/Tag Having FieldFilled(Rows/N)) > 0" row == (missing, missing)) = true := by native_decide

example : [false, true].all (fun row =>
    let nested := "Sum(Rows*/N Having FieldFilled(Rows/N))"
    let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
    let kind := KernelStaticDiagnostic.notSortable.kernelCode
    nestedFillResults ("Max(" ++ nested ++ ", \"keep\", [Missing]) > 0") row == (missing, missing) &&
    nestedFillResults ("Max(" ++ nested ++ ", \"keep\") > 0") row == (kind, kind) &&
    nestedFillResults ("{" ++ nested ++ " + \"keep\"} + [Missing] > 0") row ==
      (KernelStaticDiagnostic.noStringOrNumberForAdd.kernelCode, KernelStaticDiagnostic.noStringOrNumberForAdd.kernelCode)) = true := by native_decide

example : [false, true].all (fun row =>
    let indexed := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    let key := KernelStaticDiagnostic.semanticIndexConstantInvalid.kernelCode
    let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
    nestedFillResults "[Rows/N For \"keep\"] > 0" row == (indexed, indexed) &&
    nestedFillResults "[Rows/N For \"\"] + [Missing] > 0" row == (key, key) &&
    nestedFillResults "[Rows/N For \"keep\"] + [Missing] > 0" row == (missing, missing)) = true := by native_decide

private def markedIndexFilter : String :=
  "Rows*/N Having FieldFilled($Rows/N For \"keep\") And FieldFilled(Rows/N)"

example : [false, true].all (fun row =>
    let indexed := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
    let kind := KernelStaticDiagnostic.noNumber.kernelCode
    readerResults ("Sum(" ++ markedIndexFilter ++ ")") rowBoundModel row == (indexed, indexed) &&
    readerResults ("Sum(" ++ markedIndexFilter ++ ", Rows*/N Having FieldFilled(Missing))") rowBoundModel row == (missing, missing) &&
    readerResults ("Sum(Rows*/N Having FieldFilled(Missing), " ++ markedIndexFilter ++ ")") rowBoundModel row == (missing, missing) &&
    readerResults ("Sum(" ++ markedIndexFilter ++ ", Rows*/Tag Having FieldFilled(Rows/N))") rowBoundModel row == (kind, kind)) = true := by native_decide

example : readerResults "Sum(Rows*/N Having FieldFilled($Rows/N) And FieldFilled(Rows/N))" rowBoundModel true ==
    ("admitted", "admitted") := by native_decide

example : [false, true].all (fun row =>
    let nested := "AtLeastOneFieldFilled(Rows*/N Having FieldFilled(Rows/N)) And "
    let badType := KernelStaticDiagnostic.invalidTypeForComparison.kernelCode
    let forbidden := KernelStaticDiagnostic.disallowedConstructInFilterCondition.kernelCode
    nestedFillResults (nested ++ "[Expected] > \"keep\"") row == (badType, badType) &&
    nestedFillResults (nested ++ "[Expected] == \"keep\"") row == (forbidden, forbidden)) = true := by native_decide

private def mismatchedTargetScale : FlatModel := { rowBoundModel with
  fields := rowBoundModel.fields.map fun field => if field.id == 5 || field.id == 8 then
    { field with policy := { kind := .number { scale := 1, signed := true } } } else field }

example : [false, true].all (fun row =>
    readerResults ("Sum(" ++ markedIndexFilter ++ ")") mismatchedTargetScale row ==
      (KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode, KernelStaticDiagnostic.invalidCompareDecimalPlaces.kernelCode)) = true := by native_decide

example : [false, true].all (fun row =>
    let table := TableEnumRefusal.tableEnumExpected.catalogKey
    let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
    let group := KernelStaticDiagnostic.noGroupsAllowed.kernelCode
    let star := KernelStaticDiagnostic.noWildcardsAllowed.kernelCode
    nestedFillResults "ValueNotConsistent(Rows/N To \"keep\")" row == (table, table) &&
    nestedFillResults "ValueNotConsistent(Rows/Tag To Expected, \"keep\")" row == (table, table) &&
    nestedFillResults "ValueNotConsistent(Rows To \"keep\")" row == (group, group) &&
    nestedFillResults "ValueNotConsistent(Rows*/N To \"keep\")" row == (star, star) &&
    nestedFillResults "ValueNotConsistent(Rows*/N To Expected, Missing)" row == (missing, missing) &&
    nestedFillResults "ValueNotConsistent(Rows/N For \"keep\" To \"keep\")" row == (table, table)) = true := by native_decide

example : [false, true].all (fun row => ["==", "!="].all fun operator =>
    let scale := KernelStaticDiagnostic.invalidCompareDecimalPlaces.kernelCode
    nestedFillResults ("[Rows/N For \"keep\"] " ++ operator ++ " 0.1") row == (scale, scale) &&
    nestedFillResults ("Sum(Rows*/N Having FieldFilled(Rows/N)) " ++ operator ++ " 0.1") row == (scale, scale)) = true := by native_decide

example : [false, true].all (fun row => ["<", "<=", ">", ">="].all fun operator =>
    let indexed := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    let kind := KernelStaticDiagnostic.invalidTypeForComparison.kernelCode
    nestedFillResults ("[Rows/N For \"keep\"] " ++ operator ++ " 0.1") row == (indexed, indexed) &&
    nestedFillResults ("[Rows/Tag For \"keep\"] " ++ operator ++ " \"keep\"") row == (kind, kind) &&
    nestedFillResults ("\"keep\" " ++ operator ++ " [Rows/N For \"keep\"]") row == (kind, kind)) = true := by native_decide

example : [false, true].all (fun row =>
    let kind := KernelStaticDiagnostic.invalidTypeForToleranceOp.kernelCode
    let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
    nestedFillResults "[Rows/Tag For \"keep\"] DiffersWithToleranceRange1 0" row == (kind, kind) &&
    nestedFillResults "[Rows/N For \"keep\"] == [Missing]" row == (missing, missing)) = true := by native_decide

private def nestedCountOperators : List String := ["NumberOfFilledFields", "NumberOfDifferentValues"]

example : nestedCountOperators.all (fun operator => [false, true].all fun row =>
    let nested := operator ++ "(Rows*/N Having FieldFilled(Rows/N))"
    let forbidden := KernelStaticDiagnostic.disallowedConstructInFilterCondition.kernelCode
    let unbound := KernelStaticDiagnostic.noWildcard.kernelCode
    let outer := KernelStaticDiagnostic.invalidOuterIteration.kernelCode
    let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
    nestedFillResults (nested ++ " > 0") row == (forbidden, forbidden) &&
    nestedFillResults (nested ++ " + [Rows/N] > 0") row ==
      (if row then (forbidden, forbidden) else (unbound, unbound)) &&
    nestedFillResults (nested ++ " + [$Rows/N] > 0") row == (outer, outer) &&
    nestedFillResults (operator ++ "(Rows*/N Having FieldFilled(Rows/N), Missing) > 0") row == (missing, missing)) = true := by native_decide

example : [false, true].all (fun row =>
    let number := KernelStaticDiagnostic.numberAndNonNumber.kernelCode
    let token := KernelStaticDiagnostic.stringEnumAndNonStringEnum.kernelCode
    let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
    nestedFillResults "NumberOfDifferentValues(Rows*/N Having FieldFilled(Rows/N), Expected) > 0" row == (number, number) &&
    nestedFillResults "NumberOfDifferentValues(Rows*/Tag Having FieldFilled(Rows/N), Out) > 0" row == (token, token) &&
    nestedFillResults "NumberOfDifferentValues(Rows*/N Having FieldFilled(Rows/N), Expected, Missing) > 0" row == (missing, missing)) = true := by native_decide

private def countTypeModel : FlatModel := { rowBoundModel with fields := rowBoundModel.fields ++ [
  { id := 11, name := "DateA", groupPath := ["Form"],
    policy := { kind := .temporal .date TemporalComponents.fullDate },
    temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
  { id := 12, name := "DateB", groupPath := ["Form"],
    policy := { kind := .temporal .date TemporalComponents.fullDate },
    temporalTargetPolicy := some { format := "dd.MM.yyyy" } },
  { id := 13, name := "Flag", groupPath := ["Form"], policy := { kind := .boolean } }] }

private def countTypeResults (arguments : String) (fixture : FlatModel) (row : Bool) : String × String :=
  readerResults ("Sum(Rows*/N Having NumberOfDifferentValues(" ++ arguments ++ ") > [Rows/N For \"keep\"])") fixture row

example : countTypeModel.validate.isOk = true ∧
    [false, true].all (fun row =>
      let indexed := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
      let domain := KernelStaticDiagnostic.onlyStringEnumNumberCmpDateAllowed.kernelCode
      let temporal := KernelStaticDiagnostic.dateAndNonDate.kernelCode
      countTypeResults "DateA, DateB" countTypeModel row == (indexed, indexed) &&
      countTypeResults "Flag, Out" countTypeModel row == (domain, domain) &&
      countTypeResults "DateA, Out" countTypeModel row == (temporal, temporal) &&
      countTypeResults "Expected, Error" countTypeModel row == (indexed, indexed)) = true := by native_decide

example : [false, true].all (fun row =>
    let fixture := { rowBoundModel with fields := rowBoundModel.fields.map fun field =>
      if field.id == 2 then { field with stringValueMode := .raw, stringPolicy := { lineBreaksPermitted := true } } else field }
    let raw := KernelStaticDiagnostic.rawTypeOperandInvalid.kernelCode
    let token := KernelStaticDiagnostic.stringEnumAndNonStringEnum.kernelCode
    countTypeResults "Expected, Error" fixture row == (raw, raw) &&
    countTypeResults "Expected, Out" fixture row == (token, token)) = true := by native_decide

example : nestedCountOperators.all (fun operator => [false, true].all fun row =>
    let fixture := { rowBoundModel with fields := rowBoundModel.fields.map fun field =>
      if field.id == 2 then { field with policy := { kind := .enumeration }, enumeration := some {
        storedTokens := ["keep"], categories := [{ name := "Label", tokens := ["K"] }] } } else field }
    let check := fun arguments => readerResults
      ("Sum(Rows*/N Having " ++ operator ++ "(" ++ arguments ++ ") > [Rows/N For \"keep\"])") fixture row
    let category := KernelStaticDiagnostic.categoryNotAllowed.kernelCode
    let duplicate := KernelStaticDiagnostic.duplicateParam1.kernelCode
    let arity := KernelStaticDiagnostic.paramSizeInvalidN.kernelCode
    let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
    let indexed := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    check "Expected->Label, Expected->Label" == (category, category) &&
    check "Expected->Label, Missing" == (missing, missing) &&
    check "Expected, Expected" == (duplicate, duplicate) &&
    check "Expected" == (arity, arity) &&
    check "Expected, Error" == (indexed, indexed)) = true := by native_decide

private def countTemporalModel (partialFirst : Bool) (format : String) (baseYear : Option Int := none) : FlatModel :=
  { countTypeModel with baseYear, fields := countTypeModel.fields.map fun field =>
      if field.id == 11 then { field with temporalTargetPolicy := some {
        format := "yyyy-MM-dd", partialMode := if partialFirst then .dayOptional else .full } }
      else if field.id == 12 then { field with
        policy := { kind := .temporal .date (TemporalComponents.ofFormat format) }
        temporalTargetPolicy := some { format } }
      else field }

example : (countTemporalModel true "yyyy-MM").validate.isOk = true ∧
    (countTemporalModel false "MM-dd" (some 2026)).validate.isOk = true ∧
    [false, true].all (fun row =>
      let precision := KernelStaticDiagnostic.partialDateNotAllowed.kernelCode
      let format := KernelStaticDiagnostic.dateFormatsNotCompatible.kernelCode
      let number := KernelStaticDiagnostic.numberAndNonNumber.kernelCode
      let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
      let indexed := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
      countTypeResults "DateA, DateB" (countTemporalModel true "yyyy-MM") row == (precision, precision) &&
      countTypeResults "DateB, DateA" (countTemporalModel true "yyyy-MM") row == (precision, precision) &&
      countTypeResults "DateA, DateB, Out" (countTemporalModel false "yyyy-MM") row == (format, format) &&
      countTypeResults "Out, DateA" (countTemporalModel true "yyyy-MM") row == (number, number) &&
      countTypeResults "DateA, Missing" (countTemporalModel true "yyyy-MM") row == (missing, missing) &&
      countTypeResults "DateA, DateB" (countTemporalModel false "MM-dd") row == (format, format) &&
      countTypeResults "DateA, DateB" (countTemporalModel false "MM-dd" (some 2026)) row == (indexed, indexed)) = true := by native_decide

example : ["MinValue", "MaxValue"].all (fun operator => [false, true].all fun row =>
    let check := fun fixture => readerResults
      ("Sum(Rows*/N Having " ++ operator ++ "(DateA, DateB) + [Missing] > [Rows/N For \"keep\"])") fixture row
    let precision := KernelStaticDiagnostic.partialDateNotAllowed.kernelCode
    let format := KernelStaticDiagnostic.dateFormatsNotCompatible.kernelCode
    let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
    check (countTemporalModel true "yyyy-MM-dd") == (precision, precision) &&
    check (countTemporalModel false "MM-dd") == (format, format) &&
    check (countTemporalModel false "MM-dd" (some 2026)) == (missing, missing) &&
    check countTypeModel == (missing, missing)) = true := by native_decide

private def rawListResults (operator arguments : String) (fixture : FlatModel) (row : Bool) : String × String :=
  readerResults ("Sum(Rows*/N Having " ++ operator ++ "(" ++ arguments ++ ") + [Missing] > [Rows/N For \"keep\"])") fixture row

example : [false, true].all (fun row =>
    let forbidden := KernelStaticDiagnostic.disallowedConstructInFilterCondition.kernelCode
    let unbound := KernelStaticDiagnostic.noWildcard.kernelCode
    let outer := KernelStaticDiagnostic.invalidOuterIteration.kernelCode
    let selector := "FirstFilledValue(Rows*/N Having FieldFilled(Rows/N))"
    nestedFillResults (selector ++ " > 0") row == (forbidden, forbidden) &&
    nestedFillResults (selector ++ " + [Rows/N] > 0") row ==
      (if row then (forbidden, forbidden) else (unbound, unbound)) &&
    nestedFillResults (selector ++ " + [$Rows/N] > 0") row == (outer, outer)) = true := by native_decide

example : [false, true].all (fun row =>
    let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
    let varying := KernelStaticDiagnostic.varyingTypesNotAllowed.kernelCode
    let confirm := KernelStaticDiagnostic.noBoolyAllowed.kernelCode
    let fixture := { countTypeModel with fields := countTypeModel.fields ++ [
      { id := 14, name := "Confirm", groupPath := ["Form"], policy := { kind := .confirm } },
      { id := 15, name := "Flag2", groupPath := ["Form"], policy := { kind := .boolean } }] }
    rawListResults "FirstFilledValue" "Out, Expected" fixture row == (varying, varying) &&
    rawListResults "FirstFilledValue" "Out, Expected, Confirm" fixture row == (confirm, confirm) &&
    rawListResults "FirstFilledValue" "Confirm, Missing" fixture row == (missing, missing) &&
    rawListResults "FirstFilledValue" "Expected, Error" fixture row == (missing, missing) &&
    rawListResults "FirstFilledValue" "Flag, Flag2" fixture row == (missing, missing) &&
    rawListResults "FirstFilledValue" "DateA, DateB" fixture row == (varying, varying) &&
    rawListResults "FirstFilledValue" "DateA, DateB" (countTemporalModel true "yyyy-MM-dd") row == (missing, missing)) = true := by native_decide

example : [false, true].all (fun row =>
    let required := KernelStaticDiagnostic.wildcardAtLowestLevelRequired.kernelCode
    let group := KernelStaticDiagnostic.differentGroups.kernelCode
    let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
    let number := KernelStaticDiagnostic.noNumber.kernelCode
    let fixed := KernelStaticDiagnostic.repeatableLevelRequired.kernelCode
    let onlyLowest := KernelStaticDiagnostic.wildcardOnlyAtLowestLevelAllowed.kernelCode
    let fields := KernelStaticDiagnostic.noGroupsAllowed.kernelCode
    let arity := KernelStaticDiagnostic.paramSizeInvalidTwo.kernelCode
    rawListResults "SumOfProducts" "Rows*/N, Rows*/N" rowBoundModel row == (missing, missing) &&
    rawListResults "SumOfProducts" "Rows*/N Having FieldFilled(Rows/N), Rows*/N" rowBoundModel row == (required, required) &&
    rawListResults "SumOfProducts" "Rows*/N Having FieldFilled(Rows/N), Expected" rowBoundModel row == (group, group) &&
    rawListResults "SumOfProducts" "Rows*/Tag, Rows*/N" rowBoundModel row == (number, number) &&
    rawListResults "SumOfProducts" "Expected, Out" rowBoundModel row == (fixed, fixed) &&
    rawListResults "SumOfProducts" "Rows*/Lines*/Qty, Rows*/Lines*/Qty" rowBoundModel row == (onlyLowest, onlyLowest) &&
    rawListResults "SumOfProducts" "Rows*" rowBoundModel row == (fields, fields) &&
    rawListResults "SumOfProducts" "Rows*/N" rowBoundModel row == (arity, arity)) = true := by native_decide

private def selectorProfileModel : FlatModel := { countTypeModel with
  fields := (countTypeModel.fields.map fun field => if field.id == 2 then
    { field with stringValueMode := .raw, stringPolicy := { lineBreaksPermitted := true } } else field) ++ [
    { id := 16, name := "RangeA", groupPath := ["Form"], policy := { kind := .dateRange },
      dateRangePolicy := some { format := "MM", separator := "/" } },
    { id := 17, name := "RangeB", groupPath := ["Form"], policy := { kind := .dateRange },
      dateRangePolicy := some { format := "MM", separator := "" } },
    { id := 18, name := "Enum", groupPath := ["Form"], policy := { kind := .enumeration },
      enumeration := some { storedTokens := ["keep"], categories := [{ name := "Label", tokens := ["K"] }] } }] }

example : selectorProfileModel.validate.isOk = true ∧
    [false, true].all (fun row => ["Expected, Error", "Enum, Error", "Enum->Label, Error", "RangeA, RangeB"].all fun arguments =>
      let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
      rawListResults "FirstFilledValue" arguments selectorProfileModel row == (missing, missing)) = true := by native_decide

example : [false, true].all (fun row =>
    let fixture := { rowBoundModel with fields := rowBoundModel.fields.map fun field => if field.id == 8 then
      { field with policy := { kind := .number { scale := 2, signed := true } } } else field }
    let forbidden := KernelStaticDiagnostic.disallowedConstructInFilterCondition.kernelCode
    readerResults "Sum(Rows*/N Having FirstFilledValue(Rows*/N Having FieldFilled(Rows/N), Rows*/RowOut) == 0.12)"
      fixture row == (forbidden, forbidden)) = true := by native_decide

example : [false, true].all (fun row =>
    ["Sum", "MinValue", "MaxValue", "NumberOfFilledFields", "NumberOfDifferentValues", "FirstFilledValue"].all fun operator =>
      let duplicate := KernelStaticDiagnostic.duplicateParam1.kernelCode
      let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
      let key := KernelStaticDiagnostic.semanticIndexConstantInvalid.kernelCode
      rawListResults operator "Rows/N For \"keep\", Rows/N For \"keep\"" rowBoundModel row == (duplicate, duplicate) &&
      rawListResults operator "Rows/N For \"keep\", Rows/N For \"drop\"" rowBoundModel row == (missing, missing) &&
      rawListResults operator "Rows/N For Expected, Rows/N For /Form/Expected" rowBoundModel row == (duplicate, duplicate) &&
      rawListResults operator "Rows/N For Expected, Rows/N For Error" rowBoundModel row == (missing, missing) &&
      rawListResults operator "Rows/N For \"\", Missing" rowBoundModel row == (key, key)) = true := by native_decide

example : nestedFillOperators.all (fun operator => [false, true].all fun row =>
    let duplicate := KernelStaticDiagnostic.duplicateParam1.kernelCode
    let overlap := KernelStaticDiagnostic.duplicateParam2.kernelCode
    let indexed := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    nestedFillResults (operator ++ "(Rows/N For \"keep\", Rows/N For \"keep\")") row == (duplicate, duplicate) &&
    nestedFillResults (operator ++ "(Rows For \"keep\", Rows/N For \"keep\")") row == (overlap, overlap) &&
    nestedFillResults (operator ++ "(Rows For \"keep\", Rows/N For \"drop\")") row == (indexed, indexed)) = true := by native_decide

example : [false, true].all (fun row =>
    let overlap := KernelStaticDiagnostic.duplicateParam2.kernelCode
    let number := KernelStaticDiagnostic.noNumber.kernelCode
    let duplicate := KernelStaticDiagnostic.duplicateParam1.kernelCode
    let star := KernelStaticDiagnostic.wildcardAtLowestLevelRequired.kernelCode
    rawListResults "Sum" "Rows For \"keep\", Rows/N For \"keep\"" rowBoundModel row == (overlap, overlap) &&
    rawListResults "Sum" "Rows For \"keep\", Rows/N For \"drop\"" rowBoundModel row == (number, number) &&
    rawListResults "SumOfProducts" "Rows/N For \"keep\", Rows/N For \"keep\"" rowBoundModel row == (duplicate, duplicate) &&
    rawListResults "SumOfProducts" "Rows/N For \"keep\", Rows/N For \"drop\"" rowBoundModel row == (star, star)) = true := by native_decide

example : [false, true].all (fun row =>
    let numericKeys := { rowBoundModel with fields := rowBoundModel.fields.map fun field => if field.id == 3 then
      { field with policy := { kind := .number { scale := 0, signed := true } } } else field }
    let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
    rawListResults "Sum" "Rows/N For \"01\", Rows/N For \"1\"" numericKeys row == (missing, missing)) = true := by native_decide

example : [false, true].all (fun row =>
    let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
    let overlap := KernelStaticDiagnostic.duplicateParam2.kernelCode
    rawListResults "Sum" "Rows/Lines*/Qty For \"keep\"" rowBoundModel row == (missing, missing) &&
    rawListResults "Sum" "Rows/Lines*/Qty For \"keep\", Rows/Lines*/Qty For \"keep\"" rowBoundModel row == (missing, missing) &&
    rawListResults "Sum" "Rows For \"keep\", Rows/Lines*/Qty For \"keep\"" rowBoundModel row == (overlap, overlap) &&
    rawListResults "Sum" "Rows/N For Expected, Rows/N For $Expected" rowBoundModel row == (missing, missing) &&
    rawListResults "Sum" "Rows/N For \"keep\", $Rows/N For \"keep\"" rowBoundModel row == (missing, missing)) = true := by native_decide

example : [false, true].all (fun row =>
    let fixture := { rowBoundModel with fields := rowBoundModel.fields.map fun field => if field.id == 3 then
      { field with policy := { kind := .enumeration }, enumeration := some {
        storedTokens := ["keep", "drop"], categories := [{ name := "Label", tokens := ["K", "D"] }] } } else field }
    let same := "Rows/Tag->Label For \"keep\", Rows/Tag->Label For \"keep\""
    let different := "Rows/Tag->Label For \"keep\", Rows/Tag For \"keep\""
    let duplicate := KernelStaticDiagnostic.duplicateParam1.kernelCode
    let category := KernelStaticDiagnostic.categoryNotAllowed.kernelCode
    let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
    rawListResults "FirstFilledValue" same fixture row == (duplicate, duplicate) &&
    rawListResults "FirstFilledValue" different fixture row == (missing, missing) &&
    rawListResults "NumberOfFilledFields" same fixture row == (category, category)) = true := by native_decide

end A12Kernel.Dm.FilterReferenceInventoryLocks
