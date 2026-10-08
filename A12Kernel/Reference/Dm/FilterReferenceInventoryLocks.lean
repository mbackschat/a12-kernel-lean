import A12Kernel.Reference.Dm.HavingFixture
import A12Kernel.Reference.Dm.FilterReferenceInventory
import A12Kernel.Reference.Dm.HavingAdmission

/- The matrices separate the post-read walk, ordered body admission and the wired validation/
computation readers. Marked-index post-parse rejection and nested-filter state remain excluded. -/

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
  let .entity reference := (← (parseText .english target).toOption).body | none
  let source ← reference.path.toStarFieldPath?
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
  let dm : DmModel := { flat := fixture, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let report {α : Type} : Lowering α → String
    | .ok _ => "admitted"
    | .error refusal => refusal.detail
  (report (checkRule dm .english {
    group := ["Form"], name := "Selected", errorCode := "SELECTED", errorEntityRelPath := if rowBound then "../Rows/RowOut" else "../Error"
    condition := (if rowBound then "FieldFilled(Rows/RowOut) And " else "FieldFilled(Error) And ") ++ operation ++ " == 9", severity := "ERROR" }),
   report (lowerComputation fixture .english {
    group := ["Form"], name := "Selected", targetRelPath := if rowBound then "../Rows/RowOut" else "../Out", commonPrecondition := none
    alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }))

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

end A12Kernel.Dm.FilterReferenceInventoryLocks
