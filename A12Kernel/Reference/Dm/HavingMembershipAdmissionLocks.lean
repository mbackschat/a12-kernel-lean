import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingMembershipAdmissionLocks
open A12Kernel

private def model : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields ++ [
    { id := 6, name := "Other", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 7, name := "Text", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } },
    { id := 8, name := "RowOut", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 9, name := "N", groupPath := ["Form", "Head"],
      policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 3 }] }

private def result (body : String) (row : Bool) (fixture : FlatModel := model) : String × String :=
  HavingFixture.readerResults ("Sum(Rows*/N Having " ++ body ++ ")") fixture row

private def scalar := ["FieldValueIncludedInValueList", "FieldValueNotIncludedInValueList"]
private def quantified := ["AtLeastOneFieldValueIncludedInValueList", "NoFieldValueIncludedInValueList",
  "NotAllFieldValuesIncludedInValueList"]

example : model.validate.isOk = true ∧ [false, true].all (fun row =>
    let admitted := ("admitted", "admitted")
    scalar.all (fun op => result (op ++ "(Rows/N, [Rows/Other])") row == admitted) &&
    quantified.all (fun op => result (op ++ "(Rows/N In Rows/Other)") row == admitted)) = true := by native_decide

example : [false, true].all (fun row =>
    let duplicate := KernelStaticDiagnostic.duplicateParam1.kernelCode
    let varying := KernelStaticDiagnostic.varyingTypesNotAllowed.kernelCode
    let indexed := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    scalar.all (fun op =>
      result (op ++ "(Rows/N For \"keep\", [Rows/Other])") row == (indexed, indexed) &&
      result (op ++ "(Rows/N For \"keep\", [Rows/Tag], [Rows/N For \"keep\"])") row == (duplicate, duplicate) &&
      result (op ++ "(Rows/N For \"keep\", [Rows/Tag])") row == (varying, varying)) &&
    quantified.all (fun op =>
      result (op ++ "(Rows/N For \"keep\" In Rows/Other)") row == (indexed, indexed) &&
      result (op ++ "(Rows/N For \"keep\" In Rows/Tag, Rows/N For \"keep\")") row == (varying, varying) &&
      result (op ++ "(Rows/N For \"keep\" In Rows/N For \"keep\")") row == (duplicate, duplicate))) = true := by native_decide

example : [false, true].all (fun row =>
    let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
    let groups := KernelStaticDiagnostic.noGroupsAllowed.kernelCode
    scalar.all (fun op =>
      result (op ++ "(Rows, [Missing])") row == (missing, missing) &&
      result (op ++ "(Rows, [Rows/Other])") row == (groups, groups)) &&
    quantified.all (fun op => result (op ++ "(Rows/N, Rows/Tag In Missing)") row == (missing, missing))) = true := by native_decide

example : [false, true].all (fun row =>
    let duplicate := KernelStaticDiagnostic.duplicateParam1.kernelCode
    let varying := KernelStaticDiagnostic.varyingTypesNotAllowed.kernelCode
    scalar.all (fun op =>
      result (op ++ "(Rows/N, [Rows/N])") row == (duplicate, duplicate) &&
      result (op ++ "(Rows/N, [Rows/Tag])") row == (varying, varying)) &&
    quantified.all (fun op =>
      result (op ++ "(Rows/N In Rows/N)") row == (duplicate, duplicate) &&
      result (op ++ "(Rows/N In Rows/Tag)") row == (varying, varying))) = true := by native_decide

private def enumModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 3 || field.id == 7 then { field with policy := { kind := .enumeration }, enumeration := some {
    storedTokens := if field.id == 3 then ["keep", "drop"] else ["other"],
    categories := [{ name := "Label", tokens := if field.id == 3 then ["K", "D"] else ["O"] }] } }
  else field }

example : enumModel.validate.isOk = true ∧ [false, true].all (fun row =>
    let admitted := ("admitted", "admitted")
    let indexed := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    let types := KernelStaticDiagnostic.invalidTypesForComparison.kernelCode
    scalar.all (fun op =>
      result (op ++ "(Rows/N, 1, 2)") row == admitted &&
      result (op ++ "(Rows/N For \"keep\", 1, 2)") row == (indexed, indexed) &&
      result (op ++ "(Rows/N For \"keep\", \"1\")") row == (types, types)) &&
    quantified.all (fun op =>
      result (op ++ "(Rows/Tag, Rows/Text->Label In \"keep\", \"O\")") row enumModel == admitted &&
      result (op ++ "(Rows/Tag For \"keep\", Rows/Text->Label In \"keep\", \"O\")") row enumModel == (indexed, indexed) &&
      result (op ++ "(Rows/Tag For \"keep\", Rows/Text->Label In \"missing\")") row enumModel ==
        ("MVK_INVALID_STRING_CONSTANT_FOR_ENUMERATION_OR_CATEGORY", "MVK_INVALID_STRING_CONSTANT_FOR_ENUMERATION_OR_CATEGORY"))) = true := by native_decide

example : [false, true].all (fun row =>
    let admitted := ("admitted", "admitted")
    let domain := KernelStaticDiagnostic.invalidStringConstantForEnumeration.kernelCode
    let category := KernelStaticDiagnostic.invalidStringConstantForEnumerationCategory.kernelCode
    let unionDomain := KernelStaticDiagnostic.invalidStringConstantForEnumerationOrCategory.kernelCode
    scalar.all (fun op =>
      result (op ++ "(Rows/Tag, \"keep\")") row enumModel == admitted &&
      result (op ++ "(Rows/Tag, \"missing\")") row enumModel == (domain, domain) &&
      result (op ++ "(Rows/Tag->Label, \"K\")") row enumModel == admitted &&
      result (op ++ "(Rows/Tag->Label, \"keep\")") row enumModel == (category, category)) &&
    quantified.all (fun op =>
      result (op ++ "(Rows/Tag, Rows/Text->Label In \"missing\")") row enumModel == (unionDomain, unionDomain))) = true := by native_decide

example : [false, true].all (fun row =>
    let admitted := ("admitted", "admitted")
    let overlap := KernelStaticDiagnostic.duplicateParam2.kernelCode
    let root := KernelStaticDiagnostic.rootGroupReferenced.kernelCode
    let duplicate := KernelStaticDiagnostic.duplicateParam1.kernelCode
    quantified.all (fun op =>
      result (op ++ "(Rows/N In Head)") row == admitted &&
      result (op ++ "(Head In Head/N)") row == (overlap, overlap) &&
      result (op ++ "(Rows/N In RuleGroup)") row == (root, root) &&
      result (op ++ "(Rows/N In Rows/Tag, Rows/Tag)") row == (duplicate, duplicate))) = true := by native_decide

private def rawModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 7 then { field with stringValueMode := .raw, stringPolicy := { lineBreaksPermitted := true } } else field }

example : rawModel.validate.isOk = true ∧ [false, true].all (fun row =>
    let admitted := ("admitted", "admitted")
    let raw := KernelStaticDiagnostic.rawTypeOperandInvalid.kernelCode
    let duplicate := KernelStaticDiagnostic.duplicateParam1.kernelCode
    scalar.all (fun op =>
      result (op ++ "(Rows/Tag, [Rows/Text])") row == admitted &&
      result (op ++ "(Rows/Tag, [Rows/Text])") row rawModel == (raw, raw) &&
      result (op ++ "(Rows, [Rows/Text], [Missing])") row rawModel == (raw, raw)) &&
    quantified.all (fun op =>
      result (op ++ "(Rows/Tag In Rows/Text)") row == admitted &&
      result (op ++ "(Rows/Tag In Rows/Text)") row rawModel == (raw, raw) &&
      result (op ++ "(Rows/Tag In Rows/Text, Rows/Tag)") row rawModel == (duplicate, duplicate))) = true := by native_decide

example : [false, true].all (fun row =>
    let forbidden := KernelStaticDiagnostic.disallowedConstructInFilterCondition.kernelCode
    let unbound := KernelStaticDiagnostic.noWildcard.kernelCode
    let outer := KernelStaticDiagnostic.invalidOuterIteration.kernelCode
    let preceding := "AtLeastOneFieldFilled(Rows*/N Having FieldFilled(Rows/N)) And "
    scalar.all (fun op =>
      result (preceding ++ op ++ "(Rows/N, [Rows/Other])") row ==
        (if row then (forbidden, forbidden) else (unbound, unbound)) &&
      result (preceding ++ op ++ "($Rows/N, [Rows/Other])") row == (outer, outer)) &&
    quantified.all (fun op =>
      result (op ++ "(Rows*/N Having FieldFilled(Rows/N) In Rows/Other)") row ==
        (if row then (forbidden, forbidden) else (unbound, unbound)) &&
      result (op ++ "(Rows*/N Having FieldFilled(Rows/N) In $Rows/Other)") row == (outer, outer))) = true := by native_decide

end A12Kernel.Dm.HavingMembershipAdmissionLocks
