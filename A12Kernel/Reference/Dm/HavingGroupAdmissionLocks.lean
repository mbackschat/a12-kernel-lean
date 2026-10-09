import A12Kernel.Reference.Dm.HavingFixture
import A12Kernel.Reference.Dm.HavingAdmission

namespace A12Kernel.Dm.HavingGroupAdmissionLocks
open A12Kernel

private def model : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields ++ [
    { id := 6, name := "Qty", groupPath := ["Form", "Rows", "Lines"], repeatableScope := [10, 20],
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 8, name := "RowOut", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 9, name := "Text", groupPath := ["Form", "Head"], policy := { kind := .string } },
    { id := 10, name := "Text", groupPath := ["Form", "Rows", "Bucket"], repeatableScope := [10], policy := { kind := .string } }]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 3 },
    { level := 20, path := ["Form", "Rows", "Lines"], repeatability := some 2 }] }

private def result (body : String) (row : Bool) (fixture : FlatModel := model) : String × String :=
  HavingFixture.readerResults ("Sum(Rows*/N Having " ++ body ++ ")") fixture row

private def many : List String := ["AllGroupsFilled", "NotAllGroupsFilled", "GroupsNotCollectivelyFilled"]
private def optional : List String := ["NoGroupFilled", "AtLeastOneGroupFilled"]

example : model.validate.isOk = true ∧
    (many ++ optional).all (fun operator => [false, true].all fun row =>
      let duplicate := KernelStaticDiagnostic.duplicateParam1.kernelCode
      let missing := KernelStaticDiagnostic.invalidEntity.kernelCode
      result (operator ++ "(Rows For \"keep\", Rows For \"keep\")") row == (duplicate, duplicate) &&
      result (operator ++ "(Rows For \"keep\", Missing)") row == (missing, missing)) = true := by native_decide

example : [false, true].all (fun row =>
    let indexed := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    let arity := KernelStaticDiagnostic.paramSizeInvalid2.kernelCode
    let star := KernelStaticDiagnostic.noWildcardsGAllowed.kernelCode
    many.all (fun operator =>
      result (operator ++ "(Rows For \"keep\")") row == (arity, arity) &&
      result (operator ++ "(Rows/Lines* For \"keep\")") row == (star, star) &&
      result (operator ++ "(Rows/N For \"keep\", Rows/Tag For \"keep\")") row == (indexed, indexed)) &&
    optional.all (fun operator => result (operator ++ "(Rows For \"keep\")") row == (indexed, indexed))) = true := by native_decide

example : ["GroupFilled", "GroupNotFilled"].all (fun operator => [false, true].all fun row =>
    let indexed := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    let fields := KernelStaticDiagnostic.noFieldsAllowed.kernelCode
    let stars := KernelStaticDiagnostic.noWildcardsAllowed.kernelCode
    let arity := KernelStaticDiagnostic.paramSizeInvalid1.kernelCode
    result (operator ++ "(Rows For \"keep\")") row == (indexed, indexed) &&
    result (operator ++ "(Rows/N For \"keep\")") row == (fields, fields) &&
    result (operator ++ "(Rows/Lines* For \"keep\")") row == (stars, stars) &&
    result (operator ++ "(Rows For \"keep\", Rows For \"drop\")") row == (arity, arity)) = true := by native_decide

private def countResult (arguments : String) (row : Bool) : String × String :=
  result ("NumberOfFilledGroups(" ++ arguments ++ ") + [Rows/N For \"keep\"] > 0") row

example : [false, true].all (fun row =>
    let indexed := KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    let fields := KernelStaticDiagnostic.noFieldsAllowed.kernelCode
    let arity := KernelStaticDiagnostic.paramSizeInvalidGN.kernelCode
    let root := KernelStaticDiagnostic.rootGroupWithOtherParameters.kernelCode
    countResult "Rows/N For \"keep\"" row == (indexed, indexed) &&
    countResult "Rows/Lines* For \"keep\"" row == (indexed, indexed) &&
    countResult "Expected" row == (fields, fields) &&
    countResult "RuleGroup" row == (arity, arity) &&
    countResult "RuleGroup, Rows For \"keep\"" row == (root, root)) = true := by native_decide

/-- These controls isolate each refusal; the indexed cases above test precedence against the
filter's later index ban (spec/07 §3 and §5). -/
example : [false, true].all (fun row =>
    let admitted := ("admitted", "admitted")
    let fields := KernelStaticDiagnostic.noFieldsAllowed.kernelCode
    let stars := KernelStaticDiagnostic.noWildcardsAllowed.kernelCode
    let arity := KernelStaticDiagnostic.paramSizeInvalid1.kernelCode
    ["GroupFilled", "GroupNotFilled"].all (fun operator =>
      result (operator ++ "(Rows/Bucket)") row == admitted &&
      result (operator ++ "(Rows/N)") row == (fields, fields) &&
      result (operator ++ "(Rows/Bucket, Head)") row == (arity, arity) &&
      result (operator ++ "(Rows/Lines*)") row == (stars, stars))) = true := by native_decide

example : [false, true].all (fun row =>
    let admitted := ("admitted", "admitted")
    let arity := KernelStaticDiagnostic.paramSizeInvalid2.kernelCode
    let duplicate := KernelStaticDiagnostic.duplicateParam1.kernelCode
    let star := KernelStaticDiagnostic.noWildcardsGAllowed.kernelCode
    many.all (fun operator =>
      result (operator ++ "(Rows/N, Rows/Tag)") row == admitted &&
      result (operator ++ "(Rows/N)") row == (arity, arity) &&
      result (operator ++ "(Rows/Lines*)") row == (star, star) &&
      result (operator ++ "(Rows/Lines*/Qty)") row == (star, star) &&
      result (operator ++ "(Rows/N, Rows/N, Rows/Tag)") row == (duplicate, duplicate)) &&
    optional.all (fun operator =>
      result (operator ++ "(Rows/Bucket)") row == admitted &&
      result (operator ++ "(Rows/Bucket, Rows/Bucket)") row == (duplicate, duplicate)) &&
    result "NumberOfFilledGroups(Rows/Lines*) > 0" row == admitted) = true := by native_decide

example : [false, true].all (fun row =>
    let forbidden := KernelStaticDiagnostic.disallowedConstructInFilterCondition.kernelCode
    let unbound := KernelStaticDiagnostic.noWildcard.kernelCode
    let outer := KernelStaticDiagnostic.invalidOuterIteration.kernelCode
    let preceding := "AtLeastOneFieldFilled(Rows*/N Having FieldFilled(Rows/N)) And "
    (many ++ optional ++ ["GroupFilled", "GroupNotFilled"]).all (fun operator =>
      let suffix := if many.contains operator then ", Head" else ""
      result (preceding ++ operator ++ "(Rows/Bucket" ++ suffix ++ ")") row ==
        (if row then (forbidden, forbidden) else (unbound, unbound)) &&
      result (preceding ++ operator ++ "($Rows/Bucket" ++ suffix ++ ")") row == (outer, outer)) &&
    result "Sum(Rows*/N Having FieldFilled(Rows/N)) + NumberOfFilledGroups(Rows/Bucket, Head) > 0" row ==
      (if row then (forbidden, forbidden) else (unbound, unbound))) = true := by native_decide

example : [false, true].all (fun row =>
    let root := KernelStaticDiagnostic.rootGroupReferenced.kernelCode
    let combined := KernelStaticDiagnostic.rootGroupWithOtherParameters.kernelCode
    many.all (fun operator => result (operator ++ "(RuleGroup, Rows For \"keep\")") row == (root, root)) &&
    optional.all (fun operator => result (operator ++ "(RuleGroup, Rows For \"keep\")") row == (combined, combined))) = true := by native_decide

private def categoryModel : FlatModel := { model with fields := model.fields.map fun field => if field.id == 3 then
  { field with policy := { kind := .enumeration }, enumeration := some {
    storedTokens := ["keep", "drop"], categories := [{ name := "Label", tokens := ["K", "D"] }] } } else field }

example : categoryModel.validate.isOk = true ∧
    [false, true].all (fun row => (many ++ optional).all fun operator =>
      let suffix := if many.contains operator then ", Rows/N" else ""
      let category := KernelStaticDiagnostic.categoryNotAllowed.kernelCode
      let duplicate := KernelStaticDiagnostic.duplicateParam1.kernelCode
      result (operator ++ "(Rows/Tag" ++ suffix ++ ")") row categoryModel == ("admitted", "admitted") &&
      result (operator ++ "(Rows/Tag->Label" ++ suffix ++ ")") row categoryModel == (category, category) &&
      result (operator ++ "(Rows/Tag->Label For \"keep\", Rows/Tag->Label For \"keep\")") row categoryModel == (duplicate, duplicate)) = true := by native_decide

example : [false, true].all (fun row =>
    let category := KernelStaticDiagnostic.categoryNotAllowed.kernelCode
    result "NumberOfFilledGroups(Rows/Tag->Label For \"keep\", Rows/Tag->Label For \"keep\") > 0" row categoryModel == (category, category)) = true := by native_decide

end A12Kernel.Dm.HavingGroupAdmissionLocks
