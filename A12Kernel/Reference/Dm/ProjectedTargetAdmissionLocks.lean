import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.ProjectedTargetAdmissionLocks

private def model : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields ++ [
    { id := 6, name := "Source", groupPath := ["Form", "Rows"],
      repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 3 }] }

private def alternative (operation : String) (guard : Option String := none) : DmAlternative := {
  operation, precondition := guard }
private def projected := "[Rows/N For \"a\"]"
private def source := "[Rows/Source For \"a\"]"
private def guard := "FieldFilled(Rows/Tag)"
private def refusal (alternatives : List DmAlternative) (common : Option String := none) (fixture : FlatModel := model) (target : String := "../Rows/N") : Option String :=
  match lowerComputation fixture .english {
    group := ["Form"], name := "SelfRead", targetRelPath := target, commonPrecondition := common,
    alternatives, errorCodesToSuppress := [] } with
  | .ok _ => none
  | .error error => some error.detail

example : model.validate.isOk = true := by native_decide

-- The retained self-read-alternative-walk-2026-10-02 grid separates projected target identity
-- from selected reads of another field and from the unconditional-alternative walk (spec/09 §6).
example : refusal [alternative source] = none := by native_decide
example : [
    ([alternative projected], none),
    ([alternative projected, alternative "[Rows/Source]"], none),
    ([alternative "[Rows/Source]", alternative projected], none),
    ([alternative projected, alternative "[Rows/N]" (some guard)], none),
    ([alternative "[Rows/N]" (some guard), alternative projected], none),
    ([alternative projected], some guard),
    ([alternative "[Rows/Source]", alternative "1"], some (projected ++ " > 0")),
    ([alternative "[Rows/Source]" (some guard), alternative "1" (some guard)], some (projected ++ " > 0"))
  ].all (fun (alternatives, common) => refusal alternatives common ==
    some KernelStaticDiagnostic.errorSemanticIndexOrCategoryForErrorField.kernelCode) = true := by native_decide

private def categoryModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 4 || field.id == 6 then
    { field with
      policy := { kind := .enumeration }
      enumeration := some {
        storedTokens := ["A", "B"]
        categories := [{ name := "Label", tokens := ["B", "A"] }] } }
  else field }

example : categoryModel.validate.isOk = true ∧
    refusal [alternative "[Rows/Source->Label]"] none categoryModel = none := by native_decide

example : [
    ([alternative "[Rows/N->Label]"], none),
    ([alternative "[Rows/N->Label]", alternative "[Rows/Source]"], none),
    ([alternative "[Rows/Source]", alternative "[Rows/N->Label]"], none),
    ([alternative "[Rows/N->Label]"], some guard),
    ([alternative "[Rows/Source]", alternative "[Rows/Source]"], some "[Rows/N->Label] == \"A\""),
    ([alternative "[Rows/Source]" (some guard), alternative "[Rows/Source]" (some guard)],
      some "[Rows/N->Label] == \"A\"")
  ].all (fun (alternatives, common) => refusal alternatives common categoryModel ==
    some KernelStaticDiagnostic.errorSemanticIndexOrCategoryForErrorField.kernelCode) = true := by native_decide

example : refusal [alternative source] (some (source ++ " > 0")) = none ∧
    refusal [alternative "[Rows/Source->Label]"]
      (some "[Rows/Source->Label] == \"A\"") categoryModel = none := by native_decide

example : [false, true].all (fun reverse =>
    let projectedAlternative := alternative projected
    let malformedAlternative := alternative "[Missing]"
    refusal (if reverse then [malformedAlternative, projectedAlternative]
      else [projectedAlternative, malformedAlternative]) ==
        some KernelStaticDiagnostic.invalidEntity.kernelCode) = true := by native_decide

-- KF182 measures the target as a semantic-index key on the copy and first-filled carriers;
-- the projected context belongs to the entire indexed reference, including its key read.
example : ["[Rows/Tag For Error]", "FirstFilledValue(Rows/Tag For Error, Error)"].all
    (fun operation => refusal [alternative operation] (target := "../Expected") == none) = true := by native_decide
example : ["[Rows/Tag For Expected]", "FirstFilledValue(Rows/Tag For Expected, Error)"].all
    (fun operation => refusal [alternative operation] (target := "../Expected") ==
      some KernelStaticDiagnostic.errorSemanticIndexOrCategoryForErrorField.kernelCode) = true := by native_decide

end A12Kernel.Dm.ProjectedTargetAdmissionLocks
