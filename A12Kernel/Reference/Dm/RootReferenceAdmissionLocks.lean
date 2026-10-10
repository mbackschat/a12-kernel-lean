import A12Kernel.Reference.Dm.Validate
import A12Kernel.Reference.Dm.Compute

namespace A12Kernel.Dm.RootReferenceAdmissionLocks

private def model : FlatModel := {
  fields := [
    { id := 1, groupPath := ["Et"], name := "Anchor", repeatableScope := [10], policy := { kind := .string } },
    { id := 2, groupPath := ["Et", "Rows"], name := "Note", repeatableScope := [10, 20], policy := { kind := .string } },
    { id := 3, groupPath := ["Et", "Rows"], name := "Qty", repeatableScope := [10, 20], policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [
    { level := 10, path := ["Et"], repeatability := some 5 },
    { level := 20, path := ["Et", "Rows"], repeatability := some 5 }] }

private def admission (condition : String) (fixture : FlatModel := model) : String :=
  let dm : DmModel := { flat := fixture, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  match checkRule dm .english {
    group := ["Et", "Rows"], name := "Root", errorCode := "ROOT", errorEntityRelPath := "../Note",
    condition, severity := "ERROR" } with
  | .ok _ => "admitted"
  | .error refusal => refusal.detail

example : model.validate.isOk = true := by native_decide

-- Retained ErrTgt P0/P4 and r1/r2 distinguish root membership from row binding.
example : ["GroupFilled(/Et)", "GroupFilled(..)",
    "FieldFilled(Note) And GroupFilled(/Et) And FieldFilled(Qty)",
    "GroupFilled(/Et/Rows) And FieldFilled(Qty)"].all
    (fun condition => admission condition == "admitted") = true := by native_decide

example : ["GroupFilled(/Et) And FieldFilled(/Et/Rows/Qty)",
    "GroupFilled(..) And FieldFilled(Qty)"].all
    (fun condition => (admission condition).startsWith "A12Kernel.FlatRuleAssemblyError.formOnlyIteration") = true := by native_decide

private def classification (fixture : FlatModel) (condition : String) : Option (Option Bool × Option Bool) := do
  let parsed ← (parseText .english condition).toOption
  let checked ← (lowerCondition fixture ["Et", "Rows"] false parsed.body).toOption
  pure (checked.core.formOnlyErrorReference? 2, checked.core.errorReferenceAt? 2 20)

example : classification model "GroupFilled(/Et)" = some (some true, some false) ∧
    classification model "GroupFilled(/Et/Rows)" = some (some false, some true) ∧
    classification model "FieldFilled(Note) And GroupFilled(/Et)" = some (some false, some true) := by native_decide

private def fixedRoot : FlatModel := { model with
  fields := model.fields.map fun field => { field with repeatableScope := field.repeatableScope.filter (· != 10) }
  repeatableGroups := model.repeatableGroups.filter (·.level != 10) }

example : fixedRoot.validate.isOk = true ∧
    admission "GroupFilled(/Et)" fixedRoot = "admitted" ∧
    (admission "GroupFilled(/Et) And FieldFilled(Qty)" fixedRoot).startsWith
      "A12Kernel.FlatRuleAssemblyError.formOnlyIteration" = true ∧
    admission "FieldFilled(Note) And GroupFilled(/Et) And FieldFilled(Qty)" fixedRoot = "admitted" := by native_decide

example : ["FieldFilled(Qty) And GroupFilled(/Et)",
    "GroupFilled(/Et) Or FieldFilled(Qty)"].all (fun condition =>
      (admission condition).startsWith "A12Kernel.FlatRuleAssemblyError.formOnlyIteration") = true := by native_decide

example : (admission "GroupNotFilled(/Et) And FieldFilled(Qty)").startsWith
    "A12Kernel.FlatRuleAssemblyError.formOnlyIteration" = true := by native_decide

example : FlatRuleAssemblyError.diagnostic? (.formOnlyIteration 2 20) =
    some .errorFieldGroupIteration4Invalid := by native_decide

example : (do
    let parsed ← (parseText .english "GroupFilled(/Et) And Sum(/Et*/Rows*/Qty) > 0").toOption
    let checked ← (lowerCondition model ["Et", "Rows"] false parsed.body).toOption
    pure (checked.core.formOnlyErrorReference? 3, checked.core.errorReferenceAt? 3 10,
      checked.core.errorReferenceAt? 3 20)) = some (some false, some true, some false) := by native_decide

example : (do
    let fixed := { model with
      fields := model.fields.map fun field => { field with repeatableScope := [] }, repeatableGroups := [] }
    let parsed ← (parseText .english "GroupFilled(/Et) And FieldFilled(Note)").toOption
    let checked ← (lowerCondition fixed ["Et", "Rows"] false parsed.body).toOption
    pure (checked.core.authoredErrorReference? 2, checked.core.formOnlyErrorReference? 2)) =
    some (some true, none) := by native_decide

end A12Kernel.Dm.RootReferenceAdmissionLocks
