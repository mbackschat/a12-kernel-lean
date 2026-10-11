import A12Kernel.Reference.Dm.Compute

namespace A12Kernel.Dm.StringAlternativeAdmissionLocks

private def model : FlatModel := { fields := [
  { id := 0, name := "Out", groupPath := ["Form"], policy.kind := .string },
  { id := 1, name := "Input", groupPath := ["Form"], policy.kind := .string },
  { id := 2, name := "N", groupPath := ["Form"], policy.kind := .number { scale := 0, signed := true } }] }

private def alternative (operation : String) (guard : Option String := none) : DmAlternative := {
  operation, precondition := guard }

private def refusal (alternatives : List DmAlternative)
    (common : Option String := none) : Option String :=
  match lowerComputation model .english {
      group := ["Form"], name := "Copy", targetRelPath := "../Out",
      commonPrecondition := common, alternatives, errorCodesToSuppress := [] } with
  | .ok _ => none
  | .error error =>
      if (error.detail.splitOn "targetSelfReference").length > 1 ||
          (error.detail.splitOn "guardTargetReference").length > 1 ||
          error.detail == "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD" then some "target-read"
      else if (error.detail.splitOn "unguardedAlternative").length > 1 ||
          error.detail == "MVK_ERROR_EMPTY_PRECONDITION" then some "empty-precondition"
      else some error.detail

private def field (name : String) : StringExpr SurfaceFieldPath String :=
  .field { base := .relative 0, groups := [], field := name }

private def coreRefusal
    (alternatives : List (Option (CheckedComputationCondition model) × StringExpr SurfaceFieldPath String))
    (common : Option (CheckedComputationCondition model) := none) :
    Option StringComputationTableElabError :=
  match elaborateStringComputationTable model ["Form"] 0 alternatives common with
  | .ok _ => none
  | .error error => some error

example : refusal [alternative "[Input]"] = none := by native_decide
example : refusal [alternative "[Out]"] = some "target-read" := by native_decide
example : refusal [alternative "[Input]" (some "FieldFilled(Input)"),
    alternative "\"fallback\"" (some "FieldNotFilled(Input)")] = none := by native_decide
example : refusal [alternative "[Out]", alternative "[Input]"] = some "empty-precondition" := by native_decide
example : refusal [alternative "[Out]", alternative "[Input]" (some "FieldFilled(Input)")] =
    some "empty-precondition" := by native_decide
example : refusal [alternative "[Input]", alternative "[Out]"] (some "FieldFilled(Out)") =
    some "empty-precondition" := by native_decide
example : refusal [alternative "[Out]" (some "FieldFilled(Input)"), alternative "[Input]"] =
    some "target-read" := by native_decide
example : refusal [alternative "[Input]"] (some "FieldFilled(Out)") =
    some "target-read" := by native_decide
example : refusal [alternative "[Input]" (some "FieldFilled(Input)"), alternative "[Input]"]
    (some "FieldFilled(Out)") = some "target-read" := by native_decide
example : refusal [alternative "[Input]" (some "FieldFilled(Out)"),
    alternative "[Input]" (some "FieldFilled(Input)")] = some "target-read" := by native_decide
example : refusal [alternative "[Input]", alternative "[Input]" (some "FieldFilled(Out)")] =
    some "empty-precondition" := by native_decide

example : refusal [alternative "[N]", alternative "[Input]"] =
    refusal [alternative "[N]"] := by native_decide
example : refusal [alternative "[Input]", alternative "[N]"] =
    refusal [alternative "[N]"] := by native_decide
example : refusal [alternative "[Out]", alternative "[N]" (some "FieldFilled(Input)")] =
    refusal [alternative "[N]"] := by native_decide

example : refusal [alternative "[N]", alternative "True"] =
    refusal [alternative "[N]"] := by native_decide
example : refusal [alternative "True", alternative "[N]"] =
    refusal [alternative "True"] := by native_decide
example : refusal [alternative "[N]"] ≠ none ∧ refusal [alternative "True"] ≠ none ∧
    refusal [alternative "[N]"] ≠ refusal [alternative "True"] := by native_decide

example : coreRefusal [(none, field "Out"), (none, field "Input")] =
    some (.table (.unguardedAlternative 1)) := by native_decide
example : coreRefusal [(some (.fieldFilled 1), field "Input"), (none, field "Out")] =
    some (.table (.unguardedAlternative 2)) := by native_decide
example : coreRefusal [(none, field "Out")] =
    some (.operation 1 (.targetSelfReference 0)) := by native_decide
example : coreRefusal [(some (.fieldFilled 1), field "Out"), (none, field "Input")] =
    some (.operation 1 (.targetSelfReference 0)) := by native_decide
example : coreRefusal [(some (.fieldFilled 1), field "Input"),
    (some (.fieldFilled 0), field "Input")] =
    some (.table (.guardTargetReference 2)) := by native_decide
example : coreRefusal [(some (.fieldFilled 1), field "Input"), (none, field "Input")]
    (some (.fieldFilled 0)) = some (.table (.guardTargetReference 1)) := by native_decide
example : coreRefusal [(none, field "Input"), (some (.fieldFilled 1), field "Input")]
    (some (.fieldFilled 0)) = some (.table (.unguardedAlternative 1)) := by native_decide
example : coreRefusal [(none, field "Input"), (none, field "Out")]
    (some (.fieldFilled 0)) = some (.table (.unguardedAlternative 1)) := by native_decide
example : coreRefusal [(none, field "Input"), (some (.fieldFilled 99), field "Input")] =
    some (.table (.guardNotAdmitted 2)) := by native_decide
example : coreRefusal [(none, field "Input"), (none, field "N")] =
    some (.operation 2 (.copyComparison ["Form", "Out"] ["Form", "N"] (.kindArm .text))) :=
  by native_decide
example : (coreRefusal [(none, field "Out"), (none, field "Input")]).bind (·.diagnostic?) =
    some .errorEmptyPrecondition := by native_decide
example : (coreRefusal [(none, field "Out")]).bind (·.diagnostic?) =
    some .errorReferenceToCalculatedField := by native_decide

end A12Kernel.Dm.StringAlternativeAdmissionLocks
