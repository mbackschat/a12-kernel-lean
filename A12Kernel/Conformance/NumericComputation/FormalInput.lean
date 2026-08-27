import A12Kernel.Elaboration.NumericComputation.FormalInput

/-! # Checked numeric-computation formal-input locks -/

namespace A12Kernel.Conformance.NumericComputation.FormalInput

open A12Kernel

private def numberField (id : FieldId) (groupPath : GroupPath)
    (name : String) : FlatFieldDecl := {
  id, groupPath, name, repeatableScope := []
  policy := { kind := .number { scale := 0, signed := true } }
  numericTargetConstraints := { maximum := some 0 }
}

private def detailsAmount := numberField 0 ["Root", "Details"] "Amount"
private def detailsCode := numberField 1 ["Root", "Details"] "Code"
private def preferencesChoice := numberField 2 ["Root", "Preferences"] "Choice"
private def preferencesScore := numberField 3 ["Root", "Preferences"] "Score"
private def target := numberField 4 ["Root"] "Target"
private def unrelated := numberField 5 ["Root"] "Unrelated"

private def model : FlatModel := {
  fields := [detailsAmount, detailsCode, preferencesChoice, preferencesScore,
    target, unrelated]
}

private def surfaceGroup (path : GroupPath) : SurfaceGroupReference :=
  .path { base := .absolute, groups := path }

private def surfaceExpression : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.filledGroupCount [surfaceGroup ["Root", "Details"],
    surfaceGroup ["Root", "Preferences"]])

private def checkedOperation? : Option (CheckedNumericComputationOperation model) :=
  (elaborateNumericComputationOperation model ["Root"] target.id
    surfaceExpression).toOption

private def rejected (field : FieldId) : ClassifiedCellInput := {
  address := { field, path := [] }
  stored := "1"
  raw := .rejected .declaredConstraint
}

private def prepared : PreparedFlatStringContext model
    builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def input? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := [rejected detailsAmount.id, rejected detailsCode.id,
      rejected preferencesChoice.id, rejected preferencesScore.id,
      rejected target.id, rejected unrelated.id]
  }).toOption

/- A fixed group-count dependency expands both operand groups to every declared member field.
   The computed target and unrelated field remain outside the collected formal-input findings. -/
example :
    (do
      let operation ← checkedOperation?
      let plan ← operation.formalInputPlan.toOption
      let input ← input?
      pure (operation.fieldDependencies, plan.operandFields,
        plan.computedFields, plan.findings input)) =
      some ([detailsAmount.id, detailsCode.id, preferencesChoice.id,
        preferencesScore.id],
        [detailsAmount.id, detailsCode.id, preferencesChoice.id,
          preferencesScore.id],
        [target.id],
        [
          { address := { field := detailsAmount.id, path := [] },
            cause := .declaredConstraint },
          { address := { field := detailsCode.id, path := [] },
            cause := .declaredConstraint },
          { address := { field := preferencesChoice.id, path := [] },
            cause := .declaredConstraint },
          { address := { field := preferencesScore.id, path := [] },
            cause := .declaredConstraint }
        ]) := by
  native_decide

end A12Kernel.Conformance.NumericComputation.FormalInput
