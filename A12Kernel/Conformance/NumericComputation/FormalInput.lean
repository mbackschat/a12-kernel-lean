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
private def firstGuard := numberField 6 ["Root"] "FirstGuard"
private def secondGuard := numberField 7 ["Root"] "SecondGuard"
private def directSource := numberField 8 ["Root"] "DirectSource"

private def model : FlatModel := {
  fields := [detailsAmount, detailsCode, preferencesChoice, preferencesScore,
    target, unrelated, firstGuard, secondGuard, directSource]
}

private def surfaceGroup (path : GroupPath) : SurfaceGroupReference :=
  .path { base := .absolute, groups := path }

private def surfaceExpression : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.filledGroupCount [surfaceGroup ["Root", "Details"],
    surfaceGroup ["Root", "Preferences"]])

private def checkedOperation? : Option (CheckedNumericComputationOperation model) :=
  (elaborateNumericComputationOperation model ["Root"] target.id
    surfaceExpression).toOption

private def surfaceDirectExpression : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.field {
    base := .absolute
    groups := ["Root"]
    field := directSource.name
  })

private abbrev NumericRow := ComputationAlternative
  (CheckedNumericTargetComputationOperation model)

private def row? (guard : ComputationCondition)
    (expression : AuthoredNumericExpr SurfaceNumericAtom) : Option NumericRow := do
  let operation ← (elaborateNumericTargetComputationOperation model ["Root"]
    target.id expression).toOption
  pure { precondition := guard, operation }

private def table? : Option (CheckedNumericComputationTable model) := do
  let first ← row? (.fieldFilled firstGuard.id) surfaceExpression
  let second ← row? (.fieldNotFilled secondGuard.id) surfaceDirectExpression
  (certifyNumericComputationTable [first, second]).toOption

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

private def tableInput? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := [rejected detailsAmount.id, rejected detailsCode.id,
      rejected preferencesChoice.id, rejected preferencesScore.id,
      rejected target.id, rejected unrelated.id, rejected firstGuard.id,
      rejected secondGuard.id, rejected directSource.id]
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

/- A checked table traverses every alternative's guard and operation. The later row therefore contributes both its guard and direct operation source, while the shared target and unrelated field remain excluded. -/
example :
    (do
      let table ← table?
      let plan ← table.formalInputPlan.toOption
      let input ← tableInput?
      pure (table.fieldDependencies, plan.operandFields,
        plan.computedFields, plan.findings input)) =
      some ([detailsAmount.id, detailsCode.id, preferencesChoice.id,
        preferencesScore.id, firstGuard.id, secondGuard.id, directSource.id],
        [detailsAmount.id, detailsCode.id, preferencesChoice.id,
          preferencesScore.id, firstGuard.id, secondGuard.id, directSource.id],
        [target.id],
        [
          { address := { field := detailsAmount.id, path := [] },
            cause := .declaredConstraint },
          { address := { field := detailsCode.id, path := [] },
            cause := .declaredConstraint },
          { address := { field := preferencesChoice.id, path := [] },
            cause := .declaredConstraint },
          { address := { field := preferencesScore.id, path := [] },
            cause := .declaredConstraint },
          { address := { field := firstGuard.id, path := [] },
            cause := .declaredConstraint },
          { address := { field := secondGuard.id, path := [] },
            cause := .declaredConstraint },
          { address := { field := directSource.id, path := [] },
            cause := .declaredConstraint }
        ]) := by
  native_decide

end A12Kernel.Conformance.NumericComputation.FormalInput
