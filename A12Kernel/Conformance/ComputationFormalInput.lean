import A12Kernel.Elaboration.ComputationFormalInput

/-! # Checked direct-field computation formal-input inventory locks -/

namespace A12Kernel.Conformance.ComputationFormalInput

open A12Kernel

private def numberField (id : FieldId) (name : String) : FlatFieldDecl := {
  id, name, groupPath := ["Order"], repeatableScope := []
  policy := { kind := .number { scale := 0, signed := true } }
  numericTargetConstraints := { maximum := some 0 }
}

private def operand := numberField 1 "Operand"
private def target := numberField 2 "Target"
private def finalTarget := numberField 3 "FinalTarget"
private def unrelated := numberField 4 "Unrelated"
private def model : FlatModel := {
  fields := [operand, target, finalTarget, unrelated]
}

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
    cells := [rejected operand.id, rejected target.id,
      rejected finalTarget.id, rejected unrelated.id]
  }).toOption

private def operations : List (FieldId × List FieldId) := [
  (target.id, [operand.id]),
  (finalTarget.id, [target.id, operand.id])
]

/- Authored duplicates normalize before collection, independently in the operand and computed-target sets. -/
example :
    (match checkComputationFormalInputPlan model
      [operand.id, operand.id] [target.id, target.id] with
    | .ok plan =>
        plan.operandFields == [operand.id] &&
          plan.computedFields == [target.id]
    | .error _ => false) = true := by
  native_decide

/- Unknown operand and computed-target identities retain their distinct plan roles. -/
example :
    (match checkComputationFormalInputPlan model [99] [] with
    | .error (.operandField field _) => field == 99
    | _ => false) = true := by
  native_decide

example :
    (match checkComputationFormalInputPlan model [] [99] with
    | .error (.computedField field _) => field == 99
    | _ => false) = true := by
  native_decide

/- Operation union keeps the direct source once and excludes both computed targets, including the intermediate read by its successor. -/
example :
    (do
      let plan ←
        checkComputationFormalInputOperations model operations |>.toOption
      let input ← input?
      pure (plan.operandFields.length, plan.computedFields.length,
        [plan.operandFields.contains operand.id,
          plan.operandFields.contains target.id,
          plan.computedFields.contains target.id,
          plan.computedFields.contains finalTarget.id],
        plan.findings input)) =
      some (2, 2, [true, true, true, true], [{
        address := { field := operand.id, path := [] }
        cause := .declaredConstraint
      }]) := by
  native_decide

/- Operation order does not change the extensional finding inventory. -/
example :
    (do
      let forward ←
        checkComputationFormalInputOperations model operations |>.toOption
      let reverse ←
        checkComputationFormalInputOperations model operations.reverse |>.toOption
      let input ← input?
      pure (forward.findings input, reverse.findings input)) = some ([{
        address := { field := operand.id, path := [] }
        cause := .declaredConstraint
      }], [{
        address := { field := operand.id, path := [] }
        cause := .declaredConstraint
      }]) := by
  native_decide

end A12Kernel.Conformance.ComputationFormalInput
