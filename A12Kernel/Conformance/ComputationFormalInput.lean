import A12Kernel.Elaboration.ComputationFormalInput

/-! # Checked direct-field computation formal-input inventory locks -/

namespace A12Kernel.Conformance.ComputationFormalInput

open A12Kernel

private def numberField (id : FieldId) (name : String) : FlatFieldDecl := {
  id, name, groupPath := ["Order"], repeatableScope := []
  policy := { kind := .number { scale := 0, signed := true } }
}

private def operand := numberField 1 "Operand"
private def target := numberField 2 "Target"
private def model : FlatModel := { fields := [operand, target] }

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

end A12Kernel.Conformance.ComputationFormalInput
