import A12Kernel.Elaboration.AddressedRepetitionComputation

namespace A12Kernel

/-- A structural group containing the target does not create a self-dependency. Every real field
    dependency remains a separately certified atom, excluded from the target at admission. -/
theorem addressedRepetitionComputation_excludes_target
    (operation : CheckedAddressedRepetitionComputation model) :
    operation.referencesField operation.target.targetField = false := by
  let refers : AddressedRepetitionOperand operation.target → Bool := fun atom =>
    match atom.val with
    | .field declaration => declaration.id == operation.target.targetField
    | _ => false
  have absent (source : AddressedRepetitionOperand operation.target) : refers source = false := by
    rcases source with ⟨atom, admitted⟩
    cases atom <;> simp only [refers]
    case field declaration =>
      cases owned : model.lookupUniqueId declaration.id <;>
        simp_all [CheckedAddressedNumericTarget.admitsRepetitionOperand]
  have walk (expression : AuthoredNumericExpr (AddressedRepetitionOperand operation.target)) :
      expression.anyAtom refers = false := by
    induction expression <;> simp_all [AuthoredNumericExpr.anyAtom]
  exact walk operation.expression

end A12Kernel
