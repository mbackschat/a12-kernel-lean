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

/-- A checked completed-period difference reads no cell outside the target's row binding, on
    **either** endpoint. The pair gate is what makes this worth stating separately from the
    single-field rule: a two-operand source can satisfy its own component agreement while one
    endpoint sits on an unbound level, and this rules that out for both positions at once. The
    Base-Year endpoint reads nothing, so it carries no obligation and none is claimed for it. -/
theorem addressedRepetitionComputation_differenceEndpoints_rowBound
    {model : FlatModel} {target : CheckedAddressedNumericTarget model}
    {unit : DateDifferenceUnit} {left right : ResolvedDateDifferenceOperand}
    (admitted : target.admitsRepetitionOperand (.dateDifference unit left right) = true)
    {source : FlatTemporalField} (endpoint : left = .field source ∨ right = .field source) :
    ∃ owned, model.lookupUniqueId source.id = .ok owned ∧
      owned.repetitionBoundBy target.targetDeclaration.repeatableScope = true := by
  have bound : ∀ operand : ResolvedDateDifferenceOperand, operand = .field source →
      target.admitsDateDifferenceEndpoint operand = true →
      ∃ owned, model.lookupUniqueId source.id = .ok owned ∧
        owned.repetitionBoundBy target.targetDeclaration.repeatableScope = true := by
    rintro _ rfl endpointAdmitted
    simp only [CheckedAddressedNumericTarget.admitsDateDifferenceEndpoint,
      CheckedAddressedNumericTarget.admitsSourceField] at endpointAdmitted
    cases owned : model.lookupUniqueId source.id with
    | error _ => simp [owned] at endpointAdmitted
    | ok declaration =>
        refine ⟨declaration, rfl, ?_⟩
        simp [owned] at endpointAdmitted
        exact endpointAdmitted.2
  simp only [CheckedAddressedNumericTarget.admitsRepetitionOperand, Bool.and_eq_true] at admitted
  rcases endpoint with rfl | rfl
  · exact bound _ rfl admitted.1.2
  · exact bound _ rfl admitted.2

end A12Kernel
