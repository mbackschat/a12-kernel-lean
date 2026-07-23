import A12Kernel.Elaboration.CustomField

/-! # A12Kernel.Proofs.CustomFieldElaboration — checked custom declaration laws -/

namespace A12Kernel

@[simp]
theorem prepareCustomDeclarations_empty (world : World) :
    prepareCustomDeclarations world [] = .ok [] := by
  rfl

/-- An ordinary declaration contributes no overlay entry and requires no registry lookup. -/
theorem prepareCustomDeclarations_ordinary
    (world : World) (declaration : FlatFieldDecl)
    (ordinary : declaration.customType = none) :
    prepareCustomDeclarations world [declaration] = .ok [] := by
  simp [prepareCustomDeclarations, ordinary]

/-- A registered custom declaration retains its exact flat declaration and checked validator. -/
theorem prepareCustomDeclarations_registered
    (world : World) (declaration : FlatFieldDecl)
    (customDeclaration : CustomFieldTypeDeclaration)
    (validator : RegisteredCustomFieldValidator)
    (declared : declaration.customType = some customDeclaration)
    (resolved : world.resolveCustomFieldValidator? customDeclaration.name =
      some validator) :
    prepareCustomDeclarations world [declaration] = .ok [{
      declaration
      customType := { declaration := customDeclaration, validator }
    }] := by
  simp [prepareCustomDeclarations, declared, elaborateCustomFieldType,
    requireCustomFieldValidator, resolved] <;> rfl

/-- A model-validation failure is preserved exactly and stops before custom registry preparation. -/
theorem prepareFlatCustomFields_modelError
    (world : World) (model : FlatModel) (error : ResolveError)
    (invalid : model.validate = .error error) :
    prepareFlatCustomFields world model = .error (.model error) := by
  simp [prepareFlatCustomFields, invalid] <;> rfl

end A12Kernel
