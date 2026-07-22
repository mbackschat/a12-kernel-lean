import A12Kernel.Elaboration.Flat

/-! # A12Kernel.Elaboration.CustomField — checked flat custom declarations

This capsule prepares the optional registered custom metadata retained by flat String declarations. It validates the ordinary model first, resolves each exact validator name once from the explicit `World`, and returns an ordered overlay without changing ordinary declaration identity or raw-context checking.
-/

namespace A12Kernel

inductive FlatCustomFieldPreparationError where
  | model (error : ResolveError)
  | custom (error : CustomFieldTypeElabError)
  deriving Repr, DecidableEq

/-- One flat String declaration paired with its checked registered custom type. -/
structure PreparedFlatCustomField where
  declaration : FlatFieldDecl
  customType : CheckedCustomFieldType

/-- Ordered checked custom declarations over the exact original flat model. -/
structure PreparedFlatCustomFields where
  model : FlatModel
  fields : List PreparedFlatCustomField

def prepareCustomDeclarations (world : World) :
    List FlatFieldDecl →
      Except FlatCustomFieldPreparationError (List PreparedFlatCustomField)
  | [] => .ok []
  | declaration :: rest =>
      match declaration.customType with
      | none => prepareCustomDeclarations world rest
      | some customDeclaration => do
          let customType ←
            (elaborateCustomFieldType world customDeclaration).mapError .custom
          let preparedRest ← prepareCustomDeclarations world rest
          pure ({ declaration, customType } :: preparedRest)

/-- Validate the flat model and resolve every declared custom String validator once. -/
def prepareFlatCustomFields (world : World) (model : FlatModel) :
    Except FlatCustomFieldPreparationError PreparedFlatCustomFields :=
  match model.validate with
  | .error error => .error (.model error)
  | .ok () =>
      match prepareCustomDeclarations world model.fields with
      | .error error => .error error
      | .ok fields => .ok { model, fields }

end A12Kernel
