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
structure PreparedFlatCustomFields (model : FlatModel) where
  fields : List PreparedFlatCustomField

namespace PreparedFlatCustomFields

def lookup? (prepared : PreparedFlatCustomFields model) (id : FieldId) :
    Option PreparedFlatCustomField :=
  prepared.fields.find? fun field => field.declaration.id == id

/-- Overlay exact prepared custom declarations on an already checked context. Missing required entries and every forged declaration/type mismatch fail closed. -/
def checkContextOver (prepared : PreparedFlatCustomFields model)
    (locale : String) (fallback : FlatContext)
    (raw : RawFlatContext) : FlatContext where
  read id :=
    match model.lookupUniqueId id with
    | .error _ => malformedCheckedCell
    | .ok declaration =>
        match prepared.lookup? id with
        | none =>
            if declaration.customType.isSome then
              malformedCheckedCell
            else
              fallback.read id
        | some customField =>
            if customField.declaration == declaration &&
                declaration.customType ==
                  some customField.customType.declaration then
              customField.customType.checkValueRaw locale (raw.read id)
            else
              malformedCheckedCell

/-- Compile heterogeneous raw cells through the exact prepared custom overlay while ordinary declarations retain the model-owned checker. -/
def checkContext (prepared : PreparedFlatCustomFields model) (locale : String)
    (raw : RawFlatContext) : FlatContext :=
  prepared.checkContextOver locale (model.checkContext raw) raw

end PreparedFlatCustomFields

def prepareCustomDeclarations (world : World) :
    List FlatFieldDecl →
      Except CustomFieldTypeElabError (List PreparedFlatCustomField)
  | [] => .ok []
  | declaration :: rest =>
      match declaration.customType with
      | none => prepareCustomDeclarations world rest
      | some customDeclaration => do
          let customType ← elaborateCustomFieldType world customDeclaration
          let preparedRest ← prepareCustomDeclarations world rest
          pure ({ declaration, customType } :: preparedRest)

/-- Validate the flat model and resolve every declared custom String validator once. -/
def prepareFlatCustomFields (world : World) (model : FlatModel) :
    Except FlatCustomFieldPreparationError (PreparedFlatCustomFields model) :=
  match model.validate with
  | .error error => .error (.model error)
  | .ok () =>
      match prepareCustomDeclarations world model.fields with
      | .error error => .error (.custom error)
      | .ok fields => .ok { fields }

end A12Kernel
