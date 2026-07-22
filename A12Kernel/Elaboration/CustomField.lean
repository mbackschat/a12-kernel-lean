import A12Kernel.Elaboration.Flat

/-! # A12Kernel.Elaboration.CustomField — checked flat custom declarations

This capsule prepares the optional registered custom metadata retained by flat String declarations. It validates the ordinary model first, resolves each exact validator name once from the explicit `World`, and returns an ordered overlay without changing ordinary declaration identity or raw-context checking.
-/

namespace A12Kernel

inductive FlatCustomFieldPreparationError where
  | model (error : ResolveError)
  | custom (error : CustomFieldTypeElabError)
  deriving Repr, DecidableEq

inductive FlatCustomFieldEvaluationError where
  | preparation (error : FlatCustomFieldPreparationError)
  | condition (error : ElabError)
  deriving Repr, DecidableEq

/-- One flat String declaration paired with its checked registered custom type. -/
structure PreparedFlatCustomField where
  declaration : FlatFieldDecl
  customType : CheckedCustomFieldType

/-- Ordered checked custom declarations over the exact original flat model. -/
structure PreparedFlatCustomFields where
  model : FlatModel
  fields : List PreparedFlatCustomField

namespace PreparedFlatCustomFields

def lookup? (prepared : PreparedFlatCustomFields) (id : FieldId) :
    Option PreparedFlatCustomField :=
  prepared.fields.find? fun field => field.declaration.id == id

/-- Compile heterogeneous raw cells through the exact prepared custom overlay. Ordinary declarations reuse their declaration-owned checker; any incoherent hand-built overlay fails closed. -/
def checkContext (prepared : PreparedFlatCustomFields) (locale : String)
    (raw : RawFlatContext) : FlatContext where
  read id :=
    match prepared.model.lookupUniqueId id with
    | .error _ => malformedCheckedCell
    | .ok declaration =>
        match prepared.lookup? id with
        | none => declaration.checkRaw (raw.read id)
        | some customField =>
            if customField.declaration == declaration then
              customField.customType.checkValueRaw locale (raw.read id)
            else
              malformedCheckedCell

end PreparedFlatCustomFields

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

/-- Prepare custom declarations, elaborate against the exact same model, and evaluate through the prepared locale-aware context. -/
def elaborateAndEvalCustomFull (model : FlatModel) (world : World)
    (locale : String) (declaringGroup : GroupPath) (raw : RawFlatContext)
    (hasContent : Bool) (condition : SurfaceCondition) :
    Except FlatCustomFieldEvaluationError Verdict := do
  let prepared ← (prepareFlatCustomFields world model).mapError .preparation
  let checked ← (elaborate model declaringGroup condition).mapError .condition
  pure (checked.core.evalFull
    ((prepared.checkContext locale raw).withWorld world) hasContent)

end A12Kernel
