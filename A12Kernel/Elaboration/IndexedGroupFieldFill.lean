import A12Kernel.Elaboration.SemanticIndex
import A12Kernel.Elaboration.FieldEntityList

namespace A12Kernel

/-- The two reviewed field-fill carriers that accept one index-selected group followed by one direct
field. Keeping the operator closed here prevents the static admission from transferring to another
quantifier ([checkpoint](../../docs/SOURCES.md#src-pr2-semantic-index-carrier-matrix)). -/
inductive IndexedGroupFieldFillOperator where
  | allFieldsFilled
  | noFieldFilled
  deriving Repr, DecidableEq

/-- The exact reviewed indexed-group/direct-field authoring shape. Stars, filters, selected fields,
additional operands, and reversed order have no representation in this certificate
([checkpoint](../../docs/SOURCES.md#src-pr2-semantic-index-carrier-matrix)). -/
structure SurfaceIndexedGroupFieldFillPair where
  operator : IndexedGroupFieldFillOperator
  group : SurfaceGroupPath
  token : String
  field : SurfaceFieldPath
  deriving Repr, DecidableEq

inductive IndexedGroupFieldFillPairElabError where
  | groupReference (error : SingleGroupElabError)
  | semanticIndex (error : SemanticIndexElabError)
  | fieldEntity (error : FieldEntityShapeElabError)
  | incoherentCore
  deriving Repr, DecidableEq

/-- Static authoring certificate for the reviewed indexed-group/direct-field pair. It retains the
operator and authored order together with the selected group, index declaration, exact-text key, and
direct nonrepeatable field; it supplies no field-fill evaluator. -/
structure CheckedIndexedGroupFieldFillPair (model : FlatModel) where
  operator : IndexedGroupFieldFillOperator
  groupPath : GroupPath
  token : String
  selection : CheckedSemanticIndexSelection model
  field : FlatFieldDecl
  groupSelected : (selection.group.path == groupPath) = true
  keyRetained : (selection.key == .literal (.text token)) = true
  fieldOwned : model.fields.contains field = true
  fieldNonrepeatable : field.repeatableScope.isEmpty = true
  fieldOutsideSelection : (!selection.group.path.isPrefixOf field.groupPath) = true

/-- Certify the reviewed `AllFieldsFilled`/`NoFieldFilled` indexed-group pair. Group selection and
direct-field resolution reuse their existing checked owners, while this carrier retains order and
prevents the direct operand from collapsing into the selected group's expansion. Runtime truth and
polarity remain outside the certificate. -/
def elaborateIndexedGroupFieldFillPair (model : FlatModel)
    (declaringGroup : GroupPath) (authored : SurfaceIndexedGroupFieldFillPair)
    (writtenGroup : GroupPath := declaringGroup) :
    Except IndexedGroupFieldFillPairElabError
      (CheckedIndexedGroupFieldFillPair model) :=
  match model.validate with
  | .error error => .error (.semanticIndex (.resolve error))
  | .ok () => do
      let checkedGroup ← elaborateTextSemanticIndexGroupSelection model
        declaringGroup authored.group authored.token |>.mapError (fun
          | .group error => .groupReference error
          | error => .semanticIndex error)
      let resolvedField ← resolveFieldEntityOperandIn model declaringGroup []
        (.field authored.field .stored) (writtenGroup := writtenGroup) |>.mapError .fieldEntity
      let field ← match resolvedField with
        | .field declaration .stored => pure declaration
        | _ => throw .incoherentCore
      if hOwned : model.fields.contains field = true then
        if hNonrepeatable : field.repeatableScope.isEmpty = true then
          if hOutside :
              (!checkedGroup.selection.group.path.isPrefixOf field.groupPath) = true then
            pure {
              operator := authored.operator
              groupPath := checkedGroup.groupPath
              token := checkedGroup.token
              selection := checkedGroup.selection
              field
              groupSelected := checkedGroup.groupSelected
              keyRetained := checkedGroup.keyRetained
              fieldOwned := hOwned
              fieldNonrepeatable := hNonrepeatable
              fieldOutsideSelection := hOutside }
          else
            throw .incoherentCore
        else
          throw .incoherentCore
      else
        throw .incoherentCore

end A12Kernel
