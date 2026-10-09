import A12Kernel.Elaboration.Flat.Condition.Surface
import A12Kernel.Elaboration.NumberEntityValueList
import A12Kernel.Elaboration.TokenEntityValueList

namespace A12Kernel

namespace BoundScalarMembership

private def read (model : FlatModel) (declaringGroup bindingGroup : GroupPath)
    (bracketed : Bool) (operand : SurfaceTextFieldOperand) : Except ResolveError FlatFieldDecl := do
  let declaration ← displaceGroupRead (do
    let declaration ← model.resolveFieldDeclarationUnchecked declaringGroup operand.reference
    if let some unbound := model.unboundReadLevel? declaringGroup bindingGroup
        declaration.repeatableScope (model.repeatableScopeForGroupPath bindingGroup) then
      throw (.unboundOperandLevel declaration.path unbound)
    pure declaration) (model.ruleGroupRead declaringGroup bindingGroup operand.reference)
  let refusal := match operand.projectionRef with
    | .stored => if bracketed then declaration.fieldValueReadRefusal? else none
    | .category _ => declaration.categoryReadRefusal?
  if let some error := refusal then throw error
  pure declaration

private def entity (operand : SurfaceTextFieldOperand) : SurfaceFieldEntityOperand :=
  .field operand.reference (match operand.projectionRef with
    | .stored => .stored | .category category => .projected category)

private def literal (model : FlatModel) (declaringGroup bindingGroup : GroupPath)
    (operator : ValueListMembershipOp) (subject : SurfaceTextFieldOperand)
    (values : Sum (List Int) (List String)) : Except ElabError FlatConditionLeaf := do
  let declaration ← (read model declaringGroup bindingGroup false subject).mapError .resolve
  pure ((← elaborateLiteralMembershipCore declaration subject.projectionRef values).condition operator)

private def fields (model : FlatModel) (declaringGroup bindingGroup : GroupPath)
    (operator : ValueListMembershipOp) (subject : SurfaceTextFieldOperand)
    (members : List SurfaceTextFieldOperand) : Except ElabError FlatConditionLeaf := do
  discard <| (checkScalarMembershipReads (read model declaringGroup bindingGroup false)
    (read model declaringGroup bindingGroup true) subject members).mapError .resolve
  let first :: rest := members | throw .emptyValueListValueFields
  let subjects : SurfaceFieldEntitySource := { first := entity subject, rest := [] }
  let values : SurfaceFieldEntitySource := { first := entity first, rest := rest.map entity }
  match elaborateNumberEntityValueListSource model declaringGroup
      { quantifier := operator.quantifier, fields := subjects, values }
      (writtenGroup := bindingGroup) (bindingGroup? := some bindingGroup) with
  | .ok source =>
      let some (subject, []) := source.fields.directFields? | throw .incoherentCore
      let some (first, rest) := source.values.directFields? | throw .incoherentCore
      pure (.numberValueList operator.quantifier [subject] (.fields (first :: rest)) .membership)
  | .error _ =>
      let source ← (elaborateTokenEntityValueListSource model declaringGroup
        { quantifier := operator.quantifier, fields := subjects, values }
        (writtenGroup := bindingGroup) (bindingGroup? := some bindingGroup)).mapError fun _ => .incoherentCore
      let some [subject] := source.fields.directFields? | throw .incoherentCore
      let some members := source.values.directFields? | throw .incoherentCore
      pure (.tokenValueList operator.quantifier [subject.operand] (.fields (members.map (·.operand))) .membership)

/-- Extend only the six existing scalar forms; retain their bracket/read gates and authored marker.
The predicate-family calibration supplies direct row-bound Number/String field-member controls. -/
def elaborate (model : FlatModel) (declaringGroup bindingGroup : GroupPath) :
    SurfaceCondition → Except ElabError FlatConditionLeaf
  | .numberValueMembership operator subject values => literal model declaringGroup bindingGroup operator (.direct subject) (.inl values)
  | .stringValueMembership operator subject values => literal model declaringGroup bindingGroup operator (.direct subject) (.inr values)
  | .enumerationValueMembership operator subject values => literal model declaringGroup bindingGroup operator subject (.inr values)
  | .numberFieldValueMembership operator subject members
  | .stringFieldValueMembership operator subject members => fields model declaringGroup bindingGroup operator (.direct subject) (members.map .direct)
  | .enumerationFieldValueMembership operator subject members => fields model declaringGroup bindingGroup operator subject members
  | _ => throw .incoherentCore

end BoundScalarMembership
end A12Kernel
