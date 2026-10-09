import A12Kernel.Elaboration.Flat.Condition.Surface

namespace A12Kernel
namespace BoundTextComparison

private def operand (model : FlatModel) (declaringGroup bindingGroup : GroupPath)
    (surface : SurfaceTextFieldOperand) :
    Except ElabError (FlatFieldDecl × FlatTextFieldOperand × DirectComparableField) := do
  let declaration ← (model.resolveBoundRuleOperand declaringGroup bindingGroup true surface).mapError .resolve
  let resolved := match surface.projectionRef with
    | .stored => declaration.toTextFieldComparison?
    | projection => declaration.toEnumerationTextFieldComparison? projection
  let some (core, profile) := resolved
    | throw (.textFieldOperandKindMismatch declaration.path declaration.policy.kind.surfaceKind)
  pure (declaration, core, profile)

private def fields (model : FlatModel) (declaringGroup bindingGroup : GroupPath)
    (operator : SurfaceComparisonOp) (left right : SurfaceTextFieldOperand) : Except ElabError FlatConditionLeaf := do
  let (leftDecl, left, leftProfile) ← operand model declaringGroup bindingGroup left
  let (rightDecl, right, rightProfile) ← operand model declaringGroup bindingGroup right
  let .leaf condition ← finishTextFieldComparison operator leftDecl.path rightDecl.path
    (left, leftProfile) (right, rightProfile) | throw .incoherentCore
  pure condition

private def literal (model : FlatModel) (declaringGroup bindingGroup : GroupPath)
    (operator : SurfaceComparisonOp) (source : SurfaceTextFieldOperand)
    (expected : String) : Except ElabError FlatConditionLeaf := do
  let (declaration, core, _) ← operand model declaringGroup bindingGroup source
  match core with
  | .string field =>
      let some equality := operator.toEquality? | throw (.unsupportedOperator operator)
      pure (.compare (.string equality field expected))
  | .enumeration _ =>
      let .leaf condition ← elaborateEnumerationCore declaration operator source.projectionRef expected
        | throw .incoherentCore
      pure condition

/-- Reuse direct text comparison profiles and literal-domain checks with ordinary row-bound reads.
The fixed comparison account in spec/06 and spec/10 also owns empty/formally-invalid observations. -/
def elaborate (model : FlatModel) (declaringGroup bindingGroup : GroupPath) :
    SurfaceCondition → Except ElabError FlatConditionLeaf
  | .compare operator reference (.string expected) =>
      literal model declaringGroup bindingGroup operator (.direct reference) expected
  | .compareEnumeration operator reference projection expected =>
      literal model declaringGroup bindingGroup operator
        (match projection with | .stored => .direct reference | .category name => .category reference name) expected
  | .compareFields operator left right =>
      fields model declaringGroup bindingGroup operator (.direct left) (.direct right)
  | .compareTextFields operator left right => fields model declaringGroup bindingGroup operator left right
  | _ => throw .incoherentCore

end BoundTextComparison
end A12Kernel
