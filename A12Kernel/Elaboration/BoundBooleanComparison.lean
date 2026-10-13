import A12Kernel.Elaboration.Flat.Condition.Surface
import A12Kernel.Elaboration.ScalarFieldComparison

/-! # Row-bound Boolean and Confirm comparisons

A rule compares a Boolean or Confirm field with `True`, or two such fields, at the row its iteration
binds. Both forms reuse the arms the fixed comparison already owns: the literal arm shared with the
flat elaborator, and the pair arm that computation guards share. Only the read differs: an operand
resolves at its lexical origin under the separately supplied row binding, as the other row-bound rule
carriers read theirs.
-/

namespace A12Kernel

inductive BoundBooleanComparisonElabError where
  | literal (error : ElabError)
  | pair (error : ScalarFieldComparisonElabError)
  deriving Repr

namespace BoundBooleanComparison

private def read (model : FlatModel) (declaringGroup bindingGroup : GroupPath)
    (reference : SurfaceFieldPath) : Except ResolveError FlatFieldDecl :=
  model.resolveBoundRuleOperand declaringGroup bindingGroup true (.direct reference)

private def readsBooleanKind (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) : Bool :=
  match model.resolveFieldDeclarationUnchecked declaringGroup reference with
  | .ok declaration =>
      match declaration.policy.kind with
      | .boolean | .confirm => true
      | _ => false
  | .error _ => false

/-- Whether a comparison names a Boolean or Confirm field, which this carrier alone answers. A pair
of other kinds, or a comparison of a field of another kind with `True`, stays with the carriers that
own it, so their refusal is not displaced. -/
def readsBooleanField (model : FlatModel) (declaringGroup : GroupPath) : SurfaceCondition → Bool
  | .compare _ reference _ => readsBooleanKind model declaringGroup reference
  | .compareFields _ left right =>
      readsBooleanKind model declaringGroup left || readsBooleanKind model declaringGroup right
  | _ => false

/-- Elaborate a comparison that names a Boolean or Confirm field, with its operands read at the row
`bindingGroup` binds. -/
def elaborate (model : FlatModel) (declaringGroup bindingGroup : GroupPath) :
    SurfaceCondition → Except BoundBooleanComparisonElabError FlatConditionLeaf
  | .compare operator reference literal => do
      let declaration ← (read model declaringGroup bindingGroup reference).mapError (.literal ∘ .resolve)
      let .leaf condition ← (elaborateBooleanLiteralCore declaration operator literal).mapError .literal
        | throw (.literal .incoherentCore)
      pure condition
  | .compareFields operator left right => do
      match ← (elaborateScalarFieldComparisonWith model (read model declaringGroup bindingGroup)
          (model.repeatableScopeForGroupPath bindingGroup) operator left right).mapError .pair with
      | .boolean source => pure (.compare source.toFlat)
      | .range _ => throw (.literal .incoherentCore)
  | _ => throw (.literal .incoherentCore)

end BoundBooleanComparison
end A12Kernel
