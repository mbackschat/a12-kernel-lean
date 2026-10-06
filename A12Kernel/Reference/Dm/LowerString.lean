import A12Kernel.Reference.Dm.LowerEntity
import A12Kernel.Elaboration.StringExpression

namespace A12Kernel.Dm

/-- A String computation's operation: field reads, literals, `FieldValueAsString`, `RangeAsString`
and `+` concatenation. -/
private partial def lowerStringExprWith (read : Reference → Lowering Atom) : Expr → Lowering (StringExpr Atom String)
  | .string text =>
      if isTemporalConstant text then refuse "StringOperation" "temporal constant"
      else pure (.literal text)
  | .value reference => do
      let field ← read reference
      pure (match reference.category with | none => .field field | some name => .category field name)
  | .call "FieldValueAsString" [.mk (.entity reference@{ category := none, .. }) none none] none none =>
      (.fieldValueAsString ·) <$> read reference
  | .call "RangeAsString" [.mk (.entity reference@{ category := none, .. }) none none,
      .mk (.number start) none none, .mk (.number finish) none none] none none =>
      match start.toNat?, finish.toNat? with
      | some start, some finish => do pure (.range (← read reference) start finish)
      | _, _ => refuse "RangeAsString" "operand"
  | .arith .add left right => do pure (.concat (← lowerStringExprWith read left) (← lowerStringExprWith read right))
  | .braces body => lowerStringExprWith read body
  | other => refuse ("StringOperation/" ++ other.construct)

def lowerStringExpr : Expr → Lowering (StringExpr SurfaceFieldPath String) :=
  lowerStringExprWith fun reference => do
    if reference.index.isSome then refuse "StringOperand" "indexed source"
    let some path := reference.path.toFieldPath? | refuse "StringOperand" "path"
    pure path

def lowerSelectedStringExpr (model : FlatModel) (group : GroupPath) : Expr → Lowering SurfaceSelectedStringExpression :=
  lowerStringExprWith fun reference => match reference.index with
    | some key => Sum.inr <$> lowerIndexedSource model group reference.path key
    | none => do
        let some path := reference.path.toFieldPath? | refuse "StringOperand" "path"
        pure (.inl path)

/-- Direct field/literal comparisons keep their established typed carriers; expression nodes use
this shared route on both validation and computation arms. -/
def isCompoundStringExpression : StringExpr Atom Category → Bool
  | .field _ | .category _ _ | .literal _ => false
  | _ => true

def isStringExpressionComparisonOperand (expression : SurfaceSelectedStringExpression) : Bool :=
  match expression with
  | .category (.inr _) _ => true
  | _ => isCompoundStringExpression expression

end A12Kernel.Dm
