import A12Kernel.Reference.Dm.LowerStringCore
import A12Kernel.Reference.Dm.LowerEntity
import A12Kernel.Elaboration.StringExpression

namespace A12Kernel.Dm


def lowerStringExpr : Expr → Lowering (StringExpr SurfaceFieldPath String) :=
  lowerStringExprWith (fun reference => do
    if reference.index.isSome then refuse "StringOperand" "indexed source"
    let some path := reference.path.toFieldPath? | refuse "StringOperand" "path"
    pure path) (fun _ => refuse "StringOperand" "selection")

def lowerSelectedStringExpr (model : FlatModel) (group : GroupPath) : Expr → Lowering SurfaceSelectedStringExpression :=
  lowerStringExprWith (fun reference => match reference.index with
    | some key => Sum.inr <$> lowerIndexedSource model group reference.path key
    | none => do
        let some path := reference.path.toFieldPath? | refuse "StringOperand" "path"
        pure (.inl path)) (fun _ => refuse "StringOperand" "selection")


def isStringExpressionComparisonOperand (expression : SurfaceSelectedStringExpression) : Bool :=
  match expression with
  | .category (.inr _) _ => true
  | .group body => isStringExpressionComparisonOperand body
  | _ => isCompoundStringExpression expression

end A12Kernel.Dm
