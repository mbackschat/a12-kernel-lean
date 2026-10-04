import A12Kernel.Reference.Dm.LowerCore
import A12Kernel.Elaboration.StringExpression

namespace A12Kernel.Dm

/-- A String computation's operation: field reads, literals, `FieldValueAsString`, `RangeAsString`
and `+` concatenation. -/
partial def lowerStringExpr : Expr → Lowering (StringExpr SurfaceFieldPath)
  | .string text =>
      if isTemporalConstant text then refuse "StringOperation" "temporal constant"
      else pure (.literal text)
  | .value { path, index := none, category := none } => match path.toFieldPath? with
      | some field => pure (.field field)
      | none => refuse "StringOperand" "path"
  | .call "FieldValueAsString" [.mk field none none] none none => match field.fieldEntity? with
      | some path => pure (.fieldValueAsString path)
      | none => refuse "FieldValueAsString" "operand"
  | .call "RangeAsString" [.mk field none none, .mk (.number start) none none,
      .mk (.number finish) none none] none none =>
      match field.fieldEntity?, start.toNat?, finish.toNat? with
      | some path, some start, some finish => pure (.range path start finish)
      | _, _, _ => refuse "RangeAsString" "operand"
  | .arith .add left right => do pure (.concat (← lowerStringExpr left) (← lowerStringExpr right))
  | .braces body => lowerStringExpr body
  | other => refuse ("StringOperation/" ++ other.construct)

/-- Direct field/literal comparisons keep their established typed carriers; expression nodes use
this shared route on both validation and computation arms. -/
def isCompoundStringExpression : StringExpr Atom → Bool
  | .field _ | .literal _ => false
  | _ => true

end A12Kernel.Dm
