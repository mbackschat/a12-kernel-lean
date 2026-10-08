import A12Kernel.Reference.Dm.LowerCore
import A12Kernel.Semantics.StringComputation

namespace A12Kernel.Dm

/-- A String computation's operation: field reads, literals, `FieldValueAsString`, `RangeAsString`
and `+` concatenation. -/
partial def lowerStringExprWith (read : Reference → Lowering Atom)
    (selected : Expr → Lowering Atom := fun _ => refuse "StringOperand" "selection") : Expr → Lowering (StringExpr Atom String)
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
  | .arith .add left right => do pure (.concat (← lowerStringExprWith read selected left) (← lowerStringExprWith read selected right))
  | .braces body => lowerStringExprWith read selected body
  | source@(.call "FirstFilledValue" _ none none) => (.field ·) <$> selected source
  | other => refuse ("StringOperation/" ++ other.construct)

/-- Direct field/literal comparisons keep their established typed carriers; expression nodes use
this shared route on both validation and computation arms. -/
def isCompoundStringExpression : StringExpr Atom Category → Bool
  | .field _ | .category _ _ | .literal _ => false
  | _ => true

end A12Kernel.Dm
