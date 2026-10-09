import A12Kernel.Reference.Dm.Validate
import A12Kernel.Elaboration.ParallelFieldRule

/-! # DM lowering for checked parallel field-pair validation -/

namespace A12Kernel.Dm

private def pairField (model : FlatModel) (group : GroupPath) (value : Bool)
    (expression : Expr) : Lowering FieldId := do
  let some path := if value then expression.fieldValue? else expression.fieldEntity?
    | refuse "ParallelRule" "plain field operand required"
  pure (← elaborated "ParallelRule" (model.resolveFieldDeclarationUnchecked group path)).id

private partial def pairSyntax (model : FlatModel) (group : GroupPath) : Expr →
    Lowering (ConditionTree (ParallelFieldLeafOf FieldId))
  | .parens body => pairSyntax model group body
  | .logic op parts => do
      let lowered ← parts.mapM (pairSyntax model group)
      match lowered with
      | [] => refuse "ParallelRule" "empty connective"
      | first :: rest => pure (rest.foldl
          (fun tree next => match op with | .and => .and tree next | .or => .or tree next) first)
  | .compare op left right => do
      let some (.ordinary comparison) := op.toNumeric?
        | refuse "ParallelRule" "ordinary Number comparison required"
      pure (.leaf (.numeric comparison (← pairField model group true left)
        (← pairField model group true right)))
  | .call name [.mk field none] none none => do
      let op ← match name with
        | "FieldFilled" => pure RepeatableFieldPresenceOperator.filled
        | "FieldNotFilled" => pure .notFilled
        | _ => refuse "ParallelRule" "unsupported unary condition"
      pure (.leaf (.presence (← pairField model group false field) op))
  | .call name [.mk left none, .mk right none] none none => do
      let some op := fieldFillOp? name | refuse "ParallelRule" "field-fill pair required"
      pure (.leaf (.fill op (← pairField model group false left) (← pairField model group false right)))
  | _ => refuse "ParallelRule" "unsupported pair condition"

private def pairReferences : ConditionTree (ParallelFieldLeafOf FieldId) → List FieldId
  | .leaf (.presence field _) => [field]
  | .leaf (.numeric _ left right) | .leaf (.fill _ left right) => [left, right]
  | .and left right | .or left right => pairReferences left ++ pairReferences right

private def bindPairLeaf (left : FieldId) : ParallelFieldLeafOf FieldId → ParallelFieldLeaf
  | .presence field op => .presence (if field == left then .left else .right) op
  | .numeric op a b => .numeric op (if a == left then .left else .right)
      (if b == left then .left else .right)
  | .fill op a b => .fill op (if a == left then .left else .right)
      (if b == left then .left else .right)

/-- Lower a two-field condition onto the public parallel carrier. A shared repeating outer scope requires a separate caller-owned dispatch plan and is refused on this root entry. -/
def checkParallelRule (model : DmModel) (language : Language) (rule : DmRule) :
    Lowering (CheckedParallelFieldRule model.flat) := do
  let text ← parseValidationText language rule.condition
  let parsedCondition ← pairSyntax model.flat rule.group text.body
  let [left, right] := (pairReferences parsedCondition).eraseDups
    | refuse "ParallelRule" "exactly two distinct field operands required"
  let errorField ← errorFieldOf language model.flat rule
  let some severity := severity? rule.severity | refuse "Severity" rule.severity
  let checked ← elaborated "ParallelRule" (checkParallelFieldRule model.flat left right errorField
    (parsedCondition.map (bindPairLeaf left)) rule.errorCode severity { parts := [] }
    (text.suppressed.contains "MVK_INVALID_COMPARE_DEC_PLACES"))
  if checked.pair.groups.commonParent != rule.group then
    refuse "ParallelRule" "declaring group must be the joined common parent"
  let outer := match checked.pair.groups.outerScopePlan with
    | .common scope => scope
    | .framed _ scope _ => scope
  if !outer.isEmpty then refuse "ParallelRule" "shared outer dispatch required"
  pure checked

/-- Preserve ordinary certificates while exposing parallel plans through a separate checked sum. -/
inductive CheckedDmValidationRule (model : FlatModel) where
  | ordinary (rule : CheckedResolvedValidationRule model)
  | parallel (rule : CheckedParallelFieldRule model)

def checkValidationRule (model : DmModel) (language : Language) (rule : DmRule)
    (world : World := { now := { epochMillis := 0 } }) : Lowering (CheckedDmValidationRule model.flat) :=
  match checkRule model language rule world with
  | .ok checked => .ok (.ordinary checked)
  | .error refusal => match checkParallelRule model language rule with
    | .ok checked => .ok (.parallel checked)
    | .error _ => .error refusal

def runValidationRule (world : World) (document : CheckedDocument model) :
    CheckedDmValidationRule model → Except String (List FlatRuleMessage)
  | .ordinary rule => runRule world document rule
  | .parallel rule => do
      let preliminary ← document.applyFullIndexPreliminary |>.mapError (fun error => (repr error).pretty)
      let rows ← rule.evalFull preliminary |>.mapError (fun error => (repr error).pretty)
      pure (rows.filterMap (·.outcome.message?))

end A12Kernel.Dm
