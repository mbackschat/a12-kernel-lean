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
      if let some op := (match name with
          | "GroupFilled" => some GroupPresenceOperator.filled
          | "GroupNotFilled" => some .notFilled
          | _ => none) then
        let some reference := field.groupReference? | refuse "ParallelRule" "plain group operand required"
        let resolved ← elaborated "ParallelRule" (reference.resolveAgainst group)
        pure (.leaf (.groupPresence op { resolved with
          boundRepeatableScope := model.repeatableScopeForGroupPath resolved.path }))
      else
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
  | .leaf (.groupPresence _ _) => []
  | .leaf (.presence field _) => [field]
  | .leaf (.numeric _ left right) | .leaf (.fill _ left right) => [left, right]
  | .and left right | .or left right => pairReferences left ++ pairReferences right

private def bindPairLeaf (left : FieldId) : ParallelFieldLeafOf FieldId → ParallelFieldLeaf
  | .groupPresence op reference => .groupPresence op reference
  | .presence field op => .presence (if field == left then .left else .right) op
  | .numeric op a b => .numeric op (if a == left then .left else .right)
      (if b == left then .left else .right)
  | .fill op a b => .fill op (if a == left then .left else .right)
      (if b == left then .left else .right)

private def pairGroupReferences : ConditionTree (ParallelFieldLeafOf FieldId) → List GroupPath
  | .leaf (.groupPresence _ reference) => [reference.path]
  | .leaf _ => []
  | .and left right | .or left right => pairGroupReferences left ++ pairGroupReferences right

/-- Resolve topology without inserting the anchors into the condition's authored references. -/
private def pairAnchors (model : FlatModel) (errorField : FieldId)
    (condition : ConditionTree (ParallelFieldLeafOf FieldId)) : Lowering (FieldId × FieldId) := do
  let errorDeclaration ← elaborated "ParallelRule" (model.lookupUniqueId errorField)
  let [errorGroup] := model.indexedAncestorGroups errorDeclaration
    | refuse "ParallelRule" "one indexed error ancestor required"
  let fields := (pairReferences condition).eraseDups
  let declarations ← fields.mapM fun field => elaborated "ParallelRule" (model.lookupUniqueId field)
  let far := declarations.filter fun field => !errorGroup.path.isPrefixOf field.groupPath
  let right ← match far with
    | [field] => pure field.id
    | [] =>
        let candidates := model.repeatableGroups.filter fun candidate =>
          candidate.path != errorGroup.path && candidate.indexField.isSome &&
            (pairGroupReferences condition).any (candidate.path.isPrefixOf ·)
        match candidates with
        | [candidate] => match candidate.indexField with
          | some field => pure field
          | none => refuse "ParallelRule" "missing group index"
        | _ => refuse "ParallelRule" "one opposite indexed group required"
    | _ => refuse "ParallelRule" "one payload field per side required"
  if fields.any (fun field => field != errorField && field != right) then
    refuse "ParallelRule" "one payload field per side required"
  pure (errorField, right)

/-- Lower field/group conditions onto the checked parallel carrier. The declaring group resolves paths; the condition and error target determine the joined groups and outer dispatch. -/
def checkParallelRule (model : DmModel) (language : Language) (rule : DmRule) :
    Lowering (CheckedParallelFieldRule model.flat) := do
  let text ← parseValidationText language rule.condition
  if !model.flat.hasGroupPath rule.group then refuse "ParallelRule" "unknown declaring group"
  let parsedCondition ← pairSyntax model.flat rule.group text.body
  let errorField ← errorFieldOf language model.flat rule
  let (left, right) ← pairAnchors model.flat errorField parsedCondition
  let some severity := severity? rule.severity | refuse "Severity" rule.severity
  match checkParallelFieldRule model.flat left right errorField
      (parsedCondition.map (bindPairLeaf left)) rule.errorCode severity { parts := [] }
      (text.suppressed.contains "MVK_INVALID_COMPARE_DEC_PLACES") with
  | .ok checked => pure checked
  | .error (.static diagnostic) => refuse "ParallelErrorTarget" diagnostic.kernelCode
  | .error error => elaborated "ParallelRule" (.error error : Except _ (CheckedParallelFieldRule model.flat))

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
    | .error parallelRefusal =>
        if parallelRefusal.construct == "ParallelErrorTarget" then .error parallelRefusal else .error refusal

def runValidationRule (world : World) (document : CheckedDocument model) :
    CheckedDmValidationRule model → Except String (List FlatRuleMessage)
  | .ordinary rule => runRule world document rule
  | .parallel rule => do
      let preliminary ← document.applyFullIndexPreliminary |>.mapError (fun error => (repr error).pretty)
      let rows ← rule.evalDocument preliminary |>.mapError (fun error => (repr error).pretty)
      pure (rows.filterMap (·.outcome.message?))

end A12Kernel.Dm
