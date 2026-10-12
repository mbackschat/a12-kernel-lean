import A12Kernel.Reference.Dm.Validate
import A12Kernel.Elaboration.PartialParallelFieldRule
import A12Kernel.Elaboration.CheckedMessageCache

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
      let some comparison := op.toNumeric?
        | refuse "ParallelRule" "Number comparison required"
      let lower := lowerNumericExpr (pairField model group true) (pairField model group true)
      pure (.leaf (.comparison { op := comparison, left := ← lower left, right := ← lower right }))
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
  | .leaf (.comparison value) => value.left.atoms ++ value.right.atoms
  | .and left right | .or left right => pairReferences left ++ pairReferences right

private def bindPairLeaf (model : FlatModel) (left right : FieldId)
    (leaf : ParallelFieldLeafOf FieldId) : Lowering ParallelFieldLeaf := do
  let operand := fun field => do
    if field == left then pure ParallelFieldOperand.left
    else if field == right then pure .right
    else pure (.field (← elaborated "ParallelRule" (model.lookupUniqueId field)))
  match leaf with
  | .groupPresence op reference => pure (.groupPresence op reference)
  | .presence field op => pure (.presence (← operand field) op)
  | .numeric op a b => pure (.numeric op (← operand a) (← operand b))
  | .fill op a b => pure (.fill op (← operand a) (← operand b))
  | .comparison value => pure (.comparison { value with
      left := ← value.left.mapM operand, right := ← value.right.mapM operand })

private def pairGroupReferences : ConditionTree (ParallelFieldLeafOf FieldId) → List GroupPath
  | .leaf (.groupPresence _ reference) => [reference.path]
  | .leaf _ => []
  | .and left right | .or left right => pairGroupReferences left ++ pairGroupReferences right

private def bindPairCondition (model : FlatModel) (left right : FieldId) :
    ConditionTree (ParallelFieldLeafOf FieldId) → Lowering ParallelFieldCondition
  | .leaf leaf => (.leaf ·) <$> bindPairLeaf model left right leaf
  | .and a b => return .and (← bindPairCondition model left right a) (← bindPairCondition model left right b)
  | .or a b => return .or (← bindPairCondition model left right a) (← bindPairCondition model left right b)

/-- Resolve topology without inserting the anchors into the condition's authored references. -/
private def pairAnchors (model : FlatModel) (errorField : FieldId)
    (condition : ConditionTree (ParallelFieldLeafOf FieldId)) : Lowering (FieldId × FieldId) := do
  let errorDeclaration ← elaborated "ParallelRule" (model.lookupUniqueId errorField)
  let [errorGroup] := model.indexedAncestorGroups errorDeclaration
    | refuse "ParallelRule" "one indexed error ancestor required"
  let fields := (pairReferences condition).eraseDups
  let declarations ← fields.mapM fun field => elaborated "ParallelRule" (model.lookupUniqueId field)
  let far := declarations.filter fun field =>
    !errorGroup.path.isPrefixOf field.groupPath && !(model.indexedAncestorGroups field).isEmpty
  let candidates := model.repeatableGroups.filter fun candidate =>
    candidate.path != errorGroup.path && candidate.indexField.isSome &&
      (far.any (candidate.path.isPrefixOf ·.groupPath) ||
        (pairGroupReferences condition).any (candidate.path.isPrefixOf ·))
  let [candidate] := candidates
    | refuse "ParallelRule" "one opposite indexed group required"
  let some right := candidate.indexField | refuse "ParallelRule" "missing group index"
  pure (errorField, right)

/-- Lower field/group conditions onto the checked parallel carrier. The declaring group resolves paths; the condition and error target determine the joined groups and outer dispatch. -/
def checkParallelRule (model : DmModel) (language : Language) (rule : DmRule) :
    Lowering (CheckedParallelFieldRule model.flat) := do
  let text ← parseValidationText language rule.condition
  if !model.flat.hasGroupPath rule.group then refuse "ParallelRule" "unknown declaring group"
  let parsedCondition ← pairSyntax model.flat rule.group text.body
  let errorField ← errorFieldOf language model.flat rule
  let errorDeclaration ← elaborated "ErrorEntity" (model.flat.lookupUniqueId errorField)
  -- Authored reads precede pair construction: an unbound ordinary frame reports its missing
  -- wildcard, even when the error target has no indexed ancestor (ParallelValidationDispatchDiffTest,
  -- anUnrelatedFixedErrorBranchRefusesTheFramedOperandBeforeRuntime, 2026-10-12).
  discard <| (checkRawConditionBeforeGlobals model.flat rule.group errorDeclaration.groupPath
    text.body (text.suppressed.contains "MVK_INVALID_COMPARE_DEC_PLACES")).mapError
      (fun refusal => { refusal with construct := "ParallelAdmission" })
  let (left, right) ← pairAnchors model.flat errorField parsedCondition
  let some severity := severity? rule.severity | refuse "Severity" rule.severity
  let condition ← bindPairCondition model.flat left right parsedCondition
  match checkParallelFieldRule model.flat left right errorField
      condition rule.errorCode severity { parts := [] }
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
        if parallelRefusal.construct == "ParallelErrorTarget" ||
            parallelRefusal.construct == "ParallelAdmission" then .error parallelRefusal else .error refusal

/-- Execute a checked rule. Explicit cache context takes precedence; otherwise whole-population derivation supplies duplicate parallel error coordinates where its host profile settles them. Value reads are unchanged. A supplied cache remains caller-owned (spec/08 §4.3). Ordinary message-reference projection retains its separate API. -/
def runValidationRule (world : World) (document : CheckedDocument model)
    (rule : CheckedDmValidationRule model) (messageCache : Option MessageIndexCache := none) :
    Except String (List FlatRuleMessage) := match rule with
  | .ordinary rule => runRule world document rule
  | .parallel rule => do
      let preliminary ← document.applyFullIndexPreliminary |>.mapError (fun error => (repr error).pretty)
      let initial := rule.evalDocument preliminary (messageCache.map MessageIndexContext.known)
      let evaluated := match messageCache, initial with
        | none, .error (.join (.unresolvedDuplicatePointer _ _)) =>
            match preliminary.messageCacheContext with
            | .ok cache => rule.evalDocument preliminary (some cache)
            | .error _ => initial
        | _, _ => initial
      let rows ← evaluated.mapError (fun error => (repr error).pretty)
      pure (rows.filterMap (·.outcome.message?))

/-- Execute a checked parallel rule for one normalized partial call. Duplicate message coordinates share the partial cache producer while value reads retain partial unavailability. -/
def runPartialParallelRule (document : CheckedDocument model)
    (rule : CheckedParallelFieldRule model) (relevant : List RelevantEntityPattern)
    (messageCache : Option MessageIndexCache := none) : Except String (List FlatRuleMessage) := do
  let view ← document.applyPartialGeneratedPreliminary relevant |>.mapError (fun error => (repr error).pretty)
  let initial := rule.evalPartialDocument view (messageCache.map MessageIndexContext.known)
  let evaluated := match messageCache, initial with
    | none, .error (.join (.unresolvedDuplicatePointer _ _)) =>
        match view.messageCacheContext with
        | .ok cache => rule.evalPartialDocument view (some cache)
        | .error _ => initial
    | _, _ => initial
  let rows ← evaluated.mapError (fun error => (repr error).pretty)
  pure (rows.filterMap (·.outcome.message?))

end A12Kernel.Dm
