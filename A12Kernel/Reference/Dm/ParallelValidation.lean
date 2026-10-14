import A12Kernel.Reference.Dm.Validate
import A12Kernel.Elaboration.PartialParallelFieldRule
import A12Kernel.Elaboration.CheckedMessageCache
import A12Kernel.Elaboration.ParallelFieldReference
import A12Kernel.Elaboration.ParallelInstanceView

/-! # DM lowering for checked parallel field-pair validation -/

namespace A12Kernel.Dm

private def pairPath (model : FlatModel) (group : GroupPath) (path : SurfaceFieldPath) :
    Lowering FieldId := do
  pure (← elaborated "ParallelRule" (model.resolveFieldDeclarationUnchecked group path)).id

private def pairField (model : FlatModel) (group : GroupPath) (value : Bool)
    (expression : Expr) : Lowering FieldId := do
  let some path := if value then expression.fieldValue? else expression.fieldEntity?
    | refuse "ParallelRule" "plain field operand required"
  pairPath model group path

/-- A comparison atom is a bracketed field, a temporal component of one field, or an aggregate over a direct field list. Surface shapes reuse the ordinary validation lowering, so starred, filtered and indexed operands are refused there before any pair resolution. -/
private def pairNumericAtom (model : FlatModel) (group : GroupPath) (expression : Expr) :
    Lowering (ParallelNumericAtomOf FieldId) := do
  if expression.fieldValue?.isSome then
    return .field (← pairField model group true expression)
  match ← lowerValidationNumericAtom expression with
  | .temporalFieldPart path part => pure (.temporalPart (← pairPath model group path) part)
  | .aggregate op source =>
      pure (.aggregate op (← (source.first :: source.rest).mapM (pairPath model group)))
  | _ => refuse "ParallelRule" "plain field operand required"

/-- A pair-carrier leaf, or an ordinary leaf the carrier has no form for, kept as authored with the
fields it reads until the pair's groups fix the instance view it is lowered against. -/
private inductive PairSyntaxLeaf where
  | pair (leaf : ParallelFieldLeafOf FieldId Empty)
  | ordinary (expression : Expr) (reads : List FieldId)

/-- Every plain field path an expression reads, in authored order. -/
private partial def Expr.fieldPaths : Expr → List SurfaceFieldPath
  | .value reference | .entity reference => reference.path.toFieldPath?.toList
  | .call _ arguments listed _ =>
      (arguments ++ listed.getD []).flatMap fun (.mk expression rangeEnd) =>
        expression.fieldPaths ++ (rangeEnd.map Expr.fieldPaths).getD []
  | .arith _ left right | .compare _ left right => left.fieldPaths ++ right.fieldPaths
  | .braces body | .parens body => body.fieldPaths
  | .logic _ parts => parts.flatMap Expr.fieldPaths
  | .number _ | .string _ | .constant _ | .custom _ _ => []

private partial def pairSyntax (model : FlatModel) (group : GroupPath) : Expr →
    Lowering (ConditionTree PairSyntaxLeaf)
  | .parens body => pairSyntax model group body
  | .logic op parts => do
      let lowered ← parts.mapM (pairSyntax model group)
      match lowered with
      | [] => refuse "ParallelRule" "empty connective"
      | first :: rest => pure (rest.foldl
          (fun tree next => match op with | .and => .and tree next | .or => .or tree next) first)
  | expression@(.compare op left right) => do
      -- The pair carrier owns Number comparisons; any other comparison is an ordinary leaf over the
      -- joined instance (parallel-flat-leaves capture, 2026-10-14).
      let lower := lowerNumericExpr (pairNumericAtom model group) ((.field ·) <$> pairField model group true ·)
      let numeric : Lowering (ConditionTree PairSyntaxLeaf) := do
        let some comparison := op.toNumeric? | refuse "ParallelRule" "Number comparison required"
        let value : NumericComparisonOf (ParallelNumericAtomOf FieldId) :=
          { op := comparison, left := ← lower left, right := ← lower right }
        let plain := (value.left.atoms ++ value.right.atoms).filterMap fun
          | .field field => some field
          | _ => none
        if plain.all fun field => ((model.lookupUniqueId field).toOption.bind (·.toNumberField?)).isSome then
          pure (.leaf (.pair (.comparison value)))
        else refuse "ParallelRule" "Number comparison required"
      tryCatch numeric fun _ => ordinary expression
  | .call name [.mk field none] none none => do
      if let some op := (match name with
          | "GroupFilled" => some GroupPresenceOperator.filled
          | "GroupNotFilled" => some .notFilled
          | _ => none) then
        -- A keyed group read selects a row of a group the join does not bind, so it stays an
        -- ordinary leaf (keyed-membership capture, rows p00-p02, 2026-10-13).
        let some reference := field.groupReference? | pure (.leaf (.ordinary (.call name [.mk field none] none none) []))
        let resolved ← elaborated "ParallelRule" (reference.resolveAgainst group)
        pure (.leaf (.pair (.groupPresence op { resolved with
          boundRepeatableScope := model.repeatableScopeForGroupPath resolved.path })))
      else
       match name with
        | "FieldFilled" => pure (.leaf (.pair (.presence (← pairField model group false field) .filled)))
        | "FieldNotFilled" => pure (.leaf (.pair (.presence (← pairField model group false field) .notFilled)))
        | _ => ordinary (.call name [.mk field none] none none)
  | expression@(.call name [.mk left none, .mk right none] none none) => do
      let some op := fieldFillOp? name | ordinary expression
      pure (.leaf (.pair (.fill op (← pairField model group false left) (← pairField model group false right))))
  | .custom name quoted => do
      let spelling := if quoted then CustomConditionNameSpelling.quoted name else .unquoted name
      let some checkedName := checkCustomConditionName (fun _ => false) spelling
        | refuse "CustomCondition" "invalid name"
      pure (.leaf (.pair (.customCondition checkedName)))
  | expression => ordinary expression
where
  /-- A leaf the pair carrier has no form for, kept with the fields it reads. -/
  ordinary (expression : Expr) : Lowering (ConditionTree PairSyntaxLeaf) := do
    let reads ← expression.fieldPaths.mapM (pairPath model group)
    if reads.isEmpty then refuse "ParallelRule" "unsupported pair condition"
    pure (.leaf (.ordinary expression reads.eraseDups))

private def pairReferences : ConditionTree PairSyntaxLeaf → List FieldId
  | .leaf (.pair (.groupPresence _ _)) => []
  | .leaf (.pair (.presence field _)) => [field]
  | .leaf (.pair (.numeric _ left right)) | .leaf (.pair (.fill _ left right)) => [left, right]
  | .leaf (.pair (.comparison value)) => (value.left.atoms ++ value.right.atoms).flatMap (·.operands)
  | .leaf (.pair (.customCondition _)) | .leaf (.pair (.keyed _)) => []
  | .leaf (.pair (.flat _ reads)) | .leaf (.ordinary _ reads) => reads
  | .and left right | .or left right => pairReferences left ++ pairReferences right

/-- The repeatable groups the two anchors index, which one joined instance binds. -/
private def pairGroupPaths (model : FlatModel) (left right : FieldId) : List GroupPath :=
  [left, right].filterMap fun anchor => (model.lookupUniqueId anchor).toOption.bind fun declaration =>
    (model.indexedAncestorGroups declaration).getLast?.map (·.path)

private def bindPairLeaf (model : FlatModel) (group : GroupPath) (suppress : Bool) (left right : FieldId) :
    PairSyntaxLeaf → Lowering (ParallelFieldLeaf model)
  | .pair leaf => bindPair leaf
  | .ordinary expression _ => do
      -- The ordinary reader lowers the leaf against the instance view; only a flat leaf, whose
      -- operands are model-free field records, crosses back to the real model. A keyed group read
      -- reads no joined field, so it is lowered against the model itself, where admission places it
      -- beside the join.
      let view := model.parallelInstanceView (pairGroupPaths model left right)
      match (← lowerCondition view group suppress expression).core with
      | .leaf (.flat condition) =>
          bindPair (.flat condition (model.fields.filterMap fun declaration =>
            if condition.referencesField declaration.id then some declaration.id else none))
      | .leaf (.keyedGroupPresence ..) =>
          match (← lowerCondition model group suppress expression).core with
          | .leaf (.keyedGroupPresence operator source) => pure (.keyed { operator, source })
          | _ => refuse "ParallelRule" "unsupported pair condition"
      | _ => refuse "ParallelRule" "unsupported pair condition"
where
  bindPair (leaf : ParallelFieldLeafOf FieldId Empty) : Lowering (ParallelFieldLeaf model) := do
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
        left := ← value.left.mapM (·.mapM operand), right := ← value.right.mapM (·.mapM operand) })
    | .customCondition name => pure (.customCondition name)
    | .flat condition reads => pure (.flat condition (← reads.mapM operand))
    | .keyed leaf => nomatch leaf

private def pairGroupReferences : ConditionTree PairSyntaxLeaf → List GroupPath
  | .leaf (.pair (.groupPresence _ reference)) => [reference.path]
  | .leaf _ => []
  | .and left right | .or left right => pairGroupReferences left ++ pairGroupReferences right

private def bindPairCondition (model : FlatModel) (group : GroupPath) (suppress : Bool) (left right : FieldId) :
    ConditionTree PairSyntaxLeaf → Lowering (ParallelFieldCondition model)
  | .leaf leaf => (.leaf ·) <$> bindPairLeaf model group suppress left right leaf
  | .and a b => do
      let a ← bindPairCondition model group suppress left right a
      pure (.and a (← bindPairCondition model group suppress left right b))
  | .or a b => do
      let a ← bindPairCondition model group suppress left right a
      pure (.or a (← bindPairCondition model group suppress left right b))

/-- Resolve topology without inserting the anchors into the condition's authored references. -/
private def pairAnchors (model : FlatModel) (errorField : FieldId)
    (condition : ConditionTree PairSyntaxLeaf) : Lowering (FieldId × FieldId) := do
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
  let condition ← bindPairCondition model.flat rule.group
    (text.suppressed.contains "MVK_INVALID_COMPARE_DEC_PLACES") left right parsedCondition
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
      let initial := rule.evalDocument preliminary (messageCache.map MessageIndexContext.known) (world := some world)
      let evaluated := match messageCache, initial with
        | none, .error (.join (.unresolvedDuplicatePointer _ _)) =>
            match preliminary.messageCacheContext with
            | .ok cache => rule.evalDocument preliminary (some cache) (world := some world)
            | .error _ => initial
        | _, _ => initial
      let rows ← evaluated.mapError (fun error => (repr error).pretty)
      pure (rows.filterMap (·.outcome.message?))

/-- Every message a checked parallel rule fires in full validation, with the projection of its reference
channels at the row it fired on. Evaluation uses the document's message cache whenever it is derivable, as the
ordinary projection does; the cache only decides pointers of a duplicate-key side, so rows without one are
unaffected. A projection failure stays with its message instead of failing the run. -/
def runParallelRuleReferences (document : CheckedDocument model) (rule : CheckedParallelFieldRule model)
    (world : Option World := none) :
    Except String (List (FlatRuleMessage × Except ParallelReferenceError ValidationMessageReferences)) := do
  let preliminary ← document.applyFullIndexPreliminary |>.mapError (fun error => (repr error).pretty)
  let cache := preliminary.messageCacheContext.toOption
  let inputs := preliminary.messageReferenceInputs.toOption
  let rows ← rule.evalDocument preliminary cache (world := world) |>.mapError (fun error => (repr error).pretty)
  pure (rows.filterMap fun row => row.outcome.message?.map fun message =>
    (message, rule.condition.messageReferences rule.pair row.row row.outerEnvironment cache message inputs))

/-- Execute a checked parallel rule for one normalized partial call. Duplicate message coordinates share the partial cache producer while value reads retain partial unavailability. -/
def runPartialParallelRule (document : CheckedDocument model)
    (rule : CheckedParallelFieldRule model) (relevant : List RelevantEntityPattern)
    (messageCache : Option MessageIndexCache := none) (world : Option World := none) :
    Except String (List FlatRuleMessage) := do
  let view ← document.applyPartialGeneratedPreliminary relevant |>.mapError (fun error => (repr error).pretty)
  let initial := rule.evalPartialDocument view (messageCache.map MessageIndexContext.known) (world := world)
  let evaluated := match messageCache, initial with
    | none, .error (.join (.unresolvedDuplicatePointer _ _)) =>
        match view.messageCacheContext with
        | .ok cache => rule.evalPartialDocument view (some cache) (world := world)
        | .error _ => initial
    | _, _ => initial
  let rows ← evaluated.mapError (fun error => (repr error).pretty)
  pure (rows.filterMap (·.outcome.message?))

end A12Kernel.Dm
