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
    Lowering (ParallelNumericAtomOf FieldId Expr) := do
  if expression.fieldValue?.isSome then
    return .field (← pairField model group true expression)
  match ← lowerValidationNumericAtom expression with
  | .temporalFieldPart path part => pure (.temporalPart (← pairPath model group path) part)
  | .aggregate op source =>
      pure (.aggregate op (← (source.first :: source.rest).mapM (pairPath model group)))
  | _ => refuse "ParallelRule" "plain field operand required"

/-- A pair-carrier leaf, or an ordinary leaf the carrier has no form for, kept as authored with the
fields it reads until the pair's groups fix the instance view it is lowered against. A comparison
also keeps its reading with an ordinary atom for each operand the carrier has no form for, which
applies when no binding fixes the whole comparison. -/
private inductive PairSyntaxLeaf where
  | pair (leaf : ParallelFieldLeafOf FieldId Empty Expr)
  | ordinary (expression : Expr) (reads : List FieldId)
      (mixed : Option (ParallelFieldLeafOf FieldId Empty Expr) := none)

/-- Every plain field path an expression reads, in authored order. A starred, keyed or filtered
reference reads no single field of a joined row; a star below a joined group anchors the join
through its prefix instead (`Expr.starredReadPrefixes`). -/
private partial def Expr.fieldPaths : Expr → List SurfaceFieldPath
  | .value reference | .entity reference =>
      if reference.index.isSome || reference.filter.isSome || reference.path.segments.any (·.star) then []
      else reference.path.toFieldPath?.toList
  | .call _ arguments listed _ =>
      (arguments ++ listed.getD []).flatMap fun (.mk expression rangeEnd) =>
        expression.fieldPaths ++ (rangeEnd.map Expr.fieldPaths).getD []
  | .arith _ left right | .compare _ left right => left.fieldPaths ++ right.fieldPaths
  | .braces body | .parens body => body.fieldPaths
  | .logic _ parts => parts.flatMap Expr.fieldPaths
  | .number _ | .string _ | .constant _ | .custom _ _ => []

/-- The unstarred prefix of every unkeyed starred read, in authored order. A star below a joined
group still reads that group's joined row, so the prefix anchors the join (parallel-child capture,
`r02`, 2026-10-14); a prefix of the error side's or an unjoined group anchors nothing. -/
private partial def Expr.starredReadPrefixes : Expr → List Path
  | .value reference | .entity reference =>
      let unstarred := reference.path.segments.takeWhile (!·.star)
      if reference.index.isSome || unstarred.isEmpty ||
          unstarred.length == reference.path.segments.length then []
      else [{ reference.path with segments := unstarred }]
  | .call _ arguments listed _ =>
      (arguments ++ listed.getD []).flatMap fun (.mk expression rangeEnd) =>
        expression.starredReadPrefixes ++ (rangeEnd.map Expr.starredReadPrefixes).getD []
  | .arith _ left right | .compare _ left right => left.starredReadPrefixes ++ right.starredReadPrefixes
  | .braces body | .parens body => body.starredReadPrefixes
  | .logic _ parts => parts.flatMap Expr.starredReadPrefixes
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
      let strict := lowerNumericExpr (pairNumericAtom model group) ((.field ·) <$> pairField model group true ·)
      let orOrdinary := fun (lowerAtom : Expr → Lowering (ParallelNumericAtomOf FieldId Expr)) expression =>
        tryCatch (lowerAtom expression) fun _ => pure (ParallelNumericAtomOf.ordinary expression)
      let mixed := lowerNumericExpr (orOrdinary (pairNumericAtom model group))
        (orOrdinary ((.field ·) <$> pairField model group true ·))
      let comparison (lower : Expr → Lowering (AuthoredNumericExpr (ParallelNumericAtomOf FieldId Expr))) :
          Lowering (ParallelFieldLeafOf FieldId Empty Expr) := do
        let some comparison := op.toNumeric? | refuse "ParallelRule" "Number comparison required"
        let value : NumericComparisonOf (ParallelNumericAtomOf FieldId Expr) :=
          { op := comparison, left := ← lower left, right := ← lower right }
        let plain := (value.left.atoms ++ value.right.atoms).filterMap fun
          | .field field => some field
          | _ => none
        if plain.all fun field => ((model.lookupUniqueId field).toOption.bind (·.toNumberField?)).isSome then
          pure (.comparison value)
        else refuse "ParallelRule" "Number comparison required"
      tryCatch ((.leaf ∘ .pair) <$> comparison strict) fun _ => do
        let reads ← expression.fieldPaths.mapM (pairPath model group)
        pure (.leaf (.ordinary expression reads.eraseDups (comparison mixed).toOption))
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
       -- A keyed, filtered or starred operand reads no single joined row: an ordinary leaf.
       match name, field.fieldEntity?.isSome with
        | "FieldFilled", true => pure (.leaf (.pair (.presence (← pairField model group false field) .filled)))
        | "FieldNotFilled", true => pure (.leaf (.pair (.presence (← pairField model group false field) .notFilled)))
        | _, _ => ordinary (.call name [.mk field none] none none)
  | expression@(.call "FieldValuesNotUnique" arguments none none) => do
      let some paths := arguments.mapM (fun | .mk operand none => operand.fieldEntity? | _ => none)
        | ordinary expression
      if paths.length < 2 then ordinary expression else
      pure (.leaf (.pair (.valuesNotUnique (← paths.mapM (pairPath model group)))))
  | expression@(.call name [.mk left none, .mk right none] none none) => do
      let some op := fieldFillOp? name | ordinary expression
      if left.fieldEntity?.isNone || right.fieldEntity?.isNone then ordinary expression else
      pure (.leaf (.pair (.fill op (← pairField model group false left) (← pairField model group false right))))
  | .custom name quoted => do
      let spelling := if quoted then CustomConditionNameSpelling.quoted name else .unquoted name
      let some checkedName := checkCustomConditionName (fun _ => false) spelling
        | refuse "CustomCondition" "invalid name"
      pure (.leaf (.pair (.customCondition checkedName)))
  | expression => ordinary expression
where
  /-- A leaf the pair carrier has no form for, kept with the plain fields it reads. -/
  ordinary (expression : Expr) : Lowering (ConditionTree PairSyntaxLeaf) := do
    let reads ← expression.fieldPaths.mapM (pairPath model group)
    pure (.leaf (.ordinary expression reads.eraseDups))

private def pairReferences : ConditionTree PairSyntaxLeaf → List FieldId
  | .leaf (.pair (.groupPresence _ _)) => []
  | .leaf (.pair (.presence field _)) => [field]
  | .leaf (.pair (.numeric _ left right)) | .leaf (.pair (.fill _ left right)) => [left, right]
  | .leaf (.pair (.comparison value)) => (value.left.atoms ++ value.right.atoms).flatMap (·.operands)
  | .leaf (.pair (.customCondition _)) | .leaf (.pair (.ordinary _)) => []
  | .leaf (.pair (.valuesNotUnique operands)) => operands
  | .leaf (.pair (.flat _ reads)) | .leaf (.ordinary _ reads _) => reads
  | .and left right | .or left right => pairReferences left ++ pairReferences right

/-- The repeatable groups the two anchors index, which one joined instance binds. -/
private def pairGroupPaths (model : FlatModel) (left right : FieldId) : List GroupPath :=
  [left, right].filterMap fun anchor => (model.lookupUniqueId anchor).toOption.bind fun declaration =>
    (model.indexedAncestorGroups declaration).getLast?.map (·.path)

/-- A keyed presence read lowered with one joined side's levels bound, as a parallel rule binds a key
field on that side's row (joined-carrier capture, rows `k03b` and `k08`, and its limits capture,
row `p01`, 2026-10-14). The
ordinary reader binds the declaring group only, which refuses such a key for a rule without a join. -/
private def sideKeyedPresence (model : FlatModel) (group bound : GroupPath) :
    Expr → Option (Lowering (ValidationConditionLeaf model))
  | .call "FieldFilled" [.mk (.entity { path, index := some key, category := none, filter := none }) none] none none =>
      some (indexed .filled path key)
  | .call "FieldNotFilled" [.mk (.entity { path, index := some key, category := none, filter := none }) none] none none =>
      some (indexed .notFilled path key)
  | .call "GroupFilled" [argument@(.mk (.entity { index := some _, filter := none, .. }) none)] none none =>
      some (keyedGroup .filled argument)
  | .call "GroupNotFilled" [argument@(.mk (.entity { index := some _, filter := none, .. }) none)] none none =>
      some (keyedGroup .notFilled argument)
  | _ => none
where
  indexed (operator : RepeatableFieldPresenceOperator) (path : Path) (key : IndexKey) :
      Lowering (ValidationConditionLeaf model) := do
    let source ← lowerIndexedSource model group path key
    let checked ← elaborated "SemanticIndex"
      (elaborateSemanticIndexSource model group source (some (model.repeatableScopeForGroupPath bound)))
    pure (.indexedFieldPresence operator checked)
  keyedGroup (operator : GroupPresenceOperator) (argument : Argument) :
      Lowering (ValidationConditionLeaf model) := do
    let .keyed source .stored ← lowerEntityOperand model group argument | refuse "SemanticIndex" "group operand"
    let checked ← elaborated "SemanticIndex"
      (elaborateKeyedEntityExtent model group source (some (model.repeatableScopeForGroupPath bound)))
    if !checked.isGroup || checked.isStarredGroup then refuse "SemanticIndex" "unstarred group operand"
    pure (.keyedGroupPresence operator checked)

private def bindPairLeaf (model : FlatModel) (group : GroupPath) (suppress : Bool) (left right : FieldId) :
    PairSyntaxLeaf → Lowering (ParallelFieldLeaf model)
  | .pair leaf => bindPair leaf
  | .ordinary expression _ mixed => do
      -- The ordinary reader lowers the leaf against the instance view; only a flat leaf, whose
      -- operands are model-free field records, crosses back to the real model. Any other leaf is
      -- lowered against the model itself, where admission accepts it only when the common outer
      -- binding fixes its every iterating read.
      let view := model.parallelInstanceView (pairGroupPaths model left right)
      let viewed : Option (ValidationCondition view) :=
        (lowerCondition view group suppress expression).toOption.map (·.core)
      match viewed with
      | some (.leaf (.flat condition)) =>
          bindPair (.flat condition (model.fields.filterMap fun declaration =>
            if condition.referencesField declaration.id then some declaration.id else none))
      | _ =>
          -- A key read on the error side's row binds at that row (joined-carrier capture, rows
          -- `k03b`, `k07b` and `k08`, 2026-10-14), so a leaf the declaring group cannot bind is
          -- lowered once more with the error side's group bound.
          match ordinaryLeaf expression with
          | .ok leaf => pure (.ordinary leaf)
          | .error refusal => match mixed with
            -- No binding fixes the whole comparison: each operand without a pair form keeps its
            -- ordinary meaning as an atom (generated rule of joined-carrier capture row `j11`, 2026-10-14).
            | some leaf => tryCatch (bindPair leaf) fun _ => .error refusal
            | none => .error refusal
where
  ordinaryLeaf (expression : Expr) : Lowering (ValidationConditionLeaf model) :=
    match lowerCondition model group suppress expression with
    | .ok checked => single checked
    | .error refusal => sideBound expression refusal (pairGroupPaths model left right)
  -- Each joined side's group in turn, the error side's first.
  sideBound (expression : Expr) (refusal : Refusal) : List GroupPath → Lowering (ValidationConditionLeaf model)
    | [] => .error refusal
    | side :: rest =>
        let lowered : Lowering (ValidationConditionLeaf model) := match sideKeyedPresence model group side expression with
          | some leaf => leaf
          | none => (lowerCondition model group suppress expression (bindingGroup := side)).bind single
        match lowered with
        | .ok leaf => pure leaf
        | .error _ => sideBound expression refusal rest
  single (condition : CheckedValidationCondition model) : Lowering (ValidationConditionLeaf model) :=
    match condition.core with
    | .leaf leaf => pure leaf
    | _ => refuse "ParallelRule" "unsupported pair condition"
  -- An ordinary atom is checked as its one-atom comparison, which fixes its binding.
  atomLeaf (expression : Expr) : Lowering (ValidationConditionLeaf model) := do
    let leaf ← ordinaryLeaf (.compare .gt expression (.number "0"))
    if leaf.orderedAtom?.isNone then refuse "ParallelRule" "ordinary numeric atom"
    pure leaf
  bindPair (leaf : ParallelFieldLeafOf FieldId Empty Expr) : Lowering (ParallelFieldLeaf model) := do
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
        left := ← value.left.mapM (·.mapM operand atomLeaf), right := ← value.right.mapM (·.mapM operand atomLeaf) })
    | .customCondition name => pure (.customCondition name)
    | .valuesNotUnique operands => pure (.valuesNotUnique (← operands.mapM operand))
    | .flat condition reads => pure (.flat condition (← reads.mapM operand))
    | .ordinary leaf => nomatch leaf

private def pairGroupReferences (group : GroupPath) : ConditionTree PairSyntaxLeaf → List GroupPath
  | .leaf (.pair (.groupPresence _ reference)) => [reference.path]
  | .leaf (.ordinary expression _ _) => expression.starredReadPrefixes.filterMap fun path =>
      ((Expr.entity { path }).groupReference?.bind fun reference =>
        (reference.resolveAgainst group).toOption).map (·.path)
  | .leaf _ => []
  | .and left right | .or left right => pairGroupReferences group left ++ pairGroupReferences group right

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
private def pairAnchors (model : FlatModel) (group : GroupPath) (errorField : FieldId)
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
        (pairGroupReferences group condition).any (candidate.path.isPrefixOf ·))
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
  -- The walk needs the joined levels before the pair is built; a condition with no pair is refused
  -- by `pairAnchors` below, after its authored reads.
  let joinedLevels := ((pairAnchors model.flat rule.group errorField parsedCondition).toOption.map
    fun (left, right) => (pairGroupPaths model.flat left right).filterMap fun path =>
      (model.flat.repeatableScopeForGroupPath path).getLast?).getD []
  let facts ← (checkRawConditionBeforeGlobals model.flat rule.group errorDeclaration.groupPath
    text.body (text.suppressed.contains "MVK_INVALID_COMPARE_DEC_PLACES") joinedLevels).mapError
      (fun refusal => { refusal with construct := "ParallelAdmission" })
  -- The whole-rule gates in their order: `RepetitionNotUnique` beside the join before a filter below
  -- either joined group (parallel-child capture, `x1`, `x2`, `q05`, `q10`, `y1`; joined-carrier-limits
  -- `d06`; 2026-10-14). A filter in an unjoined group is admitted (`q11`).
  if let some diagnostic := facts.refusal? then refuse "ParallelAdmission" diagnostic.kernelCode
  let (left, right) ← pairAnchors model.flat rule.group errorField parsedCondition
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
    (message, rule.condition.messageReferences rule.pair preliminary.base row.row row.outerEnvironment cache message inputs))

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
