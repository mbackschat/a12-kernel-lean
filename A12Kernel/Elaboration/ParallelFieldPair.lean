import A12Kernel.Elaboration.CheckedIndexColumn
import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Semantics.CorrelationContext
import A12Kernel.Semantics.CustomCondition
import A12Kernel.Semantics.ValidationRule

/-! # Checked field-pair ownership and traversal for parallel validation

Key construction, optional physical environments and framed traversal are shared by pair-condition families. Missing joined sides remain observations and message coordinates, never fabricated physical cells.
-/

namespace A12Kernel

inductive ParallelPresenceRuleAssemblyError where
  | model (error : ResolveError)
  | join (error : CheckedIndexColumnError)
  | static (diagnostic : KernelStaticDiagnostic)
  | incoherentCondition
  | incoherentOperandGroup (field : FieldId) (group : GroupPath)
  | missingIndexedOperandGroup (field : FieldId)
  | multipleIndexedOperandGroups (field : FieldId)
      (groups : List GroupPath)
  | errorFieldNotOperand (field left right : FieldId)
  | errorFieldNotOnFramedSide (field : FieldId)
  | errorGroupPlacement (path : GroupPath)
  deriving Repr, DecidableEq

inductive ParallelPresenceRuleEvaluationError where
  | join (error : CheckedIndexColumnError)
  | group (error : CheckedGroupPresenceError)
  | rows (error : ActualRowEnvironmentError)
  | preliminary (error : CheckedIndexPreliminaryError)
  | customCondition (error : CustomConditionLookupError)
  /-- A keyed group read beside the join failed in the ordinary addressed evaluator. -/
  | addressing (error : CheckedAddressingError)
  | unsupportedCondition
  deriving Repr, DecidableEq

/-- One key-preserving whole-rule result. The complete outer evaluation environment distinguishes equal join keys in different frame rows; silent outcomes still require no physical error address. The resolved row stays beside its outcome because a message's reference channels point both joined sides, not only the error side. -/
structure ParallelRuleRowOutcome where
  outerEnvironment : Env
  iterationToken : String
  key : SemanticIndexKey
  row : ResolvedParallelIndexRow
  outcome : FlatRuleOutcome
  deriving Repr, DecidableEq

/-- Whether a rule's error group sits directly inside the error side's joined row: below the joined
group, its parent's levels the joined group's, with the anchor at the joined group's level. The
[checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-group-target-nested-join)
measures a repeatable child of the joined group (`group-level`, `t8`). -/
def errorGroupPlacement (model : FlatModel) (groups : CheckedParallelIndexGroups model)
    (leftDeclaration rightDeclaration : FlatFieldDecl) (errorField : FieldId) :
    Option GroupPath → Bool
  | none => true
  | some path =>
      let (joined, anchor) := if errorField == leftDeclaration.id then (groups.leftGroup, leftDeclaration)
        else (groups.rightGroup, rightDeclaration)
      model.hasGroupPath path && joined.path.isPrefixOf path && path != joined.path &&
        anchor.repeatableScope == model.repeatableScopeForGroupPath joined.path &&
        model.repeatableScopeForGroupPath path.dropLast == anchor.repeatableScope

/-- Two anchor declarations share a checked join and an error side with complete outer coordinates. Group-only conditions may use an index declaration as a topology anchor; authored reference membership remains the condition’s responsibility. Each anchor's scope extends its joined group's, and only the error anchor's may be longer: its levels below the joined group are iterated within each joined row. A rule reporting on a group names it in `errorGroup`, a group directly inside the error side's joined row, whose anchor is then a field of the joined group itself. -/
structure CheckedParallelFieldPair (model : FlatModel) where
  private mk ::
  groups : CheckedParallelIndexGroups model
  leftDeclaration : FlatFieldDecl
  rightDeclaration : FlatFieldDecl
  errorField : FieldId
  errorCode : String
  severity : ValidationSeverity
  messagePlan : MessageRenderPlan
  leftOperandGroup :
    groups.leftGroup.path.isPrefixOf leftDeclaration.groupPath = true
  rightOperandGroup :
    groups.rightGroup.path.isPrefixOf rightDeclaration.groupPath = true
  leftOperandScope :
    (model.repeatableScopeForGroupPath groups.leftGroup.path).isPrefixOf
      leftDeclaration.repeatableScope = true
  rightOperandScope :
    (model.repeatableScopeForGroupPath groups.rightGroup.path).isPrefixOf
      rightDeclaration.repeatableScope = true
  partnerOperandScope :
    (if errorField == leftDeclaration.id then
      rightDeclaration.repeatableScope == model.repeatableScopeForGroupPath groups.rightGroup.path
    else
      leftDeclaration.repeatableScope == model.repeatableScopeForGroupPath groups.leftGroup.path) = true
  errorFieldIsOperand :
    (errorField == leftDeclaration.id ||
      errorField == rightDeclaration.id) = true
  errorFieldOnFramedSide :
    groups.outerScopePlan.admitsErrorOnLeft
      (errorField == leftDeclaration.id) = true
  errorGroup : Option GroupPath
  errorGroupPlaced : errorGroupPlacement model groups leftDeclaration rightDeclaration errorField errorGroup = true

namespace CheckedParallelFieldPair

def core (pair : CheckedParallelFieldPair model) (condition : Condition) : ResolvedRule Condition := {
  condition
  errorEntity := match pair.errorGroup with
    | some path => .group path
    | none => .field pair.errorField
  errorCode := pair.errorCode
  severity := pair.severity
  messagePlan := pair.messagePlan
}

/-- The joined side holding the error field. -/
def errorSide (pair : CheckedParallelFieldPair model)
    (row : ResolvedParallelIndexRow) : ResolvedParallelIndexSide :=
  if pair.errorField == pair.leftDeclaration.id then row.left else row.right

/-- The error field's declaration, the anchor on the error side. -/
def errorDeclaration (pair : CheckedParallelFieldPair model) : FlatFieldDecl :=
  if pair.errorField == pair.leftDeclaration.id then pair.leftDeclaration else pair.rightDeclaration

/-- The error field's repeatable levels below its joined group. -/
def innerScope (pair : CheckedParallelFieldPair model) : List RepeatableLevel :=
  let joined := if pair.errorField == pair.leftDeclaration.id then pair.groups.leftGroup
    else pair.groups.rightGroup
  pair.errorDeclaration.repeatableScope.drop (model.repeatableScopeForGroupPath joined.path).length

/-- An error group's own repeatable level and whether the group is keyed. -/
private def ownLevel? (pair : CheckedParallelFieldPair model) : Option (RepeatableLevel × Bool) :=
  pair.errorGroup.bind fun path =>
    let scope := model.repeatableScopeForGroupPath path
    if scope.length > pair.errorDeclaration.repeatableScope.length then
      scope.getLast?.map (·, (model.repeatableGroups.find? (·.path == path)).any (·.indexField.isSome))
    else none

/-- An unkeyed error group's own repeatable level, which the rule does not iterate: its reads take the
group's first row, as the ordinary carrier pins it (`pinUnindexed`), and only its own presence reads
every row. -/
def pinnedLevel? (pair : CheckedParallelFieldPair model) : Option RepeatableLevel :=
  pair.ownLevel?.bind fun (level, keyed) => if keyed then none else some level

/-- A keyed error group's own level. Beside the join the Kernel leaves it at its parallel-iteration
placeholder rather than binding a row, so the group's own presence holds of no row and its message
names UNKNOWN there
([checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-keyed-group-beside-join),
`runtime-keyed`). -/
def placeholderLevel? (pair : CheckedParallelFieldPair model) : Option RepeatableLevel :=
  pair.ownLevel?.bind fun (level, keyed) => if keyed then some level else none

/-- `row` with the error side's environment binding the error group's own level at its first row. -/
def pinned (pair : CheckedParallelFieldPair model) (row : ResolvedParallelIndexRow) : ResolvedParallelIndexRow :=
  match pair.pinnedLevel? with
  | none => row
  | some level =>
      let pin := fun (side : ResolvedParallelIndexSide) =>
        { side with environment := side.environment.map (· ++ [(level, 1)]) }
      if pair.errorField == pair.leftDeclaration.id then { row with left := pin row.left }
      else { row with right := pin row.right }

/-- The error field's full-validation rows, which `innerRows` filters for a model declaring no
capacity; none for a field at its joined group's level. -/
def innerEnvironments (pair : CheckedParallelFieldPair model) (preliminary : CheckedIndexPreliminary model) :
    Except ParallelPresenceRuleEvaluationError (List Env) :=
  if pair.innerScope.isEmpty then pure []
  else preliminary.base.fullValidationRowEnvironments pair.errorDeclaration.repeatableScope |>.mapError .rows

/-- The rows one joined row contributes: the row itself when the error field sits at its joined
group's level, otherwise one row per nested row the rule visits inside it, matched or unmatched alike,
with the error side bound there (`joinedInnerCoordinates`). The Kernel iterates a nested level within
each joined row for a rule and for a computation precondition
([checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-group-target-nested-join),
`nested-join`). A model declaring no capacity keeps the full-validation rows `environments` inside a
matched joined row. -/
def innerRows (pair : CheckedParallelFieldPair model) (preliminary : CheckedIndexPreliminary model)
    (environments : List Env) (outer : Env) (row : ResolvedParallelIndexRow) :
    Except ParallelPresenceRuleEvaluationError (List ResolvedParallelIndexRow) := do
  if pair.innerScope.isEmpty then return [pair.pinned row]
  let side := pair.errorSide row
  let joinedScope := model.repeatableScopeForGroupPath side.group.path
  let bind := fun (side : ResolvedParallelIndexSide) =>
    if pair.errorField == pair.leftDeclaration.id then { row with left := side } else { row with right := side }
  let joinedDepth := side.group.path.length - 1
  let stem := model.groupCoordinates side.group.path (side.environment.getD outer)
  match preliminary.base.joinedInnerCoordinates pair.errorDeclaration.groupPath joinedDepth stem with
  | some suffixes =>
      pure (suffixes.map fun suffix =>
        let inner := pair.innerScope.map fun level =>
          let depth := (model.repeatableGroupAtLevel? level).map (·.path.length - 1) |>.getD 0
          (level, suffix[depth - joinedDepth - 1]?.getD 1)
        match side.environment with
        | some environment => bind { side with environment := some (environment ++ inner) }
        | none => bind { side with inner })
  | none =>
      let some environment := side.environment | return []
      let joinedPath ← environment.pathForScope joinedScope |>.mapError fun error => .join (.environment error)
      pure ((environments.filter fun inner => (inner.pathForScope joinedScope).toOption == some joinedPath).map
        fun inner => bind { side with environment := some inner })

/-- The error pointer a custom-condition callback receives at one joined row: the error field's levels bound from the error side's environment, from the outer environment where that side is unmatched, and UNKNOWN wherever no unique row is bound (spec/11 §14). A duplicate-key side gets no cache-resolved coordinate here; the fired message keeps that projection in `evalRow`. -/
def customErrorPointer (pair : CheckedParallelFieldPair model)
    (row : ResolvedParallelIndexRow) (outer : Env) : MessagePointer :=
  let declaration := pair.errorDeclaration
  let environment := (pair.errorSide row).environment.getD outer
  { field := pair.errorField
    coordinates := declaration.repeatableScope.map fun level =>
      (environment.uniqueRowAt? level).map MessageRepetitionCoordinate.concrete |>.getD .unknown }

/-- The error entity's coordinates at one joined row: the anchor's, and an error group's own level at
its first row (`group-level`, `t8`). A keyed error group's message names the joined level's first row
whichever row joined, and UNKNOWN at its own level (`runtime-keyed`, `mixed`). -/
private def errorCoordinates (pair : CheckedParallelFieldPair model) (row : ResolvedParallelIndexRow)
    (outer : Env) (messageCache : Option MessageIndexContext) :
    Except ParallelPresenceRuleEvaluationError (List MessageRepetitionCoordinate) := do
  let pointer ← (pair.errorSide row).messagePointer model outer pair.errorField
    (messageCache.map fun cache => (cache, row.key)) |>.mapError .join
  if pair.placeholderLevel?.isSome then return pointer.coordinates.dropLast ++ [.concrete 1, .unknown]
  pure (pointer.coordinates ++ pair.pinnedLevel?.toList.map fun _ => .concrete 1)

private def evalRow (pair : CheckedParallelFieldPair model) (condition : Condition)
    (evaluate : ResolvedParallelIndexRow → CheckedIndexPreliminary model →
      Except ParallelPresenceRuleEvaluationError Verdict)
    (preliminary : CheckedIndexPreliminary model)
    (outerEnvironment : Env) (messageCache : Option MessageIndexContext)
    (row : ResolvedParallelIndexRow) :
    Except ParallelPresenceRuleEvaluationError ParallelRuleRowOutcome := do
  let verdict ← evaluate row preliminary
  let outcome ← match verdict with
    | .fired _ => do
        let coordinates ← pair.errorCoordinates row outerEnvironment messageCache
        pure ((pair.core condition).emitAtCoordinates coordinates verdict)
    | .notFired | .unknown => pure ((pair.core condition).emitAt [] verdict)
  pure { outerEnvironment, iterationToken := row.iterationToken, key := row.key, row, outcome }

/-- Evaluate joined rows in order. A `caught` failure ends the traversal at the row raising it and
reports there at the traversal's first row's error pointer, as the ordinary carrier's whole-rule
handler reports at its iterator's first error address (rule `M04` of the
[call capture](../../docs/sources/model-structure-and-declaration-probes.md#src-custom-condition-calls)).
The flag says the traversal stopped. -/
private def evalRows (pair : CheckedParallelFieldPair model) (condition : Condition)
    (evaluate : ResolvedParallelIndexRow → CheckedIndexPreliminary model →
      Except ParallelPresenceRuleEvaluationError Verdict)
    (preliminary : CheckedIndexPreliminary model) (frameOuter : Env)
    (messageCache : Option MessageIndexContext)
    (caught : ParallelPresenceRuleEvaluationError → Bool) :
    Option (Env × ResolvedParallelIndexRow) → List ResolvedParallelIndexRow →
      Except ParallelPresenceRuleEvaluationError
        (List ParallelRuleRowOutcome × Option (Env × ResolvedParallelIndexRow) × Bool)
  | first?, [] => pure ([], first?, false)
  | first?, row :: remaining => do
      let first := first?.getD (frameOuter, row)
      match pair.evalRow condition evaluate preliminary frameOuter messageCache row with
      | .ok outcome =>
          let (outcomes, first?, stopped) ←
            evalRows pair condition evaluate preliminary frameOuter messageCache caught (some first) remaining
          pure (outcome :: outcomes, first?, stopped)
      | .error error =>
          if !caught error then throw error
          let coordinates ← pair.errorCoordinates first.2 first.1 messageCache
          let outcome := (pair.core condition).emitRuntimeFailureAtCoordinates coordinates
          let reported : ParallelRuleRowOutcome :=
            { outerEnvironment := frameOuter, iterationToken := row.iterationToken, key := row.key, row, outcome }
          pure ([reported], some first, true)

/-- Traverse the certified key union in lexical order, within each declared-domain one-sided frame when present. The supplied condition evaluator consumes the same resolved rows used for error projection. -/
def evalWith (pair : CheckedParallelFieldPair model) (condition : Condition)
    (evaluate : Env → ResolvedParallelIndexRow → CheckedIndexPreliminary model →
      Except ParallelPresenceRuleEvaluationError Verdict)
    (preliminary : CheckedIndexPreliminary model) (outer : Env := [])
    (messageCache : Option MessageIndexContext := none)
    (includeAddress : CellAddr → Bool := fun _ => true)
    (admitOuter : Env → Bool := fun _ => true)
    (caught : ParallelPresenceRuleEvaluationError → Bool := fun _ => false) :
    Except ParallelPresenceRuleEvaluationError (List ParallelRuleRowOutcome) := do
  let inner ← pair.innerEnvironments preliminary
  let runJoin := fun first? frameOuter (join : ResolvedParallelIndexJoin) => do
    if !admitOuter frameOuter then pure ([], first?, false)
    else
      let rows := (← join.rows.mapM (pair.innerRows preliminary inner frameOuter)).flatten
      pair.evalRows condition (evaluate frameOuter) preliminary frameOuter messageCache caught first? rows
  match pair.groups.outerScopePlan with
  | .common _ =>
      let join ← preliminary.resolveCheckedParallelIndexJoin pair.groups outer includeAddress |>.mapError .join
      pure (← runJoin none outer join).1
  | .framed _ _ _ =>
      let frames ← preliminary.resolveCheckedParallelFrameEnvironments pair.groups outer |>.mapError .join
      let rec runFrames (first? : Option (Env × ResolvedParallelIndexRow)) :
          List Env → Except ParallelPresenceRuleEvaluationError (List ParallelRuleRowOutcome)
        | [] => pure []
        | frame :: remaining => do
            let join ← preliminary.resolveCheckedParallelIndexJoinInFrame pair.groups frame outer includeAddress |>.mapError .join
            let (outcomes, first?, stopped) ← runJoin first? frame join
            if stopped then pure outcomes else pure (outcomes ++ (← runFrames first? remaining))
      runFrames none frames

/-- Full validation instantiates the shared traversal with unrestricted key admission and dispatch. -/
def evalFullWith (pair : CheckedParallelFieldPair model) (condition : Condition)
    (evaluate : ResolvedParallelIndexRow → CheckedIndexPreliminary model →
      Except ParallelPresenceRuleEvaluationError Verdict)
    (preliminary : CheckedIndexPreliminary model) (outer : Env := [])
    (messageCache : Option MessageIndexContext := none) :
    Except ParallelPresenceRuleEvaluationError (List ParallelRuleRowOutcome) :=
  pair.evalWith condition (fun _ => evaluate) preliminary outer messageCache

end CheckedParallelFieldPair

/-- Resolve the sole indexed repeatable ancestor that owns one parallel operand. Nonrepeatable path segments do not appear in this candidate set. -/
private def indexedOperandGroup (model : FlatModel)
    (declaration : FlatFieldDecl) :
    Except ParallelPresenceRuleAssemblyError RepeatableGroupDecl :=
  match model.indexedAncestorGroups declaration with
  | [] => .error (.missingIndexedOperandGroup declaration.id)
  | [group] => .ok group
  | groups =>
      .error (.multipleIndexedOperandGroups declaration.id
        (groups.map (·.path)))

/-- Check the narrow parallel rule plan without passing caller-selected groups or iteration rows. Each operand declaration determines its sole keyed repeatable ancestor; the partner's complete repeatable scope must end at that group, and the error anchor's may continue below it. -/
def checkParallelFieldPair (model : FlatModel)
    (leftField rightField errorField : FieldId)
    (errorCode : String) (severity : ValidationSeverity)
    (messagePlan : MessageRenderPlan) (errorGroup : Option GroupPath := none) :
    Except ParallelPresenceRuleAssemblyError
      (CheckedParallelFieldPair model) := do
  let leftDeclaration ←
    model.lookupUniqueId leftField |>.mapError .model
  let rightDeclaration ←
    model.lookupUniqueId rightField |>.mapError .model
  let leftGroup ← indexedOperandGroup model leftDeclaration
  let rightGroup ← indexedOperandGroup model rightDeclaration
  let groups ←
    checkParallelIndexGroups model leftGroup rightGroup
      |>.mapError .join
  if hLeftGroup :
      groups.leftGroup.path.isPrefixOf leftDeclaration.groupPath = true then
    if hRightGroup :
        groups.rightGroup.path.isPrefixOf
          rightDeclaration.groupPath = true then
      if hLeftScope :
          (model.repeatableScopeForGroupPath groups.leftGroup.path).isPrefixOf
            leftDeclaration.repeatableScope = true then
        if hRightScope :
            (model.repeatableScopeForGroupPath groups.rightGroup.path).isPrefixOf
              rightDeclaration.repeatableScope = true then
          if hPartner :
            (if errorField == leftDeclaration.id then
              rightDeclaration.repeatableScope == model.repeatableScopeForGroupPath groups.rightGroup.path
            else
              leftDeclaration.repeatableScope == model.repeatableScopeForGroupPath groups.leftGroup.path) = true then
            if hError :
                (errorField == leftDeclaration.id ||
                  errorField == rightDeclaration.id) = true then
              if hFrameError :
                  groups.outerScopePlan.admitsErrorOnLeft
                    (errorField == leftDeclaration.id) = true then
               if hGroup : errorGroupPlacement model groups leftDeclaration rightDeclaration errorField
                   errorGroup = true then
                pure {
                  groups
                  leftDeclaration
                  rightDeclaration
                  errorField
                  errorCode
                  severity
                  messagePlan
                  leftOperandGroup := hLeftGroup
                  rightOperandGroup := hRightGroup
                  leftOperandScope := hLeftScope
                  rightOperandScope := hRightScope
                  partnerOperandScope := hPartner
                  errorFieldIsOperand := hError
                  errorFieldOnFramedSide := hFrameError
                  errorGroup
                  errorGroupPlaced := hGroup
                }
               else
                throw (.errorGroupPlacement (errorGroup.getD []))
              else
                throw (.errorFieldNotOnFramedSide errorField)
            else
              throw (.errorFieldNotOperand errorField
                leftDeclaration.id rightDeclaration.id)
          else
            throw (.incoherentOperandGroup
              (if errorField == leftDeclaration.id then rightDeclaration.id else leftDeclaration.id)
              (if errorField == leftDeclaration.id then groups.rightGroup.path else groups.leftGroup.path))
        else
          throw (.incoherentOperandGroup
            rightDeclaration.id groups.rightGroup.path)
      else
        throw (.incoherentOperandGroup
          leftDeclaration.id groups.leftGroup.path)
    else
      throw (.incoherentOperandGroup
        rightDeclaration.id groups.rightGroup.path)
  else
    throw (.incoherentOperandGroup
      leftDeclaration.id groups.leftGroup.path)


end A12Kernel
