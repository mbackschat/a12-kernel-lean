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

/-- Two anchor declarations share a checked join and an error side with complete outer coordinates. Group-only conditions may use an index declaration as a topology anchor; authored reference membership remains the condition’s responsibility. -/
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
    (leftDeclaration.repeatableScope ==
      model.repeatableScopeForGroupPath groups.leftGroup.path) = true
  rightOperandScope :
    (rightDeclaration.repeatableScope ==
      model.repeatableScopeForGroupPath groups.rightGroup.path) = true
  errorFieldIsOperand :
    (errorField == leftDeclaration.id ||
      errorField == rightDeclaration.id) = true
  errorFieldOnFramedSide :
    groups.outerScopePlan.admitsErrorOnLeft
      (errorField == leftDeclaration.id) = true

namespace CheckedParallelFieldPair

def core (pair : CheckedParallelFieldPair model) (condition : Condition) : ResolvedRule Condition := {
  condition
  errorField := pair.errorField
  errorCode := pair.errorCode
  severity := pair.severity
  messagePlan := pair.messagePlan
}

/-- The joined side holding the error field. -/
def errorSide (pair : CheckedParallelFieldPair model)
    (row : ResolvedParallelIndexRow) : ResolvedParallelIndexSide :=
  if pair.errorField == pair.leftDeclaration.id then row.left else row.right

/-- The error pointer a custom-condition callback receives at one joined row: the error field's levels bound from the error side's environment, from the outer environment where that side is unmatched, and UNKNOWN wherever no unique row is bound (spec/11 §14). A duplicate-key side gets no cache-resolved coordinate here; the fired message keeps that projection in `evalRow`. -/
def customErrorPointer (pair : CheckedParallelFieldPair model)
    (row : ResolvedParallelIndexRow) (outer : Env) : MessagePointer :=
  let declaration := if pair.errorField == pair.leftDeclaration.id then pair.leftDeclaration
    else pair.rightDeclaration
  let environment := (pair.errorSide row).environment.getD outer
  { field := pair.errorField
    coordinates := declaration.repeatableScope.map fun level =>
      (environment.uniqueRowAt? level).map MessageRepetitionCoordinate.concrete |>.getD .unknown }

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
        let pointer ← (pair.errorSide row).messagePointer model outerEnvironment pair.errorField
          (messageCache.map fun cache => (cache, row.key))
          |>.mapError .join
        pure ((pair.core condition).emitAtCoordinates pointer.coordinates verdict)
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
          let pointer ← (pair.errorSide first.2).messagePointer model first.1 pair.errorField
            (messageCache.map fun cache => (cache, first.2.key)) |>.mapError .join
          let outcome := (pair.core condition).emitRuntimeFailureAtCoordinates pointer.coordinates
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
  let runJoin := fun first? frameOuter (join : ResolvedParallelIndexJoin) =>
    if !admitOuter frameOuter then pure ([], first?, false)
    else pair.evalRows condition (evaluate frameOuter) preliminary frameOuter messageCache caught first? join.rows
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

/-- Check the narrow parallel rule plan without passing caller-selected groups or iteration rows. Each operand declaration determines its sole keyed repeatable ancestor, and its complete repeatable scope must end at that group. -/
def checkParallelFieldPair (model : FlatModel)
    (leftField rightField errorField : FieldId)
    (errorCode : String) (severity : ValidationSeverity)
    (messagePlan : MessageRenderPlan) :
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
          (leftDeclaration.repeatableScope ==
            model.repeatableScopeForGroupPath groups.leftGroup.path) =
              true then
        if hRightScope :
            (rightDeclaration.repeatableScope ==
              model.repeatableScopeForGroupPath groups.rightGroup.path) =
                true then
          if hError :
              (errorField == leftDeclaration.id ||
                errorField == rightDeclaration.id) = true then
            if hFrameError :
                groups.outerScopePlan.admitsErrorOnLeft
                  (errorField == leftDeclaration.id) = true then
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
                errorFieldIsOperand := hError
                errorFieldOnFramedSide := hFrameError
              }
            else
              throw (.errorFieldNotOnFramedSide errorField)
          else
            throw (.errorFieldNotOperand errorField
              leftDeclaration.id rightDeclaration.id)
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
