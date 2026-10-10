import A12Kernel.Elaboration.CheckedIndexColumn
import A12Kernel.Semantics.ValidationRule

/-! # Checked field-pair ownership and traversal for parallel validation

Key construction, optional physical environments and framed traversal are shared by pair-condition families. Missing joined sides remain observations and message coordinates, never fabricated physical cells.
-/

namespace A12Kernel

inductive ParallelPresenceRuleAssemblyError where
  | model (error : ResolveError)
  | join (error : CheckedIndexColumnError)
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
  | unsupportedCondition
  deriving Repr, DecidableEq

/-- One key-preserving whole-rule result. The complete outer evaluation environment distinguishes equal join keys in different frame rows; silent outcomes still require no physical error address. -/
structure ParallelRuleRowOutcome where
  outerEnvironment : Env
  iterationToken : String
  key : SemanticIndexKey
  outcome : FlatRuleOutcome
  deriving Repr, DecidableEq

/-- Two payload declarations share a checked join and an error side with complete outer coordinates. -/
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

private def errorSide (pair : CheckedParallelFieldPair model)
    (row : ResolvedParallelIndexRow) : ResolvedParallelIndexSide :=
  if pair.errorField == pair.leftDeclaration.id then row.left else row.right

private def evalRow (pair : CheckedParallelFieldPair model) (condition : Condition)
    (evaluate : ResolvedParallelIndexRow → CheckedIndexPreliminary model →
      Except ParallelPresenceRuleEvaluationError Verdict)
    (preliminary : CheckedIndexPreliminary model)
    (outerEnvironment : Env) (row : ResolvedParallelIndexRow) :
    Except ParallelPresenceRuleEvaluationError ParallelRuleRowOutcome := do
  let verdict ← evaluate row preliminary
  let outcome ← match verdict with
    | .fired _ => do
        let pointer ← (pair.errorSide row).messagePointer model outerEnvironment pair.errorField
          |>.mapError .join
        pure ((pair.core condition).emitAtCoordinates pointer.coordinates verdict)
    | .notFired | .unknown => pure ((pair.core condition).emitAt [] verdict)
  pure { outerEnvironment, iterationToken := row.iterationToken, key := row.key, outcome }

/-- Traverse the certified key union in lexical order, within each actual one-sided frame when present. The supplied condition evaluator consumes the same resolved rows used for error projection. -/
def evalFullWith (pair : CheckedParallelFieldPair model) (condition : Condition)
    (evaluate : ResolvedParallelIndexRow → CheckedIndexPreliminary model →
      Except ParallelPresenceRuleEvaluationError Verdict)
    (preliminary : CheckedIndexPreliminary model) (outer : Env := []) :
    Except ParallelPresenceRuleEvaluationError (List ParallelRuleRowOutcome) := do
  let runJoin := fun frameOuter (join : ResolvedParallelIndexJoin) =>
    join.rows.mapM (pair.evalRow condition evaluate preliminary frameOuter)
  match pair.groups.outerScopePlan with
  | .common _ =>
      let join ← preliminary.resolveCheckedParallelIndexJoin pair.groups outer |>.mapError .join
      runJoin outer join
  | .framed _ _ _ =>
      let frames ← preliminary.resolveCheckedParallelFrameEnvironments pair.groups outer |>.mapError .join
      let rows ← frames.mapM fun frame => do
        let join ← preliminary.resolveCheckedParallelIndexJoinInFrame pair.groups frame outer |>.mapError .join
        runJoin frame join
      pure rows.flatten

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
