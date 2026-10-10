import A12Kernel.Elaboration.ParallelFieldPair
import A12Kernel.Semantics.NumericExpression
import A12Kernel.Semantics.ValidationFillQuantifier
import A12Kernel.Elaboration.IterationGuard
import A12Kernel.Elaboration.ErrorTargetDeclaration

/-! # Parallel validation over one checked field/group pair

The pair owns key identity, optional physical rows and error projection. Field leaves retain the existing scalar consumers; group leaves reuse resolved group content after index availability. Topology anchors never count as authored references. See spec/07 §2 and the parallel-group-outer source checkpoint.
-/

namespace A12Kernel

inductive ParallelFieldSide where
  | left
  | right
  deriving Repr, BEq, DecidableEq

inductive ParallelFieldLeafOf (Field : Type) where
  | groupPresence (op : GroupPresenceOperator) (reference : ResolvedGroupReference)
  | presence (side : Field) (op : RepeatableFieldPresenceOperator)
  | numeric (op : NumericComparisonOp) (left right : Field)
  | fill (op : FieldFillQuantifier) (left right : Field)
  deriving Repr, DecidableEq

abbrev ParallelFieldLeaf := ParallelFieldLeafOf ParallelFieldSide

abbrev ParallelFieldCondition := ConditionTree ParallelFieldLeaf

def CheckedParallelFieldPair.declaration (pair : CheckedParallelFieldPair model) :
    ParallelFieldSide → FlatFieldDecl
  | .left => pair.leftDeclaration
  | .right => pair.rightDeclaration

namespace ParallelFieldLeaf

def uses (pair : CheckedParallelFieldPair model) (side : ParallelFieldSide) : ParallelFieldLeaf → Bool
  | .groupPresence _ reference =>
      let group := match side with | .left => pair.groups.leftGroup | .right => pair.groups.rightGroup
      group.path.isPrefixOf reference.path
  | .presence selected _ => side == selected
  | .numeric _ lhs rhs => side == lhs || side == rhs
  | .fill _ lhs rhs => side == lhs || side == rhs

/-- The direct pair profile uses the existing exact-comparison scale warning and its sole suppression. -/
def admitted (pair : CheckedParallelFieldPair model) (suppress : Bool) : ParallelFieldLeaf → Bool
  | .numeric op lhs rhs =>
      match (pair.declaration lhs).toNumberField?, (pair.declaration rhs).toNumberField? with
      | some a, some b => (NumericValidationOp.ordinary op).acceptsScalesWithSuppression suppress
          (.field a.info.scale) (.field b.info.scale)
      | _, _ => false
  | .groupPresence _ reference =>
      let scope := model.repeatableScopeForGroupPath reference.path
      model.hasGroupPath reference.path && reference.boundRepeatableScope == scope &&
        ((pair.groups.leftGroup.path.isPrefixOf reference.path &&
            scope == pair.leftDeclaration.repeatableScope) ||
         (pair.groups.rightGroup.path.isPrefixOf reference.path &&
            scope == pair.rightDeclaration.repeatableScope) ||
         reference.path.isPrefixOf pair.groups.commonParent)
  | .presence _ _ => true
  | .fill _ lhs rhs => lhs != rhs

/-- For direct fields on the joined pair, the parallel guard follows the source operator's iteration test, not its runtime empty verdict (Kernel `IterationNotValidVisitor`). -/
def guards (pair : CheckedParallelFieldPair model) : ParallelFieldLeaf → Bool
  | leaf@(.groupPresence .filled _) => leaf.uses pair .left || leaf.uses pair .right
  | .groupPresence .notFilled _ => false
  | .presence _ .filled | .numeric _ _ _ => true
  | .presence _ .notFilled => false
  | .fill op _ _ => match op with
    | .noFieldFilled | .notAllFieldsFilled | .notExactlyOneFieldFilled => false
    | .allFieldsFilled | .atLeastOneFieldFilled | .moreThanOneFieldFilled
    | .fieldsNotCollectivelyFilled => true

/-- A one-sided frame has ordinary iteration levels in addition to the parallel key level. Direct pair leaves specialize the existing iteration guard table at each such level. -/
def guardAt (pair : CheckedParallelFieldPair model) (level : RepeatableLevel)
    (value : ParallelFieldLeaf) : IterationGuardStatus :=
  match value with
  | .groupPresence op reference =>
      if !reference.boundRepeatableScope.contains level then .noReference
      else if op.canFireOnEmpty then .unguarded else .guarded
  | _ =>
    let left := value.uses pair .left && pair.leftDeclaration.repeatableScope.contains level
    let right := value.uses pair .right && pair.rightDeclaration.repeatableScope.contains level
    if !(left || right) then .noReference
    else if value.guards pair then
      match value with
      | .fill .atLeastOneFieldFilled _ _ | .fill .fieldsNotCollectivelyFilled _ _ =>
          if left && right then .guarded else .unguarded
      | _ => .guarded
    else .unguarded

/-- Joined group reads preserve index unavailability before deriving physical group content; ancestors use the same outer coordinates without acquiring a join-level reference. -/
private def groupState (row : ResolvedParallelIndexRow)
    (preliminary : CheckedIndexPreliminary model) (reference : ResolvedGroupReference) :
    Except ParallelPresenceRuleEvaluationError GroupPresenceState := do
  let side := if row.left.group.path.isPrefixOf reference.path then some row.left
    else if row.right.group.path.isPrefixOf reference.path then some row.right else none
  let environment := match side with
    | some selected => selected.environment
    | none => row.left.environment.orElse fun _ => row.right.environment
  match environment with
  | some environment =>
      let input ← preliminary.groupPresenceInput reference.path environment .fullyRelevant false
        |>.mapError .group
      pure input.derive
  | none =>
      pure {
        content := false
        erroneous := false
        relevance := if side.any (·.unavailableKey.isSome) then .noneRelevant else .fullyRelevant }

/-- Missing and invalid joined sides enter the same scalar observation consumers as physical reads. -/
def eval (pair : CheckedParallelFieldPair model) (row : ResolvedParallelIndexRow)
    (preliminary : CheckedIndexPreliminary model) : ParallelFieldLeaf →
    Except ParallelPresenceRuleEvaluationError Verdict
  | .groupPresence op reference => do
      pure (op.eval (← groupState row preliminary reference))
  | .presence side op => do
      let observation ← row.readValidation preliminary (pair.declaration side).id |>.mapError .join
      pure (op.eval observation)
  | .numeric op lhs rhs => do
      let some a := (pair.declaration lhs).toNumberField? | throw .unsupportedCondition
      let some b := (pair.declaration rhs).toNumberField? | throw .unsupportedCondition
      let leftValue ← row.readValidation preliminary a.id |>.mapError .join
      let rightValue ← row.readValidation preliminary b.id |>.mapError .join
      pure (op.eval (leftValue.asDirectNumericComparisonOperand a.info)
        (rightValue.asDirectNumericComparisonOperand b.info))
  | .fill op lhs rhs => do
      let leftValue ← row.readValidation preliminary (pair.declaration lhs).id |>.mapError .join
      let rightValue ← row.readValidation preliminary (pair.declaration rhs).id |>.mapError .join
      pure ((op.evalValidation (leftValue.asValidationFillTally.combine
        rightValue.asValidationFillTally)).asConservativeVerdict)

end ParallelFieldLeaf

namespace ParallelFieldCondition

/-- A conjunction needs a guarding member; every disjunction branch needs one (`IterationNotValidVisitor.visit(ICompositeCondition)`). -/
def guarded (pair : CheckedParallelFieldPair model) (condition : ParallelFieldCondition) : Bool :=
  condition.iterationGuarded (ParallelFieldLeaf.guards pair)

/-- Common outer coordinates are caller-bound; each extra frame level needs a guard from its own side. -/
def framesGuarded (pair : CheckedParallelFieldPair model) (condition : ParallelFieldCondition) : Bool :=
  match pair.groups.outerScopePlan with
  | .common _ => true
  | .framed _ common frame => frame.all fun level =>
      common.contains level || decide
        (condition.iterationGuardStatus (ParallelFieldLeaf.guardAt pair level) = .guarded)

def admitted (pair : CheckedParallelFieldPair model) (suppress : Bool)
    (condition : ParallelFieldCondition) : Bool :=
  condition.allLeaves (ParallelFieldLeaf.admitted pair suppress) &&
    condition.anyLeaf (ParallelFieldLeaf.uses pair .left) &&
    condition.anyLeaf (ParallelFieldLeaf.uses pair .right) && condition.guarded pair && framesGuarded pair condition

/-- Authored references alone satisfy the error-target gate; topology anchor declarations are not implicit condition references. -/
def references (pair : CheckedParallelFieldPair model) : ParallelFieldCondition → List ConditionReference
  | .leaf (.groupPresence _ reference) => [{
      isGroup := true, isRootGroup := reference.path.length == 1,
      ancestorOrEqual := reference.path.isPrefixOf
        (if pair.errorField == pair.leftDeclaration.id then pair.leftDeclaration.groupPath
         else pair.rightDeclaration.groupPath) }]
  | .leaf (.presence side _) => [{ sameEntity := (pair.declaration side).id == pair.errorField }]
  | .leaf (.numeric _ lhs rhs) | .leaf (.fill _ lhs rhs) =>
      [{ sameEntity := (pair.declaration lhs).id == pair.errorField },
       { sameEntity := (pair.declaration rhs).id == pair.errorField }]
  | .and left right | .or left right => references pair left ++ references pair right

def errorTargetRefusal (pair : CheckedParallelFieldPair model) (condition : ParallelFieldCondition) :
    Option KernelStaticDiagnostic :=
  conditionSideRefusal {
    declaration := .declared true, references := condition.references pair,
    iteration := {
      parallelIteration := true
      indexFieldLevel := (if pair.errorField == pair.leftDeclaration.id then pair.groups.leftGroup.path
        else pair.groups.rightGroup.path).length - 1 } }

end ParallelFieldCondition

structure CheckedParallelFieldRule (model : FlatModel) where
  private mk ::
  pair : CheckedParallelFieldPair model
  condition : ParallelFieldCondition
  suppressExactScaleWarning : Bool
  errorTargetAllowed : condition.errorTargetRefusal pair = none
  admitted : condition.admitted pair suppressExactScaleWarning = true

/-- Public construction retains the pair's topology certificate and checks the entire condition before any read. -/
def checkParallelFieldRule (model : FlatModel)
    (leftField rightField errorField : FieldId) (condition : ParallelFieldCondition)
    (errorCode : String) (severity : ValidationSeverity) (messagePlan : MessageRenderPlan)
    (suppressExactScaleWarning : Bool := false) :
    Except ParallelPresenceRuleAssemblyError (CheckedParallelFieldRule model) := do
  let pair ← checkParallelFieldPair model leftField rightField errorField errorCode severity messagePlan
  if hTarget : condition.errorTargetRefusal pair = none then
    if h : condition.admitted pair suppressExactScaleWarning = true then
      pure { pair, condition, suppressExactScaleWarning, errorTargetAllowed := hTarget, admitted := h }
    else throw .incoherentCondition
  else
    match condition.errorTargetRefusal pair with
    | some diagnostic => throw (.static diagnostic)
    | none => throw .incoherentCondition

/-- Execute the certified tree on the shared lexical join/frame traversal. Structural failures stay separate from semantic UNKNOWN. -/
def CheckedParallelFieldRule.evalFull (rule : CheckedParallelFieldRule model)
    (preliminary : CheckedIndexPreliminary model) (outer : Env := [])
    (messageCache : Option MessageIndexCache := none) :
    Except ParallelPresenceRuleEvaluationError (List ParallelRuleRowOutcome) :=
  rule.pair.evalFullWith rule.condition
    (fun row view => rule.condition.evalVerdictExcept (ParallelFieldLeaf.eval rule.pair row view))
    preliminary outer messageCache

/-- Parallel unions are local to each in-capacity common outer row. An implicit outer row has no child index entries, hence no parallel evaluation to fabricate. -/
def CheckedParallelFieldRule.evalDocument (rule : CheckedParallelFieldRule model)
    (preliminary : CheckedIndexPreliminary model)
    (messageCache : Option MessageIndexCache := none) :
    Except ParallelPresenceRuleEvaluationError (List ParallelRuleRowOutcome) := do
  let scope := match rule.pair.groups.outerScopePlan with
    | .common shared | .framed _ shared _ => shared
  let environments ← if scope.isEmpty then pure [[]]
    else preliminary.base.inCapacityRowEnvironments scope |>.mapError .rows
  pure (← environments.mapM (fun outer => rule.evalFull preliminary outer messageCache)).flatten

end A12Kernel
