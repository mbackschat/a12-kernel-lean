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

/-- Anchors preserve the small pair API; explicit declarations retain every authored payload and
bound scalar read independently of the topology anchors (spec/07 parallel iteration). -/
inductive ParallelFieldOperand where
  | left
  | right
  | field (declaration : FlatFieldDecl)
  deriving Repr, DecidableEq

inductive ParallelFieldLeafOf (Field : Type) where
  | groupPresence (op : GroupPresenceOperator) (reference : ResolvedGroupReference)
  | presence (side : Field) (op : RepeatableFieldPresenceOperator)
  | numeric (op : NumericComparisonOp) (left right : Field)
  | fill (op : FieldFillQuantifier) (left right : Field)
  | comparison (value : NumericComparisonOf Field)
  deriving Repr, DecidableEq

abbrev ParallelFieldLeaf := ParallelFieldLeafOf ParallelFieldOperand

abbrev ParallelFieldCondition := ConditionTree ParallelFieldLeaf

def CheckedParallelFieldPair.declaration (pair : CheckedParallelFieldPair model) :
    ParallelFieldOperand → FlatFieldDecl
  | .left => pair.leftDeclaration
  | .right => pair.rightDeclaration
  | .field declaration => declaration

def CheckedParallelFieldPair.admitsOperand (pair : CheckedParallelFieldPair model)
    (operand : ParallelFieldOperand) : Bool :=
  let declaration := pair.declaration operand
  let scope := match pair.groups.outerScopePlan with
    | .common common => common
    | .framed _ common frame => common ++ frame
  (model.lookupUniqueId declaration.id).toOption == some declaration &&
    ((pair.groups.leftGroup.path.isPrefixOf declaration.groupPath &&
        declaration.repeatableScope == pair.leftDeclaration.repeatableScope) ||
     (pair.groups.rightGroup.path.isPrefixOf declaration.groupPath &&
        declaration.repeatableScope == pair.rightDeclaration.repeatableScope) ||
     declaration.repeatableScope.isPrefixOf scope)

namespace ParallelFieldLeaf

def fields : ParallelFieldLeaf → List ParallelFieldOperand
  | .groupPresence _ _ => []
  | .presence field _ => [field]
  | .numeric _ lhs rhs | .fill _ lhs rhs => [lhs, rhs]
  | .comparison value => value.left.atoms ++ value.right.atoms
def uses (pair : CheckedParallelFieldPair model) (side : ParallelFieldSide)
    (leaf : ParallelFieldLeaf) : Bool :=
  let group := match side with | .left => pair.groups.leftGroup | .right => pair.groups.rightGroup
  match leaf with
  | .groupPresence _ reference => group.path.isPrefixOf reference.path
  | _ => leaf.fields.any fun field => group.path.isPrefixOf (pair.declaration field).groupPath

/-- Every payload is model-owned and addressable from the join or frame; comparisons reuse the shared authoring and scale gates. -/
def admitted (pair : CheckedParallelFieldPair model) (suppress : Bool)
    (leaf : ParallelFieldLeaf) : Bool :=
  leaf.fields.all (CheckedParallelFieldPair.admitsOperand pair) && match leaf with
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
  | .fill _ lhs rhs => (pair.declaration lhs).id != (pair.declaration rhs).id
  | .comparison value =>
      { value with suppressExactScaleWarning := suppress }.admittedWith
        (fun field => (pair.declaration field).toNumberField?.isSome)
        (fun field => match (pair.declaration field).toNumberField? with
          | some number => .field number.info.scale
          | none => { scale := .unknown, canExpandScale := false })

/-- Direct fields and operation-list wrappers retain the ordinary literal-sensitive guard;
composite arithmetic has its own parse-tree branch (spec/07 §2). -/
private def numericGuard (participates : ParallelFieldOperand → Bool)
    (value : NumericComparisonOf ParallelFieldOperand) : IterationGuardStatus :=
  let rec sensitive : AuthoredNumericExpr ParallelFieldOperand → Option Bool
    | .group body => sensitive body
    | .atom _ => some false
    | .abs _ | .round _ _ _ | .extremum _ _ _ | .extremumCall _ _ => some true
    | _ => none
  let classify expression constant := do
    let rejectMixed ← sensitive expression
    let .literal literal := constant | none
    let bits := expression.atoms.map participates
    if !bits.any id then return IterationGuardStatus.noReference
    if rejectMixed && !bits.all id then return .unguarded
    let some converted := literal.javaRoundedInt32? | return .unclassified
    pure (value.op.literalIterationGuard converted bits rejectMixed)
  match classify value.left value.right with
  | some result => result
  | none => match classify value.right value.left with
    | some result => result
    | none => if (value.left.atoms ++ value.right.atoms).any participates then .guarded else .noReference

/-- Presence quantifiers share one participation rule for ordinary and parallel iteration.
The two mixed-sensitive operators require every operand to iterate (spec/07 §2; IterationNotValidVisitor). -/
private def fillGuard (participates : ParallelFieldOperand → Bool)
    (op : FieldFillQuantifier) (left right : ParallelFieldOperand) : IterationGuardStatus :=
  if !(participates left || participates right) then .noReference else
    match op with
    | .noFieldFilled | .notAllFieldsFilled | .notExactlyOneFieldFilled => .unguarded
    | .atLeastOneFieldFilled | .fieldsNotCollectivelyFilled =>
        if participates left && participates right then .guarded else .unguarded
    | .allFieldsFilled | .moreThanOneFieldFilled => .guarded

/-- For direct fields on the joined pair, the parallel guard follows the source operator's iteration test, not its runtime empty verdict (Kernel `IterationNotValidVisitor`). -/
def guards (pair : CheckedParallelFieldPair model) : ParallelFieldLeaf → Bool
  | leaf@(.groupPresence .filled _) => leaf.uses pair .left || leaf.uses pair .right
  | .groupPresence .notFilled _ => false
  | leaf@(.presence _ .filled) | leaf@(.numeric _ _ _) =>
      leaf.uses pair .left || leaf.uses pair .right
  | .comparison value => decide (numericGuard (fun field =>
      pair.groups.leftGroup.path.isPrefixOf (pair.declaration field).groupPath ||
      pair.groups.rightGroup.path.isPrefixOf (pair.declaration field).groupPath) value = .guarded)
  | .presence _ .notFilled => false
  | .fill op left right => decide (fillGuard (fun field =>
      pair.groups.leftGroup.path.isPrefixOf (pair.declaration field).groupPath ||
      pair.groups.rightGroup.path.isPrefixOf (pair.declaration field).groupPath) op left right = .guarded)

/-- A one-sided frame has ordinary iteration levels in addition to the parallel key level. Direct pair leaves specialize the existing iteration guard table at each such level. -/
def guardAt (pair : CheckedParallelFieldPair model) (level : RepeatableLevel)
    (value : ParallelFieldLeaf) : IterationGuardStatus :=
  match value with
  | .comparison value => numericGuard (fun field => (pair.declaration field).repeatableScope.contains level) value
  | .groupPresence op reference =>
      if !reference.boundRepeatableScope.contains level then .noReference
      else if op.canFireOnEmpty then .unguarded else .guarded
  | .fill op left right => fillGuard
      (fun field => (pair.declaration field).repeatableScope.contains level) op left right
  | .presence field op =>
      if !(pair.declaration field).repeatableScope.contains level then .noReference
      else match op with | .filled => .guarded | .notFilled => .unguarded
  | .numeric _ left right =>
      if (pair.declaration left).repeatableScope.contains level ||
          (pair.declaration right).repeatableScope.contains level then .guarded else .noReference

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

/-- Full and partial calls share scalar consumers; absent observations mean call-local unavailability without an invented formal cause. -/
def evalWith (pair : CheckedParallelFieldPair model)
    (read : ParallelFieldOperand → Except ParallelPresenceRuleEvaluationError (Option CellObservation))
    (readGroup : ResolvedGroupReference → Except ParallelPresenceRuleEvaluationError GroupPresenceState) :
    ParallelFieldLeaf → Except ParallelPresenceRuleEvaluationError Verdict
  | .groupPresence op reference => do
      pure (op.eval (← readGroup reference))
  | .presence side op => do
      pure ((← read side).map op.eval |>.getD .unknown)
  | .numeric op lhs rhs => do
      let some a := (pair.declaration lhs).toNumberField? | throw .unsupportedCondition
      let some b := (pair.declaration rhs).toNumberField? | throw .unsupportedCondition
      let leftValue ← read lhs
      let rightValue ← read rhs
      match leftValue, rightValue with
      | some left, some right =>
          pure (op.eval (left.asDirectNumericComparisonOperand a.info)
            (right.asDirectNumericComparisonOperand b.info))
      | _, _ => pure .unknown
  | .comparison value => do
      let observe := fun field => do
        let some number := (pair.declaration field).toNumberField? | throw .unsupportedCondition
        let observation ← read field
        pure (observation.map (fun cell =>
          (cell.asDirectNumericComparisonOperand number.info).toValidationArithmetic)
          |>.getD (.error NumericValidationUnavailable.silentlyUnavailable))
      let left ← value.left.mapM observe
      let right ← value.right.mapM observe
      pure ({ value with left, right }.evalWith id)
  | .fill op lhs rhs => do
      let unknown : ValidationFillTally := { filled := 0, empty := 0, unknown := 1, uninstantiated := 0 }
      let left ← read lhs
      let right ← read rhs
      pure ((op.evalValidation ((left.map (·.asValidationFillTally) |>.getD unknown).combine
        (right.map (·.asValidationFillTally) |>.getD unknown))).asConservativeVerdict)

/-- Missing and invalid joined sides enter the same scalar observation consumers as physical reads. -/
def eval (pair : CheckedParallelFieldPair model) (row : ResolvedParallelIndexRow)
    (preliminary : CheckedIndexPreliminary model) (outer : Env := []) : ParallelFieldLeaf →
    Except ParallelPresenceRuleEvaluationError Verdict :=
  evalWith pair
    (fun field => do
      let declaration := pair.declaration field
      if row.left.group.path.isPrefixOf declaration.groupPath ||
          row.right.group.path.isPrefixOf declaration.groupPath then
        (row.readValidation preliminary declaration.id).map some |>.mapError .join
      else
        let path ← outer.pathForScope declaration.repeatableScope
          |>.mapError (fun error => .join (.environment error))
        let cell ← preliminary.readAuthoredValidation { field := declaration.id, path }
          |>.mapError (fun error => .join (.document error))
        pure (some (observeCell .validation cell)))
    (groupState row preliminary)

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
  | .leaf leaf => leaf.fields.map fun field =>
      { sameEntity := (pair.declaration field).id == pair.errorField }
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
    (messageCache : Option MessageIndexContext := none) :
    Except ParallelPresenceRuleEvaluationError (List ParallelRuleRowOutcome) :=
  rule.pair.evalWith rule.condition
    (fun outer row view => rule.condition.evalVerdictExcept (ParallelFieldLeaf.eval rule.pair row view outer))
    preliminary outer messageCache

/-- Parallel unions are local to each in-capacity common outer row. An implicit outer row has no child index entries, hence no parallel evaluation to fabricate. -/
def CheckedParallelFieldRule.evalDocument (rule : CheckedParallelFieldRule model)
    (preliminary : CheckedIndexPreliminary model)
    (messageCache : Option MessageIndexContext := none) :
    Except ParallelPresenceRuleEvaluationError (List ParallelRuleRowOutcome) := do
  let scope := match rule.pair.groups.outerScopePlan with
    | .common shared | .framed _ shared _ => shared
  let environments ← if scope.isEmpty then pure [[]]
    else preliminary.base.inCapacityRowEnvironments scope |>.mapError .rows
  pure (← environments.mapM (fun outer => rule.evalFull preliminary outer messageCache)).flatten

end A12Kernel
