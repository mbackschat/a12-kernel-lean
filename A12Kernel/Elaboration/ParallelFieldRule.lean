import A12Kernel.Elaboration.ParallelFieldPair
import A12Kernel.Semantics.NumericExpression
import A12Kernel.Semantics.ValidationFillQuantifier
import A12Kernel.Elaboration.ValidationCondition.Core

/-! # Parallel validation over one checked field pair

The pair owns key identity, optional physical rows and error projection. This carrier retains the existing numeric polarity, field-fill tally and connective evaluators; its leaves select the pair's declarations rather than synthesizing cell addresses for absent sides.
-/

namespace A12Kernel

inductive ParallelFieldSide where
  | left
  | right
  deriving Repr, BEq, DecidableEq

inductive ParallelFieldLeafOf (Field : Type) where
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

def uses (side : ParallelFieldSide) : ParallelFieldLeaf → Bool
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
  | .presence _ _ => true
  | .fill _ lhs rhs => lhs != rhs

/-- For direct fields on the joined pair, the parallel guard follows the source operator's iteration test, not its runtime empty verdict (Kernel `IterationNotValidVisitor`). -/
def guards : ParallelFieldLeaf → Bool
  | .presence _ .filled | .numeric _ _ _ => true
  | .presence _ .notFilled => false
  | .fill op _ _ => match op with
    | .noFieldFilled | .notAllFieldsFilled | .notExactlyOneFieldFilled => false
    | .allFieldsFilled | .atLeastOneFieldFilled | .moreThanOneFieldFilled
    | .fieldsNotCollectivelyFilled => true

/-- A one-sided frame has ordinary iteration levels in addition to the parallel key level. Direct pair leaves specialize the existing iteration guard table at each such level. -/
def guardAt (pair : CheckedParallelFieldPair model) (level : RepeatableLevel)
    (value : ParallelFieldLeaf) : IterationGuardStatus :=
  let left := value.uses .left && pair.leftDeclaration.repeatableScope.contains level
  let right := value.uses .right && pair.rightDeclaration.repeatableScope.contains level
  if !(left || right) then .noReference
  else match value with
    | .presence _ .filled | .numeric _ _ _ => .guarded
    | .presence _ .notFilled => .unguarded
    | .fill op _ _ => match op with
      | .noFieldFilled | .notAllFieldsFilled | .notExactlyOneFieldFilled => .unguarded
      | .atLeastOneFieldFilled | .fieldsNotCollectivelyFilled =>
          if left && right then .guarded else .unguarded
      | .allFieldsFilled | .moreThanOneFieldFilled => .guarded

/-- Missing and invalid joined sides enter the same scalar observation consumers as physical reads. -/
def eval (pair : CheckedParallelFieldPair model) (row : ResolvedParallelIndexRow)
    (preliminary : CheckedIndexPreliminary model) : ParallelFieldLeaf →
    Except ParallelPresenceRuleEvaluationError Verdict
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
def guarded (condition : ParallelFieldCondition) : Bool :=
  decide (condition.iterationGuardStatus
    (fun value => if value.guards then .guarded else .unguarded) = .guarded)

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
    condition.anyLeaf (ParallelFieldLeaf.uses .left) &&
    condition.anyLeaf (ParallelFieldLeaf.uses .right) && condition.guarded && framesGuarded pair condition

end ParallelFieldCondition

structure CheckedParallelFieldRule (model : FlatModel) where
  private mk ::
  pair : CheckedParallelFieldPair model
  condition : ParallelFieldCondition
  suppressExactScaleWarning : Bool
  admitted : condition.admitted pair suppressExactScaleWarning = true

/-- Public construction retains the pair's topology certificate and checks the entire condition before any read. -/
def checkParallelFieldRule (model : FlatModel)
    (leftField rightField errorField : FieldId) (condition : ParallelFieldCondition)
    (errorCode : String) (severity : ValidationSeverity) (messagePlan : MessageRenderPlan)
    (suppressExactScaleWarning : Bool := false) :
    Except ParallelPresenceRuleAssemblyError (CheckedParallelFieldRule model) := do
  let pair ← checkParallelFieldPair model leftField rightField errorField errorCode severity messagePlan
  if h : condition.admitted pair suppressExactScaleWarning = true then
    pure { pair, condition, suppressExactScaleWarning, admitted := h }
  else throw .incoherentCondition

/-- Execute the certified tree on the shared lexical join/frame traversal. Structural failures stay separate from semantic UNKNOWN. -/
def CheckedParallelFieldRule.evalFull (rule : CheckedParallelFieldRule model)
    (preliminary : CheckedIndexPreliminary model) (outer : Env := []) :
    Except ParallelPresenceRuleEvaluationError (List ParallelRuleRowOutcome) :=
  rule.pair.evalFullWith rule.condition
    (fun row view => rule.condition.evalVerdictExcept (ParallelFieldLeaf.eval rule.pair row view))
    preliminary outer

end A12Kernel
