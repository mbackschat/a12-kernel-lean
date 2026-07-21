import A12Kernel.Elaboration.NumericExpression
import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Semantics.ComputationCondition

/-! # Checked literal-Number generated validation

This capsule admits one nonrepeatable Number target, an optional common precondition, and a complete nonempty literal table: either one optionally guarded operation or at least two guarded operations, with optional per-alternative fixed tolerance. Computation lowers every present guard through the shared first-match mechanism; the generated rule structurally translates the same guard syntax into ordinary validation conditions, places the common guard outside the alternatives' declaration-ordered disjunction, and retains every mismatch branch. Zero/default authoring, expression operations, repeatable evaluation, warning-suppressed assignment legality, runtime target checks, and general computation authoring remain outside.
-/

namespace A12Kernel

/-- One literal Number alternative with validation-only tolerance metadata. First-match computation selection deliberately consumes only the inherited precondition and operation. -/
structure LiteralNumberComputationAlternative extends
    ComputationAlternative DecodedNumericLiteral where
  tolerance : Option NumericToleranceRange := none
  deriving Repr, DecidableEq

/-- The sole source alternative may omit its precondition. It remains distinct from a guarded row so the semantic core never fabricates an always-true condition. -/
structure SingleLiteralNumberComputationAlternative where
  precondition : Option ComputationCondition := none
  operation : DecodedNumericLiteral
  tolerance : Option NumericToleranceRange := none
  deriving Repr, DecidableEq

/-- A guarded table with at least two alternatives. -/
structure GuardedLiteralNumberAlternatives where
  first : LiteralNumberComputationAlternative
  second : LiteralNumberComputationAlternative
  remaining : List LiteralNumberComputationAlternative := []
  deriving Repr, DecidableEq

namespace GuardedLiteralNumberAlternatives

/-- Recover the complete authored alternative order. The two leading fields make an empty or singleton table unrepresentable in this fragment. -/
def declaredAlternatives (alternatives : GuardedLiteralNumberAlternatives) :
    List LiteralNumberComputationAlternative :=
  alternatives.first :: alternatives.second :: alternatives.remaining

/-- Computation consumes every guarded row in declaration order and stops at the first holding row. -/
def selectFirst (alternatives : GuardedLiteralNumberAlternatives)
    (commonPrecondition : Option ComputationCondition)
    (context : ScalarComputationContext) :
    ComputationAlternativeSelection DecodedNumericLiteral :=
  ComputationAlternative.selectFirst
    (ComputationAlternative.expandCommonPrecondition
      commonPrecondition
      (alternatives.declaredAlternatives.map
        LiteralNumberComputationAlternative.toComputationAlternative)) context

end GuardedLiteralNumberAlternatives

namespace SingleLiteralNumberComputationAlternative

/-- Select the sole operation directly only when both source guards are absent. Every present guard still uses the shared ordered selector and common-precondition expansion. -/
def selectFirst (alternative : SingleLiteralNumberComputationAlternative)
    (commonPrecondition : Option ComputationCondition)
    (context : ScalarComputationContext) :
    ComputationAlternativeSelection DecodedNumericLiteral :=
  match alternative.precondition, commonPrecondition with
  | none, none => .selected alternative.operation
  | none, some common =>
      ComputationAlternative.selectFirst
        [{ precondition := common, operation := alternative.operation }] context
  | some precondition, common =>
      ComputationAlternative.selectFirst
        (ComputationAlternative.expandCommonPrecondition common
          [{ precondition, operation := alternative.operation }]) context

end SingleLiteralNumberComputationAlternative

/-- The complete nonempty literal table fragment: either one optionally guarded row or at least two fully guarded rows. -/
inductive LiteralNumberComputationAlternatives where
  | singleton (alternative : SingleLiteralNumberComputationAlternative)
  | guarded (alternatives : GuardedLiteralNumberAlternatives)
  deriving Repr, DecidableEq

/-- One checked literal-Number computation shell shared by runtime selection and generated validation. -/
structure LiteralNumberComputation where
  targetField : FieldId
  name : String
  commonPrecondition : Option ComputationCondition := none
  alternatives : LiteralNumberComputationAlternatives
  messagePlan : MessageRenderPlan
  deriving Repr, DecidableEq

namespace LiteralNumberComputation

def selectFirst (computation : LiteralNumberComputation)
    (context : ScalarComputationContext) :
    ComputationAlternativeSelection DecodedNumericLiteral :=
  match computation.alternatives with
  | .singleton alternative =>
      alternative.selectFirst computation.commonPrecondition context
  | .guarded alternatives =>
      alternatives.selectFirst computation.commonPrecondition context

end LiteralNumberComputation

/-- Authored location of a computation guard. Alternative indices are one-based, matching source diagnostics. -/
inductive GeneratedComputationGuardPosition where
  | common
  | alternative (index : Nat)
  deriving Repr, DecidableEq

inductive GeneratedComputationValidationError where
  | resolve (error : ResolveError)
  | targetNotNumber (field : FieldId)
  | targetSelfReference (guard : GeneratedComputationGuardPosition)
  | operationScaleMismatch (alternative : Nat)
      (targetScale : Nat) (authoredScale : Int)
  | condition (error : ElabError)
  | rule (error : FlatRuleAssemblyError)
  deriving Repr, DecidableEq

private def FlatModel.resolveGeneratedGuardField
    (model : FlatModel) (field : FieldId) :
    Except GeneratedComputationValidationError FlatField := do
  let declaration ← (model.resolveNonrepeatableDeclarationById field).mapError
    GeneratedComputationValidationError.resolve
  match declaration.policy.kind with
  | .number info => pure (.number { id := declaration.id, info })
  | .boolean => pure (.boolean { id := declaration.id })
  | .confirm => pure (.confirm { id := declaration.id })
  | .string => pure (.string { id := declaration.id })
  | .temporal kind components =>
      pure (.temporal { id := declaration.id, kind, components })

private def FlatModel.resolveGeneratedNumberTarget
    (model : FlatModel) (field : FieldId) :
    Except GeneratedComputationValidationError FlatNumberField := do
  let declaration ← (model.resolveNonrepeatableDeclarationById field).mapError
    GeneratedComputationValidationError.resolve
  match declaration.toNumberField? with
  | some target => pure target
  | none => throw (.targetNotNumber field)

namespace ComputationCondition

/-- Whether this condition mentions the computed target directly. The checked fragment has already resolved every path to a field ID. -/
def referencesField (condition : ComputationCondition) (target : FieldId) : Bool :=
  match condition with
  | .fieldFilled field | .fieldNotFilled field => field == target
  | .and left right | .or left right =>
      left.referencesField target || right.referencesField target

/-- Translate guard syntax without evaluating it. Validation then applies its own phase observation, unknown handling, connective algebra, and polarity. -/
private def lowerForGeneratedValidationUnchecked (model : FlatModel) :
    ComputationCondition →
      Except GeneratedComputationValidationError FlatCondition
  | .fieldFilled field => do
      pure (.fieldFilled (← model.resolveGeneratedGuardField field))
  | .fieldNotFilled field => do
      pure (.fieldNotFilled (← model.resolveGeneratedGuardField field))
  | .and left right => do
      pure (.and
        (← left.lowerForGeneratedValidationUnchecked model)
        (← right.lowerForGeneratedValidationUnchecked model))
  | .or left right => do
      pure (.or
        (← left.lowerForGeneratedValidationUnchecked model)
        (← right.lowerForGeneratedValidationUnchecked model))

/-- Reject a computed-target reference before translating the otherwise admitted guard syntax into validation phase. -/
def lowerForGeneratedValidation (condition : ComputationCondition)
    (model : FlatModel) (target : FieldId)
    (position : GeneratedComputationGuardPosition) :
    Except GeneratedComputationValidationError FlatCondition :=
  if condition.referencesField target then
    throw (.targetSelfReference position)
  else
    condition.lowerForGeneratedValidationUnchecked model

end ComputationCondition

/-- One literal comparison in the generated rule. Omitted metadata means strict inequality; a present band reuses the shared tolerance operator. -/
def generatedLiteralNumberComparison (target : FlatNumberField)
    (operation : Rat)
    (tolerance : Option NumericToleranceRange) : FlatCondition :=
  let mismatch := match tolerance with
    | none => NumericValidationOp.ordinary .notEqual
    | some range => .tolerance range
  .compare (.number mismatch target operation)

/-- Add the source guard to one literal comparison without changing either subtree. -/
def generatedLiteralNumberMismatch (target : FlatNumberField)
    (guard : FlatCondition) (operation : Rat)
    (tolerance : Option NumericToleranceRange) : FlatCondition :=
  .and guard (generatedLiteralNumberComparison target operation tolerance)

/-- Join already-lowered mismatch branches by left-associated `Or`, preserving declaration order. The caller supplies the structurally guaranteed first branch. -/
def disjoinGeneratedNumberMismatches (first : FlatCondition)
    (remaining : List FlatCondition) : FlatCondition :=
  remaining.foldl .or first

/-- The admitted generated shape. Every supplied mismatch remains below one target-filled gate and optional common guard; this function never calls the first-match selector. -/
def generatedNumberCondition (target : FlatNumberField)
    (commonGuard : Option FlatCondition) (firstMismatch : FlatCondition)
    (remainingMismatches : List FlatCondition) :
    FlatCondition :=
  let alternatives := disjoinGeneratedNumberMismatches
    firstMismatch remainingMismatches
  .and (.fieldFilled (.number target))
    (match commonGuard with
    | none => alternatives
    | some common => .and common alternatives)

private def checkGeneratedOperationScale (target : FlatNumberField)
    (alternative : Nat) (operation : DecodedNumericLiteral)
    (tolerance : Option NumericToleranceRange) :
    Except GeneratedComputationValidationError Unit :=
  match tolerance with
  | some _ => pure ()
  | none =>
      if exactNumericScaleComparisonAllowed
          (NumericScaleSummary.field target.info.scale)
          (NumericScaleSummary.constant operation.authoredScale) then
        pure ()
      else
        throw (.operationScaleMismatch alternative target.info.scale
          operation.authoredScale)

private def checkGeneratedOperationScales (target : FlatNumberField) :
    Nat → List LiteralNumberComputationAlternative →
      Except GeneratedComputationValidationError Unit
  | _, [] => pure ()
  | alternativeIndex, alternative :: remaining => do
      checkGeneratedOperationScale target alternativeIndex alternative.operation
        alternative.tolerance
      checkGeneratedOperationScales target (alternativeIndex + 1) remaining

/-- Preserve source diagnostic order by admitting every literal scale before lowering any guard. -/
private def checkLiteralNumberAlternativeScales (target : FlatNumberField) :
    LiteralNumberComputationAlternatives →
      Except GeneratedComputationValidationError Unit
  | .singleton alternative =>
      checkGeneratedOperationScale target 1 alternative.operation
        alternative.tolerance
  | .guarded alternatives =>
      checkGeneratedOperationScales target 1 alternatives.declaredAlternatives

private def lowerGeneratedLiteralNumberMismatch (model : FlatModel)
    (target : FlatNumberField)
    (alternativeIndex : Nat)
    (alternative : LiteralNumberComputationAlternative) :
    Except GeneratedComputationValidationError FlatCondition := do
  let guard ← alternative.precondition.lowerForGeneratedValidation model
    target.id (.alternative alternativeIndex)
  pure (generatedLiteralNumberMismatch target guard alternative.operation.value
    alternative.tolerance)

private def lowerGeneratedLiteralNumberMismatches (model : FlatModel)
    (target : FlatNumberField) :
    Nat → List LiteralNumberComputationAlternative →
      Except GeneratedComputationValidationError (List FlatCondition)
  | _, [] => pure []
  | alternativeIndex, alternative :: remaining => do
      let mismatch ← lowerGeneratedLiteralNumberMismatch model target
        alternativeIndex alternative
      let remainingMismatches ← lowerGeneratedLiteralNumberMismatches model target
        (alternativeIndex + 1) remaining
      pure (mismatch :: remainingMismatches)

private def lowerSingleLiteralNumberMismatch (model : FlatModel)
    (target : FlatNumberField)
    (alternative : SingleLiteralNumberComputationAlternative) :
    Except GeneratedComputationValidationError FlatCondition := do
  let comparison := generatedLiteralNumberComparison target
    alternative.operation.value alternative.tolerance
  match alternative.precondition with
  | none => pure comparison
  | some precondition => do
      let guard ← precondition.lowerForGeneratedValidation model target.id
        (.alternative 1)
      pure (.and guard comparison)

private def lowerLiteralNumberAlternatives (model : FlatModel)
    (target : FlatNumberField) :
    LiteralNumberComputationAlternatives →
      Except GeneratedComputationValidationError (FlatCondition × List FlatCondition)
  | .singleton alternative => do
      pure (← lowerSingleLiteralNumberMismatch model target alternative, [])
  | .guarded alternatives => do
      let firstMismatch ← lowerGeneratedLiteralNumberMismatch model target
        1 alternatives.first
      let remainingMismatches ←
        lowerGeneratedLiteralNumberMismatches model target 2
          (alternatives.second :: alternatives.remaining)
      pure (firstMismatch, remainingMismatches)

/-- Check the model, target, guard fields, and unsuppressed exact-comparison scales before assembling the generated ERROR rule at the target. This does not claim general computation-table, assignment, or runtime target legality. -/
def assembleGeneratedLiteralNumberRule (model : FlatModel)
    (computation : LiteralNumberComputation) :
    Except GeneratedComputationValidationError
      (CheckedResolvedFlatRule model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let target ← model.resolveGeneratedNumberTarget computation.targetField
      checkLiteralNumberAlternativeScales target computation.alternatives
      let commonGuard ← match computation.commonPrecondition with
        | none => pure none
        | some common =>
            pure (some (← common.lowerForGeneratedValidation model target.id .common))
      let (firstMismatch, remainingMismatches) ←
        lowerLiteralNumberAlternatives model target computation.alternatives
      let core := generatedNumberCondition target commonGuard
        firstMismatch remainingMismatches
      let checked ←
        (core.checkAgainstValidatedModel model hModel).mapError
          GeneratedComputationValidationError.condition
      (assembleResolvedFlatRule model checked computation.targetField
        computation.name .error computation.messagePlan).mapError
          GeneratedComputationValidationError.rule

end A12Kernel
