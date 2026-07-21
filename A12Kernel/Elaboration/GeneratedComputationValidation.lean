import A12Kernel.Elaboration.NumericExpression
import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Semantics.ComputationCondition

/-! # Checked guarded literal-Number generated validation

This capsule admits one nonrepeatable Number target, an optional common precondition, and at least two guarded literal operations with optional per-alternative fixed tolerance. Computation lowers the common guard through the shared first-match mechanism; the generated rule structurally translates the same guard syntax into ordinary validation conditions, places the common guard outside the alternatives' declaration-ordered disjunction, and retains every mismatch branch. Zero/singleton/default authoring, expression operations, repeatable evaluation, warning-suppressed assignment legality, runtime target checks, and general computation authoring remain outside.
-/

namespace A12Kernel

/-- One literal Number alternative with validation-only tolerance metadata. First-match computation selection deliberately consumes only the inherited precondition and operation. -/
structure LiteralNumberComputationAlternative extends
    ComputationAlternative DecodedNumericLiteral where
  tolerance : Option NumericToleranceRange := none
  deriving Repr, DecidableEq

/-- A guarded table with at least two alternatives, which separates first-match computation from all-alternatives validation. Decoded literals retain authored scale until checked lowering; wider computation authoring legality is an input assumption. -/
structure GuardedLiteralNumberComputation where
  targetField : FieldId
  name : String
  commonPrecondition : Option ComputationCondition := none
  first : LiteralNumberComputationAlternative
  second : LiteralNumberComputationAlternative
  remaining : List LiteralNumberComputationAlternative := []
  messagePlan : MessageRenderPlan
  deriving Repr, DecidableEq

namespace GuardedLiteralNumberComputation

/-- Recover the complete authored alternative order. The two leading fields make an empty or singleton table unrepresentable in this fragment. -/
def declaredAlternatives (computation : GuardedLiteralNumberComputation) :
    List LiteralNumberComputationAlternative :=
  computation.first :: computation.second :: computation.remaining

/-- Computation consumes the same authored guards in declaration order and stops at the first holding row. -/
def selectFirst (computation : GuardedLiteralNumberComputation)
    (context : ScalarComputationContext) :
    ComputationAlternativeSelection DecodedNumericLiteral :=
  ComputationAlternative.selectFirst
    (ComputationAlternative.expandCommonPrecondition
      computation.commonPrecondition
      (computation.declaredAlternatives.map
        LiteralNumberComputationAlternative.toComputationAlternative)) context

end GuardedLiteralNumberComputation

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

private def FlatModel.resolveNonrepeatableDeclarationById
    (model : FlatModel) (field : FieldId) :
    Except GeneratedComputationValidationError FlatFieldDecl := do
  let declaration ← (model.lookupUniqueId field).mapError
    GeneratedComputationValidationError.resolve
  if declaration.repeatableScope.isEmpty then
    pure declaration
  else
    throw (.resolve (.repeatableReference declaration.path))

private def FlatModel.resolveGeneratedGuardField
    (model : FlatModel) (field : FieldId) :
    Except GeneratedComputationValidationError FlatField := do
  let declaration ← model.resolveNonrepeatableDeclarationById field
  match declaration.policy.kind with
  | .number info => pure (.number { id := declaration.id, info })
  | .boolean => pure (.boolean { id := declaration.id })
  | .confirm => pure (.confirm { id := declaration.id })
  | .string => pure (.string { id := declaration.id })

private def FlatModel.resolveGeneratedNumberTarget
    (model : FlatModel) (field : FieldId) :
    Except GeneratedComputationValidationError FlatNumberField := do
  let declaration ← model.resolveNonrepeatableDeclarationById field
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

/-- One guarded mismatch in the generated rule. Omitted metadata means strict inequality; a present band reuses the shared tolerance operator. -/
def generatedLiteralNumberMismatch (target : FlatNumberField)
    (guard : FlatCondition) (operation : Rat)
    (tolerance : Option NumericToleranceRange) : FlatCondition :=
  let mismatch := match tolerance with
    | none => NumericValidationOp.ordinary .notEqual
    | some range => .tolerance range
  .and guard (.compare (.number mismatch target operation))

/-- Join already-lowered mismatch branches by left-associated `Or`, preserving declaration order. The caller supplies the structurally guaranteed first branch. -/
def disjoinGeneratedNumberMismatches (first : FlatCondition)
    (remaining : List FlatCondition) : FlatCondition :=
  remaining.foldl .or first

/-- The admitted generated shape. Every supplied mismatch remains below one target-filled gate and optional common guard; this function never calls the first-match selector. -/
def guardedGeneratedNumberCondition (target : FlatNumberField)
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

/-- Check the model, target, guard fields, and unsuppressed exact-comparison scales before assembling the generated ERROR rule at the target. This does not claim general computation-table, assignment, or runtime target legality. -/
def assembleGeneratedLiteralNumberRule (model : FlatModel)
    (computation : GuardedLiteralNumberComputation) :
    Except GeneratedComputationValidationError
      (CheckedResolvedFlatRule model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let target ← model.resolveGeneratedNumberTarget computation.targetField
      checkGeneratedOperationScales target 1 computation.declaredAlternatives
      let commonGuard ← match computation.commonPrecondition with
        | none => pure none
        | some common =>
            pure (some (← common.lowerForGeneratedValidation model target.id .common))
      let firstMismatch ← lowerGeneratedLiteralNumberMismatch model target
        1 computation.first
      let remainingMismatches ←
        lowerGeneratedLiteralNumberMismatches model target 2
          (computation.second :: computation.remaining)
      let core := guardedGeneratedNumberCondition target commonGuard
        firstMismatch remainingMismatches
      let checked ←
        (core.checkAgainstValidatedModel model hModel).mapError
          GeneratedComputationValidationError.condition
      (assembleResolvedFlatRule model checked computation.targetField
        computation.name .error computation.messagePlan).mapError
          GeneratedComputationValidationError.rule

end A12Kernel
