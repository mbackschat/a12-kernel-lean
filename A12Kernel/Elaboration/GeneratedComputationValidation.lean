import A12Kernel.Elaboration.NumericExpression
import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Semantics.ComputationCondition

/-! # Checked two-alternative literal-Number generated validation

This capsule admits one nonrepeatable Number target and exactly two guarded literal operations. Computation consumes the guards with computation-phase first-match selection; the generated rule structurally translates the same guard syntax into ordinary validation conditions and retains both mismatch branches. Common preconditions, expression operations, tolerance, repeatable evaluation, warning-suppressed assignment legality, runtime target checks, and general computation authoring remain outside.
-/

namespace A12Kernel

/-- The smallest table that separates first-match computation from all-alternatives validation. Decoded literals retain the authored scale until checked lowering; general computation authoring legality is an input assumption. -/
structure TwoAlternativeLiteralNumberComputation where
  targetField : FieldId
  name : String
  first : ComputationAlternative DecodedNumericLiteral
  second : ComputationAlternative DecodedNumericLiteral
  messagePlan : MessageRenderPlan
  deriving Repr, DecidableEq

namespace TwoAlternativeLiteralNumberComputation

/-- Computation consumes the same authored guards in declaration order and stops at the first holding row. -/
def selectFirst (computation : TwoAlternativeLiteralNumberComputation)
    (context : ScalarComputationContext) :
    ComputationAlternativeSelection DecodedNumericLiteral :=
  ComputationAlternative.selectFirst [computation.first, computation.second] context

end TwoAlternativeLiteralNumberComputation

inductive GeneratedComputationValidationError where
  | resolve (error : ResolveError)
  | unsupportedGuardField (field : FieldId)
  | targetNotNumber (field : FieldId)
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
  | .string => throw (.unsupportedGuardField field)

private def FlatModel.resolveGeneratedNumberTarget
    (model : FlatModel) (field : FieldId) :
    Except GeneratedComputationValidationError FlatNumberField := do
  let declaration ← model.resolveNonrepeatableDeclarationById field
  match declaration.toNumberField? with
  | some target => pure target
  | none => throw (.targetNotNumber field)

namespace ComputationCondition

/-- Translate guard syntax without evaluating it. Validation then applies its own phase observation, unknown handling, connective algebra, and polarity. -/
private def lowerForGeneratedValidation (model : FlatModel) :
    ComputationCondition →
      Except GeneratedComputationValidationError FlatCondition
  | .fieldFilled field => do
      pure (.fieldFilled (← model.resolveGeneratedGuardField field))
  | .fieldNotFilled field => do
      pure (.fieldNotFilled (← model.resolveGeneratedGuardField field))
  | .and left right => do
      pure (.and
        (← left.lowerForGeneratedValidation model)
        (← right.lowerForGeneratedValidation model))
  | .or left right => do
      pure (.or
        (← left.lowerForGeneratedValidation model)
        (← right.lowerForGeneratedValidation model))

end ComputationCondition

/-- One guarded strict mismatch in the generated rule. The fixed-tolerance family is deliberately outside this capsule. -/
def generatedLiteralNumberMismatch (target : FlatNumberField)
    (guard : FlatCondition) (operation : Rat) : FlatCondition :=
  .and guard (.compare (.number .notEqual target operation))

/-- The exact admitted generated shape. Both alternatives remain present; this function never calls the first-match selector. -/
def twoAlternativeGeneratedNumberCondition (target : FlatNumberField)
    (firstGuard : FlatCondition) (firstOperation : Rat)
    (secondGuard : FlatCondition) (secondOperation : Rat) :
    FlatCondition :=
  .and (.fieldFilled (.number target))
    (.or
      (generatedLiteralNumberMismatch target firstGuard firstOperation)
      (generatedLiteralNumberMismatch target secondGuard secondOperation))

private def checkGeneratedOperationScale (target : FlatNumberField)
    (alternative : Nat) (operation : DecodedNumericLiteral) :
    Except GeneratedComputationValidationError Unit :=
  if exactNumericScaleComparisonAllowed
      (NumericScaleSummary.field target.info.scale)
      (NumericScaleSummary.constant operation.authoredScale) then
    pure ()
  else
    throw (.operationScaleMismatch alternative target.info.scale
      operation.authoredScale)

/-- Check the model, target, guard fields, and unsuppressed exact-comparison scales before assembling the generated ERROR rule at the target. This does not claim general computation-table, assignment, or runtime target legality. -/
def assembleGeneratedLiteralNumberRule (model : FlatModel)
    (computation : TwoAlternativeLiteralNumberComputation) :
    Except GeneratedComputationValidationError
      (CheckedResolvedFlatRule model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let target ← model.resolveGeneratedNumberTarget computation.targetField
      checkGeneratedOperationScale target 1 computation.first.operation
      checkGeneratedOperationScale target 2 computation.second.operation
      let firstGuard ←
        computation.first.precondition.lowerForGeneratedValidation model
      let secondGuard ←
        computation.second.precondition.lowerForGeneratedValidation model
      let core := twoAlternativeGeneratedNumberCondition target
        firstGuard computation.first.operation.value
        secondGuard computation.second.operation.value
      let checked ←
        (core.checkAgainstValidatedModel model hModel).mapError
          GeneratedComputationValidationError.condition
      (assembleResolvedFlatRule model checked computation.targetField
        computation.name .error computation.messagePlan).mapError
          GeneratedComputationValidationError.rule

end A12Kernel
