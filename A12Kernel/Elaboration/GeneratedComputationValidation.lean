import A12Kernel.Elaboration.NumericExpression
import A12Kernel.Elaboration.NumericComputation
import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Semantics.ComputationCondition

/-! # Checked generated computation validation

This capsule admits one nonrepeatable Number target, an optional common precondition, and a complete nonempty table: either one optionally guarded operation or at least two guarded operations, with optional per-alternative fixed tolerance. Literal Number and already-checked numeric-expression payloads share that cardinality, first-match selector, gate/common/body shape, and validation-only tolerance metadata. Generated expression validation retains computation's model-wide operand policy, every declaration-ordered mismatch branch, and the common-outside-disjunction rule while reusing the shared model-indexed condition and whole-rule boundary. Direct entity-list aggregates narrow to the established scalar atom; repeatable aggregates, row-paired `SumOfProducts`, and Number `FirstFilledValue` retain their exact checked sources and evaluate through the bounded addressed leaf context without flattening model certificates or row topology. Runtime target checks, wider addressed leaves and whole-rule orchestration, and general computation scheduling remain outside.

Numeric value count also retains its exact checked source so generated validation cannot collapse per-cell filter-match provenance into one aggregate-wide flag.
-/

namespace A12Kernel

/-- One computation alternative with validation-only tolerance metadata. First-match computation selection deliberately consumes only the inherited precondition and operation. -/
structure GeneratedComputationAlternative (Operation : Type) extends
    ComputationAlternative Operation where
  tolerance : Option NumericToleranceRange := none
  deriving Repr, DecidableEq

/-- The sole source alternative may omit its precondition. It remains distinct from a guarded row so the semantic core never fabricates an always-true condition. -/
structure SingleGeneratedComputationAlternative (Operation : Type) where
  precondition : Option ComputationCondition := none
  operation : Operation
  tolerance : Option NumericToleranceRange := none
  deriving Repr, DecidableEq

/-- A guarded table with at least two alternatives. -/
structure GuardedGeneratedComputationAlternatives (Operation : Type) where
  first : GeneratedComputationAlternative Operation
  second : GeneratedComputationAlternative Operation
  remaining : List (GeneratedComputationAlternative Operation) := []
  deriving Repr, DecidableEq

namespace GuardedGeneratedComputationAlternatives

/-- Recover the complete authored alternative order. The two leading fields make an empty or singleton table unrepresentable in this fragment. -/
def declaredAlternatives
    (alternatives : GuardedGeneratedComputationAlternatives Operation) :
    List (GeneratedComputationAlternative Operation) :=
  alternatives.first :: alternatives.second :: alternatives.remaining

/-- Computation consumes every guarded row in declaration order and stops at the first holding row. -/
def selectFirst (alternatives : GuardedGeneratedComputationAlternatives Operation)
    (commonPrecondition : Option ComputationCondition)
    (context : ScalarComputationContext) :
    ComputationAlternativeSelection Operation :=
  ComputationAlternative.selectFirst
    (ComputationAlternative.expandCommonPrecondition
      commonPrecondition
      (alternatives.declaredAlternatives.map
        GeneratedComputationAlternative.toComputationAlternative)) context

end GuardedGeneratedComputationAlternatives

namespace SingleGeneratedComputationAlternative

/-- Select the sole operation directly only when both source guards are absent. Every present guard still uses the shared ordered selector and common-precondition expansion. -/
def selectFirst (alternative : SingleGeneratedComputationAlternative Operation)
    (commonPrecondition : Option ComputationCondition)
    (context : ScalarComputationContext) :
    ComputationAlternativeSelection Operation :=
  match alternative.precondition, commonPrecondition with
  | none, none => .selected alternative.operation
  | none, some common =>
      ComputationAlternative.selectFirst
        [{ precondition := common, operation := alternative.operation }] context
  | some precondition, common =>
      ComputationAlternative.selectFirst
        (ComputationAlternative.expandCommonPrecondition common
          [{ precondition, operation := alternative.operation }]) context

end SingleGeneratedComputationAlternative

/-- The complete nonempty generated-validation table: either one optionally guarded row or at least two fully guarded rows. -/
inductive GeneratedComputationAlternatives (Operation : Type) where
  | singleton (alternative : SingleGeneratedComputationAlternative Operation)
  | guarded (alternatives : GuardedGeneratedComputationAlternatives Operation)
  deriving Repr, DecidableEq

/-- One computation shell shared by runtime selection and generated validation. -/
structure GeneratedComputationTable (Operation : Type) where
  targetField : FieldId
  name : String
  commonPrecondition : Option ComputationCondition := none
  alternatives : GeneratedComputationAlternatives Operation
  messagePlan : MessageRenderPlan
  deriving Repr, DecidableEq

namespace GeneratedComputationTable

def selectFirst (computation : GeneratedComputationTable Operation)
    (context : ScalarComputationContext) :
    ComputationAlternativeSelection Operation :=
  match computation.alternatives with
  | .singleton alternative =>
      SingleGeneratedComputationAlternative.selectFirst alternative
        computation.commonPrecondition context
  | .guarded alternatives =>
      GuardedGeneratedComputationAlternatives.selectFirst alternatives
        computation.commonPrecondition context

end GeneratedComputationTable

abbrev LiteralNumberComputationAlternative :=
  GeneratedComputationAlternative DecodedNumericLiteral

abbrev SingleLiteralNumberComputationAlternative :=
  SingleGeneratedComputationAlternative DecodedNumericLiteral

abbrev GuardedLiteralNumberAlternatives :=
  GuardedGeneratedComputationAlternatives DecodedNumericLiteral

abbrev LiteralNumberComputationAlternatives :=
  GeneratedComputationAlternatives DecodedNumericLiteral

abbrev LiteralNumberComputation :=
  GeneratedComputationTable DecodedNumericLiteral

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
  | operationTargetMismatch (alternative : Nat)
      (expected actual : FieldId)
  | condition (error : ElabError)
  | conditionAssembly (error : ValidationConditionAssemblyError)
  | rule (error : FlatRuleAssemblyError)
  deriving Repr, DecidableEq

private def FlatModel.resolveGeneratedGuardField
    (model : FlatModel) (field : FieldId) :
    Except GeneratedComputationValidationError FlatField := do
  let declaration ← (model.resolveNonrepeatableDeclarationById field).mapError
    GeneratedComputationValidationError.resolve
  pure declaration.toPresenceField

private def FlatModel.resolveGeneratedNumberTarget
    (model : FlatModel) (field : FieldId) :
    Except GeneratedComputationValidationError
      (FlatFieldDecl × FlatNumberField) := do
  let declaration ← (model.resolveNonrepeatableDeclarationById field).mapError
    GeneratedComputationValidationError.resolve
  match declaration.toNumberField? with
  | some target => pure (declaration, target)
  | none => throw (.targetNotNumber field)

namespace ComputationCondition

/-- Whether this condition mentions the computed target directly. The checked fragment has already resolved every path to a field ID. -/
def referencesField (condition : ComputationCondition) (target : FieldId) : Bool :=
  match condition with
  | .leaf (.fieldFilled field) | .leaf (.fieldNotFilled field) => field == target
  | .and left right | .or left right =>
      left.referencesField target || right.referencesField target

/-- Translate guard syntax without evaluating it. Validation then applies its own phase observation, unknown handling, connective algebra, and polarity. -/
private def lowerForGeneratedValidationUnchecked (model : FlatModel) :
    ComputationCondition →
      Except GeneratedComputationValidationError FlatCondition
  | .leaf (.fieldFilled field) => do
      pure (.fieldFilled (← model.resolveGeneratedGuardField field))
  | .leaf (.fieldNotFilled field) => do
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

/-- Place one already-built mismatch body below its target-filled gate and optional common guard. Flat literal and mixed expression tables share this exact source shape. -/
def generatedConditionWithGate (gate : ConditionTree Leaf)
    (commonGuard : Option (ConditionTree Leaf))
    (alternatives : ConditionTree Leaf) : ConditionTree Leaf :=
  .and gate (match commonGuard with
    | none => alternatives
    | some common => .and common alternatives)

/-- The admitted generated shape. Every supplied mismatch remains below one target-filled gate and optional common guard; this function never calls the first-match selector. -/
def generatedNumberCondition (target : FlatNumberField)
    (commonGuard : Option FlatCondition) (firstMismatch : FlatCondition)
    (remainingMismatches : List FlatCondition) :
    FlatCondition :=
  let alternatives := disjoinGeneratedNumberMismatches
    firstMismatch remainingMismatches
  generatedConditionWithGate
    (FlatCondition.fieldFilled (.number target)) commonGuard alternatives

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
      checkGeneratedOperationScales target 1
        (GuardedGeneratedComputationAlternatives.declaredAlternatives alternatives)

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
      let (targetDeclaration, target) ←
        model.resolveGeneratedNumberTarget computation.targetField
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
        (core.checkAgainstValidatedModel model targetDeclaration.groupPath hModel).mapError
          GeneratedComputationValidationError.condition
      (assembleResolvedFlatRule model checked computation.targetField
        computation.name .error computation.messagePlan).mapError
          GeneratedComputationValidationError.rule

def CheckedNumericComputationAtom.toValidationAtom :
    CheckedNumericComputationAtom model →
      Except GeneratedComputationValidationError
        (OrderedNumericValidationAtom model)
  | .firstFilled source =>
      pure (.firstFilled source)
  | .valueCount expected source =>
      pure (.valueCount expected source)
  | .sumOfProducts source =>
      pure (.sumOfProducts source)
  | .numeric (.field declaration) =>
      match declaration.toNumberField? with
      | some field => pure (.ordinary (.field field))
      | none => throw (.conditionAssembly .incoherentCore)
  | .numeric (.baseYear year) => pure (.ordinary (.baseYear year))
  | .numeric (.baseYearDatePart year source part) =>
      pure (.ordinary (.baseYearDatePart year source part))
  | .numeric (.temporalFieldPart source part) =>
      pure (.ordinary (.temporalFieldPart source part))
  | .numeric (.stringLength source) => pure (.ordinary (.stringLength source))
  | .numeric (.stringRange source start finish) =>
      pure (.ordinary (.stringRange source start finish))
  | .numeric (.fieldValueAsNumber source) =>
      pure (.ordinary (.fieldValueAsNumber source))
  | .numeric (.dateDifference unit left right) =>
      pure (.ordinary (.dateDifference unit left right))
  | .numeric (.dayDifference profile left right) =>
      pure (.ordinary (.dayDifference profile left right))
  | .numeric (.aggregate op source) =>
      match source.directAggregateFields? with
      | some direct => pure (.ordinary (.aggregate op direct))
      | none => pure (.aggregate op source)
  | .numeric (.filledGroupCount _) =>
      throw (.conditionAssembly .incoherentCore)

/-- The pure generated mismatch core after the checked computation expression has been narrowed to validation atoms. -/
def generatedNumericOperationMismatch
    (operation : NumericComputationOperation model)
    (expression : AuthoredNumericExpr (OrderedNumericValidationAtom model))
    (tolerance : Option NumericToleranceRange) :
    OrderedNumericComparison model :=
  { op := match tolerance with
      | none => .ordinary .notEqual
      | some range => .tolerance range
    left := .atom (.ordinary (.field operation.target))
    right := expression
    suppressExactScaleWarning := operation.suppressExactScaleWarning }

/-- Reuse one checked computation expression as the right side of its generated validation mismatch. The authored tree narrows scalar declarations while retaining every model-certified addressed first-filled, entity-list aggregate, or row-product source; no surface syntax is reconstructed or re-elaborated. -/
def CheckedNumericComputationOperation.generatedMismatchComparison
    (operation : CheckedNumericComputationOperation model)
    (tolerance : Option NumericToleranceRange) :
    Except GeneratedComputationValidationError
      (CheckedOrderedNumericComparison model) := do
  let targetDeclaration ←
    (model.lookupUniqueId operation.core.target.id).mapError
      GeneratedComputationValidationError.resolve
  let expression ← operation.core.expression.mapM
    CheckedNumericComputationAtom.toValidationAtom
  let comparison := generatedNumericOperationMismatch operation.core expression tolerance
  let operandScope :=
    if comparison.requiresAddressedValidation then
      NumericOperandScope.modelWideCheckedComputation
    else
      NumericOperandScope.modelWideNonrepeatable
  if hCore : comparison.wellFormedInBool targetDeclaration.groupPath
      operandScope = true then
    pure {
      rowGroup := targetDeclaration.groupPath
      operandScope
      core := comparison
      modelWellFormed := operation.modelWellFormed
      wellFormed := hCore }
  else
    throw (.conditionAssembly .incoherentCore)

private def generatedGuardCondition (model : FlatModel) (target : FieldId)
    (position : GeneratedComputationGuardPosition)
    (condition : ComputationCondition) :
    Except GeneratedComputationValidationError (ValidationCondition model) := do
  let lowered ← condition.lowerForGeneratedValidation model target position
  pure (ValidationCondition.flat lowered)

private def generatedNumericOperationMismatchCondition (target : FlatNumberField)
    (alternativeIndex : Nat)
    (operation : CheckedNumericComputationOperation model)
    (tolerance : Option NumericToleranceRange) :
    Except GeneratedComputationValidationError (ValidationCondition model) := do
  if operation.core.target != target then
    throw (.operationTargetMismatch alternativeIndex target.id
      operation.core.target.id)
  let mismatch ← operation.generatedMismatchComparison tolerance
  pure (ValidationCondition.orderedNumericIn
    mismatch.operandScope mismatch.core)

private def generatedNumericMismatch (model : FlatModel)
    (target : FlatNumberField) (alternativeIndex : Nat)
    (alternative : GeneratedComputationAlternative
      (CheckedNumericComputationOperation model)) :
    Except GeneratedComputationValidationError (ValidationCondition model) := do
  let guard ← generatedGuardCondition model target.id
    (.alternative alternativeIndex) alternative.precondition
  let mismatch ← generatedNumericOperationMismatchCondition target
    alternativeIndex alternative.operation alternative.tolerance
  pure (.and guard mismatch)

private def generatedNumericMismatches (model : FlatModel)
    (target : FlatNumberField) :
    Nat → List (GeneratedComputationAlternative
      (CheckedNumericComputationOperation model)) →
      Except GeneratedComputationValidationError
        (List (ValidationCondition model))
  | _, [] => pure []
  | alternativeIndex, alternative :: remaining => do
      let first ← generatedNumericMismatch model target alternativeIndex alternative
      let rest ← generatedNumericMismatches model target
        (alternativeIndex + 1) remaining
      pure (first :: rest)

private def singleGeneratedNumericMismatch (model : FlatModel)
    (target : FlatNumberField)
    (alternative : SingleGeneratedComputationAlternative
      (CheckedNumericComputationOperation model)) :
    Except GeneratedComputationValidationError (ValidationCondition model) := do
  let mismatch ← generatedNumericOperationMismatchCondition target 1
    alternative.operation alternative.tolerance
  match alternative.precondition with
  | none => pure mismatch
  | some precondition => do
      let guard ← generatedGuardCondition model target.id
        (.alternative 1) precondition
      pure (.and guard mismatch)

private def generatedNumericAlternatives (model : FlatModel)
    (target : FlatNumberField) :
    GeneratedComputationAlternatives
      (CheckedNumericComputationOperation model) →
      Except GeneratedComputationValidationError (ValidationCondition model)
  | .singleton alternative =>
      singleGeneratedNumericMismatch model target alternative
  | .guarded alternatives => do
      let first ← generatedNumericMismatch model target 1 alternatives.first
      let remaining ← generatedNumericMismatches model target 2
        (alternatives.second :: alternatives.remaining)
      pure (remaining.foldl .or first)

/-- Assemble the complete generated validation twin of a nonempty table whose payloads are already-checked numeric operations. Computation selection remains the generic first-match scan; this route retains every guarded mismatch in declaration order under one optional common guard and target-filled gate. -/
def assembleGeneratedNumericOperationTableRule (model : FlatModel)
    (computation : GeneratedComputationTable
      (CheckedNumericComputationOperation model)) :
    Except GeneratedComputationValidationError
      (CheckedResolvedValidationRule model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let (targetDeclaration, target) ←
        model.resolveGeneratedNumberTarget computation.targetField
      let alternatives ← generatedNumericAlternatives model target
        computation.alternatives
      let commonGuard ← match computation.commonPrecondition with
        | none => pure none
        | some common => do
            let checkedCommon ← generatedGuardCondition model target.id .common common
            pure (some checkedCommon)
      let core := generatedConditionWithGate
        (ValidationCondition.flat (.fieldFilled (.number target)))
        commonGuard alternatives
      let condition ← (CheckedValidationCondition.checkCore model
        targetDeclaration.groupPath core (by rw [hModel]; rfl)).mapError
          GeneratedComputationValidationError.conditionAssembly
      (assembleResolvedValidationRule model condition computation.targetField
        computation.name .error computation.messagePlan).mapError
          GeneratedComputationValidationError.rule

/-- Assemble the generated validation twin of one checked unconditional numeric operation through the same singleton-table route used by guarded operations. -/
def assembleGeneratedNumericOperationRule (model : FlatModel)
    (operation : CheckedNumericComputationOperation model)
    (name : String) (tolerance : Option NumericToleranceRange)
    (messagePlan : MessageRenderPlan) :
    Except GeneratedComputationValidationError
      (CheckedResolvedValidationRule model) :=
  assembleGeneratedNumericOperationTableRule model {
    targetField := operation.core.target.id
    name
    alternatives := .singleton { operation, tolerance }
    messagePlan }

end A12Kernel
