import A12Kernel.Elaboration.NumericExpression
import A12Kernel.Elaboration.NumericComputation
import A12Kernel.Elaboration.ValidationRule
import A12Kernel.Semantics.ComputationCondition

/-! # Checked generated computation validation assembly

This capsule admits one nonrepeatable Number target, an optional common precondition, and a complete nonempty table: either one optionally guarded operation or at least two guarded operations, with optional per-alternative fixed tolerance. Literal Number and already-checked numeric-expression payloads share that cardinality, first-match selector, gate/common/body shape, and validation-only tolerance metadata. Generated expression validation retains computation's model-wide operand policy, every declaration-ordered mismatch branch, and the common-outside-disjunction rule while reusing the shared model-indexed condition and whole-rule boundary. Direct entity-list aggregates narrow to the established scalar atom; repeatable aggregates, row-paired `SumOfProducts`, and Number `FirstFilledValue` retain their exact checked sources and evaluate through the bounded addressed leaf context without flattening model certificates or row topology. Runtime selection and target completion live in the sibling Execution module; applied-destination composition lives in its narrow follow-on module. General whole-rule orchestration and scheduling remain outside.

Numeric, typed String/stored-Enumeration, and Boolean/Confirm value counts retain their exact checked direct/plain-star/filtered-star sources so generated validation cannot collapse per-cell provenance, discard literal-domain certificates, or merge distinct field-kind matrices.
-/

namespace A12Kernel

/-- One guarded computation alternative with validation-only tolerance metadata. First-match computation selection consumes only the required precondition and operation. -/
structure GeneratedComputationAlternative (Operation : Type) (Guard : Type := ComputationCondition) where
  precondition : Guard
  operation : Operation
  tolerance : Option NumericToleranceRange := none
  deriving Repr, DecidableEq

namespace GeneratedComputationAlternative

/-- Erase validation-only tolerance while retaining the required guarded-row shape. -/
def toComputationAlternative
    (alternative : GeneratedComputationAlternative Operation Guard) :
    ComputationAlternative Operation Guard := {
  precondition := some alternative.precondition
  operation := alternative.operation
}

end GeneratedComputationAlternative

/-- The sole source alternative may omit its precondition. It remains distinct from a guarded row so the semantic core never fabricates an always-true condition. -/
structure SingleGeneratedComputationAlternative (Operation : Type) (Guard : Type := ComputationCondition) where
  precondition : Option Guard := none
  operation : Operation
  tolerance : Option NumericToleranceRange := none
  deriving Repr, DecidableEq

/-- A guarded table with at least two alternatives. -/
structure GuardedGeneratedComputationAlternatives (Operation : Type) (Guard : Type := ComputationCondition) where
  first : GeneratedComputationAlternative Operation Guard
  second : GeneratedComputationAlternative Operation Guard
  remaining : List (GeneratedComputationAlternative Operation Guard) := []
  deriving Repr, DecidableEq

namespace GuardedGeneratedComputationAlternatives

/-- Recover the complete authored alternative order. The two leading fields make an empty or singleton table unrepresentable in this fragment. -/
def declaredAlternatives
    (alternatives : GuardedGeneratedComputationAlternatives Operation Guard) :
    List (GeneratedComputationAlternative Operation Guard) :=
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

/-- Reuse the shared selector for the complete optional singleton-guard shape. -/
def selectFirst (alternative : SingleGeneratedComputationAlternative Operation)
    (commonPrecondition : Option ComputationCondition)
    (context : ScalarComputationContext) :
    ComputationAlternativeSelection Operation :=
  ComputationAlternative.selectFirst
    (ComputationAlternative.expandCommonPrecondition commonPrecondition
      [{ precondition := alternative.precondition
         operation := alternative.operation }]) context

end SingleGeneratedComputationAlternative

/-- The complete nonempty generated-validation table: either one optionally guarded row or at least two fully guarded rows. -/
inductive GeneratedComputationAlternatives (Operation : Type) (Guard : Type := ComputationCondition) where
  | singleton (alternative : SingleGeneratedComputationAlternative Operation Guard)
  | guarded (alternatives : GuardedGeneratedComputationAlternatives Operation Guard)
  deriving Repr, DecidableEq

/-- One computation shell shared by runtime selection and generated validation. -/
structure GeneratedComputationTable (Operation : Type) (Guard : Type := ComputationCondition) where
  targetField : FieldId
  name : String
  commonPrecondition : Option Guard := none
  alternatives : GeneratedComputationAlternatives Operation Guard
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

/-- Checked generated execution retains structural guard failures through the common selector. -/
def selectFirstChecked (computation : GeneratedComputationTable Operation)
    (context : ScalarComputationContext) :
    Except ComputationConditionError (ComputationAlternativeSelection Operation) :=
  let alternatives := match computation.alternatives with
    | .singleton alternative => [{ precondition := alternative.precondition, operation := alternative.operation }]
    | .guarded alternatives => alternatives.declaredAlternatives.map (·.toComputationAlternative)
  ComputationAlternative.selectFirstChecked
    (ComputationAlternative.expandCommonPrecondition computation.commonPrecondition alternatives) context

/-- Expand source-table shape once before either scalar or addressed guard evaluation. -/
def checkedNumericAlternatives
    (computation : GeneratedComputationTable Operation (CheckedComputationCondition model)) :
    List (CheckedComputationAlternative model Operation) :=
  let alternatives : List (CheckedComputationAlternative model Operation) :=
    match computation.alternatives with
    | .singleton alternative => [{ precondition := alternative.precondition, operation := alternative.operation }]
    | .guarded alternatives => alternatives.declaredAlternatives.map (·.toComputationAlternative)
  CheckedComputationAlternative.expandCommonPrecondition computation.commonPrecondition alternatives

/-- Model-indexed guards retain their numeric and predicate sources during the common scan. -/
def selectFirstCheckedNumeric
    (computation : GeneratedComputationTable Operation (CheckedComputationCondition model))
    (context : ScalarComputationContext) :
    Except CheckedComputationConditionError (ComputationAlternativeSelection Operation) :=
  CheckedComputationAlternative.selectFirstChecked computation.checkedNumericAlternatives context

def selectFirstCheckedNumericIn
    (computation : GeneratedComputationTable Operation (CheckedComputationCondition model))
    (context : NumericComputationEvaluationContext) :
    Except CheckedComputationConditionError (ComputationAlternativeSelection Operation) :=
  CheckedComputationAlternative.selectFirstCheckedIn computation.checkedNumericAlternatives context

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
  | numericGuardRequiresConditionTree
  | fieldFillGuardRequiresConditionTree
  | groupGuardRequiresConditionTree
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

private structure ResolvedGeneratedNumberTarget (model : FlatModel)
    (field : FieldId) where
  declaration : FlatFieldDecl
  target : FlatNumberField
  policy : NumericTargetPolicy
  declarationResolved :
    model.resolveNonrepeatableDeclarationById field = .ok declaration
  policyOwned : declaration.toNumericTargetPolicy? = some policy

private def FlatModel.resolveGeneratedNumberTarget
    (model : FlatModel) (field : FieldId) :
    Except GeneratedComputationValidationError
      (ResolvedGeneratedNumberTarget model field) :=
  match hResolved : model.resolveNonrepeatableDeclarationById field with
  | .error cause => .error (.resolve cause)
  | .ok declaration =>
      match declaration.toNumberField? with
      | none => .error (.targetNotNumber field)
      | some target =>
          match hPolicy : declaration.toNumericTargetPolicy? with
          | none => .error (.resolve
              (.numericMinimumFractionalDigitsExceedMaximum declaration.path
                declaration.numericTargetConstraints.minFractionalDigits
                target.info.scale))
          | some policy => .ok {
              declaration
              target
              policy
              declarationResolved := hResolved
              policyOwned := hPolicy }

namespace ComputationCondition

/-- Translate guard syntax without evaluating it. Validation then applies its own phase observation, unknown handling, connective algebra, and polarity. -/
private def lowerForGeneratedValidationUnchecked (model : FlatModel) :
    ComputationCondition →
      Except GeneratedComputationValidationError FlatCondition
  | .leaf (.fieldFilled field) => do
      pure (.fieldFilled (← model.resolveGeneratedGuardField field))
  | .leaf (.fieldNotFilled field) => do
      pure (.fieldNotFilled (← model.resolveGeneratedGuardField field))
  | .leaf (.text comparison) | .leaf (.scalar comparison) => pure (.compare comparison)
  | .leaf (.predicate source) => nomatch source
  | .leaf (.numeric _) => throw .numericGuardRequiresConditionTree
  | .leaf (.fieldFill _ _) => throw .fieldFillGuardRequiresConditionTree
  | .leaf (.groupPresence _ _) => throw .groupGuardRequiresConditionTree
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
      let resolvedTarget ←
        model.resolveGeneratedNumberTarget computation.targetField
      let targetDeclaration := resolvedTarget.declaration
      let target := resolvedTarget.target
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
  | .filledFieldCount source => pure (.filledFieldCount source)
  | .firstFilled source =>
      pure (.firstFilled source)
  | .valueCount expected source =>
      pure (.valueCount expected source)
  | .tokenDistinctCount source => pure (.tokenDistinctCount source)
  | .temporalDistinctCount run => pure (.temporalDistinctCount run)
  | .tokenValueCount source =>
      pure (.tokenValueCount source)
  | .booleanValueCount source =>
      pure (.booleanValueCount source)
  | .sumOfProducts source =>
      pure (.sumOfProducts source)
  -- Same arm-crossing boundary the fixed filled-group count already has below, and for a sharper
  -- reason: this project's validation carrier owns the starred group count in its own operator,
  -- so narrowing one into a validation atom here would mint a second representation of it.
  | .filledGroupCountMixed _ =>
      throw (.conditionAssembly .incoherentCore)
  | .numeric (.field declaration) =>
      match declaration.toNumberField? with
      | some field => pure (.ordinary (.field field))
      | none => throw (.conditionAssembly .incoherentCore)
  | .numeric (.baseYear year) => pure (.ordinary (.baseYear year))
  | .numeric (.fixedCurrentRepetition reference) =>
      pure (.ordinary (.fixedCurrentRepetition reference))
  | .numeric (.boundCurrentRepetition _) =>
      throw (.conditionAssembly .incoherentCore)
  | .numeric (.baseYearDatePart year source part) =>
      pure (.ordinary (.baseYearDatePart year source part))
  | .numeric (.temporalFieldPart source part) =>
      pure (.ordinary (.temporalFieldPart source part))
  | .numeric (.dateRangeBoundPart source bound part) =>
      pure (.ordinary (.dateRangeBoundPart source bound part))
  | .numeric (.stringLength source) => pure (.ordinary (.stringLength source))
  | .numeric (.stringRange source start finish) =>
      pure (.ordinary (.stringRange source start finish))
  | .numeric (.fieldValueAsNumber source) =>
      pure (.ordinary (.fieldValueAsNumber source))
  | .numeric (.dateDifference unit left right) =>
      pure (.ordinary (.dateDifference unit left right))
  | .numeric (.dateTimeDifference unit left right) =>
      pure (.ordinary (.dateTimeDifference unit left right))
  | .numeric (.dayDifference profile left right) =>
      pure (.ordinary (.dayDifference profile left right))
  | .numeric (.aggregate op source) =>
      match source.directAggregateFields? with
      | some direct => pure (.ordinary (.aggregate op direct))
      | none => pure (.aggregate op source)
  -- Refused because narrowing is arm-crossing, not because the operator is unmodelled: the
  -- same group operand over the same cells counts a formally invalid descendant in
  -- computation and answers unavailable in validation, so reusing the atom here would
  -- silently erase that inversion. Do not "fix" this by mapping it to a validation count.
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
    (condition : CheckedComputationCondition model) :
    Except GeneratedComputationValidationError (ValidationCondition model) := do
  if condition.referencesField target then throw (.targetSelfReference position)
  match condition with
  | .leaf (.numeric comparison) =>
      let left ← comparison.left.mapM CheckedNumericComputationAtom.toValidationAtom
      let right ← comparison.right.mapM CheckedNumericComputationAtom.toValidationAtom
      let resolved : OrderedNumericComparison model :=
        { left, right, op := comparison.op, suppressExactScaleWarning := comparison.suppressExactScaleWarning }
      pure (ValidationCondition.orderedNumericIn
        (if resolved.requiresAddressedValidation then .modelWideCheckedComputation else .modelWideNonrepeatable)
        resolved)
  | .leaf (.predicate (.temporal source)) => pure (.leaf (.scalarTemporal source))
  | .leaf (.predicate (.stringExpression source)) => pure (.leaf (.stringExpression source))
  | .leaf (.predicate (.fieldComparison (.boolean source))) =>
      pure (ValidationCondition.flat (.compare source.toFlat))
  | .leaf (.predicate (.fieldComparison (.range source))) =>
      pure (.leaf (.iteratedDateRange (.storedEquality source)))
  | .leaf (.predicate (.valueList source)) => pure (.leaf (.valueList source))
  | .leaf (.predicate (.scalarValueList operator source)) =>
      let source := match source with
        | .number source => .number { source with quantifier := operator.quantifier }
        | .token source => .token { source with quantifier := operator.quantifier }
        | .literals source => .literals { source with quantifier := operator.quantifier }
      pure (.leaf (.valueList source))
  | .leaf (.predicate (.scalarNumberLiterals operator source values)) =>
      pure (ValidationCondition.flat (.numberValueList operator.quantifier [source.field]
        (.literals (values.map Rat.ofInt))))
  | .leaf (.fieldFilled field) => pure (ValidationCondition.flat
      (.fieldFilled (← model.resolveGeneratedGuardField field)))
  | .leaf (.fieldNotFilled field) => pure (ValidationCondition.flat
      (.fieldNotFilled (← model.resolveGeneratedGuardField field)))
  | .leaf (.text comparison) | .leaf (.scalar comparison) => pure (ValidationCondition.flat (.compare comparison))
  | .leaf (.fieldFill _ _) => throw .fieldFillGuardRequiresConditionTree
  | .leaf (.groupPresence _ _) => throw .groupGuardRequiresConditionTree
  | .and left right => pure (.and (← generatedGuardCondition model target position left)
      (← generatedGuardCondition model target position right))
  | .or left right => pure (.or (← generatedGuardCondition model target position left)
      (← generatedGuardCondition model target position right))

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
      (CheckedNumericComputationOperation model) (CheckedComputationCondition model)) :
    Except GeneratedComputationValidationError (ValidationCondition model) := do
  let guard ← generatedGuardCondition model target.id
    (.alternative alternativeIndex) alternative.precondition
  let mismatch ← generatedNumericOperationMismatchCondition target
    alternativeIndex alternative.operation alternative.tolerance
  pure (.and guard mismatch)

private def generatedNumericMismatches (model : FlatModel)
    (target : FlatNumberField) :
    Nat → List (GeneratedComputationAlternative
      (CheckedNumericComputationOperation model) (CheckedComputationCondition model)) →
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
      (CheckedNumericComputationOperation model) (CheckedComputationCondition model)) :
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
      (CheckedNumericComputationOperation model) (CheckedComputationCondition model) →
      Except GeneratedComputationValidationError (ValidationCondition model)
  | .singleton alternative =>
      singleGeneratedNumericMismatch model target alternative
  | .guarded alternatives => do
      let first ← generatedNumericMismatch model target 1 alternatives.first
      let remaining ← generatedNumericMismatches model target 2
        (alternatives.second :: alternatives.remaining)
      pure (remaining.foldl .or first)

/-- A generated numeric table admitted together with the exact declaration-owned target policy needed by later target completion. -/
structure AdmittedGeneratedNumericOperationTable (model : FlatModel)
    (computation : GeneratedComputationTable
      (CheckedNumericComputationOperation model) (CheckedComputationCondition model)) where
  private mk ::
  rule : CheckedResolvedValidationRule model
  targetDeclaration : FlatFieldDecl
  targetPolicy : NumericTargetPolicy
  modelWellFormed : model.validate.isOk = true
  targetResolved :
    model.resolveNonrepeatableDeclarationById computation.targetField =
      .ok targetDeclaration
  targetPolicyOwned :
    targetDeclaration.toNumericTargetPolicy? = some targetPolicy

/-- Admit the complete generated validation twin and retain its resolved target policy. Computation selection remains the generic first-match scan; this route retains every guarded mismatch in declaration order under one optional common guard and target-filled gate. -/
def admitGeneratedNumericOperationTable (model : FlatModel)
    (computation : GeneratedComputationTable
      (CheckedNumericComputationOperation model) (CheckedComputationCondition model)) :
    Except GeneratedComputationValidationError
      (AdmittedGeneratedNumericOperationTable model computation) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let resolvedTarget ←
        model.resolveGeneratedNumberTarget computation.targetField
      let targetDeclaration := resolvedTarget.declaration
      let target := resolvedTarget.target
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
      let rule ← (assembleResolvedValidationRule model condition
        computation.targetField computation.name .error
        computation.messagePlan).mapError GeneratedComputationValidationError.rule
      pure {
        rule
        targetDeclaration
        targetPolicy := resolvedTarget.policy
        modelWellFormed := by rw [hModel]; rfl
        targetResolved := resolvedTarget.declarationResolved
        targetPolicyOwned := resolvedTarget.policyOwned }

/-- Project the admitted generated validation twin for callers that do not consume runtime target policy. -/
def assembleGeneratedNumericOperationTableRule (model : FlatModel)
    (computation : GeneratedComputationTable
      (CheckedNumericComputationOperation model) (CheckedComputationCondition model)) :
    Except GeneratedComputationValidationError
      (CheckedResolvedValidationRule model) :=
  (admitGeneratedNumericOperationTable model computation).map (·.rule)

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
