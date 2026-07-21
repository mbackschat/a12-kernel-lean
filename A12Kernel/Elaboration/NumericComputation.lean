import A12Kernel.Elaboration.Flat
import A12Kernel.Elaboration.NumericExpression
import A12Kernel.Semantics.ComputationCondition
import A12Kernel.Semantics.NumericTarget

/-! # Numeric computation-expression outcomes

This capsule checks one parser-independent, nonrepeatable plain numeric operation against a validated model and then evaluates the resolved expression. Admission resolves the Number target and operands, rejects nested direct target self-reference, applies the existing plain-arithmetic authoring and result-scale gates, and certifies model coherence. The one explicit scale-warning suppression bypasses only that result-scale gate and selects the existing warning-suppressed target branch after evaluation. Evaluation preserves ordinary values, arithmetic domain failure, and inherited computation-read poison as three distinct results. Concrete parsing, operation-valued wrappers, target-policy construction, application, delta projection, table integration, and scheduling remain outside this module.
-/

namespace A12Kernel

/-- Fail-closed faults outside the admitted numeric computation-expression fragment. -/
inductive NumericComputationFault where
  | fieldKindMismatch (field : FieldId)
  deriving Repr, DecidableEq

inductive NumericComputationElabError where
  | resolve (error : ResolveError)
  | targetNotNumber (field : FieldId)
  | operandNotNumber (path : List String)
  | targetSelfReference (field : FieldId)
  | authoring (result : NumericAuthoringCheck)
  | unsupportedExpression
  | operationScaleMismatch (targetScale : Nat) (operation : NumericScaleSummary)
  | incoherentCore
  deriving Repr, DecidableEq

/-- One resolved numeric operation before target storage, retaining whether its result-scale warning was explicitly suppressed. -/
structure NumericComputationOperation where
  target : FlatNumberField
  expression : AuthoredNumericExpr FlatFieldDecl
  suppressExactScaleWarning : Bool := false
  deriving Repr, DecidableEq

def FlatModel.admitsNumericComputationOperand
    (model : FlatModel) (declaration : FlatFieldDecl) : Bool :=
  match model.lookupUniqueId declaration.id with
  | .ok admitted =>
      admitted == declaration &&
        declaration.repeatableScope.isEmpty &&
        declaration.toNumberField?.isSome
  | .error _ => false

def FlatModel.admitsNumericComputationTarget
    (model : FlatModel) (target : FlatNumberField) : Bool :=
  match model.lookupUniqueId target.id with
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.toNumberField? == some target
  | .error _ => false

def FlatFieldDecl.numericScaleSummary
    (declaration : FlatFieldDecl) : NumericScaleSummary :=
  match declaration.toNumberField? with
  | some field => NumericScaleSummary.field field.info.scale
  | none => { scale := .unknown, canExpandScale := false }

def NumericComputationOperation.wellFormedBool
    (operation : NumericComputationOperation) (model : FlatModel) : Bool :=
  model.admitsNumericComputationTarget operation.target &&
    operation.expression.allAtoms model.admitsNumericComputationOperand &&
    !operation.expression.anyAtom (fun declaration =>
      declaration.id == operation.target.id) &&
    operation.expression.authoringCheck == .accepted &&
    match operation.expression.summary? FlatFieldDecl.numericScaleSummary with
    | some summary =>
        operation.suppressExactScaleWarning ||
          exactNumericScaleComparisonAllowed
            (NumericScaleSummary.field operation.target.info.scale) summary
    | none => false

def NumericComputationOperation.WellFormed
    (operation : NumericComputationOperation) (model : FlatModel) : Prop :=
  operation.wellFormedBool model = true

/-- A model-coherent operation produced only after target, operands, authoring shape, self-reference, and result scale have been checked. -/
structure CheckedNumericComputationOperation (model : FlatModel) where
  core : NumericComputationOperation
  modelWellFormed : model.validate.isOk = true
  wellFormed : core.WellFormed model

private def FlatModel.resolveNumericComputationTarget
    (model : FlatModel) (target : FieldId) :
    Except NumericComputationElabError FlatNumberField := do
  let declaration ← (model.resolveNonrepeatableDeclarationById target).mapError .resolve
  match declaration.toNumberField? with
  | some field => pure field
  | none => throw (.targetNotNumber target)

private def FlatModel.resolveNumericComputationExpression
    (model : FlatModel) (declaringGroup : GroupPath) (target : FieldId)
    (expression : AuthoredNumericExpr SurfaceFieldPath) :
    Except NumericComputationElabError (AuthoredNumericExpr FlatFieldDecl) :=
  expression.mapM fun reference => do
    let declaration ←
      (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
    if declaration.id == target then
      throw (.targetSelfReference target)
    else if declaration.toNumberField?.isSome then
      pure declaration
    else
      throw (.operandNotNumber declaration.path)

/-- Resolve and check one nonrepeatable plain numeric computation operation. The default unsuppressed route preserves the exact result-scale gate; the explicit suppression flag bypasses only that gate. Operation-valued wrappers, repeatable evaluation, table integration, target-policy construction, and scheduling remain separate owners. -/
def elaborateNumericComputationOperation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (expression : AuthoredNumericExpr SurfaceFieldPath)
    (suppressExactScaleWarning : Bool := false) :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation model) := do
  match hModel : model.validate with
  | .error error => throw (.resolve error)
  | .ok () =>
      if !GroupPath.isValid declaringGroup then
        throw (.resolve (.invalidRuleGroup declaringGroup))
      let target ← model.resolveNumericComputationTarget targetField
      let resolved ← model.resolveNumericComputationExpression
        declaringGroup targetField expression
      match resolved.authoringCheck with
      | .accepted => pure ()
      | result => throw (.authoring result)
      let summary ← match resolved.summary? FlatFieldDecl.numericScaleSummary with
        | some summary => pure summary
        | none => throw .unsupportedExpression
      if !(suppressExactScaleWarning || exactNumericScaleComparisonAllowed
          (NumericScaleSummary.field target.info.scale) summary) then
        throw (.operationScaleMismatch target.info.scale summary)
      let core : NumericComputationOperation := {
        target
        expression := resolved
        suppressExactScaleWarning }
      if hCore : core.wellFormedBool model = true then
        pure {
          core
          modelWellFormed := by
            rw [hModel]
            rfl
          wellFormed := hCore }
      else
        throw .incoherentCore

namespace ScalarComputationContext

/-- Read one already-resolved declaration in computation phase. A non-Number declaration is a structural fault even when its cell is empty; required-only Number emptiness remains zero and ordinary formal invalidity remains poison. -/
def readNumeric (context : ScalarComputationContext) (declaration : FlatFieldDecl) :
    Except NumericComputationFault NumericComputationResult :=
  match declaration.toNumberField? with
  | none => throw (.fieldKindMismatch declaration.id)
  | some field =>
      match observeCell .computation (context.read field.id) with
      | .empty => pure (.value 0)
      | .value (.num amount) => pure (.value amount)
      | .value _ => throw (.fieldKindMismatch field.id)
      | .unknown cause | .poison cause => pure (.poison cause)

end ScalarComputationContext

namespace NumericComputationResult

/-- Combine two already-reached arithmetic operands through the shared poison/domain/value table. -/
def evalBinary (op : NumericScaleBinaryOp) :
    NumericComputationResult → NumericComputationResult → NumericComputationResult
  | left, right =>
      NumericComputationResult.combineReached
        (fun leftValue rightValue => ofArithmetic (op.evalValues leftValue rightValue))
        left right

/-- Evaluate an ordered pair once. A left poison prevents the right computation from being reached; a value or domain failure reaches it and delegates the final result to the supplied semantic combiner. -/
def evalOrdered
    (left : Except NumericComputationFault NumericComputationResult)
    (right : Unit → Except NumericComputationFault NumericComputationResult)
    (combine : NumericComputationResult → NumericComputationResult →
      NumericComputationResult) :
    Except NumericComputationFault NumericComputationResult := do
  let leftResult ← left
  match leftResult with
  | .poison cause => pure (.poison cause)
  | .value _ | .domainFailure =>
      pure (combine leftResult (← right ()))

end NumericComputationResult

namespace LoweredNumericExpr

/-- The first structural fault in the complete lowered tree. This pass runs before any context read, so a non-Number declaration cannot be hidden by data-dependent poison. -/
def computationFault? : LoweredNumericExpr FlatFieldDecl →
    Option NumericComputationFault
  | .atom declaration =>
      if declaration.toNumberField?.isSome then
        none
      else
        some (.fieldKindMismatch declaration.id)
  | .literal _ => none
  | .binary _ left right | .power left right | .extremum _ left right =>
      match left.computationFault? with
      | some fault => some fault
      | none => right.computationFault?
  | .abs body => body.computationFault?
  | .round _ _ body => body.computationFault?

/-- Evaluate the admitted computation fragment left-to-right. A reached poison aborts the remaining expression; arithmetic domain failure remains a value-level result and propagates through later arithmetic, including runtime-invalid power. -/
def evalComputation
    (read : Atom → Except NumericComputationFault NumericComputationResult) :
    LoweredNumericExpr Atom →
      Except NumericComputationFault NumericComputationResult
  | .atom sourceAtom => read sourceAtom
  | .literal amount => pure (.value amount)
  | .binary op left right =>
      NumericComputationResult.evalOrdered
        (left.evalComputation read) (fun _ => right.evalComputation read)
        (NumericComputationResult.evalBinary op)
  | .power base exponent =>
      NumericComputationResult.evalOrdered
        (base.evalComputation read) (fun _ => exponent.evalComputation read)
        NumericComputationResult.evalPower
  | .abs body => do
      pure ((← body.evalComputation read).absolute)
  | .extremum op left right =>
      NumericComputationResult.evalOrdered
        (left.evalComputation read) (fun _ => right.evalComputation read)
        op.selectComputationResult
  | .round mode places body => do
      pure ((← body.evalComputation read).round mode places)

end LoweredNumericExpr

namespace AuthoredNumericExpr

/-- Lower exactly once, then evaluate one already-resolved numeric computation expression against the common checked computation context. -/
def evaluateComputation (expression : AuthoredNumericExpr FlatFieldDecl)
    (context : ScalarComputationContext) :
    Except NumericComputationFault NumericComputationResult :=
  let lowered := expression.lowerForEvaluation
  match lowered.computationFault? with
  | some fault => .error fault
  | none => lowered.evalComputation context.readNumeric

end AuthoredNumericExpr

namespace CheckedNumericComputationOperation

def evaluate (operation : CheckedNumericComputationOperation model)
    (context : ScalarComputationContext) :
    Except NumericComputationFault NumericComputationResult :=
  operation.core.expression.evaluateComputation context

/-- Evaluate the checked expression and route it through the target branch certified by the retained warning-suppression choice. The equality proof prevents a caller from pairing the operation with another target's signedness or maximum scale; the target's minimum scale remains an explicit policy input because the current flat declaration does not retain it. -/
def evaluateTarget (operation : CheckedNumericComputationOperation model)
    (policy : NumericTargetPolicy)
    (_targetMatches : policy.info = operation.core.target.info)
    (context : ScalarComputationContext) :
    Except NumericComputationFault NumericTargetCheckResult := do
  let result ← operation.evaluate context
  if operation.core.suppressExactScaleWarning then
    pure (policy.checkWithScaleWarningSuppressed result)
  else
    pure (policy.check result)

end CheckedNumericComputationOperation

end A12Kernel
