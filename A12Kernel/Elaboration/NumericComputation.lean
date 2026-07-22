import A12Kernel.Elaboration.NumericSource
import A12Kernel.Semantics.ComputationCondition
import A12Kernel.Semantics.NumericTarget

/-! # Numeric computation-expression outcomes

This capsule checks one parser-independent, nonrepeatable numeric operation against a validated model and then evaluates the resolved expression. Admission resolves the Number target plus Number-field, numeric-`BaseYear`, Base-Year date-component, and direct temporal field-component sources, rejects nested direct target self-reference, applies the shared plain-arithmetic or direct Number-field-root value-function fragment and result-scale gate, and certifies model coherence. The complete externally resolved target policy attaches once to that checked operation after its scale and signedness have been matched, so evaluation cannot substitute another policy. The one explicit scale-warning suppression bypasses only the result-scale gate and selects the existing warning-suppressed target branch after evaluation. Evaluation preserves ordinary values, arithmetic domain failure, and inherited computation-read poison as three distinct results. Concrete parsing, partial-known Date policy, target-policy construction from declarations, general operation-valued wrapper traversal, application, delta projection, table integration, and scheduling remain outside this module.
-/

namespace A12Kernel

abbrev NumericComputationAtom := ResolvedNumericAtom FlatFieldDecl

/-- Fail-closed faults outside the admitted numeric computation-expression fragment. -/
inductive NumericComputationFault where
  | fieldKindMismatch (field : FieldId)
  deriving Repr, DecidableEq

inductive NumericComputationElabError where
  | resolve (error : ResolveError)
  | targetNotNumber (field : FieldId)
  | operandNotNumber (path : List String)
  | incompatibleTemporalSource (path : List String)
  | baseYearNotDeclared
  | targetSelfReference (field : FieldId)
  | authoring (result : NumericAuthoringCheck)
  | unsupportedExpression
  | operationScaleMismatch (targetScale : Nat) (operation : NumericScaleSummary)
  | targetPolicyMismatch (target policy : NumField)
  | incoherentCore
  deriving Repr, DecidableEq

/-- One resolved numeric operation before target storage, retaining whether its result-scale warning was explicitly suppressed. -/
structure NumericComputationOperation where
  target : FlatNumberField
  expression : AuthoredNumericExpr NumericComputationAtom
  suppressExactScaleWarning : Bool := false
  deriving Repr, DecidableEq

private def FlatModel.admitsTemporalComputationOperand
    (model : FlatModel) (source : FlatTemporalField) (accepts : Bool) : Bool :=
  match model.lookupUniqueId source.id with
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.toTemporalField? == some source && accepts
  | .error _ => false

def FlatModel.admitsNumericComputationOperand
    (model : FlatModel) : NumericComputationAtom → Bool
  | .field declaration =>
      match model.lookupUniqueId declaration.id with
      | .ok admitted =>
          admitted == declaration &&
            declaration.repeatableScope.isEmpty &&
            declaration.toNumberField?.isSome
      | .error _ => false
  | .baseYear year => model.baseYear == some year
  | .baseYearDatePart year _ _ => model.baseYear == some year
  | .temporalFieldPart source part =>
      model.admitsTemporalComputationOperand source
        (part.admittedBy source model.hasBaseYear)

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

def NumericComputationAtom.numericScaleSummary
    (atom : NumericComputationAtom) : NumericScaleSummary :=
  atom.summary FlatFieldDecl.numericScaleSummary

def NumericComputationAtom.references
    (field : FieldId) : NumericComputationAtom → Bool
  | .field declaration => declaration.id == field
  | .baseYear _ => false
  | .baseYearDatePart _ _ _ => false
  | .temporalFieldPart source _ => source.id == field

def NumericComputationOperation.wellFormedBool
    (operation : NumericComputationOperation) (model : FlatModel) : Bool :=
  model.admitsNumericComputationTarget operation.target &&
    operation.expression.allAtoms model.admitsNumericComputationOperand &&
    !operation.expression.anyAtom
      (NumericComputationAtom.references operation.target.id) &&
    operation.expression.isAdmittedResolvedNumericOperation &&
    operation.expression.numericOperationAuthoringCheck == .accepted &&
    match operation.expression.summary? NumericComputationAtom.numericScaleSummary with
    | some summary =>
        exactNumericScaleComparisonAllowedWithSuppression
          operation.suppressExactScaleWarning
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

/-- A checked numeric operation paired once with its complete resolved target policy. Evaluation cannot substitute a different policy. -/
structure CheckedNumericTargetComputationOperation (model : FlatModel) where
  operation : CheckedNumericComputationOperation model
  policy : NumericTargetPolicy
  targetMatches : policy.info = operation.core.target.info

private def FlatModel.resolveNumericComputationTarget
    (model : FlatModel) (target : FieldId) :
    Except NumericComputationElabError FlatNumberField := do
  let declaration ← (model.resolveNonrepeatableDeclarationById target).mapError .resolve
  match declaration.toNumberField? with
  | some field => pure field
  | none => throw (.targetNotNumber target)

private def FlatModel.resolveTemporalNumericComputationField
    (model : FlatModel) (declaringGroup : GroupPath) (target : FieldId)
    (reference : SurfaceFieldPath) (accepts : FlatTemporalField → Bool) :
    Except NumericComputationElabError FlatTemporalField := do
  let declaration ←
    (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
  if declaration.id == target then
    throw (.targetSelfReference target)
  match declaration.toTemporalField? with
  | some field =>
      if accepts field then pure field
      else throw (.incompatibleTemporalSource declaration.path)
  | none => throw (.incompatibleTemporalSource declaration.path)

private def FlatModel.resolveNumericComputationExpression
    (model : FlatModel) (declaringGroup : GroupPath) (target : FieldId)
    (expression : AuthoredNumericExpr SurfaceNumericAtom) :
    Except NumericComputationElabError
      (AuthoredNumericExpr NumericComputationAtom) :=
  expression.mapM fun
    | .field reference => do
        let declaration ←
          (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
        if declaration.id == target then
          throw (.targetSelfReference target)
        else if declaration.toNumberField?.isSome then
          pure (.field declaration)
        else
          throw (.operandNotNumber declaration.path)
    | .baseYear =>
        match model.baseYear with
        | some year => pure (.baseYear year)
        | none => throw .baseYearNotDeclared
    | .baseYearDatePart source part =>
        match model.baseYear with
        | some year => pure (.baseYearDatePart year source part)
        | none => throw .baseYearNotDeclared
    | .temporalFieldPart reference part => do
        let field ← model.resolveTemporalNumericComputationField
          declaringGroup target reference
          (fun source => part.admittedBy source model.hasBaseYear)
        pure (.temporalFieldPart field part)

/-- Resolve and check one nonrepeatable numeric computation operation in the shared plain-arithmetic or direct root value-function fragment. The default unsuppressed route preserves the exact result-scale gate; the explicit suppression flag bypasses only that gate. General wrapper traversal, repeatable evaluation, table integration, target-policy construction, and scheduling remain separate owners. -/
def elaborateNumericComputationOperation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
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
      if !resolved.isAdmittedResolvedNumericOperation then
        throw .unsupportedExpression
      match resolved.numericOperationAuthoringCheck with
      | .accepted => pure ()
      | result => throw (.authoring result)
      let summary ← match resolved.summary?
          NumericComputationAtom.numericScaleSummary with
        | some summary => pure summary
        | none => throw .unsupportedExpression
      if !exactNumericScaleComparisonAllowedWithSuppression
          suppressExactScaleWarning
          (NumericScaleSummary.field target.info.scale) summary then
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

/-- Read either direct temporal component family through one computation-phase empty/value/poison and kind-checking boundary. -/
def readTemporalNumeric (context : ScalarComputationContext)
    (field : FlatTemporalField) (project : TemporalValue → Option Rat) :
    Except NumericComputationFault NumericComputationResult :=
  match observeCell .computation (context.read field.id) with
  | .empty => pure (.value 0)
  | .value (.temporal value) =>
      if value.kind != field.kind then
        throw (.fieldKindMismatch field.id)
      else
        match project value with
        | some amount => pure (.value amount)
        | none => throw (.fieldKindMismatch field.id)
  | .value _ => throw (.fieldKindMismatch field.id)
  | .unknown cause | .poison cause => pure (.poison cause)

def readNumericComputationAtom (context : ScalarComputationContext) :
    NumericComputationAtom →
      Except NumericComputationFault NumericComputationResult
  | .field declaration => context.readNumeric declaration
  | .baseYear year => pure (.value year)
  | .baseYearDatePart year source part =>
      pure (.value (baseYearDateSourceNumericPart year source part))
  | .temporalFieldPart field part =>
      context.readTemporalNumeric field part.project?

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

def FlatFieldDecl.numericComputationFault?
    (declaration : FlatFieldDecl) : Option NumericComputationFault :=
  if declaration.toNumberField?.isSome then
    none
  else
    some (.fieldKindMismatch declaration.id)

/-- Preflight one resolved source atom. Checked temporal component atoms already retain their kind, while a forged direct declaration can still carry a non-Number kind. -/
def NumericComputationAtom.numericComputationFault? :
    NumericComputationAtom → Option NumericComputationFault
  | .field declaration => declaration.numericComputationFault?
  | .baseYear _ => none
  | .baseYearDatePart _ _ _ => none
  | .temporalFieldPart _ _ => none

namespace LoweredNumericExpr

/-- The first structural fault in the complete lowered tree. This pass runs before any context read, so a bad atom cannot be hidden by data-dependent poison. -/
def computationFaultWith?
    (fault? : Atom → Option NumericComputationFault) :
    LoweredNumericExpr Atom → Option NumericComputationFault
  | .atom sourceAtom => fault? sourceAtom
  | .literal _ => none
  | .binary _ left right | .power left right | .extremum _ left right =>
      match left.computationFaultWith? fault? with
      | some fault => some fault
      | none => right.computationFaultWith? fault?
  | .abs body => body.computationFaultWith? fault?
  | .round _ _ body => body.computationFaultWith? fault?

def computationFault? (expression : LoweredNumericExpr FlatFieldDecl) :
    Option NumericComputationFault :=
  expression.computationFaultWith? FlatFieldDecl.numericComputationFault?

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

def evaluateResolvedComputation
    (expression : AuthoredNumericExpr NumericComputationAtom)
    (context : ScalarComputationContext) :
    Except NumericComputationFault NumericComputationResult :=
  let lowered := expression.lowerForEvaluation
  match lowered.computationFaultWith?
      NumericComputationAtom.numericComputationFault? with
  | some fault => .error fault
  | none => lowered.evalComputation context.readNumericComputationAtom

end AuthoredNumericExpr

namespace CheckedNumericComputationOperation

def evaluate (operation : CheckedNumericComputationOperation model)
    (context : ScalarComputationContext) :
    Except NumericComputationFault NumericComputationResult :=
  operation.core.expression.evaluateResolvedComputation context

/-- Attach the complete resolved target policy once, rejecting scale/signedness drift from the already-resolved target. The remaining constraints are intentionally not inferred from `FlatFieldDecl`, which does not retain them. -/
def attachTargetPolicy (operation : CheckedNumericComputationOperation model)
    (policy : NumericTargetPolicy) :
    Except NumericComputationElabError
      (CheckedNumericTargetComputationOperation model) :=
  if targetMatches : policy.info = operation.core.target.info then
    pure { operation, policy, targetMatches }
  else
    throw (.targetPolicyMismatch operation.core.target.info policy.info)

end CheckedNumericComputationOperation

namespace CheckedNumericTargetComputationOperation

/-- Evaluate with the retained target policy and route solely by the checked operation's warning-suppression choice. -/
def evaluate (operation : CheckedNumericTargetComputationOperation model)
    (context : ScalarComputationContext) :
    Except NumericComputationFault NumericTargetCheckResult := do
  let result ← operation.operation.evaluate context
  if operation.operation.core.suppressExactScaleWarning then
    pure (operation.policy.checkWithScaleWarningSuppressed result)
  else
    pure (operation.policy.check result)

end CheckedNumericTargetComputationOperation

end A12Kernel
