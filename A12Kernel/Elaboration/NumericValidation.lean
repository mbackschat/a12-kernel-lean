import A12Kernel.Elaboration.NumericAggregate
import A12Kernel.Semantics.NumericTolerance

/-! # Checked numeric validation

This capsule connects two model-resolved nonrepeatable numeric expressions to the existing authored-scale, one-pass lowering, arithmetic-fillability, ordinary-comparison, and fixed-tolerance semantics. Ordinary rules retain exact same-group admission; generated computation validation explicitly selects model-wide nonrepeatable admission for its already-checked operation. Number fields, numeric `BaseYear`, Base-Year date-component extraction, direct temporal field-component sources, checked ordinary String/Enumeration/category `FieldValueAsNumber`, Date-only month/year differences, and direct Number field-list aggregates share arithmetic. Operation-form rounding, absolute value, and Min/Max operand-list calls compose at ordinary arithmetic operand positions. Every Min/Max list member is a complete numeric operation, while each call independently permits at most one immediate or grouped literal. Rounding and absolute value still reject an immediate literal body. Structured input is assumed to come from a grammar-valid decoder that keeps each literal value coherent with its authored scale; concrete parsing, partially-known Date policy, constructed-Date legacy execution, and that decoder contract remain outside this module.
-/

namespace A12Kernel

/-- Model-resolved numeric-validation atoms. Numeric Base Year and component sources remain non-expandable scale-0 atoms rather than becoming authored literals. -/
abbrev NumericValidationAtom := ResolvedNumericAtom FlatNumberField

/-- Parser-independent input to the checked numeric consumer. -/
structure SurfaceNumericComparison where
  op : NumericValidationOp
  left : AuthoredNumericExpr SurfaceNumericAtom
  right : AuthoredNumericExpr SurfaceNumericAtom
  suppressExactScaleWarning : Bool := false
  deriving Repr, DecidableEq

/-- Resolved runtime representation; static guarantees belong to `CheckedNumericComparison`. -/
structure NumericComparison where
  op : NumericValidationOp
  left : AuthoredNumericExpr NumericValidationAtom
  right : AuthoredNumericExpr NumericValidationAtom
  suppressExactScaleWarning : Bool := false
  deriving Repr, DecidableEq

/-- Closed rejection classes for this deliberately narrow consumer, not kernel diagnostic codes. -/
inductive NumericValidationElabError where
  | resolve (error : ResolveError)
  | fieldOutsideRowGroup (path : List String) (rowGroup : GroupPath)
  | fieldNotNumber (path : List String)
  | rangeOperandNotString (path : List String)
  | invalidStringRange (start finish : Nat)
  | fieldValueAsNumberNotConvertible (path : List String)
  | fieldValueAsNumberEnumeration (path : List String)
      (error : EnumerationOperandError)
  | incompatibleTemporalSource (path : List String)
  | incompatibleDateDifference
  | baseYearNotDeclared
  | aggregate (error : NumericAggregateElabError)
  | constantExpression
  | unsupportedExpression
  | authoring (result : NumericAuthoringCheck)
  | exactScaleMismatch (left right : NumericScaleSummary)
  | incoherentCore
  deriving Repr, DecidableEq

/-- Static field-admission policy for one resolved numeric comparison. Ordinary rules keep their exact rule group; generated computation validation preserves the computation's already-checked model-wide nonrepeatable operand scope. -/
inductive NumericOperandScope where
  | sameGroup
  | modelWideNonrepeatable
  deriving Repr, DecidableEq

private def FlatModel.admitsNumberInGroup (model : FlatModel) (rowGroup : GroupPath)
    (field : FlatNumberField) : Bool :=
  match model.lookupUniqueId field.id with
  | .ok declaration =>
      declaration.groupPath == rowGroup &&
        declaration.repeatableScope.isEmpty &&
        declaration.toNumberField? == some field
  | .error _ => false

private def FlatModel.admitsTemporalInGroup (model : FlatModel)
    (rowGroup : GroupPath) (field : FlatTemporalField) : Bool :=
  match model.lookupUniqueId field.id with
  | .ok declaration =>
      declaration.groupPath == rowGroup &&
        declaration.repeatableScope.isEmpty &&
        declaration.toTemporalField? == some field
  | .error _ => false

private def FlatModel.admitsStringInGroup (model : FlatModel)
    (rowGroup : GroupPath) (field : FlatStringField) : Bool :=
  match model.lookupUniqueId field.id with
  | .ok declaration =>
      declaration.groupPath == rowGroup &&
        declaration.repeatableScope.isEmpty &&
        declaration.toStringValueField? == some field
  | .error _ => false

private def FlatModel.admitsNumberModelWide (model : FlatModel)
    (field : FlatNumberField) : Bool :=
  match model.lookupUniqueId field.id with
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.toNumberField? == some field
  | .error _ => false

private def FlatModel.admitsTemporalModelWide (model : FlatModel)
    (field : FlatTemporalField) : Bool :=
  match model.lookupUniqueId field.id with
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.toTemporalField? == some field
  | .error _ => false

private def FlatModel.admitsStringModelWide (model : FlatModel)
    (field : FlatStringField) : Bool :=
  model.admitsStringValueField field

private def FlatModel.admitsFieldValueAsNumberInGroup (model : FlatModel)
    (rowGroup : GroupPath) (source : ResolvedFieldValueAsNumberSource) : Bool :=
  match model.lookupUniqueId source.fieldId with
  | .ok declaration =>
      declaration.groupPath == rowGroup &&
        model.admitsFieldValueAsNumberSource source
  | .error _ => false

private def resolveTemporalNumericField (model : FlatModel) (rowGroup : GroupPath)
    (reference : SurfaceFieldPath) (accepts : FlatTemporalField → Bool) :
    Except NumericValidationElabError FlatTemporalField := do
  let declaration ← (model.resolveField rowGroup reference).mapError .resolve
  if declaration.groupPath != rowGroup then
    throw (.fieldOutsideRowGroup declaration.path rowGroup)
  match declaration.toTemporalField? with
  | some field =>
      if accepts field then pure field
      else throw (.incompatibleTemporalSource declaration.path)
  | none => throw (.incompatibleTemporalSource declaration.path)

private def numericValidationSummary (atom : NumericValidationAtom) :
    NumericScaleSummary :=
  atom.summary fun source => NumericScaleSummary.field source.info.scale

private def NumericValidationAtom.admitted
    (model : FlatModel) (rowGroup : GroupPath) (scope : NumericOperandScope) :
    NumericValidationAtom → Bool
  | .field source =>
      match scope with
      | .sameGroup => model.admitsNumberInGroup rowGroup source
      | .modelWideNonrepeatable => model.admitsNumberModelWide source
  | .baseYear year => model.baseYear == some year
  | .baseYearDatePart year _ _ => model.baseYear == some year
  | .temporalFieldPart source part =>
      (match scope with
        | .sameGroup => model.admitsTemporalInGroup rowGroup source
        | .modelWideNonrepeatable => model.admitsTemporalModelWide source) &&
        part.admittedBy source model.hasBaseYear
  | .stringRange source start finish =>
      validStringRange start finish &&
        match scope with
        | .sameGroup => model.admitsStringInGroup rowGroup source
        | .modelWideNonrepeatable => model.admitsStringModelWide source
  | .fieldValueAsNumber source =>
      match scope with
      | .sameGroup => model.admitsFieldValueAsNumberInGroup rowGroup source
      | .modelWideNonrepeatable => model.admitsFieldValueAsNumberSource source
  | .dateDifference unit left right =>
      let admitted : ResolvedDateDifferenceOperand → Bool
        | .field source =>
            source.kind == .date &&
              match scope with
              | .sameGroup => model.admitsTemporalInGroup rowGroup source
              | .modelWideNonrepeatable => model.admitsTemporalModelWide source
        | .baseYear year _ => model.baseYear == some year
      admitted left && admitted right &&
        unit.compatible model.hasBaseYear left.components right.components
  | .aggregate _ source =>
      source.hasMultipleFields && source.hasUniqueFields &&
        source.fields.all fun field =>
          match scope with
          | .sameGroup => model.admitsNumberInGroup rowGroup field
          | .modelWideNonrepeatable => model.admitsNumberModelWide field

/-- Tolerance deliberately bypasses the ordinary exact-comparison scale gate. -/
def NumericValidationOp.acceptsScales (op : NumericValidationOp)
    (left right : NumericScaleSummary) : Bool :=
  match op with
  | .ordinary comparison => comparison.acceptsScales left right
  | .tolerance _ => true

/-- The one legal parser warning suppression bypasses only the exact-comparison scale gate. Every other authoring check remains independent. -/
def NumericValidationOp.acceptsScalesWithSuppression
    (op : NumericValidationOp) (suppressExactScaleWarning : Bool)
    (left right : NumericScaleSummary) : Bool :=
  match op with
  | .ordinary .equal | .ordinary .notEqual =>
      exactNumericScaleComparisonAllowedWithSuppression
        suppressExactScaleWarning left right
  | .ordinary .less | .ordinary .lessEqual
  | .ordinary .greater | .ordinary .greaterEqual
  | .tolerance _ => true

def NumericComparison.wellFormedInBool
    (comparison : NumericComparison)
    (model : FlatModel) (rowGroup : GroupPath)
    (scope : NumericOperandScope) : Bool :=
  (comparison.left.anyAtom ResolvedNumericAtom.isField ||
      comparison.right.anyAtom ResolvedNumericAtom.isField) &&
    comparison.left.isAdmittedResolvedNumericOperation &&
    comparison.right.isAdmittedResolvedNumericOperation &&
    comparison.left.allAtoms (NumericValidationAtom.admitted model rowGroup scope) &&
    comparison.right.allAtoms (NumericValidationAtom.admitted model rowGroup scope) &&
    comparison.left.numericOperationAuthoringCheck == .accepted &&
    comparison.right.numericOperationAuthoringCheck == .accepted &&
    match
        comparison.left.summary? numericValidationSummary,
        comparison.right.summary? numericValidationSummary with
    | some leftSummary, some rightSummary =>
        comparison.op.acceptsScalesWithSuppression
          comparison.suppressExactScaleWarning leftSummary rightSummary
    | _, _ => false

def NumericComparison.wellFormedBool
    (comparison : NumericComparison)
    (model : FlatModel) (rowGroup : GroupPath) : Bool :=
  comparison.wellFormedInBool model rowGroup .sameGroup

def NumericComparison.WellFormedIn
    (comparison : NumericComparison)
    (model : FlatModel) (rowGroup : GroupPath)
    (scope : NumericOperandScope) : Prop :=
  comparison.wellFormedInBool model rowGroup scope = true

def NumericComparison.WellFormed
    (comparison : NumericComparison)
    (model : FlatModel) (rowGroup : GroupPath) : Prop :=
  comparison.wellFormedBool model rowGroup = true

/-- A model-coherent numeric comparison produced only after every static stage succeeds. -/
structure CheckedNumericComparison (model : FlatModel) where
  rowGroup : GroupPath
  operandScope : NumericOperandScope := .sameGroup
  core : NumericComparison
  modelWellFormed : model.validate.isOk = true
  wellFormed : core.WellFormedIn model rowGroup operandScope

/-- Whether one resolved validation atom references a field ID. Context-free Base-Year sources contribute no reference. -/
def NumericValidationAtom.referencesField : NumericValidationAtom → FieldId → Bool
  | .field source, field => source.id == field
  | .baseYear _, _ | .baseYearDatePart _ _ _, _ => false
  | .temporalFieldPart source _, field => source.id == field
  | .stringRange source _ _, field => source.id == field
  | .fieldValueAsNumber source, field => source.fieldId == field
  | .dateDifference _ left right, field =>
      left.references field || right.references field
  | .aggregate _ source, field => source.referencesField field

/-- Whether every field read by one resolved validation atom is relevant. -/
def NumericValidationAtom.allRelevant (atom : NumericValidationAtom)
    (isRelevant : FlatRelevance) : Bool :=
  match atom with
  | .field source => isRelevant source.id
  | .baseYear _ | .baseYearDatePart _ _ _ => true
  | .temporalFieldPart source _ => isRelevant source.id
  | .stringRange source _ _ => isRelevant source.id
  | .fieldValueAsNumber source => isRelevant source.fieldId
  | .dateDifference _ left right =>
      let operandRelevant : ResolvedDateDifferenceOperand → Bool
        | .field source => isRelevant source.id
        | .baseYear _ _ => true
      operandRelevant left && operandRelevant right
  | .aggregate _ source => source.allRelevant isRelevant

/-- Reference membership traverses both authored operands without erasing expression shape. -/
def NumericComparison.referencesField (comparison : NumericComparison)
    (field : FieldId) : Bool :=
  comparison.left.anyAtom (·.referencesField field) ||
    comparison.right.anyAtom (·.referencesField field)

/-- Partial relevance covers every field atom across both operands. -/
def NumericComparison.allRelevant (comparison : NumericComparison)
    (isRelevant : FlatRelevance) : Bool :=
  comparison.left.allAtoms (·.allRelevant isRelevant) &&
    comparison.right.allAtoms (·.allRelevant isRelevant)

private def FlatModel.ensureNumericAggregateRowGroup (model : FlatModel)
    (rowGroup : GroupPath) :
    List FlatNumberField → Except NumericValidationElabError Unit
  | [] => pure ()
  | field :: remaining =>
      match model.lookupUniqueId field.id with
      | .error _ => throw .incoherentCore
      | .ok declaration => do
          if declaration.groupPath != rowGroup then
            throw (.fieldOutsideRowGroup declaration.path rowGroup)
          model.ensureNumericAggregateRowGroup rowGroup remaining

private def resolveNumericAtom (model : FlatModel) (rowGroup : GroupPath) :
    SurfaceNumericAtom → Except NumericValidationElabError NumericValidationAtom
  | .field reference => do
      let declaration ←
        (model.resolveField rowGroup reference).mapError .resolve
      if declaration.groupPath != rowGroup then
        throw (.fieldOutsideRowGroup declaration.path rowGroup)
      match declaration.toNumberField? with
      | some field => pure (.field field)
      | none => throw (.fieldNotNumber declaration.path)
  | .baseYear =>
      match model.baseYear with
      | some year => pure (.baseYear year)
      | none => throw .baseYearNotDeclared
  | .baseYearDatePart source part =>
      match model.baseYear with
      | some year => pure (.baseYearDatePart year source part)
      | none => throw .baseYearNotDeclared
  | .temporalFieldPart reference part => do
      let field ← resolveTemporalNumericField model rowGroup reference
        (fun source => part.admittedBy source model.hasBaseYear)
      pure (.temporalFieldPart field part)
  | .stringRange reference start finish => do
      let declaration ← (model.resolveField rowGroup reference).mapError .resolve
      if declaration.groupPath != rowGroup then
        throw (.fieldOutsideRowGroup declaration.path rowGroup)
      if !validStringRange start finish then
        throw (.invalidStringRange start finish)
      match declaration.toStringValueField? with
      | some field => pure (.stringRange field start finish)
      | none => throw (.rangeOperandNotString declaration.path)
  | .fieldValueAsNumber surface => do
      let declaration ←
        (model.resolveField rowGroup surface.reference).mapError .resolve
      if declaration.groupPath != rowGroup then
        throw (.fieldOutsideRowGroup declaration.path rowGroup)
      match declaration.resolveFieldValueAsNumberSource surface.projectionRef with
      | .ok source => pure (.fieldValueAsNumber source)
      | .error .notConvertible =>
          throw (.fieldValueAsNumberNotConvertible declaration.path)
      | .error (.enumeration error) =>
          throw (.fieldValueAsNumberEnumeration declaration.path error)
      | .error .incoherentEnumeration => throw .incoherentCore
  | .dateDifference unit left right => do
      let resolveOperand : SurfaceDateDifferenceOperand →
          Except NumericValidationElabError ResolvedDateDifferenceOperand
        | .field reference => do
            let field ← resolveTemporalNumericField model rowGroup reference
              (fun source => source.kind == .date &&
                unit.admittedBy model.hasBaseYear source.components)
            pure (.field field)
        | .baseYear source =>
            match model.baseYear with
            | some year => pure (.baseYear year source)
            | none => throw .baseYearNotDeclared
      let resolvedLeft ← resolveOperand left
      let resolvedRight ← resolveOperand right
      if unit.compatible model.hasBaseYear
          resolvedLeft.components resolvedRight.components then
        pure (.dateDifference unit resolvedLeft resolvedRight)
      else
        throw .incompatibleDateDifference
  | .aggregate op source => do
      let checked ← (elaborateNumericAggregateFields model rowGroup source).mapError
        NumericValidationElabError.aggregate
      model.ensureNumericAggregateRowGroup rowGroup checked.fields
      pure (.aggregate op checked.resolvedFields)

private def resolveNumericExpression (model : FlatModel) (rowGroup : GroupPath) :
    AuthoredNumericExpr SurfaceNumericAtom →
      Except NumericValidationElabError
        (AuthoredNumericExpr NumericValidationAtom) :=
  AuthoredNumericExpr.mapM (resolveNumericAtom model rowGroup)

/-- Resolve and check both operands before performing their one-pass lowering at evaluation time. -/
def elaborateNumericComparison (model : FlatModel) (rowGroup : GroupPath)
    (surface : SurfaceNumericComparison) :
    Except NumericValidationElabError (CheckedNumericComparison model) := do
  match hModel : model.validate with
  | .error error => throw (.resolve error)
  | .ok () =>
      if !GroupPath.isValid rowGroup then
        throw (.resolve (.invalidRuleGroup rowGroup))
      let left ← resolveNumericExpression model rowGroup surface.left
      let right ← resolveNumericExpression model rowGroup surface.right
      if !(left.anyAtom ResolvedNumericAtom.isField ||
          right.anyAtom ResolvedNumericAtom.isField) then
        throw .constantExpression
      if !left.isAdmittedResolvedNumericOperation then
        throw .unsupportedExpression
      if !right.isAdmittedResolvedNumericOperation then
        throw .unsupportedExpression
      match left.numericOperationAuthoringCheck with
      | .accepted => pure ()
      | result => throw (.authoring result)
      match right.numericOperationAuthoringCheck with
      | .accepted => pure ()
      | result => throw (.authoring result)
      let leftSummary ← match left.summary? numericValidationSummary with
        | some summary => pure summary
        | none => throw .unsupportedExpression
      let rightSummary ← match right.summary? numericValidationSummary with
        | some summary => pure summary
        | none => throw .unsupportedExpression
      if !surface.op.acceptsScalesWithSuppression
          surface.suppressExactScaleWarning leftSummary rightSummary then
        throw (.exactScaleMismatch leftSummary rightSummary)
      let core : NumericComparison := {
        op := surface.op
        left
        right
        suppressExactScaleWarning := surface.suppressExactScaleWarning }
      if hCore : core.wellFormedBool model rowGroup = true then
        pure {
          rowGroup
          core
          modelWellFormed := by
            rw [hModel]
            rfl
          wellFormed := hCore
        }
      else
        throw .incoherentCore

/-- Lift one already-classified validation numeric operand into the arithmetic outcome domain. Number and temporal component reads share this exact boundary. -/
def NumericOperand.toValidationArithmetic
    (operand : NumericOperand) : Except FormalCause NumericArithmeticOutcome :=
  match operand with
  | .value amount fillability => .ok (.value amount fillability)
  | .unknown cause => .error cause

/-- Lift the existing validation-phase Number read into the arithmetic outcome domain. -/
def FlatContext.resolveNumericArithmetic (context : FlatContext)
    (field : FlatNumberField) : Except FormalCause NumericArithmeticOutcome :=
  (context.resolveNumberComparisonOperand field).toValidationArithmetic

def FlatContext.resolveNumericValidationAtom (context : FlatContext) :
    NumericValidationAtom → Except FormalCause NumericArithmeticOutcome
  | .field field => context.resolveNumericArithmetic field
  | .baseYear year => .ok (.value year .fixed)
  | .baseYearDatePart year source part =>
      .ok (.value (baseYearDateSourceNumericPart year source part) .fixed)
  | .temporalFieldPart field part =>
      (context.resolveTemporalNumericOperand field part).toValidationArithmetic
  | .stringRange field start finish =>
      match context.observeValidationAt field.id with
      | .empty => .ok (.value 0 .growOnly)
      | .value (.str value) =>
          .ok (.value (utf16RangeAsNatural value start finish) .fixed)
      | .value _ => .error .malformed
      | .unknown cause | .poison cause => .error cause
  | .fieldValueAsNumber source =>
      match context.observeValidationAt source.fieldId with
      | .empty => .ok (.value 0 .both)
      | .value value =>
          match source.valueFor? value with
          | some amount => .ok (.value amount .fixed)
          | none => .error .malformed
      | .unknown cause | .poison cause => .error cause
  | .dateDifference unit left right =>
      match DateDifferenceOperand.evaluate unit
          (left.validationOperand context) (right.validationOperand context) with
      | .ok operand => operand.toValidationArithmetic
      | .error _ => .error .malformed
  | .aggregate op source =>
      (source.evaluate op context.observeValidationAt).toValidationArithmetic

def combineNumericValidationOutcomes
    (combine : NumericArithmeticOutcome → NumericArithmeticOutcome →
      NumericArithmeticOutcome)
    (left right : Except FormalCause NumericArithmeticOutcome) :
    Except FormalCause NumericArithmeticOutcome :=
  match left, right with
  | .error cause, _ => .error cause
  | _, .error cause => .error cause
  | .ok leftOutcome, .ok rightOutcome => .ok (combine leftOutcome rightOutcome)

def evalPlainBinary (op : NumericScaleBinaryOp)
    (left right : Except FormalCause NumericArithmeticOutcome) :
    Except FormalCause NumericArithmeticOutcome :=
  combineNumericValidationOutcomes
    (fun leftOutcome rightOutcome =>
      match op with
        | .add => NumericArithmeticOutcome.eval .add leftOutcome rightOutcome
        | .subtract => NumericArithmeticOutcome.eval .subtract leftOutcome rightOutcome
        | .multiply => NumericArithmeticOutcome.eval .multiply leftOutcome rightOutcome
        | .divide => NumericArithmeticOutcome.divide leftOutcome rightOutcome)
    left right

/-- Whether a lowered tree lies in the consumer's binary-arithmetic runtime subset. -/
def LoweredNumericExpr.isPlainArithmetic : LoweredNumericExpr Atom → Bool
  | .atom _ | .literal _ => true
  | .binary _ left right => left.isPlainArithmetic && right.isPlainArithmetic
  | .power base exponent =>
      base.isPlainArithmetic && exponent.isPlainArithmetic
  | .abs _ | .extremum _ _ _ | .extremumCall _ _ _ | .round _ _ _ => false

/-- Runtime-shape mirror of one authored extremum call, including its independent per-call constant budget. -/
def LoweredNumericExpr.extremumCallConstantUse?
    (expected : NumericExtremumOp) :
    LoweredNumericExpr Atom → Option Bool
  | .extremumCall actual constantUse _ =>
      if actual != expected then none else constantUse
  | _ => none

/-- Read the source-derived admission certificate retained across lowering. -/
def LoweredNumericExpr.isExtremumCall : LoweredNumericExpr Atom → Bool
  | .extremumCall _ constantUse _ => constantUse.isSome
  | _ => false

/-- Runtime-capable numeric-operation shape after grouping erasure. -/
def LoweredNumericExpr.isNumericOperation : LoweredNumericExpr Atom → Bool
  | .atom _ | .literal _ => true
  | .binary _ left right | .power left right =>
      left.isNumericOperation && right.isNumericOperation
  | .abs body | .round _ _ body => body.isNumericOperation
  | expression@(.extremumCall _ _ _) => expression.isExtremumCall
  | .extremum _ _ _ => false

def LoweredNumericExpr.isAdmittedValidation (expression : LoweredNumericExpr Atom) :
    Bool :=
  expression.isNumericOperation

/-- Preserve the first formal cause across exact extremum selection of two reached validation outcomes. -/
def NumericExtremumOp.selectValidationOutcome (op : NumericExtremumOp) :
    Except FormalCause NumericArithmeticOutcome →
      Except FormalCause NumericArithmeticOutcome →
        Except FormalCause NumericArithmeticOutcome
  | left, right =>
      combineNumericValidationOutcomes op.selectOutcome left right

def LoweredNumericExpr.evalNumericOperationTree
    (read : Atom → Except FormalCause NumericArithmeticOutcome) :
    LoweredNumericExpr Atom → Except FormalCause NumericArithmeticOutcome
  | .atom sourceAtom => read sourceAtom
  | .literal amount => .ok (.value amount .fixed)
  | .binary op left right =>
      evalPlainBinary op
        (left.evalNumericOperationTree read)
        (right.evalNumericOperationTree read)
  | .power base exponent =>
      combineNumericValidationOutcomes NumericArithmeticOutcome.power
        (base.evalNumericOperationTree read)
        (exponent.evalNumericOperationTree read)
  | .abs body =>
      match body.evalNumericOperationTree read with
      | .ok outcome => .ok outcome.absolute
      | .error cause => .error cause
  | .extremum op left right =>
      op.selectValidationOutcome
        (left.evalNumericOperationTree read)
        (right.evalNumericOperationTree read)
  | .extremumCall _ _ body => body.evalNumericOperationTree read
  | .round mode places body =>
      match body.evalNumericOperationTree read with
      | .ok outcome => .ok (outcome.round mode places)
      | .error cause => .error cause

/-- Evaluate one complete numeric operation after checking its lowered admission certificate. -/
def LoweredNumericExpr.evalNumericOperation?
    (read : Atom → Except FormalCause NumericArithmeticOutcome)
    (expression : LoweredNumericExpr Atom) :
      Option (Except FormalCause NumericArithmeticOutcome) :=
  if expression.isNumericOperation then
    some (expression.evalNumericOperationTree read)
  else
    none

/-- Evaluate exactly the checked runtime fragment. Value functions compose recursively with arithmetic while formal invalidity and arithmetic domain failure remain distinct. -/
def LoweredNumericExpr.evalAdmittedValidation?
    (read : Atom → Except FormalCause NumericArithmeticOutcome)
    (expression : LoweredNumericExpr Atom) :
      Option (Except FormalCause NumericArithmeticOutcome) :=
  expression.evalNumericOperation? read

/-- Evaluate a raw core. The unknown fallback fails closed for a forged unsupported operand and is unreachable through the checked route. -/
def NumericComparison.evalSelected
    (comparison : NumericComparison) (context : FlatContext) : Verdict :=
  match
      comparison.left.lowerForEvaluation.evalAdmittedValidation?
        context.resolveNumericValidationAtom,
      comparison.right.lowerForEvaluation.evalAdmittedValidation?
        context.resolveNumericValidationAtom with
  | some left, some right => comparison.op.evalArithmetic left right
  | _, _ => .unknown

/-- Evaluate one already row-selected checked comparison. -/
def CheckedNumericComparison.evalSelected
    (checked : CheckedNumericComparison model)
    (context : FlatContext) : Verdict :=
  checked.core.evalSelected context

/-- An admitted comparison never fires on an entirely blank full-validation row. -/
def CheckedNumericComparison.evalFull
    (checked : CheckedNumericComparison model)
    (context : FlatContext) (hasContent : Bool) : Verdict :=
  if hasContent then checked.evalSelected context else .notFired

/-- Check a surface comparison and evaluate it against model-derived cells under full validation. -/
def elaborateAndEvalNumericComparison (model : FlatModel) (rowGroup : GroupPath)
    (raw : RawFlatContext) (hasContent : Bool)
    (surface : SurfaceNumericComparison) :
    Except NumericValidationElabError Verdict := do
  let checked ← elaborateNumericComparison model rowGroup surface
  pure (checked.evalFull (model.checkContext raw) hasContent)

end A12Kernel
