import A12Kernel.Elaboration.NumericAggregate
import A12Kernel.Elaboration.StringContext
import A12Kernel.Elaboration.ValidationContext
import A12Kernel.Semantics.FirstFilledValue
import A12Kernel.Semantics.NumericTolerance

/-! # Checked numeric validation

This capsule connects two model-resolved nonrepeatable numeric expressions to the existing authored-scale, one-pass lowering, arithmetic-fillability, ordinary-comparison, and fixed-tolerance semantics. Ordinary rules retain exact same-group admission; generated computation validation explicitly selects model-wide nonrepeatable admission for its already-checked operation. Number fields, numeric `BaseYear`, Base-Year date-component extraction, direct temporal field-component sources, UTF-16 String `Length`, checked ordinary String/Enumeration/category `FieldValueAsNumber`, Date-only month/year differences, and direct Number field-list aggregates share arithmetic. The atom-parameterized comparison carrier also lets generated validation retain a checked direct `FirstFilledValue` source whose relevance is resolved in prefix order, without adding another arithmetic tree or evaluator. Operation-form rounding, absolute value, and Min/Max operand-list calls compose at ordinary arithmetic operand positions. Every Min/Max list member is a complete numeric operation, while each call independently permits at most one immediate or grouped literal. Rounding and absolute value still reject an immediate literal body. Structured input is assumed to come from a grammar-valid decoder that keeps each literal value coherent with its authored scale; concrete parsing, partially-known Date policy, constructed-Date legacy execution, and that decoder contract remain outside this module.
-/

namespace A12Kernel

/-- Model-resolved numeric-validation atoms. Numeric Base Year and component sources remain non-expandable scale-0 atoms rather than becoming authored literals. -/
abbrev NumericValidationAtom := ResolvedNumericAtom FlatNumberField

/-- Numeric source unavailability preserves a reached formal cell cause when one exists while representing unresolved/erroneous group product state without fabricating such a cause. Both project to `Verdict.unknown`; the distinction remains available to Explain and later checked-document consumers. -/
inductive NumericValidationUnavailable where
  | formal (cause : FormalCause)
  | groupState
  | nonRelevant
  deriving Repr, DecidableEq

/-- Parser-independent input to the checked numeric consumer. -/
structure SurfaceNumericComparison where
  op : NumericValidationOp
  left : AuthoredNumericExpr SurfaceNumericAtom
  right : AuthoredNumericExpr SurfaceNumericAtom
  suppressExactScaleWarning : Bool := false
  deriving Repr, DecidableEq

/-- Resolved runtime representation parameterized only at the checked numeric-source boundary. -/
structure NumericComparisonOf (Atom : Type) where
  op : NumericValidationOp
  left : AuthoredNumericExpr Atom
  right : AuthoredNumericExpr Atom
  suppressExactScaleWarning : Bool := false
  deriving Repr, DecidableEq

/-- Ordinary resolved numeric comparisons retain their established atom type and API. -/
abbrev NumericComparison := NumericComparisonOf NumericValidationAtom

/-- A relevance-aware numeric leaf either delegates one established atom unchanged or retains one checked direct field list whose prefix consumer must gate each reached source separately. -/
inductive OrderedNumericValidationAtom where
  | ordinary (source : NumericValidationAtom)
  | firstFilled (source : ResolvedDirectNumberEntityFields)
  deriving Repr, DecidableEq

/-- One numeric comparison whose atom resolver, rather than the containing leaf, owns relevance timing. -/
abbrev OrderedNumericComparison :=
  NumericComparisonOf OrderedNumericValidationAtom

/-- Closed rejection classes for this deliberately narrow consumer, not kernel diagnostic codes. -/
inductive NumericValidationElabError where
  | resolve (error : ResolveError)
  | fieldOutsideRowGroup (path : List String) (rowGroup : GroupPath)
  | fieldNotNumber (path : List String)
  | lengthOperandNotEvaluatedString (path : List String)
  | rangeOperandNotString (path : List String)
  | invalidStringRange (start finish : Nat)
  | fieldValueAsNumberNotConvertible (path : List String)
  | fieldValueAsNumberEnumeration (path : List String)
      (error : EnumerationOperandError)
  | incompatibleTemporalSource (path : List String)
  | incompatibleDateDifference
  | baseYearNotDeclared
  | aggregate (error : NumericAggregateElabError)
  | groupReference (error : SingleGroupElabError)
  | unknownGroupInCount (path : GroupPath)
  | repeatableGroupCountRequiresStar (path : GroupPath)
  | groupCountNeedsMultipleOperands
  | rootGroupInGroupCount (path : GroupPath)
  | overlappingGroupCountOperands (left right : GroupPath)
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
  | .stringLength source =>
      match scope with
      | .sameGroup => model.admitsStringInGroup rowGroup source
      | .modelWideNonrepeatable => model.admitsStringModelWide source
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
  | .filledGroupCount groups =>
      1 < groups.length &&
        !groups.any ResolvedGroupReference.isRoot &&
        (ResolvedGroupReferences.firstOverlap? groups).isNone &&
        ResolvedGroupReferences.wellFormedBool groups model rowGroup

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
  (comparison.left.anyAtom ResolvedNumericAtom.isDataDependent ||
      comparison.right.anyAtom ResolvedNumericAtom.isDataDependent) &&
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

/-- Whether one resolved validation atom references a field ID. Context-free Base-Year sources contribute no reference; a fixed group count references every field in each counted subtree. -/
def NumericValidationAtom.referencesField (model : FlatModel) :
    NumericValidationAtom → FieldId → Bool
  | .field source, field => source.id == field
  | .baseYear _, _ | .baseYearDatePart _ _ _, _ => false
  | .temporalFieldPart source _, field => source.id == field
  | .stringLength source, field => source.id == field
  | .stringRange source _ _, field => source.id == field
  | .fieldValueAsNumber source, field => source.fieldId == field
  | .dateDifference _ left right, field =>
      left.references field || right.references field
  | .aggregate _ source, field => source.referencesField field
  | .filledGroupCount groups, field =>
      groups.any fun group => group.referencesField model field

/-- Whether every field read by one resolved validation atom is relevant. -/
def NumericValidationAtom.allRelevant (atom : NumericValidationAtom)
    (isRelevant : FlatRelevance) : Bool :=
  match atom with
  | .field source => isRelevant source.id
  | .baseYear _ | .baseYearDatePart _ _ _ => true
  | .temporalFieldPart source _ => isRelevant source.id
  | .stringLength source => isRelevant source.id
  | .stringRange source _ _ => isRelevant source.id
  | .fieldValueAsNumber source => isRelevant source.fieldId
  | .dateDifference _ left right =>
      let operandRelevant : ResolvedDateDifferenceOperand → Bool
        | .field source => isRelevant source.id
        | .baseYear _ _ => true
      operandRelevant left && operandRelevant right
  | .aggregate _ source => source.allRelevant isRelevant
  | .filledGroupCount _ => true

/-- Reference membership traverses both authored operands without erasing expression shape. -/
def NumericComparison.referencesField (comparison : NumericComparison)
    (model : FlatModel) (field : FieldId) : Bool :=
  comparison.left.anyAtom (·.referencesField model field) ||
    comparison.right.anyAtom (·.referencesField model field)

/-- Partial relevance covers every field atom across both operands. -/
def NumericComparison.allRelevant (comparison : NumericComparison)
    (isRelevant : FlatRelevance) : Bool :=
  comparison.left.allAtoms (·.allRelevant isRelevant) &&
    comparison.right.allAtoms (·.allRelevant isRelevant)

namespace OrderedNumericValidationAtom

def isDataDependent : OrderedNumericValidationAtom → Bool
  | .ordinary source => source.isDataDependent
  | .firstFilled _ => true

def summary : OrderedNumericValidationAtom → NumericScaleSummary
  | .ordinary source => numericValidationSummary source
  | .firstFilled source => source.scaleSummary

def admitted (atom : OrderedNumericValidationAtom)
    (model : FlatModel) (rowGroup : GroupPath)
    (scope : NumericOperandScope) : Bool :=
  match atom with
  | .ordinary source => source.admitted model rowGroup scope
  | .firstFilled source =>
      source.hasMultipleFields && source.hasUniqueFields &&
        source.fields.all fun field =>
          match scope with
          | .sameGroup => model.admitsNumberInGroup rowGroup field
          | .modelWideNonrepeatable => model.admitsNumberModelWide field

def referencesField (atom : OrderedNumericValidationAtom)
    (model : FlatModel) (field : FieldId) : Bool :=
  match atom with
  | .ordinary source => source.referencesField model field
  | .firstFilled source => source.referencesField field

end OrderedNumericValidationAtom

/-- Static admission for the relevance-aware numeric leaf reuses the complete authored-operation checks and delegates only atom-specific model coherence. -/
def OrderedNumericComparison.wellFormedInBool
    (comparison : OrderedNumericComparison)
    (model : FlatModel) (rowGroup : GroupPath)
    (scope : NumericOperandScope) : Bool :=
  (comparison.left.anyAtom OrderedNumericValidationAtom.isDataDependent ||
      comparison.right.anyAtom OrderedNumericValidationAtom.isDataDependent) &&
    comparison.left.isAdmittedResolvedNumericOperation &&
    comparison.right.isAdmittedResolvedNumericOperation &&
    comparison.left.allAtoms (·.admitted model rowGroup scope) &&
    comparison.right.allAtoms (·.admitted model rowGroup scope) &&
    comparison.left.numericOperationAuthoringCheck == .accepted &&
    comparison.right.numericOperationAuthoringCheck == .accepted &&
    match
        comparison.left.summary? OrderedNumericValidationAtom.summary,
        comparison.right.summary? OrderedNumericValidationAtom.summary with
    | some leftSummary, some rightSummary =>
        comparison.op.acceptsScalesWithSuppression
          comparison.suppressExactScaleWarning leftSummary rightSummary
    | _, _ => false

def OrderedNumericComparison.referencesField
    (comparison : OrderedNumericComparison)
    (model : FlatModel) (field : FieldId) : Bool :=
  comparison.left.anyAtom (·.referencesField model field) ||
    comparison.right.anyAtom (·.referencesField model field)

structure CheckedOrderedNumericComparison (model : FlatModel) where
  rowGroup : GroupPath
  operandScope : NumericOperandScope := .sameGroup
  core : OrderedNumericComparison
  modelWellFormed : model.validate.isOk = true
  wellFormed : core.wellFormedInBool model rowGroup operandScope = true

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

private def NumericValidationElabError.ofFixedGroupReferenceError :
    FixedGroupReferenceError → NumericValidationElabError
  | .reference error => .groupReference error
  | .unknownGroup path => .unknownGroupInCount path
  | .repeatableGroupRequiresAddress path =>
      .repeatableGroupCountRequiresStar path

private def resolveFixedGroupCountOperands (model : FlatModel)
    (rowGroup : GroupPath) :
    List SurfaceGroupReference →
      Except NumericValidationElabError (List ResolvedGroupReference)
  | [] => pure []
  | surface :: remaining => do
      let resolved ← model.resolveFixedGroupReference rowGroup surface
        |>.mapError NumericValidationElabError.ofFixedGroupReferenceError
      pure (resolved :: (← resolveFixedGroupCountOperands model rowGroup remaining))

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
  | .stringLength reference => do
      let declaration ← (model.resolveField rowGroup reference).mapError .resolve
      if declaration.groupPath != rowGroup then
        throw (.fieldOutsideRowGroup declaration.path rowGroup)
      match declaration.toStringValueField? with
      | some field => pure (.stringLength field)
      | none => throw (.lengthOperandNotEvaluatedString declaration.path)
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
  | .filledGroupCount surfaces => do
      let groups ← resolveFixedGroupCountOperands model rowGroup surfaces
      if groups.length < 2 then
        throw .groupCountNeedsMultipleOperands
      match groups.find? ResolvedGroupReference.isRoot with
      | some root => throw (.rootGroupInGroupCount root.path)
      | none => pure ()
      match ResolvedGroupReferences.firstOverlap? groups with
      | some (left, right) =>
          throw (.overlappingGroupCountOperands left right)
      | none => pure (.filledGroupCount groups)

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
      if !(left.anyAtom ResolvedNumericAtom.isDataDependent ||
          right.anyAtom ResolvedNumericAtom.isDataDependent) then
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
    (operand : NumericOperand) :
    Except NumericValidationUnavailable NumericArithmeticOutcome :=
  match operand with
  | .value amount fillability => .ok (.value amount fillability)
  | .unknown cause => .error (.formal cause)

/-- Lift the existing validation-phase Number read into the arithmetic outcome domain. -/
def FlatContext.resolveNumericArithmetic (context : FlatContext)
    (field : FlatNumberField) :
    Except NumericValidationUnavailable NumericArithmeticOutcome :=
  (context.resolveNumberComparisonOperand field).toValidationArithmetic

def ValidationEvaluationContext.resolveNumericValidationAtom
    (context : ValidationEvaluationContext) :
    NumericValidationAtom →
      Except NumericValidationUnavailable NumericArithmeticOutcome
  | .field field => context.fields.resolveNumericArithmetic field
  | .baseYear year => .ok (.value year .fixed)
  | .baseYearDatePart year source part =>
      .ok (.value (baseYearDateSourceNumericPart year source part) .fixed)
  | .temporalFieldPart field part =>
      (context.fields.resolveTemporalNumericOperand field part).toValidationArithmetic
  | .stringLength field =>
      (context.fields.resolveStringLengthOperand field).toValidationArithmetic
  | .stringRange field start finish =>
      match context.fields.observeValidationAt field.id with
      | .empty => .ok (.value 0 .growOnly)
      | .value (.str value) =>
          .ok (.value (utf16RangeAsNatural value start finish) .fixed)
      | .value _ => .error (.formal .malformed)
      | .unknown cause | .poison cause => .error (.formal cause)
  | .fieldValueAsNumber source =>
      match context.fields.observeValidationAt source.fieldId with
      | .empty => .ok (.value 0 .both)
      | .value value =>
          match source.valueFor? value with
          | some amount => .ok (.value amount .fixed)
          | none => .error (.formal .malformed)
      | .unknown cause | .poison cause => .error (.formal cause)
  | .dateDifference unit left right =>
      match DateDifferenceOperand.evaluate unit
          (left.validationOperand context.fields)
          (right.validationOperand context.fields) with
      | .ok operand => operand.toValidationArithmetic
      | .error _ => .error (.formal .malformed)
  | .aggregate op source =>
      (source.evaluate op context.fields.observeValidationAt).toValidationArithmetic
  | .filledGroupCount groups =>
      match context.groups.resolveAll groups with
      | none => .error .groupState
      | some states =>
          match numberOfFilledGroups states with
          | .unknown => .error .groupState
          | .value count =>
              .ok (.value count
                (if count < groups.length then .growOnly else .fixed))

/-- Preserve the established flat-only numeric entry point. A group-count atom evaluated without resolved group state becomes explicitly unavailable. -/
def FlatContext.resolveNumericValidationAtom (context : FlatContext)
    (atom : NumericValidationAtom) :
    Except NumericValidationUnavailable NumericArithmeticOutcome :=
  ({ fields := context, groups := GroupPresenceContext.unavailable } :
    ValidationEvaluationContext).resolveNumericValidationAtom atom

@[simp]
theorem ValidationEvaluationContext.resolveNumericValidationAtom_withoutGroups
    (fields : FlatContext) (atom : NumericValidationAtom) :
    ({ fields, groups := GroupPresenceContext.unavailable } :
      ValidationEvaluationContext).resolveNumericValidationAtom atom =
        fields.resolveNumericValidationAtom atom := by
  rfl

namespace OrderedNumericValidationAtom

/-- Resolve one nonempty direct Number field list in order, gating each reached source before its checked validation read. This proof-visible worker is used only by the relevance-aware numeric atom. -/
def resolveFirstFilledFields
    (context : ValidationEvaluationContext) (isRelevant : FlatRelevance) :
    List FlatNumberField → FirstFilledScanState →
      Except NumericValidationUnavailable NumericArithmeticOutcome
  | [], state => state.finish.asValidationOperand.toValidationArithmetic
  | field :: remaining, state =>
      if isRelevant field.id then
        match state.step (field.valueListCell context.fields) with
        | .continue next =>
            resolveFirstFilledFields context isRelevant remaining next
        | .done result =>
            result.asNumber.asValidationOperand.toValidationArithmetic
      else
        .error .nonRelevant

/-- Resolve one reached atom with its own relevance rule. Ordinary atoms preserve the previous all-fields gate; direct `FirstFilledValue` checks each source immediately before its declaration-owned read and hides the suffix after a terminal value or formal failure. -/
def resolve (atom : OrderedNumericValidationAtom)
    (context : ValidationEvaluationContext) (isRelevant : FlatRelevance) :
    Except NumericValidationUnavailable NumericArithmeticOutcome :=
  match atom with
  | .ordinary source =>
      if source.allRelevant isRelevant then
        context.resolveNumericValidationAtom source
      else
        .error .nonRelevant
  | .firstFilled source =>
      resolveFirstFilledFields context isRelevant source.fields {}

end OrderedNumericValidationAtom

def combineNumericValidationOutcomes
    (combine : NumericArithmeticOutcome → NumericArithmeticOutcome →
      NumericArithmeticOutcome)
    (left right : Except Error NumericArithmeticOutcome) :
    Except Error NumericArithmeticOutcome :=
  match left, right with
  | .error cause, _ => .error cause
  | _, .error cause => .error cause
  | .ok leftOutcome, .ok rightOutcome => .ok (combine leftOutcome rightOutcome)

def evalPlainBinary (op : NumericScaleBinaryOp)
    (left right : Except Error NumericArithmeticOutcome) :
    Except Error NumericArithmeticOutcome :=
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
    Except Error NumericArithmeticOutcome →
      Except Error NumericArithmeticOutcome →
        Except Error NumericArithmeticOutcome
  | left, right =>
      combineNumericValidationOutcomes op.selectOutcome left right

def LoweredNumericExpr.evalNumericOperationTree
    (read : Atom → Except Error NumericArithmeticOutcome) :
    LoweredNumericExpr Atom → Except Error NumericArithmeticOutcome
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
    (read : Atom → Except Error NumericArithmeticOutcome)
    (expression : LoweredNumericExpr Atom) :
      Option (Except Error NumericArithmeticOutcome) :=
  if expression.isNumericOperation then
    some (expression.evalNumericOperationTree read)
  else
    none

/-- Evaluate exactly the checked runtime fragment. Value functions compose recursively with arithmetic while formal invalidity and arithmetic domain failure remain distinct. -/
def LoweredNumericExpr.evalAdmittedValidation?
    (read : Atom → Except Error NumericArithmeticOutcome)
    (expression : LoweredNumericExpr Atom) :
      Option (Except Error NumericArithmeticOutcome) :=
  expression.evalNumericOperation? read

/-- Evaluate a raw core through one supplied numeric-source resolver. The unknown fallback fails closed for a forged unsupported operand and is unreachable through every checked specialization. -/
def NumericComparisonOf.evalWith
    (comparison : NumericComparisonOf Atom)
    (resolve :
      Atom →
        Except NumericValidationUnavailable NumericArithmeticOutcome) : Verdict :=
  match
      comparison.left.lowerForEvaluation.evalAdmittedValidation?
        resolve,
      comparison.right.lowerForEvaluation.evalAdmittedValidation?
        resolve with
  | some left, some right => comparison.op.evalArithmeticWith left right
  | _, _ => .unknown

/-- Compatibility wrapper for the established ordinary numeric comparison. -/
def NumericComparison.evalWith
    (comparison : NumericComparison)
    (resolve :
      NumericValidationAtom →
        Except NumericValidationUnavailable NumericArithmeticOutcome) : Verdict :=
  NumericComparisonOf.evalWith comparison resolve

/-- Dot-notation compatibility for ordinary comparisons after extracting the atom-parameterized carrier. -/
def NumericComparisonOf.evalSelectedWithGroups
    (comparison : NumericComparisonOf NumericValidationAtom)
    (context : ValidationEvaluationContext) : Verdict :=
  comparison.evalWith context.resolveNumericValidationAtom

/-- Dot-notation compatibility for the established field-only entry point. -/
def NumericComparisonOf.evalSelected
    (comparison : NumericComparisonOf NumericValidationAtom)
    (context : FlatContext) : Verdict :=
  comparison.evalWith context.resolveNumericValidationAtom

/-- Evaluate against resolved field and group state. -/
def NumericComparison.evalSelectedWithGroups
    (comparison : NumericComparison)
    (context : ValidationEvaluationContext) : Verdict :=
  comparison.evalWith context.resolveNumericValidationAtom

/-- Preserve the established field-only entry point. Group-count sources require the explicit resolved-group variant and therefore evaluate as unavailable here. -/
def NumericComparison.evalSelected
    (comparison : NumericComparison) (context : FlatContext) : Verdict :=
  comparison.evalWith context.resolveNumericValidationAtom

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

/-- Evaluate a reached relevance-aware numeric comparison through the one generic arithmetic evaluator. -/
def OrderedNumericComparison.evalSelected
    (comparison : OrderedNumericComparison)
    (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance) : Verdict :=
  comparison.evalWith fun atom => atom.resolve context isRelevant

def CheckedOrderedNumericComparison.evalSelected
    (checked : CheckedOrderedNumericComparison model)
    (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance) : Verdict :=
  checked.core.evalSelected context isRelevant

/-- Full validation supplies universal relevance and the established unavailable group projection. -/
def CheckedOrderedNumericComparison.evalFull
    (checked : CheckedOrderedNumericComparison model)
    (context : FlatContext) (hasContent : Bool) : Verdict :=
  if hasContent then
    checked.evalSelected
      { fields := context, groups := GroupPresenceContext.unavailable }
      (fun _ => true)
  else
    .notFired

/-- Check a surface comparison and evaluate it against one model-indexed prepared String context under full validation. -/
def elaborateAndEvalNumericComparison
    (prepared : PreparedFlatStringContext model compilePattern)
    (locale : String) (rowGroup : GroupPath) (raw : RawFlatContext)
    (hasContent : Bool)
    (surface : SurfaceNumericComparison) :
    Except NumericValidationElabError Verdict := do
  let checked ← elaborateNumericComparison model rowGroup surface
  pure (checked.evalFull (prepared.checkContext locale raw) hasContent)

end A12Kernel
