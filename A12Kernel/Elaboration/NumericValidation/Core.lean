import A12Kernel.Elaboration.NumericAggregate
import A12Kernel.Elaboration.FirstFilledValue
import A12Kernel.Elaboration.StringContext
import A12Kernel.Elaboration.TokenValueCount
import A12Kernel.Elaboration.ValidationContext
import A12Kernel.Semantics.FirstFilledValue
import A12Kernel.Semantics.NumericTolerance

/-! # Checked numeric validation

This capsule connects model-resolved numeric expressions to the existing authored-scale, one-pass lowering, arithmetic-fillability, ordinary-comparison, and fixed-tolerance semantics. Ordinary rules retain exact same-group admission; generated computation validation selects model-wide nonrepeatable admission for scalar sources and model-wide checked-computation admission for sources that retain repeatable certificates. Number fields, numeric `BaseYear`, Base-Year date-component extraction, direct temporal field-component sources, UTF-16 String `Length`, checked ordinary String/Enumeration/category `FieldValueAsNumber`, Date-only month/year differences, exact-instant DateTime hour/minute/second differences, concrete-profile Date/DateTime day differences, and direct Number field-list aggregates share arithmetic. The atom-parameterized comparison carrier lets generated validation retain checked direct/plain-star/filtered-star `FirstFilledValue`, entity-list aggregate, and row-paired `SumOfProducts` sources without adding another arithmetic tree or evaluator; ordinary addressed rules accept that same checked product source through the immutable checked document. Its bounded addressed context is full-validation-only; partial filter/relevance orchestration remains separate, and structural address failures remain outside semantic UNKNOWN. Operation-form rounding, absolute value, and Min/Max operand-list calls compose at ordinary arithmetic operand positions. Every Min/Max list member is a complete numeric operation, while each call independently permits at most one immediate or grouped literal. Rounding and absolute value still reject an immediate literal body. Structured input is assumed to come from a grammar-valid decoder that keeps each literal value coherent with its authored scale; concrete parsing, partially-known Date policy, constructed-Date legacy execution, and that decoder contract remain outside this module.

The numeric and typed String/stored-Enumeration value-count atoms retain their existing checked entity-list sources, static certificates, and per-cell selected-match provenance; scalar validation accepts only their direct subsets, while repeatable evaluation requires the bounded addressed context.
-/

/-! This focused module owns checked numeric-validation syntax, admission, resolution, and elaboration. Runtime evaluation is isolated in `A12Kernel.Elaboration.NumericValidation.Evaluation`. -/

namespace A12Kernel

/-- Model-resolved numeric-validation atoms. Numeric Base Year and component sources remain non-expandable scale-0 atoms rather than becoming authored literals. -/
abbrev NumericValidationAtom := ResolvedNumericAtom FlatNumberField

/-- Numeric source unavailability preserves a reached formal cell cause when one exists while representing unresolved/erroneous group product state without fabricating such a cause. Both project to `Verdict.unknown`; the distinction remains available to Explain and later checked-document consumers. -/
inductive NumericValidationUnavailable where
  | formal (cause : FormalCause)
  | groupState
  | nonRelevant
  deriving Repr, DecidableEq

/-- One exclusive backing input for addressed validation. Generated computation validation retains its established bounded document/read pair; whole-rule validation consumes the immutable model-certified checked document directly. The two forms cannot drift inside one context. -/
inductive AddressedValidationInput (model : FlatModel) where
  | legacy (document : Document) (read : Env → FieldId → CheckedCell)
  | checked (document : CheckedDocument model)

/-- The bounded checked inputs needed when one full-validation numeric leaf retains a repeatable source. Partial validation has distinct filter/relevance orchestration and is intentionally unrepresentable here. This is an addressed leaf context, not a scheduler or result boundary. -/
structure AddressedValidationEvaluationContext (model : FlatModel) where
  scalar : ValidationEvaluationContext
  outer : Env
  input : AddressedValidationInput model

namespace AddressedValidationEvaluationContext

/-- Read one addressed cell without collapsing a checked-document field, environment, or placement failure into semantic malformed input. -/
def readCell (context : AddressedValidationEvaluationContext model)
    (environment : Env) (field : FieldId) :
    Except CheckedAddressingError CheckedCell :=
  match context.input with
  | .legacy _ read => pure (read environment field)
  | .checked document =>
      (document.addressedCell environment field).map (·.cell)

end AddressedValidationEvaluationContext

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

/-- A numeric leaf either delegates one established scalar atom unchanged or retains a model-certified first-filled, aggregate, or row-product source for full addressed validation. -/
inductive OrderedNumericValidationAtom (model : FlatModel) where
  | ordinary (source : NumericValidationAtom)
  | firstFilled (source : CheckedNumberEntitySource model)
  | valueCount (expected : Rat) (source : CheckedNumberEntitySource model)
  | tokenValueCount (source : CheckedTokenValueCountSource model)
  | aggregate (op : NumericAggregateOp)
      (source : CheckedNumberEntitySource model)
  | sumOfProducts (source : CheckedNumericProductAggregate model)

/-- One model-indexed numeric comparison whose atom resolver, rather than the containing leaf, owns relevance timing and addressed-source selection. -/
abbrev OrderedNumericComparison (model : FlatModel) :=
  NumericComparisonOf (OrderedNumericValidationAtom model)

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
  | unsupportedCalendarProfile (zoneId : String)
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

/-- Static field-admission policy for one resolved numeric comparison. Ordinary rules keep their exact rule group; generated computation validation either retains the legacy nonrepeatable scope or carries a model-certified repeatable computation source. -/
inductive NumericOperandScope where
  | sameGroup
  | sameGroupAddressed
  | modelWideNonrepeatable
  | modelWideCheckedComputation
  deriving Repr, DecidableEq

private def FlatModel.admitsNumberInGroup (model : FlatModel) (rowGroup : GroupPath)
    (field : FlatNumberField) : Bool :=
  match model.lookupUniqueId field.id with
  | .ok declaration =>
      declaration.groupPath == rowGroup &&
        declaration.repeatableScope.isEmpty &&
        declaration.toNumberField? == some field
  | .error _ => false

private def FlatModel.admitsAddressedNumber (model : FlatModel)
    (rowGroup : GroupPath) (field : FlatNumberField) : Bool :=
  match model.lookupUniqueId field.id with
  | .ok declaration =>
      declaration.toNumberField? == some field &&
        declaration.repeatableScope.isPrefixOf
          (model.repeatableScopeForGroupPath rowGroup)
  | .error _ => false

private def FlatModel.admitsAddressedTemporal (model : FlatModel)
    (rowGroup : GroupPath) (field : FlatTemporalField) : Bool :=
  match model.lookupUniqueId field.id with
  | .ok declaration =>
      declaration.toTemporalField? == some field &&
        declaration.repeatableScope.isPrefixOf
          (model.repeatableScopeForGroupPath rowGroup)
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

private def FlatModel.admitsAddressedString (model : FlatModel)
    (rowGroup : GroupPath) (field : FlatStringField) : Bool :=
  match model.lookupUniqueId field.id with
  | .ok declaration =>
      declaration.toStringValueField? == some field &&
        declaration.repeatableScope.isPrefixOf
          (model.repeatableScopeForGroupPath rowGroup)
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

private def FlatModel.admitsAddressedFieldValueAsNumber (model : FlatModel)
    (rowGroup : GroupPath) (source : ResolvedFieldValueAsNumberSource) : Bool :=
  match model.certifiedFieldValueAsNumberDeclaration? source with
  | some declaration =>
      declaration.repeatableScope.isPrefixOf
        (model.repeatableScopeForGroupPath rowGroup)
  | none => false

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

private def resolveDateDifferenceOperandWith
    (model : FlatModel)
    (resolveField : SurfaceFieldPath →
      Except NumericValidationElabError FlatTemporalField) :
    SurfaceDateDifferenceOperand →
      Except NumericValidationElabError ResolvedDateDifferenceOperand
  | .field reference => return .field (← resolveField reference)
  | .baseYear source =>
      match model.baseYear with
      | some year => pure (.baseYear year source)
      | none => throw .baseYearNotDeclared

private def numericValidationSummary (atom : NumericValidationAtom) :
    NumericScaleSummary :=
  atom.summary fun source => NumericScaleSummary.field source.info.scale

private def NumericValidationAtom.admitted
    (model : FlatModel) (rowGroup : GroupPath) (scope : NumericOperandScope) :
    NumericValidationAtom → Bool
  | .field source =>
      match scope with
      | .sameGroup => model.admitsNumberInGroup rowGroup source
      | .sameGroupAddressed =>
          model.admitsAddressedNumber rowGroup source
      | .modelWideNonrepeatable | .modelWideCheckedComputation =>
          model.admitsNumberModelWide source
  | .baseYear year => model.baseYear == some year
  | .baseYearDatePart year _ _ => model.baseYear == some year
  | .temporalFieldPart source part =>
      (match scope with
        | .sameGroup => model.admitsTemporalInGroup rowGroup source
        | .sameGroupAddressed =>
            model.admitsAddressedTemporal rowGroup source
        | .modelWideNonrepeatable | .modelWideCheckedComputation =>
            model.admitsTemporalModelWide source) &&
        part.admittedBy source model.hasBaseYear
  | .stringLength source =>
      match scope with
      | .sameGroup => model.admitsStringInGroup rowGroup source
      | .sameGroupAddressed =>
          model.admitsAddressedString rowGroup source
      | .modelWideNonrepeatable | .modelWideCheckedComputation =>
          model.admitsStringModelWide source
  | .stringRange source start finish =>
      validStringRange start finish &&
        match scope with
        | .sameGroup => model.admitsStringInGroup rowGroup source
        | .sameGroupAddressed =>
            model.admitsAddressedString rowGroup source
        | .modelWideNonrepeatable | .modelWideCheckedComputation =>
            model.admitsStringModelWide source
  | .fieldValueAsNumber source =>
      match scope with
      | .sameGroup => model.admitsFieldValueAsNumberInGroup rowGroup source
      | .sameGroupAddressed =>
          model.admitsAddressedFieldValueAsNumber rowGroup source
      | .modelWideNonrepeatable | .modelWideCheckedComputation =>
          model.admitsFieldValueAsNumberSource source
  | .dateDifference unit left right =>
      let admitted : ResolvedDateDifferenceOperand → Bool
        | .field source =>
            source.kind == .date &&
              match scope with
              | .sameGroup => model.admitsTemporalInGroup rowGroup source
              | .sameGroupAddressed =>
                  model.admitsAddressedTemporal rowGroup source
              | .modelWideNonrepeatable | .modelWideCheckedComputation =>
                  model.admitsTemporalModelWide source
        | .baseYear year _ => model.baseYear == some year
      admitted left && admitted right &&
        unit.compatible model.hasBaseYear left.components right.components
  | .dateTimeDifference unit left right =>
      let admitted (source : FlatTemporalField) : Bool :=
        source.kind == .dateTime &&
          unit.admittedBy source.components &&
          match scope with
          | .sameGroup => model.admitsTemporalInGroup rowGroup source
          | .sameGroupAddressed =>
              model.admitsAddressedTemporal rowGroup source
          | .modelWideNonrepeatable | .modelWideCheckedComputation =>
              model.admitsTemporalModelWide source
      admitted left && admitted right &&
        unit.compatible left.components right.components
  | .dayDifference profile left right =>
      let admitted : ResolvedDateDifferenceOperand → Bool
        | .field source =>
            (match scope with
              | .sameGroup => model.admitsTemporalInGroup rowGroup source
              | .sameGroupAddressed =>
                  model.admitsAddressedTemporal rowGroup source
              | .modelWideNonrepeatable | .modelWideCheckedComputation =>
                  model.admitsTemporalModelWide source) &&
              CalendarDayDifference.admittedBy source.kind source.components
        | .baseYear year _ => model.baseYear == some year
      ModelZone.ConcreteProfile.ofId? model.timeZoneId == some profile &&
        admitted left && admitted right &&
        CalendarDayDifference.yearCompatible model.hasBaseYear
          left.components right.components
  | .aggregate _ source =>
      source.hasMultipleFields && source.hasUniqueFields &&
        source.fields.all fun field =>
          match scope with
          | .sameGroup => model.admitsNumberInGroup rowGroup field
          | .sameGroupAddressed => false
          | .modelWideNonrepeatable | .modelWideCheckedComputation =>
              model.admitsNumberModelWide field
  | .filledGroupCount groups =>
      scope != .sameGroupAddressed &&
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
  | .dateTimeDifference _ left right, field =>
      left.id == field || right.id == field
  | .dayDifference _ left right, field =>
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
  | .dateTimeDifference _ left right =>
      isRelevant left.id && isRelevant right.id
  | .dayDifference _ left right =>
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

@[simp]
def addressedNumericValidationFieldIds :
    NumericValidationAtom → List FieldId
  | .field source => [source.id]
  | .temporalFieldPart source _ => [source.id]
  | .stringLength source => [source.id]
  | .stringRange source _ _ => [source.id]
  | .fieldValueAsNumber source => [source.fieldId]
  | .dateDifference _ left right | .dayDifference _ left right =>
      let fieldId : ResolvedDateDifferenceOperand → List FieldId
        | .field source => [source.id]
        | .baseYear _ _ => []
      (fieldId left ++ fieldId right).eraseDups
  | .dateTimeDifference _ left right => [left.id, right.id].eraseDups
  | _ => []

private def checkedNumberEntitySourceAdmittedIn
    (source : CheckedNumberEntitySource model)
    (rowGroup : GroupPath) (scope : NumericOperandScope) : Bool :=
  match scope with
  | .modelWideCheckedComputation => true
  | .sameGroupAddressed => source.directResolvedFields?.isNone
  | .sameGroup | .modelWideNonrepeatable =>
      match source.directResolvedFields? with
      | none => false
      | some direct =>
          direct.hasMultipleFields && direct.hasUniqueFields &&
            direct.fields.all fun field =>
              match scope with
              | .sameGroup => model.admitsNumberInGroup rowGroup field
              | .sameGroupAddressed => false
              | .modelWideNonrepeatable => model.admitsNumberModelWide field
              | .modelWideCheckedComputation => true

private def checkedTokenValueCountAdmittedIn
    (source : CheckedTokenValueCountSource model)
    (rowGroup : GroupPath) (scope : NumericOperandScope) : Bool :=
  match scope with
  | .modelWideCheckedComputation => true
  | .sameGroupAddressed => source.source.directFields?.isNone
  | .sameGroup | .modelWideNonrepeatable =>
      match source.source.directFields? with
      | none => false
      | some direct =>
          direct.all fun field =>
            match scope with
            | .sameGroup => field.declaration.groupPath == rowGroup
            | .sameGroupAddressed => false
            | .modelWideNonrepeatable => true
            | .modelWideCheckedComputation => true

def isDataDependent : OrderedNumericValidationAtom model → Bool
  | .ordinary source => source.isDataDependent
  | .firstFilled _ | .valueCount _ _ | .tokenValueCount _ | .aggregate _ _
  | .sumOfProducts _ => true

def summary : OrderedNumericValidationAtom model → NumericScaleSummary
  | .ordinary source => numericValidationSummary source
  | .firstFilled source => source.scaleSummary
  | .valueCount _ _ => NumericScaleSummary.field 0
  | .tokenValueCount source => source.scaleSummary
  | .aggregate op source => source.aggregateScaleSummary op
  | .sumOfProducts source => source.scaleSummary

/-- An ordinary direct atom needs addressed evaluation exactly when any checked field declaration is repeatable. Specialized sources retain their established addressed criteria. -/
def requiresAddressedValidation : OrderedNumericValidationAtom model → Bool
  | .ordinary source =>
      (addressedNumericValidationFieldIds source).any fun field =>
          match model.lookupUniqueId field with
          | .ok declaration => !declaration.repeatableScope.isEmpty
          | .error _ => false
  | .firstFilled source => source.directResolvedFields?.isNone
  | .valueCount _ source => source.directResolvedFields?.isNone
  | .tokenValueCount source => source.source.directFields?.isNone
  | .aggregate _ _ | .sumOfProducts _ => true

def admitted (atom : OrderedNumericValidationAtom model)
    (rowGroup : GroupPath)
    (scope : NumericOperandScope) : Bool :=
  match atom with
  | .ordinary source => source.admitted model rowGroup scope
  | .firstFilled source =>
      checkedNumberEntitySourceAdmittedIn source rowGroup scope
  | .valueCount _ source =>
      checkedNumberEntitySourceAdmittedIn source rowGroup scope
  | .tokenValueCount source =>
      checkedTokenValueCountAdmittedIn source rowGroup scope
  | .aggregate _ source =>
      (scope == .modelWideCheckedComputation ||
        scope == .sameGroupAddressed) &&
        source.directAggregateFields?.isNone
  | .sumOfProducts _ =>
      scope == .modelWideCheckedComputation ||
        scope == .sameGroupAddressed

def referencesField (atom : OrderedNumericValidationAtom model)
    (field : FieldId) : Bool :=
  match atom with
  | .ordinary source => source.referencesField model field
  | .firstFilled source => source.referencesField field
  | .valueCount _ source => source.referencesField field
  | .tokenValueCount source => source.referencesField field
  | .aggregate _ source => source.referencesField field
  | .sumOfProducts source =>
      source.left.field.id == field || source.right.field.id == field

/-- Whether this exact checked atom retains any filtered entity-list slot. This is static source structure, not a statement about which runtime branch or candidate will be reached. -/
def hasHaving : OrderedNumericValidationAtom model → Bool
  | .firstFilled source | .valueCount _ source | .aggregate _ source =>
      source.hasHaving
  | .tokenValueCount source => source.source.hasHaving
  | .ordinary _ | .sumOfProducts _ => false

end OrderedNumericValidationAtom

/-- Static admission for the relevance-aware numeric leaf reuses the complete authored-operation checks and delegates only atom-specific model coherence. -/
def OrderedNumericComparison.wellFormedInBool
    (comparison : OrderedNumericComparison model)
    (rowGroup : GroupPath)
    (scope : NumericOperandScope) : Bool :=
  (comparison.left.anyAtom OrderedNumericValidationAtom.isDataDependent ||
      comparison.right.anyAtom OrderedNumericValidationAtom.isDataDependent) &&
    comparison.left.isAdmittedResolvedNumericOperation &&
    comparison.right.isAdmittedResolvedNumericOperation &&
    comparison.left.allAtoms (·.admitted rowGroup scope) &&
    comparison.right.allAtoms (·.admitted rowGroup scope) &&
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
    (comparison : OrderedNumericComparison model)
    (field : FieldId) : Bool :=
  comparison.left.anyAtom (·.referencesField field) ||
    comparison.right.anyAtom (·.referencesField field)

/-- Discover `Having` across both complete authored operands without evaluating or lowering away their expression shape. -/
def OrderedNumericComparison.hasHaving
    (comparison : OrderedNumericComparison model) : Bool :=
  comparison.left.anyAtom OrderedNumericValidationAtom.hasHaving ||
    comparison.right.anyAtom OrderedNumericValidationAtom.hasHaving

def OrderedNumericComparison.requiresAddressedValidation
    (comparison : OrderedNumericComparison model) : Bool :=
  comparison.left.anyAtom OrderedNumericValidationAtom.requiresAddressedValidation ||
    comparison.right.anyAtom OrderedNumericValidationAtom.requiresAddressedValidation

structure CheckedOrderedNumericComparison (model : FlatModel) where
  rowGroup : GroupPath
  operandScope : NumericOperandScope := .sameGroup
  core : OrderedNumericComparison model
  modelWellFormed : model.validate.isOk = true
  wellFormed : core.wellFormedInBool rowGroup operandScope = true

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

private def resolveFieldValueAsNumberAtom
    (declaration : FlatFieldDecl) (projectionRef : EnumerationProjectionRef) :
    Except NumericValidationElabError NumericValidationAtom :=
  match declaration.resolveFieldValueAsNumberSource projectionRef with
  | .ok source => pure (.fieldValueAsNumber source)
  | .error .notConvertible =>
      throw (.fieldValueAsNumberNotConvertible declaration.path)
  | .error (.enumeration error) =>
      throw (.fieldValueAsNumberEnumeration declaration.path error)
  | .error .incoherentEnumeration => throw .incoherentCore

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
      resolveFieldValueAsNumberAtom declaration surface.projectionRef
  | .dateDifference unit left right => do
      let resolveOperand := resolveDateDifferenceOperandWith model
        (fun reference =>
          resolveTemporalNumericField model rowGroup reference
            (fun source => source.kind == .date &&
              unit.admittedBy model.hasBaseYear source.components))
      let resolvedLeft ← resolveOperand left
      let resolvedRight ← resolveOperand right
      if unit.compatible model.hasBaseYear
          resolvedLeft.components resolvedRight.components then
        pure (.dateDifference unit resolvedLeft resolvedRight)
      else
        throw .incompatibleDateDifference
  | .dateTimeDifference unit left right => do
      let resolveOperand (reference : SurfaceDateDifferenceOperand) :
          Except NumericValidationElabError FlatTemporalField :=
        match reference with
        | .baseYear _ => throw .incompatibleDateDifference
        | .field path =>
            resolveTemporalNumericField model rowGroup path
              (fun source =>
                source.kind == .dateTime &&
                  unit.admittedBy source.components)
      let resolvedLeft ← resolveOperand left
      let resolvedRight ← resolveOperand right
      if unit.compatible resolvedLeft.components resolvedRight.components then
        pure (.dateTimeDifference unit resolvedLeft resolvedRight)
      else
        throw .incompatibleDateDifference
  | .dayDifference left right => do
      let profile ← match ModelZone.ConcreteProfile.ofId? model.timeZoneId with
        | some profile => pure profile
        | none => throw (.unsupportedCalendarProfile model.timeZoneId)
      let resolveOperand := resolveDateDifferenceOperandWith model
        (fun reference =>
          resolveTemporalNumericField model rowGroup reference
            (fun source =>
              CalendarDayDifference.admittedBy
                source.kind source.components))
      let resolvedLeft ← resolveOperand left
      let resolvedRight ← resolveOperand right
      if CalendarDayDifference.yearCompatible model.hasBaseYear
          resolvedLeft.components resolvedRight.components then
        pure (.dayDifference profile resolvedLeft resolvedRight)
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

private def resolveAddressedNumericDeclaration (model : FlatModel)
    (rowGroup : GroupPath) (reference : SurfaceFieldPath) :
    Except NumericValidationElabError FlatFieldDecl := do
  let declaration ←
    (model.resolveFieldDeclarationUnchecked rowGroup reference).mapError .resolve
  if !declaration.repeatableScope.isPrefixOf
      (model.repeatableScopeForGroupPath rowGroup) then
    throw (.fieldOutsideRowGroup declaration.path rowGroup)
  pure declaration

private def resolveAddressedNumericAtom (model : FlatModel)
    (rowGroup : GroupPath) :
    SurfaceNumericAtom → Except NumericValidationElabError NumericValidationAtom
  | .field reference => do
      let declaration ←
        resolveAddressedNumericDeclaration model rowGroup reference
      match declaration.toNumberField? with
      | some field => pure (.field field)
      | none => throw (.fieldNotNumber declaration.path)
  | .temporalFieldPart reference part => do
      let declaration ←
        resolveAddressedNumericDeclaration model rowGroup reference
      match declaration.toTemporalField? with
      | some field =>
          if part.admittedBy field model.hasBaseYear then
            pure (.temporalFieldPart field part)
          else
            throw (.incompatibleTemporalSource declaration.path)
      | none => throw (.incompatibleTemporalSource declaration.path)
  | .stringLength reference => do
      let declaration ←
        resolveAddressedNumericDeclaration model rowGroup reference
      match declaration.toStringValueField? with
      | some field => pure (.stringLength field)
      | none => throw (.lengthOperandNotEvaluatedString declaration.path)
  | .stringRange reference start finish => do
      let declaration ←
        resolveAddressedNumericDeclaration model rowGroup reference
      if !validStringRange start finish then
        throw (.invalidStringRange start finish)
      match declaration.toStringValueField? with
      | some field => pure (.stringRange field start finish)
      | none => throw (.rangeOperandNotString declaration.path)
  | .fieldValueAsNumber surface => do
      let declaration ←
        resolveAddressedNumericDeclaration model rowGroup surface.reference
      resolveFieldValueAsNumberAtom declaration surface.projectionRef
  | .dateDifference unit left right => do
      let resolveOperand := resolveDateDifferenceOperandWith model
        (fun reference => do
          let declaration ←
            resolveAddressedNumericDeclaration model rowGroup reference
          match declaration.toTemporalField? with
          | some field =>
              if field.kind == .date &&
                  unit.admittedBy model.hasBaseYear field.components then
                pure field
              else
                throw (.incompatibleTemporalSource declaration.path)
          | none => throw (.incompatibleTemporalSource declaration.path))
      let resolvedLeft ← resolveOperand left
      let resolvedRight ← resolveOperand right
      if unit.compatible model.hasBaseYear
          resolvedLeft.components resolvedRight.components then
        pure (.dateDifference unit resolvedLeft resolvedRight)
      else
        throw .incompatibleDateDifference
  | .dateTimeDifference unit left right => do
      let resolveOperand (operand : SurfaceDateDifferenceOperand) :
          Except NumericValidationElabError FlatTemporalField :=
        match operand with
        | .baseYear _ => throw .incompatibleDateDifference
        | .field reference => do
            let declaration ←
              resolveAddressedNumericDeclaration model rowGroup reference
            match declaration.toTemporalField? with
            | some field =>
                if field.kind == .dateTime &&
                    unit.admittedBy field.components then
                  pure field
                else
                  throw (.incompatibleTemporalSource declaration.path)
            | none => throw (.incompatibleTemporalSource declaration.path)
      let resolvedLeft ← resolveOperand left
      let resolvedRight ← resolveOperand right
      if unit.compatible resolvedLeft.components resolvedRight.components then
        pure (.dateTimeDifference unit resolvedLeft resolvedRight)
      else
        throw .incompatibleDateDifference
  | .dayDifference left right => do
      let profile ← match ModelZone.ConcreteProfile.ofId? model.timeZoneId with
        | some profile => pure profile
        | none => throw (.unsupportedCalendarProfile model.timeZoneId)
      let resolveOperand := resolveDateDifferenceOperandWith model
        (fun reference => do
          let declaration ←
            resolveAddressedNumericDeclaration model rowGroup reference
          match declaration.toTemporalField? with
          | some field =>
              if CalendarDayDifference.admittedBy
                  field.kind field.components then
                pure field
              else
                throw (.incompatibleTemporalSource declaration.path)
          | none => throw (.incompatibleTemporalSource declaration.path))
      let resolvedLeft ← resolveOperand left
      let resolvedRight ← resolveOperand right
      if CalendarDayDifference.yearCompatible model.hasBaseYear
          resolvedLeft.components resolvedRight.components then
        pure (.dayDifference profile resolvedLeft resolvedRight)
      else
        throw .incompatibleDateDifference
  | source => resolveNumericAtom model rowGroup source

private def elaborateNumericComparisonWith
    (model : FlatModel) (rowGroup : GroupPath)
    (scope : NumericOperandScope)
    (resolveAtom : SurfaceNumericAtom →
      Except NumericValidationElabError NumericValidationAtom)
    (surface : SurfaceNumericComparison) :
    Except NumericValidationElabError (CheckedNumericComparison model) := do
  match hModel : model.validate with
  | .error error => throw (.resolve error)
  | .ok () =>
      if !GroupPath.isValid rowGroup then
        throw (.resolve (.invalidRuleGroup rowGroup))
      let left ← surface.left.mapM resolveAtom
      let right ← surface.right.mapM resolveAtom
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
      if hCore : core.wellFormedInBool model rowGroup scope = true then
        pure {
          rowGroup
          operandScope := scope
          core
          modelWellFormed := by
            rw [hModel]
            rfl
          wellFormed := hCore
        }
      else
        throw .incoherentCore

/-- Resolve and check both nonrepeatable operands before performing their one-pass lowering at evaluation time. -/
def elaborateNumericComparison (model : FlatModel) (rowGroup : GroupPath)
    (surface : SurfaceNumericComparison) :
    Except NumericValidationElabError (CheckedNumericComparison model) :=
  elaborateNumericComparisonWith model rowGroup .sameGroup
    (resolveNumericAtom model rowGroup) surface

/-- Admit ordinary addressed field operands through the existing ordered-numeric carrier. Each atom retains its typed declaration certificates while only repeatable reads change from scalar to addressed. -/
def elaborateRepeatableNumericComparison
    (model : FlatModel) (rowGroup : GroupPath)
    (surface : SurfaceNumericComparison) :
    Except NumericValidationElabError
      (CheckedOrderedNumericComparison model) := do
  let checked ← elaborateNumericComparisonWith model rowGroup
    .sameGroupAddressed (resolveAddressedNumericAtom model rowGroup) surface
  let core : OrderedNumericComparison model := {
    op := checked.core.op
    left := checked.core.left.map .ordinary
    right := checked.core.right.map .ordinary
    suppressExactScaleWarning := checked.core.suppressExactScaleWarning }
  if !core.requiresAddressedValidation then
    throw .unsupportedExpression
  if hCore : core.wellFormedInBool rowGroup .sameGroupAddressed = true then
    pure {
      rowGroup
      operandScope := .sameGroupAddressed
      core
      modelWellFormed := checked.modelWellFormed
      wellFormed := hCore }
  else
    throw .incoherentCore

end A12Kernel
