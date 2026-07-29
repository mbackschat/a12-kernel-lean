import A12Kernel.Elaboration.NumericAggregate
import A12Kernel.Elaboration.FirstFilledValue
import A12Kernel.Elaboration.StringContext
import A12Kernel.Elaboration.TokenValueCount
import A12Kernel.Elaboration.ValidationContext
import A12Kernel.Semantics.FirstFilledValue
import A12Kernel.Semantics.NumericTolerance

/-! # Checked numeric validation

This capsule connects model-resolved numeric expressions to the existing authored-scale, one-pass lowering, arithmetic-fillability, ordinary-comparison, and fixed-tolerance semantics. Ordinary rules retain exact same-group admission; generated computation validation selects model-wide nonrepeatable admission for scalar sources and model-wide checked-computation admission for sources that retain repeatable certificates. Number fields, numeric `BaseYear`, Base-Year date-component extraction, direct temporal field-component sources, UTF-16 String `Length`, checked ordinary String/Enumeration/category `FieldValueAsNumber`, Date-only month/year differences, exact-instant DateTime field/`Now` hour/minute/second differences, concrete-profile Date/DateTime day differences, and direct Number field-list aggregates share arithmetic. Dynamic `Now` is read only from the explicit evaluation `World`; checking retains the dependency without sampling it. The atom-parameterized comparison carrier lets generated validation retain checked direct/plain-star/filtered-star `FirstFilledValue`, entity-list aggregate, and row-paired `SumOfProducts` sources without adding another arithmetic tree or evaluator; ordinary addressed rules accept that same checked product source through the immutable checked document. Its bounded addressed context is full-validation-only; partial filter/relevance orchestration remains separate, and structural address failures remain outside semantic UNKNOWN. Operation-form rounding, absolute value, and Min/Max operand-list calls compose at ordinary arithmetic operand positions. Every Min/Max list member is a complete numeric operation, while each call independently permits at most one immediate or grouped literal. Rounding and absolute value still reject an immediate literal body. Structured input is assumed to come from a grammar-valid decoder that keeps each literal value coherent with its authored scale; concrete parsing, partially-known Date policy, constructed-Date legacy execution, and that decoder contract remain outside this module.

The numeric, typed String/stored-Enumeration, and direct Boolean/Confirm value-count atoms retain their checked sources, distinct static family certificates, and per-cell provenance; scalar validation accepts only direct subsets, while repeatable evaluation requires the bounded addressed context.
-/

/-! This focused module owns checked numeric-validation syntax and admission. Surface resolution and checked-carrier construction live in `A12Kernel.Elaboration.NumericValidation.Resolution`; runtime evaluation is isolated in `A12Kernel.Elaboration.NumericValidation.Evaluation`. -/

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

/-- One resolved numeric operation before a comparison or another checked consumer projects its arithmetic outcome. -/
abbrev NumericValidationExpression :=
  AuthoredNumericExpr NumericValidationAtom

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

/-- Whether one checked Number field is the model-owned nonrepeatable declaration in an exact ordinary validation group. -/
def FlatModel.admitsNumberInGroup (model : FlatModel) (rowGroup : GroupPath)
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

/-- Whether one checked Number field is a model-owned nonrepeatable declaration independent of an ordinary rule group. -/
def FlatModel.admitsNumberModelWide (model : FlatModel)
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

/-- Static numeric-scale summary shared by admission and checked surface resolution. -/
def numericValidationSummary (atom : NumericValidationAtom) :
    NumericScaleSummary :=
  atom.summary fun source => NumericScaleSummary.field source.info.scale

/-- Static admission for one scalar numeric-validation atom under the selected ordinary, addressed, or generated-computation scope. -/
def NumericValidationAtom.admitted
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
      let admitted : FlatTemporalOperand → Bool
        | .fieldValue source =>
            source.kind == .dateTime &&
              unit.admittedBy source.components &&
              match scope with
              | .sameGroup => model.admitsTemporalInGroup rowGroup source
              | .sameGroupAddressed =>
                  model.admitsAddressedTemporal rowGroup source
              | .modelWideNonrepeatable | .modelWideCheckedComputation =>
                  model.admitsTemporalModelWide source
        | .nowValue => unit.admittedBy TemporalComponents.now
        | _ => false
      match left.dateTimeDifferenceComponents?,
          right.dateTimeDifferenceComponents? with
      | some leftComponents, some rightComponents =>
          admitted left && admitted right &&
            unit.compatible leftComponents rightComponents
      | _, _ => false
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

/-- Check one standalone numeric operation without importing comparison-only data-dependency or cross-side scale rules. -/
def NumericValidationExpression.wellFormedInBool
    (expression : NumericValidationExpression)
    (model : FlatModel) (rowGroup : GroupPath)
    (scope : NumericOperandScope) : Bool :=
  expression.isAdmittedResolvedNumericOperation &&
    expression.allAtoms (NumericValidationAtom.admitted model rowGroup scope) &&
    expression.numericOperationAuthoringCheck == .accepted &&
    (expression.summary? numericValidationSummary).isSome

/-- A model-coherent standalone numeric operation whose existing arithmetic outcome can be consumed without fabricating a comparison. -/
structure CheckedNumericValidationExpression (model : FlatModel) where
  rowGroup : GroupPath
  operandScope : NumericOperandScope := .sameGroup
  core : NumericValidationExpression
  modelWellFormed : model.validate.isOk = true
  wellFormed :
    NumericValidationExpression.wellFormedInBool
      core model rowGroup operandScope = true

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
      left.dateTimeDifferenceReferences field ||
        right.dateTimeDifferenceReferences field
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
      left.fields.all (isRelevant ∘ FlatField.id) &&
        right.fields.all (isRelevant ∘ FlatField.id)
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

end A12Kernel
