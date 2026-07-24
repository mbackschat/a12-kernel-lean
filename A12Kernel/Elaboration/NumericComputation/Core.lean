import A12Kernel.Elaboration.FirstFilledValue
import A12Kernel.Elaboration.NumericAggregate
import A12Kernel.Elaboration.TokenValueCount
import A12Kernel.Semantics.ComputationCondition
import A12Kernel.Semantics.NumericTarget

/-! # Numeric computation-expression outcomes

This capsule checks one parser-independent numeric operation with an ordinary nonrepeatable Number target against a validated model and then evaluates the resolved expression. Admission resolves scalar Number-field, numeric-`BaseYear`, Base-Year date-component, direct temporal field-component, UTF-16 String `Length`, checked ordinary String/Enumeration/category `FieldValueAsNumber`, Date-only month/year differences, exact-instant DateTime hour/minute/second differences, concrete-profile Date/DateTime day differences, checked direct/plain-star/filtered-star Number entity-list aggregates and `FirstFilledValue`, typed String/stored-Enumeration value count, and the distinct row-aligned `SumOfProducts` pair through one shared numeric tree. The direct aggregate surface maps into the checked entity-list payload, while the complete surface retains each specialized checked source and the product pair's proof-bearing common-row plan. Target self-reference traversal reaches selected entity-list fields, every `Having` reference, and both product fields; scale checking uses the selected declarations' union, integral count result, or product of pair scales. Each operand-list Min/Max call independently enforces its immediate-constant budget without flattening nested calls. A rounding or absolute-value node rejects an immediate numeric literal body; numeric `BaseYear` remains a distinct admitted source. The primary checked target entry points construct the complete policy from the validated target declaration and attach it once, so evaluation cannot substitute caller-selected constraints; the lower-level attachment remains an explicit compatibility seam for already-resolved policies and still rejects scale/signedness drift. The one explicit scale-warning suppression bypasses only the result-scale gate and selects the existing warning-suppressed target branch after evaluation. Scalar computation evaluation remains available for direct-only sources and rejects repeatable atoms explicitly. Addressed computation evaluation accepts the document, outer environment, and checked readers required by the existing entity-list and product traversals, maps structural addressing failure into the computation-fault domain, and otherwise preserves ordinary values, arithmetic domain failure, inherited computation-read poison, and the fail-closed legacy-calendar boundary. Generated validation narrows direct ordinary aggregates back into its existing nonrepeatable atom and retains repeatable entity-list, token-count, product, and first-filled payloads through the full-only addressed validation context; its scalar checked entry point rejects such a rule with an explicit context requirement. Concrete parsing, partially-known Date policy, constructed-Date legacy execution, application, delta projection, wider whole-rule repeatable generated validation, and scheduling remain outside this module.

Numeric `NumberOfValueInFields` remains a distinct checked atom over the same entity-list source so its per-cell filter-match provenance survives arithmetic, target evaluation, and generated validation without a second expression tree or aggregate fold.
-/

namespace A12Kernel

abbrev NumericComputationAtom := ResolvedNumericAtom FlatFieldDecl

/-- The complete computation surface keeps ordinary numeric atoms in their shared representation and adds distinct prefix-selecting and row-aligned aggregate atoms without creating another arithmetic tree. -/
inductive SurfaceNumericComputationAtom where
  | numeric (source : SurfaceNumericAtom SurfaceNumberEntitySource)
  | firstFilled (source : SurfaceNumberEntitySource)
  | valueCount (expected : Rat) (source : SurfaceNumberEntitySource)
  | tokenValueCount (expected : String) (source : SurfaceTokenValueCountSource)
  | sumOfProducts (source : SurfaceNumericProductAggregate)
  deriving Repr, DecidableEq

/-- One checked numeric computation atom. Ordinary scalar/entity-list sources retain the shared resolved atom, `FirstFilledValue` and value count retain their distinct scans over that same entity-list source, and `SumOfProducts` retains its proof-bearing common-row plan. -/
inductive CheckedNumericComputationAtom (model : FlatModel) where
  | numeric
      (source : ResolvedNumericAtom FlatFieldDecl
        (CheckedNumberEntitySource model))
  | firstFilled (source : CheckedNumberEntitySource model)
  | valueCount (expected : Rat) (source : CheckedNumberEntitySource model)
  | tokenValueCount (source : CheckedTokenValueCountSource model)
  | sumOfProducts (source : CheckedNumericProductAggregate model)

/-- Fail-closed faults outside the admitted numeric computation-expression fragment. -/
inductive NumericComputationFault where
  | fieldKindMismatch (field : FieldId)
  | unsupportedDateCalendar
  | unsupportedGroupCount
  | repeatableContextRequired
  | repeatableAddressing (error : StarAddressingError)
  deriving Repr, DecidableEq

/-- The bounded runtime inputs needed when one checked numeric expression contains repeatable entity-list atoms. This is an expression evaluator context, not a document scheduler or dependency overlay. -/
structure NumericComputationEvaluationContext where
  scalar : ScalarComputationContext
  document : Document
  outer : Env
  filterRead : Env → FieldId → CheckedCell
  starRead : Env → FieldId → CheckedCell

inductive NumericComputationElabError where
  | resolve (error : ResolveError)
  | targetNotNumber (field : FieldId)
  | operandNotNumber (path : List String)
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
  | aggregate (error : NumberEntityElabError)
  | tokenValueCount (error : TokenValueCountElabError)
  | productAggregate (error : NumericProductAggregateElabError)
  | targetSelfReference (field : FieldId)
  | authoring (result : NumericAuthoringCheck)
  | unsupportedExpression
  | operationScaleMismatch (targetScale : Nat) (operation : NumericScaleSummary)
  | targetPolicyMismatch (target policy : NumField)
  | incoherentCore
  deriving Repr, DecidableEq

/-- One resolved numeric operation before target storage, retaining whether its result-scale warning was explicitly suppressed. -/
structure NumericComputationOperation (model : FlatModel) where
  target : FlatNumberField
  expression : AuthoredNumericExpr (CheckedNumericComputationAtom model)
  suppressExactScaleWarning : Bool := false

private def FlatModel.admitsTemporalComputationOperand
    (model : FlatModel) (source : FlatTemporalField) (accepts : Bool) : Bool :=
  match model.lookupUniqueId source.id with
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.toTemporalField? == some source && accepts
  | .error _ => false

def FlatModel.admitsNumericComputationOperand
    (model : FlatModel) : CheckedNumericComputationAtom model → Bool
  | .firstFilled _ => true
  | .valueCount _ _ => true
  | .tokenValueCount _ => true
  | .sumOfProducts _ => true
  | .numeric (.field declaration) =>
      match model.lookupUniqueId declaration.id with
      | .ok admitted =>
          admitted == declaration &&
            declaration.repeatableScope.isEmpty &&
            declaration.toNumberField?.isSome
      | .error _ => false
  | .numeric (.baseYear year) => model.baseYear == some year
  | .numeric (.baseYearDatePart year _ _) => model.baseYear == some year
  | .numeric (.temporalFieldPart source part) =>
      model.admitsTemporalComputationOperand source
        (part.admittedBy source model.hasBaseYear)
  | .numeric (.stringLength source) => model.admitsStringValueField source
  | .numeric (.stringRange source start finish) =>
      validStringRange start finish && model.admitsStringValueField source
  | .numeric (.fieldValueAsNumber source) =>
      model.admitsFieldValueAsNumberSource source
  | .numeric (.dateDifference unit left right) =>
      let admitted : ResolvedDateDifferenceOperand → Bool
        | .field source =>
            source.kind == .date &&
              model.admitsTemporalComputationOperand source
                (unit.admittedBy model.hasBaseYear source.components)
        | .baseYear year _ => model.baseYear == some year
      admitted left && admitted right &&
        unit.compatible model.hasBaseYear left.components right.components
  | .numeric (.dateTimeDifference unit left right) =>
      let admitted (source : FlatTemporalField) : Bool :=
        source.kind == .dateTime &&
          model.admitsTemporalComputationOperand source
            (unit.admittedBy source.components)
      admitted left && admitted right &&
        unit.compatible left.components right.components
  | .numeric (.dayDifference profile left right) =>
      let admitted : ResolvedDateDifferenceOperand → Bool
        | .field source =>
            model.admitsTemporalComputationOperand source
              (CalendarDayDifference.admittedBy
                source.kind source.components)
        | .baseYear year _ => model.baseYear == some year
      ModelZone.ConcreteProfile.ofId? model.timeZoneId == some profile &&
        admitted left && admitted right &&
        CalendarDayDifference.yearCompatible model.hasBaseYear
          left.components right.components
  | .numeric (.aggregate _ _) => true
  | .numeric (.filledGroupCount _) => false

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

def CheckedNumericComputationAtom.numericScaleSummary
    (atom : CheckedNumericComputationAtom model) : NumericScaleSummary :=
  match atom with
  | .numeric source =>
      source.summaryWith FlatFieldDecl.numericScaleSummary
        CheckedNumberEntitySource.aggregateScaleSummary
  | .firstFilled source => source.scaleSummary
  | .valueCount _ _ => NumericScaleSummary.field 0
  | .tokenValueCount source => source.scaleSummary
  | .sumOfProducts source => source.scaleSummary

def CheckedNumericComputationAtom.references
    (model : FlatModel) (field : FieldId) :
    CheckedNumericComputationAtom model → Bool
  | .firstFilled source => source.referencesField field
  | .valueCount _ source => source.referencesField field
  | .tokenValueCount source => source.referencesField field
  | .sumOfProducts source =>
      source.left.field.id == field || source.right.field.id == field
  | .numeric (.field declaration) => declaration.id == field
  | .numeric (.baseYear _) => false
  | .numeric (.baseYearDatePart _ _ _) => false
  | .numeric (.temporalFieldPart source _) => source.id == field
  | .numeric (.stringLength source) => source.id == field
  | .numeric (.stringRange source _ _) => source.id == field
  | .numeric (.fieldValueAsNumber source) => source.fieldId == field
  | .numeric (.dateDifference _ left right) =>
      left.references field || right.references field
  | .numeric (.dateTimeDifference _ left right) =>
      left.id == field || right.id == field
  | .numeric (.dayDifference _ left right) =>
      left.references field || right.references field
  | .numeric (.aggregate _ source) => source.referencesField field
  | .numeric (.filledGroupCount groups) =>
      groups.any fun group => group.referencesField model field

def NumericComputationOperation.wellFormedBool
    (operation : NumericComputationOperation model) : Bool :=
  model.admitsNumericComputationTarget operation.target &&
    operation.expression.allAtoms model.admitsNumericComputationOperand &&
    !operation.expression.anyAtom
      (CheckedNumericComputationAtom.references model operation.target.id) &&
    operation.expression.isAdmittedResolvedNumericOperation &&
    operation.expression.numericOperationAuthoringCheck == .accepted &&
    match operation.expression.summary?
        CheckedNumericComputationAtom.numericScaleSummary with
    | some summary =>
        exactNumericScaleComparisonAllowedWithSuppression
          operation.suppressExactScaleWarning
          (NumericScaleSummary.field operation.target.info.scale) summary
    | none => false

def NumericComputationOperation.WellFormed
    (operation : NumericComputationOperation model) : Prop :=
  operation.wellFormedBool = true

/-- A model-coherent operation produced only after target, operands, authoring shape, self-reference, and result scale have been checked. -/
structure CheckedNumericComputationOperation (model : FlatModel) where
  core : NumericComputationOperation model
  modelWellFormed : model.validate.isOk = true
  wellFormed : core.WellFormed

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

def SurfaceNumericAggregateFields.toNumberEntitySource
    (source : SurfaceNumericAggregateFields) : SurfaceNumberEntitySource :=
  { first := .field source.first
    rest := source.rest.map SurfaceFieldEntityOperand.field }

def SurfaceNumericAtom.toNumberEntityComputationAtom :
    SurfaceNumericAtom →
      SurfaceNumericAtom SurfaceNumberEntitySource
  | .field path => .field path
  | .baseYear => .baseYear
  | .baseYearDatePart source part => .baseYearDatePart source part
  | .temporalFieldPart path part => .temporalFieldPart path part
  | .stringLength path => .stringLength path
  | .stringRange path start finish => .stringRange path start finish
  | .fieldValueAsNumber source => .fieldValueAsNumber source
  | .dateDifference unit left right => .dateDifference unit left right
  | .dateTimeDifference unit left right =>
      .dateTimeDifference unit left right
  | .dayDifference left right => .dayDifference left right
  | .aggregate op source => .aggregate op source.toNumberEntitySource
  | .filledGroupCount groups => .filledGroupCount groups

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
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom) :
    Except NumericComputationElabError
      (AuthoredNumericExpr (CheckedNumericComputationAtom model)) :=
  expression.mapM fun
    | .firstFilled source => do
        let checked ←
          (elaborateNumberEntitySource model declaringGroup source).mapError
            NumericComputationElabError.aggregate
        if checked.referencesField target then
          throw (.targetSelfReference target)
        pure (.firstFilled checked)
    | .valueCount expected source => do
        let checked ←
          (elaborateNumberEntitySource model declaringGroup source).mapError
            NumericComputationElabError.aggregate
        if checked.referencesField target then
          throw (.targetSelfReference target)
        pure (.valueCount expected checked)
    | .tokenValueCount expected source => do
        let checked ←
          (elaborateTokenValueCountSource model declaringGroup expected source).mapError
            NumericComputationElabError.tokenValueCount
        if checked.referencesField target then
          throw (.targetSelfReference target)
        pure (.tokenValueCount checked)
    | .sumOfProducts source => do
        let checked ←
          (elaborateNumericProductAggregate model declaringGroup source).mapError
            NumericComputationElabError.productAggregate
        if checked.left.field.id == target ||
            checked.right.field.id == target then
          throw (.targetSelfReference target)
        pure (.sumOfProducts checked)
    | .numeric (.field reference) => do
        let declaration ←
          (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
        if declaration.id == target then
          throw (.targetSelfReference target)
        else if declaration.toNumberField?.isSome then
          pure (.numeric (.field declaration))
        else
          throw (.operandNotNumber declaration.path)
    | .numeric .baseYear =>
        match model.baseYear with
        | some year => pure (.numeric (.baseYear year))
        | none => throw .baseYearNotDeclared
    | .numeric (.baseYearDatePart source part) =>
        match model.baseYear with
        | some year => pure (.numeric (.baseYearDatePart year source part))
        | none => throw .baseYearNotDeclared
    | .numeric (.temporalFieldPart reference part) => do
        let field ← model.resolveTemporalNumericComputationField
          declaringGroup target reference
          (fun source => part.admittedBy source model.hasBaseYear)
        pure (.numeric (.temporalFieldPart field part))
    | .numeric (.stringLength reference) => do
        let declaration ←
          (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
        if declaration.id == target then
          throw (.targetSelfReference target)
        match declaration.toStringValueField? with
        | some field => pure (.numeric (.stringLength field))
        | none => throw (.lengthOperandNotEvaluatedString declaration.path)
    | .numeric (.stringRange reference start finish) => do
        let declaration ←
          (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError .resolve
        if !validStringRange start finish then
          throw (.invalidStringRange start finish)
        match declaration.toStringValueField? with
        | none => throw (.rangeOperandNotString declaration.path)
        | some field =>
            if declaration.id == target then
              throw (.targetSelfReference target)
            pure (.numeric (.stringRange field start finish))
    | .numeric (.fieldValueAsNumber surface) => do
        let declaration ←
          (model.resolveNonrepeatableFieldUnchecked
            declaringGroup surface.reference).mapError .resolve
        if declaration.id == target then
          throw (.targetSelfReference target)
        match declaration.resolveFieldValueAsNumberSource surface.projectionRef with
        | .ok source => pure (.numeric (.fieldValueAsNumber source))
        | .error .notConvertible =>
            throw (.fieldValueAsNumberNotConvertible declaration.path)
        | .error (.enumeration error) =>
            throw (.fieldValueAsNumberEnumeration declaration.path error)
        | .error .incoherentEnumeration => throw .incoherentCore
    | .numeric (.dateDifference unit left right) => do
        let resolveOperand : SurfaceDateDifferenceOperand →
            Except NumericComputationElabError ResolvedDateDifferenceOperand
          | .field reference => do
              let field ← model.resolveTemporalNumericComputationField
                declaringGroup target reference
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
          pure (.numeric (.dateDifference unit resolvedLeft resolvedRight))
        else
          throw .incompatibleDateDifference
    | .numeric (.dateTimeDifference unit left right) => do
        let resolveOperand : SurfaceDateDifferenceOperand →
            Except NumericComputationElabError FlatTemporalField
          | .baseYear _ => throw .incompatibleDateDifference
          | .field reference =>
              model.resolveTemporalNumericComputationField
                declaringGroup target reference
                (fun source =>
                  source.kind == .dateTime &&
                    unit.admittedBy source.components)
        let resolvedLeft ← resolveOperand left
        let resolvedRight ← resolveOperand right
        if unit.compatible resolvedLeft.components resolvedRight.components then
          pure (.numeric
            (.dateTimeDifference unit resolvedLeft resolvedRight))
        else
          throw .incompatibleDateDifference
    | .numeric (.dayDifference left right) => do
        let profile ← match ModelZone.ConcreteProfile.ofId? model.timeZoneId with
          | some profile => pure profile
          | none => throw (.unsupportedCalendarProfile model.timeZoneId)
        let resolveOperand : SurfaceDateDifferenceOperand →
            Except NumericComputationElabError ResolvedDateDifferenceOperand
          | .field reference => do
              let field ← model.resolveTemporalNumericComputationField
                declaringGroup target reference
                (fun source =>
                  CalendarDayDifference.admittedBy
                    source.kind source.components)
              pure (.field field)
          | .baseYear source =>
              match model.baseYear with
              | some year => pure (.baseYear year source)
              | none => throw .baseYearNotDeclared
        let resolvedLeft ← resolveOperand left
        let resolvedRight ← resolveOperand right
        if CalendarDayDifference.yearCompatible model.hasBaseYear
            resolvedLeft.components resolvedRight.components then
          pure (.numeric
            (.dayDifference profile resolvedLeft resolvedRight))
        else
          throw .incompatibleDateDifference
    | .numeric (.aggregate op source) => do
        let checked ←
          (elaborateNumberEntitySource model declaringGroup source).mapError
            NumericComputationElabError.aggregate
        if checked.referencesField target then
          throw (.targetSelfReference target)
        pure (.numeric (.aggregate op checked))
    | .numeric (.filledGroupCount _) => throw .unsupportedExpression

/-- Resolve and check the complete numeric computation surface, including checked entity-list atoms and the distinct row-aligned `SumOfProducts` source, through the one shared numeric expression tree. -/
def elaborateCompleteNumericComputationOperation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom)
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
          CheckedNumericComputationAtom.numericScaleSummary with
        | some summary => pure summary
        | none => throw .unsupportedExpression
      if !exactNumericScaleComparisonAllowedWithSuppression
          suppressExactScaleWarning
          (NumericScaleSummary.field target.info.scale) summary then
        throw (.operationScaleMismatch target.info.scale summary)
      let core : NumericComputationOperation model := {
        target
        expression := resolved
        suppressExactScaleWarning }
      if hCore : core.wellFormedBool = true then
        pure {
          core
          modelWellFormed := by
            rw [hModel]
            rfl
          wellFormed := hCore }
      else
        throw .incoherentCore

/-- Compatibility surface for direct/plain-star/filtered-star entity-list sources. -/
def elaborateNumberEntityComputationOperation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (expression :
      AuthoredNumericExpr (SurfaceNumericAtom SurfaceNumberEntitySource))
    (suppressExactScaleWarning : Bool := false) :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation model) :=
  elaborateCompleteNumericComputationOperation model declaringGroup targetField
    (expression.map SurfaceNumericComputationAtom.numeric)
    suppressExactScaleWarning

/-- Backwards-compatible direct-field aggregate surface. It maps its aggregate payload into the sole checked entity-list representation before using the complete computation elaborator. -/
def elaborateNumericComputationOperation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (suppressExactScaleWarning : Bool := false) :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation model) :=
  elaborateNumberEntityComputationOperation model declaringGroup targetField
    (expression.map SurfaceNumericAtom.toNumberEntityComputationAtom)
    suppressExactScaleWarning

end A12Kernel
