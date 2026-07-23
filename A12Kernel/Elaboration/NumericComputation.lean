import A12Kernel.Elaboration.NumericAggregate
import A12Kernel.Semantics.ComputationCondition
import A12Kernel.Semantics.NumericTarget

/-! # Numeric computation-expression outcomes

This capsule checks one parser-independent numeric operation with an ordinary nonrepeatable Number target against a validated model and then evaluates the resolved expression. Admission resolves scalar Number-field, numeric-`BaseYear`, Base-Year date-component, direct temporal field-component, UTF-16 String `Length`, checked ordinary String/Enumeration/category `FieldValueAsNumber`, Date-only month/year-difference, checked direct/plain-star/filtered-star Number entity-list aggregates, and the distinct row-aligned `SumOfProducts` pair through one shared numeric tree. The direct aggregate surface maps into the checked entity-list payload, while the complete surface retains the product pair's proof-bearing common-row plan. Target self-reference traversal reaches selected aggregate fields, every `Having` reference, and both product fields; scale checking uses the aggregate declarations' union, integral distinct-count result, or product of pair scales. Each operand-list Min/Max call independently enforces its immediate-constant budget without flattening nested calls. A rounding or absolute-value node rejects an immediate numeric literal body; numeric `BaseYear` remains a distinct admitted source. The complete externally resolved target policy attaches once to that checked operation after its scale and signedness have been matched, so evaluation cannot substitute another policy. The one explicit scale-warning suppression bypasses only the result-scale gate and selects the existing warning-suppressed target branch after evaluation. Scalar evaluation remains available for direct-only sources and rejects repeatable atoms explicitly. Addressed evaluation accepts the document, outer environment, and checked readers required by the existing entity-list and product traversals, maps structural addressing failure into the computation-fault domain, and otherwise preserves ordinary values, arithmetic domain failure, inherited computation-read poison, and the fail-closed legacy-calendar boundary. Generated validation narrows direct aggregate payloads back into its existing nonrepeatable atom and rejects repeatable entity-list and product payloads until an addressed validation context exists. Concrete parsing, partially-known Date policy, constructed-Date legacy execution, target-policy construction from declarations, application, delta projection, whole-rule repeatable generated validation, and scheduling remain outside this module.
-/

namespace A12Kernel

abbrev NumericComputationAtom := ResolvedNumericAtom FlatFieldDecl

/-- The complete computation surface keeps ordinary numeric atoms in their shared representation and adds the row-aligned product aggregate without creating another arithmetic tree. -/
inductive SurfaceNumericComputationAtom where
  | numeric (source : SurfaceNumericAtom SurfaceNumberEntitySource)
  | sumOfProducts (source : SurfaceNumericProductAggregate)
  deriving Repr, DecidableEq

/-- One checked numeric computation atom. Ordinary scalar/entity-list sources retain the shared resolved atom; `SumOfProducts` retains its distinct proof-bearing common-row plan. -/
inductive CheckedNumericComputationAtom (model : FlatModel) where
  | numeric
      (source : ResolvedNumericAtom FlatFieldDecl
        (CheckedNumberEntitySource model))
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
  | baseYearNotDeclared
  | aggregate (error : NumberEntityElabError)
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
  | .sumOfProducts source => source.scaleSummary

def CheckedNumericComputationAtom.references
    (model : FlatModel) (field : FieldId) :
    CheckedNumericComputationAtom model → Bool
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

def NumericOperand.toComputationResult : NumericOperand → NumericComputationResult
  | .value amount _ => .value amount
  | .unknown cause => .poison cause

namespace CheckedNumericProductAggregate

/-- Project the checked paired-row fold through computation-phase reads. Required-only emptiness remains numeric zero; every other reached formal invalidity becomes poison. -/
def evaluateComputation (checked : CheckedNumericProductAggregate model)
    (document : Document) (outer : Env)
    (read : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericComputationResult := do
  pure ((← checked.evaluateAt .computation document outer read).toComputationResult)

end CheckedNumericProductAggregate

namespace CheckedNumberEntitySource

/-- Project the checked mixed direct/star Number aggregate through computation-phase reads, preserving the first reached filter or target poison and erasing only validation fillability from a successful numeric fold. -/
def evaluateComputation (checked : CheckedNumberEntitySource model)
    (op : NumericAggregateOp) (document : Document) (outer : Env)
    (directRead : FieldId → CheckedCell)
    (filterRead starRead : Env → FieldId → CheckedCell) :
    Except StarAddressingError NumericComputationResult := do
  pure ((← checked.evaluateComputationAggregate op document outer directRead
    filterRead starRead).toComputationResult)

end CheckedNumberEntitySource

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

def readDateDifferenceOperand (context : ScalarComputationContext) :
    ResolvedDateDifferenceOperand → DateDifferenceOperand
  | .field source => DateDifferenceOperand.ofObservation
      (observeCell .computation (context.read source.id))
  | .baseYear year source => .value (source.parts year)

/-- Share every non-aggregate computation atom branch while allowing the direct and addressed evaluators to supply their own aggregate projection. -/
def readNumericComputationAtomWith
    (context : ScalarComputationContext)
    (readAggregate : NumericAggregateOp → Aggregate →
      Except NumericComputationFault NumericComputationResult) :
    ResolvedNumericAtom FlatFieldDecl Aggregate →
      Except NumericComputationFault NumericComputationResult
  | .field declaration => context.readNumeric declaration
  | .baseYear year => pure (.value year)
  | .baseYearDatePart year source part =>
      pure (.value (baseYearDateSourceNumericPart year source part))
  | .temporalFieldPart field part =>
      context.readTemporalNumeric field part.project?
  | .stringLength field =>
      pure ((observeCell .computation
        (context.read field.id)).asStringLengthOperand.toComputationResult)
  | .stringRange field start finish =>
      match observeCell .computation (context.read field.id) with
      | .empty => pure (.value 0)
      | .value (.str value) =>
          pure (.value (utf16RangeAsNatural value start finish))
      | .value _ => throw (.fieldKindMismatch field.id)
      | .unknown cause | .poison cause => pure (.poison cause)
  | .fieldValueAsNumber source =>
      match observeCell .computation (context.read source.fieldId) with
      | .empty => pure (.value 0)
      | .value value =>
          match source.valueFor? value with
          | some amount => pure (.value amount)
          | none => throw (.fieldKindMismatch source.fieldId)
      | .unknown cause | .poison cause => pure (.poison cause)
  | .dateDifference unit left right =>
      match DateDifferenceOperand.evaluate unit
          (context.readDateDifferenceOperand left)
          (context.readDateDifferenceOperand right) with
      | .error _ => throw .unsupportedDateCalendar
      | .ok operand => pure operand.toComputationResult
  | .aggregate op source => readAggregate op source
  | .filledGroupCount _ => throw .unsupportedGroupCount

/-- Preserve the direct-only resolved evaluator used by low-level proofs and callers. -/
def readNumericComputationAtom (context : ScalarComputationContext) :
    NumericComputationAtom →
      Except NumericComputationFault NumericComputationResult :=
  context.readNumericComputationAtomWith fun op source =>
    pure ((source.evaluate op fun field =>
      observeCell .computation (context.read field)).toComputationResult)

/-- Evaluate a checked computation atom without a repeatable document only when its entity-list payload narrows exactly to direct fields. A repeatable operand fails explicitly rather than silently observing an empty synthetic document. -/
def readCheckedNumericComputationAtom (context : ScalarComputationContext) :
    CheckedNumericComputationAtom model →
      Except NumericComputationFault NumericComputationResult
  | .sumOfProducts _ => throw .repeatableContextRequired
  | .numeric source =>
      context.readNumericComputationAtomWith (Aggregate := CheckedNumberEntitySource model)
        (fun op aggregate =>
          match aggregate.directAggregateFields? with
          | some direct =>
              pure ((direct.evaluate op fun field =>
                observeCell .computation
                  (context.read field)).toComputationResult)
          | none => throw .repeatableContextRequired) source

end ScalarComputationContext

namespace NumericComputationEvaluationContext

/-- Evaluate one model-checked atom against its complete direct/repeatable computation inputs. Addressing failures stay explicit and cannot collapse into a numeric value, clean absence, or formal poison. -/
def readCheckedNumericComputationAtom
    (context : NumericComputationEvaluationContext) :
    CheckedNumericComputationAtom model →
      Except NumericComputationFault NumericComputationResult
  | .sumOfProducts source =>
      (source.evaluateComputation context.document context.outer
        context.starRead).mapError NumericComputationFault.repeatableAddressing
  | .numeric source =>
      context.scalar.readNumericComputationAtomWith
        (fun op aggregate =>
          (aggregate.evaluateComputation op context.document context.outer
            context.scalar.read context.filterRead context.starRead).mapError
              NumericComputationFault.repeatableAddressing) source

end NumericComputationEvaluationContext

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
    ResolvedNumericAtom FlatFieldDecl Aggregate →
      Option NumericComputationFault
  | .field declaration => declaration.numericComputationFault?
  | .baseYear _ => none
  | .baseYearDatePart _ _ _ => none
  | .temporalFieldPart _ _ => none
  | .stringLength _ => none
  | .stringRange _ _ _ => none
  | .fieldValueAsNumber _ => none
  | .dateDifference _ left right =>
      let fault? : ResolvedDateDifferenceOperand → Option NumericComputationFault
        | .field source =>
            if source.kind == .date then none
            else some (.fieldKindMismatch source.id)
        | .baseYear _ _ => none
      match fault? left with
      | some fault => some fault
      | none => fault? right
  | .aggregate _ _ => none
  | .filledGroupCount _ => some .unsupportedGroupCount

def CheckedNumericComputationAtom.numericComputationFault? :
    CheckedNumericComputationAtom model → Option NumericComputationFault
  | .numeric source =>
      NumericComputationAtom.numericComputationFault? source
  | .sumOfProducts _ => none

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
  | .abs body | .extremumCall _ _ body => body.computationFaultWith? fault?
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
  | .extremumCall _ _ body => body.evalComputation read
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

private def evaluateComputationWith
    (expression : AuthoredNumericExpr Atom)
    (fault? : Atom → Option NumericComputationFault)
    (read : Atom →
      Except NumericComputationFault NumericComputationResult) :
    Except NumericComputationFault NumericComputationResult :=
  let lowered := expression.lowerForEvaluation
  match lowered.computationFaultWith? fault? with
  | some fault => .error fault
  | none => lowered.evalComputation read

def evaluateResolvedComputation
    (expression : AuthoredNumericExpr NumericComputationAtom)
    (context : ScalarComputationContext) :
    Except NumericComputationFault NumericComputationResult :=
  expression.evaluateComputationWith
    NumericComputationAtom.numericComputationFault?
    context.readNumericComputationAtom

/-- Evaluate the unified checked computation tree through the scalar compatibility boundary. Repeatable atoms are rejected explicitly. -/
def evaluateCheckedComputation
    (expression : AuthoredNumericExpr (CheckedNumericComputationAtom model))
    (context : ScalarComputationContext) :
    Except NumericComputationFault NumericComputationResult :=
  expression.evaluateComputationWith
    CheckedNumericComputationAtom.numericComputationFault?
    context.readCheckedNumericComputationAtom

/-- Evaluate the same checked computation tree with the explicit repeatable document, environment, and readers required by entity-list atoms. -/
def evaluateCheckedComputationIn
    (expression : AuthoredNumericExpr (CheckedNumericComputationAtom model))
    (context : NumericComputationEvaluationContext) :
    Except NumericComputationFault NumericComputationResult :=
  expression.evaluateComputationWith
    CheckedNumericComputationAtom.numericComputationFault?
    context.readCheckedNumericComputationAtom

end AuthoredNumericExpr

namespace CheckedNumericComputationOperation

def evaluate (operation : CheckedNumericComputationOperation model)
    (context : ScalarComputationContext) :
    Except NumericComputationFault NumericComputationResult :=
  operation.core.expression.evaluateCheckedComputation context

def evaluateIn (operation : CheckedNumericComputationOperation model)
    (context : NumericComputationEvaluationContext) :
    Except NumericComputationFault NumericComputationResult :=
  operation.core.expression.evaluateCheckedComputationIn context

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

/-- Preserve the same retained target-policy dispatch after repeatable expression evaluation. Source-relative target policy and result classification are not recomputed or reordered. -/
def evaluateIn (operation : CheckedNumericTargetComputationOperation model)
    (context : NumericComputationEvaluationContext) :
    Except NumericComputationFault NumericTargetCheckResult := do
  let result ← operation.operation.evaluateIn context
  if operation.operation.core.suppressExactScaleWarning then
    pure (operation.policy.checkWithScaleWarningSuppressed result)
  else
    pure (operation.policy.check result)

end CheckedNumericTargetComputationOperation

end A12Kernel
