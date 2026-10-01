import A12Kernel.Elaboration.DateRangeBoundComponent
import A12Kernel.Elaboration.FirstFilledValue
import A12Kernel.Elaboration.NumericAggregate
import A12Kernel.Elaboration.LiteralComparisonDiagnostic
import A12Kernel.Elaboration.TokenValueCount
import A12Kernel.Semantics.ComputationCondition
import A12Kernel.Semantics.NumericTarget

/-! # Numeric computation-expression outcomes

This capsule checks one parser-independent numeric operation with an ordinary nonrepeatable Number target against a validated model and then evaluates the resolved expression. Admission resolves scalar Number-field, numeric-`BaseYear`, Base-Year date-component, direct temporal field-component, UTF-16 String `Length`, checked ordinary String/Enumeration/category `FieldValueAsNumber`, Date-only month/year differences, exact-instant DateTime field/`Now` hour/minute/second differences, concrete-profile Date/DateTime day differences, checked direct/plain-star/filtered-star Number entity-list aggregates and `FirstFilledValue`, typed String/stored-Enumeration and Boolean/Confirm value counts, the distinct row-aligned `SumOfProducts` pair, and fixed distinct disjoint multi-group filled counts through one shared numeric tree. The direct aggregate surface maps into the checked entity-list payload, while the complete surface retains each specialized checked source and the product pair's proof-bearing common-row plan. Target self-reference traversal reaches selected entity-list fields, every `Having` reference, both product fields, and every counted group subtree; the Boolean/Confirm count cannot include its Number target by construction. Scale checking uses the selected declarations' union, integral count result, or product of pair scales. Each operand-list Min/Max call independently enforces its immediate-constant budget without flattening nested calls. A rounding or absolute-value node rejects an immediate numeric literal body; numeric `BaseYear` remains a distinct admitted source. The primary checked target entry points construct the complete policy from the validated target declaration and attach it once, so evaluation cannot substitute caller-selected constraints; the lower-level attachment remains an explicit compatibility seam for already-resolved policies and still rejects scale/signedness drift. The one explicit scale-warning suppression bypasses only the result-scale gate and selects the existing warning-suppressed target branch after evaluation. Scalar computation evaluation remains available for direct-only sources, reads dynamic `Now` only from its explicit optional `World`, fails structurally when that input is absent, and rejects repeatable atoms explicitly. Addressed computation evaluation accepts the document, outer environment, and checked readers required by the existing entity-list and product traversals, maps structural addressing failure into the computation-fault domain, and otherwise preserves ordinary values, arithmetic domain failure, inherited computation-read poison, and the fail-closed legacy-calendar boundary. Generated validation narrows direct ordinary aggregates and every direct-only specialized source into its existing nonrepeatable atoms, while repeatable entity-list, token-count, product, and first-filled payloads retain their checked certificates through the full-only addressed validation context; fixed filled-group computation remains an explicit arm-crossing generated-validation boundary. Concrete parsing, partially-known Date policy, constructed-Date legacy execution, application, delta projection, wider whole-rule repeatable generated validation, and scheduling remain outside this module.

The measured arithmetic surface retains the target through scale summarization so it reaches the target-scale gate before self-reference: `+`, `-`, or `*` reading the target on exactly one side, against an immediate literal or a different direct Number field. The gate order rather than the authored shape is what that surface encodes. Every other target read keeps its pre-existing immediate local refusal, including when a later operand would otherwise fail resolution, and receives no projected Kernel class. Both operand kinds are measured at both scale relations: a field operand whose declared scale differs from the target's reports the scale gate first and exposes the self-reference under suppression, exactly as a matching one does.

Numeric and Boolean/Confirm `NumberOfValueInFields` remain distinct checked atoms so their different field-kind matrices and per-cell provenance survive arithmetic, target evaluation, and generated validation without a second expression tree or aggregate fold.
-/

namespace A12Kernel

abbrev NumericComputationAtom := ResolvedNumericAtom FlatFieldDecl

/-- The complete computation surface keeps ordinary numeric atoms in their shared representation and adds distinct prefix-selecting and row-aligned aggregate atoms without creating another arithmetic tree. -/
inductive SurfaceNumericComputationAtom where
  | numeric (source : SurfaceNumericAtom SurfaceNumberEntitySource)
  | firstFilled (source : SurfaceNumberEntitySource)
  | valueCount (expected : Rat) (source : SurfaceNumberEntitySource)
  | tokenValueCount (expected : String) (source : SurfaceTokenValueCountSource)
  | booleanValueCount (expected : Bool)
      (source : SurfaceBooleanValueCountSource)
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
  | booleanValueCount (source : CheckedBooleanValueCountSource model)
  | sumOfProducts (source : CheckedNumericProductAggregate model)
  /-- A filled-group count whose operand list carries at least one star. The fixed-only list
  keeps the established `numeric` atom untouched, so widening this operator costs the
  already-measured form nothing. -/
  | filledGroupCountMixed (operands : List (CheckedGroupCountOperand model))

/-- Fail-closed faults outside the admitted numeric computation-expression fragment. -/
inductive NumericComputationFault where
  | fieldKindMismatch (field : FieldId)
  | unsupportedDateCalendar
  | unsupportedDateTimeDifferenceOperand
  | worldRequired
  /-- One resolved group operand of a filled-group count lies outside the admitted scalar boundary.
  The path names *which* operand, so an Explain or Qualify consumer can point at it rather than at the
  whole count; the count itself is order-insensitive, so nothing else about the refusal is ordered. -/
  | unsupportedGroupCount (group : GroupPath)
  /-- The model-free resolved evaluator cannot enumerate any group's descendants, so no single operand
  is at fault. Kept distinct from the class above because the remedy differs: that one is an authoring
  boundary, this one a missing evaluation input. -/
  | groupCountNeedsModel
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
  | copyComparison (targetPath sourcePath : List String) (refusal : CopyComparisonRefusal)
  | lengthOperandNotEvaluatedString (path : List String)
  | rangeOperandNotString (path : List String)
  | invalidStringRange (start finish : Nat)
  | fieldValueAsNumberSource (path : List String)
      (error : FieldValueAsNumberSourceError)
  | incompatibleTemporalSource (path : List String)
  /-- The declared DateRange profile does not expose the requested date component at its
  endpoint; the same measured class the validation surface reports. -/
  | dateRangeBoundPartNotExposed (path : List String) (part : DateNumericPart)
  | incompatibleDateDifference
  | unsupportedCalendarProfile (zoneId : String)
  | baseYearNotDeclared
  | aggregate (error : NumberEntityElabError)
  | tokenValueCount (error : TokenValueCountElabError)
  | booleanValueCount (error : BooleanValueCountElabError)
  | productAggregate (error : NumericProductAggregateElabError)
  | groupReference (error : FixedGroupReferenceError)
  | currentRepetitionSource (error : FixedGroupReferenceError)
  | groupCountNeedsMultipleOperands
  /-- The starred group plan itself refused; the underlying error carries the class. -/
  | starredGroupCountPlan (error : StarredGroupElabError)
  | overlappingGroupCountOperands (left right : GroupPath)
  /-- A root group beside any other operand. Reached only once containment is ruled out, because
  the Kernel checks the two gates in that order on both arms. -/
  | rootGroupInGroupCount (path : GroupPath)
  /-- An operand leaves a repeatable level for its evaluation to bind, which this arm's fixed target
  cannot do; the record carries what selects the class. -/
  | unboundOperandLevel (unbound : UnboundOperandLevel)
  | targetSelfReference (field : FieldId)
  | authoring (result : NumericAuthoringCheck)
  | unsupportedExpression
  | operationScaleMismatch (targetScale : Nat) (operation : NumericScaleSummary)
  | targetPolicyMismatch (target policy : NumField)
  | incoherentCore
  deriving Repr, DecidableEq

namespace NumericComputationElabError

/-- Project the measured fixed filled-group computation admission failures to their exact
    Kernel diagnostic classes. Every other computation refusal remains unmapped. -/
def groupCountDiagnostic? :
    NumericComputationElabError → Option KernelStaticDiagnostic
  | .groupCountNeedsMultipleOperands => some .paramSizeInvalidGN
  -- The plan's empty-group class and the resolver classes are measured on this arm too, not
  -- borrowed from validation's
  -- ([empty](../../../docs/sources/static-admission-and-class-probes.md#src-entity-list-kind-empty-and-root-carriers),
  -- [resolver](../../../docs/sources/path-resolution-class-probes.md#src-group-operand-resolution-classes)).
  | .starredGroupCountPlan error => error.diagnostic?
  | .groupReference error => error.diagnostic?
  | .overlappingGroupCountOperands left right =>
      if left == right then some .duplicateParam1 else some .duplicateParam2
  | .rootGroupInGroupCount _ => some .rootGroupWithOtherParameters
  | _ => none

/-- Project the measured computed Number target-scale rejection, a read of the target, which
every measured shape reaches only past the authoring and scale gates, and a copied field the
generated comparison refuses. An aggregate or group-count read of the target takes the same order
unmeasured. Other computation failures remain unmapped. -/
def targetDiagnostic? :
    NumericComputationElabError → Option KernelStaticDiagnostic
  | .operationScaleMismatch _ _ => some .invalidCompareDecimalPlaces
  | .copyComparison _ _ refusal => some refusal.diagnostic
  | .targetSelfReference _ => some .errorReferenceToCalculatedField
  | _ => none

/-- Project the per-row operand gate, whether this arm, an operand's resolver or an entity list's
    shape asked it. The target repeats at no level on this arm, so a per-row read's class is
    containment when the target lies outside the declaring group and otherwise decided by where its
    outermost level lies beside or below the target's group
    ([checkpoint](../../../docs/sources/group-list-and-capacity-probes.md#src-computation-star-binding-gate)). -/
def iterationDiagnostic? :
    NumericComputationElabError → Option KernelStaticDiagnostic
  | .unboundOperandLevel unbound
  | .resolve (.unboundOperandLevel _ unbound)
  | .groupReference (.unboundOperandLevel _ unbound)
  | .aggregate (.shape (.unboundOperandLevel unbound))
  | .tokenValueCount (.source (.shape (.unboundOperandLevel unbound)))
  | .booleanValueCount (.shape (.unboundOperandLevel unbound)) => unbound.diagnostic?
  | _ => none

end NumericComputationElabError

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
  | .booleanValueCount _ => true
  | .sumOfProducts _ => true
  -- Every operand carries its own model certificate, so admission is settled at elaboration.
  | .filledGroupCountMixed _ => true
  | .numeric (.field declaration) =>
      match model.lookupUniqueId declaration.id with
      | .ok admitted =>
          admitted == declaration &&
            declaration.repeatableScope.isEmpty &&
            declaration.toNumberField?.isSome
      | .error _ => false
  | .numeric (.baseYear year) => model.baseYear == some year
  | .numeric (.fixedCurrentRepetition reference) =>
      reference.scalarRepetitionWellFormedBool model
  | .numeric (.boundCurrentRepetition _) => false
  | .numeric (.baseYearDatePart year _ _) => model.baseYear == some year
  | .numeric (.temporalFieldPart source part) =>
      model.admitsTemporalComputationOperand source
        (part.admittedBy source model.hasBaseYear)
  | .numeric (.dateRangeBoundPart source _ part) =>
      model.nonrepeatableDateRangeSource source &&
        model.exposesDateRangeBoundPart source part
  | .numeric (.stringLength source) => model.admitsStringValueField source
  | .numeric (.stringRange source start finish) =>
      validStringRange start finish && model.admitsStringValueField source
  | .numeric (.fieldValueAsNumber source) =>
      model.admitsFieldValueAsNumberSource source
  | .numeric (.dateDifference unit left right) =>
      let admitted : ResolvedDateDifferenceOperand → Bool
        | .field source =>
            model.admitsTemporalComputationOperand source
              (unit.admittedBy model.hasBaseYear source.components)
        | .baseYear year _ => model.baseYear == some year
      admitted left && admitted right &&
        unit.compatible model.hasBaseYear left.components right.components
  | .numeric (.dateTimeDifference unit left right) =>
      let admitted : FlatTemporalOperand → Bool
        | .fieldValue source =>
            model.admitsTemporalComputationOperand source
              (unit.admittedBy source.components)
        | .nowValue => unit.admittedBy TemporalComponents.now
        | _ => false
      match left.dateTimeDifferenceComponents?,
          right.dateTimeDifferenceComponents? with
      | some leftComponents, some rightComponents =>
          admitted left && admitted right &&
            unit.compatible leftComponents rightComponents
      | _, _ => false
  | .numeric (.dayDifference profile left right) =>
      let admitted : ResolvedDateDifferenceOperand → Bool
        | .field source =>
            model.admitsTemporalComputationOperand source
              (CalendarDayDifference.admittedBy source.components)
        | .baseYear year _ => model.baseYear == some year
      ModelZone.ConcreteProfile.ofId? model.timeZoneId == some profile &&
        admitted left && admitted right &&
        CalendarDayDifference.yearCompatible model.hasBaseYear
          left.components right.components
  | .numeric (.aggregate _ _) => true
  | .numeric (.filledGroupCount groups) =>
      1 < groups.length &&
        (ResolvedGroupReferences.firstOverlap? groups).isNone &&
        groups.all fun reference =>
          model.hasGroupPath reference.path &&
            reference.origin == .path &&
            (model.repeatableScopeForGroupPath reference.path).isEmpty

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
  | .booleanValueCount source => source.scaleSummary
  | .sumOfProducts source => source.scaleSummary
  -- A count is integral, exactly like the fixed-only form's `filledGroupCount` summary.
  | .filledGroupCountMixed _ => NumericScaleSummary.field 0

/-- Whether one resolved numeric atom reads a given field. Structural coordinates and model
    constants read none; every other kind reports the field or fields it addresses, including both
    endpoints of a two-operand difference. Carriers share this rather than re-deciding it, because a
    dependency query that silently answers `false` for a source kind it forgot is worse than one
    that refuses: nothing fails, and the missing edge reaches a consumer as a fact. -/
def ResolvedNumericAtom.referencesFieldWith {Aggregate : Type}
    (model : FlatModel) (field : FieldId)
    (referencesAggregate : Aggregate → Bool) :
    ResolvedNumericAtom FlatFieldDecl Aggregate → Bool
  | .field declaration => declaration.id == field
  | .baseYear _ => false
  | .fixedCurrentRepetition _ => false
  | .boundCurrentRepetition _ => false
  | .baseYearDatePart _ _ _ => false
  | .temporalFieldPart source _ => source.id == field
  | .dateRangeBoundPart source _ _ => source.id == field
  | .stringLength source => source.id == field
  | .stringRange source _ _ => source.id == field
  | .fieldValueAsNumber source => source.fieldId == field
  | .dateDifference _ left right => left.references field || right.references field
  | .dateTimeDifference _ left right =>
      left.dateTimeDifferenceReferences field || right.dateTimeDifferenceReferences field
  | .dayDifference _ left right => left.references field || right.references field
  | .aggregate _ source => referencesAggregate source
  | .filledGroupCount groups => groups.any fun group => group.referencesField model field

/-- The ordinary computation atom's instance of that walk, resolving its aggregate through the
    checked entity-list source. -/
def NumericComputationAtom.referencesField (model : FlatModel) (field : FieldId)
    (atom : NumericComputationAtom) : Bool :=
  atom.referencesFieldWith model field (·.referencesField field)

def CheckedNumericComputationAtom.references
    (model : FlatModel) (field : FieldId) :
    CheckedNumericComputationAtom model → Bool
  | .firstFilled source => source.referencesField field
  | .valueCount _ source => source.referencesField field
  | .tokenValueCount source => source.referencesField field
  | .booleanValueCount source => source.referencesField field
  | .sumOfProducts source =>
      source.left.field.id == field || source.right.field.id == field
  | .filledGroupCountMixed operands =>
      operands.any fun operand => operand.referencesField model field
  | .numeric atom => atom.referencesFieldWith model field (·.referencesField field)

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

/-- A model-coherent operation produced only after target, operands, authoring shape, self-reference,
result scale, and computation declaration-group syntax have been checked. -/
structure CheckedNumericComputationOperation (model : FlatModel) where
  declaringGroup : GroupPath
  core : NumericComputationOperation model
  declaringGroupValid : GroupPath.isValid declaringGroup = true
  modelWellFormed : model.validate.isOk = true
  wellFormed : core.WellFormed

/-- A checked numeric operation paired once with its complete resolved target policy. Evaluation cannot substitute a different policy. -/
structure CheckedNumericTargetComputationOperation (model : FlatModel) where
  operation : CheckedNumericComputationOperation model
  policy : NumericTargetPolicy
  targetMatches : policy.info = operation.core.target.info

/-- The fixed Number target and the group it lies in, which decides a per-row read's class. -/
private def FlatModel.resolveNumericComputationTarget
    (model : FlatModel) (target : FieldId) :
    Except NumericComputationElabError (FlatNumberField × GroupPath) := do
  let declaration ← (model.resolveNonrepeatableDeclarationById target).mapError .resolve
  match declaration.toNumberField? with
  | some field => pure (field, declaration.groupPath)
  | none => throw (.targetNotNumber target)

def SurfaceNumericAggregateFields.toNumberEntitySource
    (source : SurfaceNumericAggregateFields) : SurfaceNumberEntitySource :=
  { first := .field source.first
    rest := source.rest.map SurfaceFieldEntityOperand.field }

def SurfaceNumericAtom.toNumberEntityComputationAtom :
    SurfaceNumericAtom →
      SurfaceNumericAtom SurfaceNumberEntitySource
  | .field path => .field path
  | .currentRepetition path => .currentRepetition path
  | .baseYear => .baseYear
  | .baseYearDatePart source part => .baseYearDatePart source part
  | .temporalFieldPart path part => .temporalFieldPart path part
  | .dateRangeBoundPart path bound part => .dateRangeBoundPart path bound part
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
    (model : FlatModel) (declaringGroup targetGroup : GroupPath)
    (reference : SurfaceFieldPath) (accepts : FlatTemporalField → Bool) :
    Except NumericComputationElabError FlatTemporalField := do
  let declaration ←
    (model.resolveNonrepeatableComputationOperandUnchecked declaringGroup targetGroup reference).mapError .resolve
  match declaration.toTemporalField? with
  | some field =>
      if accepts field then pure field
      else throw (.incompatibleTemporalSource declaration.path)
  | none => throw (.incompatibleTemporalSource declaration.path)

/-- Refuse an operand that reads per row, for the atoms that are not entity lists: the product
    aggregate and the group count. Each scope lists the repeatable levels one operand leaves for its
    evaluation to bind, and this arm's target repeats at none, so the first nonempty scope is refused
    with the class `UnboundOperandLevel` selects. An entity list asks the same question list-wide
    inside its shape, ahead of its duplicate scans
    ([checkpoint](../../../docs/sources/group-list-and-capacity-probes.md#src-computation-star-binding-gate)). -/
def FlatModel.requireOperandLevelsBound (model : FlatModel)
    (declaringGroup targetGroup : GroupPath) (scopes : List (List RepeatableLevel)) :
    Except NumericComputationElabError Unit :=
  match model.firstUnboundOperandLevel? declaringGroup targetGroup scopes with
  | none => pure ()
  | some unbound => throw (.unboundOperandLevel unbound)

private def FlatModel.resolveNumericComputationAtoms
    (model : FlatModel) (declaringGroup targetGroup : GroupPath)
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom) :
    Except NumericComputationElabError
      (AuthoredNumericExpr (CheckedNumericComputationAtom model)) :=
  expression.mapM fun
    | .firstFilled source => do
        let checked ←
          (elaborateNumberEntitySource model declaringGroup source (fixedTargetGroup? := some targetGroup)).mapError
            NumericComputationElabError.aggregate
        pure (.firstFilled checked)
    | .valueCount expected source => do
        let checked ←
          (elaborateNumberEntitySource model declaringGroup source (fixedTargetGroup? := some targetGroup)).mapError
            NumericComputationElabError.aggregate
        pure (.valueCount expected checked)
    | .tokenValueCount expected source => do
        let checked ←
          (elaborateTokenValueCountSource model declaringGroup expected source
              (fixedTargetGroup? := some targetGroup)).mapError
            NumericComputationElabError.tokenValueCount
        pure (.tokenValueCount checked)
    | .booleanValueCount expected source => do
        let checked ←
          (elaborateBooleanValueCountSource model declaringGroup expected source
              (fixedTargetGroup? := some targetGroup)).mapError
            NumericComputationElabError.booleanValueCount
        pure (.booleanValueCount checked)
    | .sumOfProducts source => do
        let checked ←
          (elaborateNumericProductAggregate model declaringGroup source targetGroup).mapError
            NumericComputationElabError.productAggregate
        model.requireOperandLevelsBound declaringGroup targetGroup
          [checked.left.source.bindingScope, checked.right.source.bindingScope]
        pure (.sumOfProducts checked)
    | .numeric (.field reference) => do
        let declaration ←
          (model.resolveComputationFieldValueRead declaringGroup targetGroup reference).mapError .resolve
        if declaration.toNumberField?.isSome then
          pure (.numeric (.field declaration))
        else
          throw (.operandNotNumber declaration.path)
    | .numeric .baseYear =>
        match model.baseYear with
        | some year => pure (.numeric (.baseYear year))
        | none => throw .baseYearNotDeclared
    | .numeric (.currentRepetition path) => do
        let reference ← model.resolveFixedGroupReference declaringGroup (.path path)
          |>.mapError .currentRepetitionSource
        pure (.numeric (.fixedCurrentRepetition reference))
    | .numeric (.baseYearDatePart source part) =>
        match model.baseYear with
        | some year => pure (.numeric (.baseYearDatePart year source part))
        | none => throw .baseYearNotDeclared
    | .numeric (.temporalFieldPart reference part) => do
        let field ← model.resolveTemporalNumericComputationField
          declaringGroup targetGroup reference
          (fun source => part.admittedBy source model.hasBaseYear)
        pure (.numeric (.temporalFieldPart field part))
    | .numeric (.dateRangeBoundPart reference bound part) => do
        let declaration ←
          (model.resolveComputationEntityRead declaringGroup targetGroup reference).mapError
            .resolve
        -- The target is a Number field, so a DateRange operand can never be the target itself.
        let source : FlatDateRangeField := { id := declaration.id }
        if model.exposesDateRangeBoundPart source part then
          pure (.numeric (.dateRangeBoundPart source bound part))
        else
          throw (.dateRangeBoundPartNotExposed declaration.path part)
    | .numeric (.stringLength reference) => do
        let declaration ←
          (model.resolveComputationEntityRead declaringGroup targetGroup reference).mapError .resolve
        match declaration.toStringValueField? with
        | some field => pure (.numeric (.stringLength field))
        | none => throw (.lengthOperandNotEvaluatedString declaration.path)
    | .numeric (.stringRange reference start finish) => do
        let declaration ←
          (model.resolveComputationEntityRead declaringGroup targetGroup reference).mapError .resolve
        if !validStringRange start finish then
          throw (.invalidStringRange start finish)
        match declaration.toStringValueField? with
        | none => throw (.rangeOperandNotString declaration.path)
        | some field => pure (.numeric (.stringRange field start finish))
    | .numeric (.fieldValueAsNumber surface) => do
        let declaration ←
          (model.resolveComputationEntityRead
            declaringGroup targetGroup surface.reference).mapError .resolve
        match declaration.resolveFieldValueAsNumberSource surface.projectionRef with
        | .ok source => pure (.numeric (.fieldValueAsNumber source))
        | .error error =>
            throw (.fieldValueAsNumberSource declaration.path error)
    | .numeric (.dateDifference unit left right) => do
        let resolveOperand : SurfaceDateDifferenceOperand →
            Except NumericComputationElabError ResolvedDateDifferenceOperand
          | .field reference => do
              let field ← model.resolveTemporalNumericComputationField
                declaringGroup targetGroup reference
                (fun source =>
                  unit.admittedBy model.hasBaseYear source.components)
              pure (.field field)
          | .baseYear source =>
              match model.baseYear with
              | some year => pure (.baseYear year source)
              | none => throw .baseYearNotDeclared
          | .now => throw .incompatibleDateDifference
        let resolvedLeft ← resolveOperand left
        let resolvedRight ← resolveOperand right
        if unit.compatible model.hasBaseYear
            resolvedLeft.components resolvedRight.components then
          pure (.numeric (.dateDifference unit resolvedLeft resolvedRight))
        else
          throw .incompatibleDateDifference
    | .numeric (.dateTimeDifference unit left right) => do
        let resolveOperand : SurfaceDateDifferenceOperand →
            Except NumericComputationElabError FlatTemporalOperand
          | .baseYear _ => throw .incompatibleDateDifference
          | .now => pure .nowValue
          | .field reference => do
              let field ← model.resolveTemporalNumericComputationField
                declaringGroup targetGroup reference
                (fun source => unit.admittedBy source.components)
              pure (.fieldValue field)
        let resolvedLeft ← resolveOperand left
        let resolvedRight ← resolveOperand right
        match resolvedLeft.dateTimeDifferenceComponents?,
            resolvedRight.dateTimeDifferenceComponents? with
        | some leftComponents, some rightComponents =>
            if unit.compatible leftComponents rightComponents then
              pure (.numeric
                (.dateTimeDifference unit resolvedLeft resolvedRight))
            else
              throw .incompatibleDateDifference
        | _, _ => throw .incompatibleDateDifference
    | .numeric (.dayDifference left right) => do
        let profile ← match ModelZone.ConcreteProfile.ofId? model.timeZoneId with
          | some profile => pure profile
          | none => throw (.unsupportedCalendarProfile model.timeZoneId)
        let resolveOperand : SurfaceDateDifferenceOperand →
            Except NumericComputationElabError ResolvedDateDifferenceOperand
          | .field reference => do
              let field ← model.resolveTemporalNumericComputationField
                declaringGroup targetGroup reference
                (fun source =>
                  CalendarDayDifference.admittedBy source.components)
              pure (.field field)
          | .baseYear source =>
              match model.baseYear with
              | some year => pure (.baseYear year source)
              | none => throw .baseYearNotDeclared
          | .now => throw .incompatibleDateDifference
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
          (elaborateNumberEntitySource model declaringGroup source (fixedTargetGroup? := some targetGroup)).mapError
            NumericComputationElabError.aggregate
        pure (.numeric (.aggregate op checked))
    | .numeric (.filledGroupCount operands) => do
        match SurfaceGroupCountOperand.fixedOnly? operands with
        | some surfaces => do
            -- Each operand's per-row class answers when it resolves, so ahead of the arity
            -- minimum as the Kernel orders them.
            let groups ← surfaces.mapM (model.resolveFixedTargetGroupReference declaringGroup targetGroup)
              |>.mapError NumericComputationElabError.groupReference
            -- The arity minimum governs the unstarred form only. A list carrying a star takes the
            -- branch below, where one operand is a complete list; both halves are measured.
            if groups.length < 2 then
              throw .groupCountNeedsMultipleOperands
            match ResolvedGroupReferences.firstOverlap? groups with
            | some (left, right) =>
                throw (.overlappingGroupCountOperands left right)
            | none =>
                match groups.find? ResolvedGroupReference.isRoot with
                | some root => throw (.rootGroupInGroupCount root.path)
                | none => pure (.numeric (.filledGroupCount groups))
        | none => do
            let checked ← operands.mapM fun operand =>
              match operand with
              | .fixed reference => do
                  let resolved ← model.resolveFixedTargetGroupReference declaringGroup targetGroup reference
                    |>.mapError NumericComputationElabError.groupReference
                  pure (CheckedGroupCountOperand.fixed resolved)
              | .starred path => do
                  let checked ← match elaborateStarredGroupOperandSource model declaringGroup path with
                    | .error error =>
                        throw (NumericComputationElabError.starredGroupCountPlan
                          (error.placeBelowStar model declaringGroup targetGroup))
                    | .ok (.terminalRepeatable source) =>
                        pure (CheckedGroupCountOperand.starred source)
                    -- Admitted alone, beside a fixed group, and twice on this arm too
                    -- ([checkpoint](../../../docs/SOURCES.md#src-ancestor-starred-group-count-computation)).
                    | .ok (.terminalPresence source) =>
                        pure (CheckedGroupCountOperand.starredPresence source)
                  -- Judged where it resolves, as a fixed operand is, so the first per-row operand
                  -- in authored order decides the class whichever form it takes.
                  model.requireOperandLevelsBound declaringGroup targetGroup [checked.bindingScope]
                  pure checked
            -- Containment reaches every member whichever side carries the star, and it runs
            -- **before** rootness: a root beside its own descendant draws the overlap class, and
            -- the root class is what remains for a root beside a disjoint operand. Both gates and
            -- their order are measured on this arm rather than carried over from validation.
            match CheckedGroupCountOperand.firstDuplicate? checked with
            | some (left, right) =>
                throw (.overlappingGroupCountOperands left right)
            | none =>
                match checked.find? CheckedGroupCountOperand.isRoot with
                | some operand => throw (.rootGroupInGroupCount operand.groupPath)
                | none => pure (.filledGroupCountMixed checked)

/-- Check computation-group syntax independently of whether the Numeric expression has an operand. -/
private def certifyNumericComputationDeclaringGroup (declaringGroup : GroupPath) :
    Except NumericComputationElabError { group : GroupPath // GroupPath.isValid group = true } :=
  if hValid : GroupPath.isValid declaringGroup = true then
    .ok ⟨declaringGroup, hValid⟩
  else
    .error (.resolve (.invalidRuleGroup declaringGroup))

/-- The comparison the computation generates between its target and a **directly copied** field,
asked after the target's read and then the copied field's read, ahead of this carrier's own kind
gates ([checkpoint](../../../docs/sources/static-admission-and-class-probes.md#src-field-copy-comparison-grid)).
A wider expression is not typed here, and two Numbers pass to the scale rule. -/
private def FlatModel.checkNumericCopyComparison (model : FlatModel) (declaringGroup : GroupPath)
    (targetField : FieldId) :
    AuthoredNumericExpr SurfaceNumericComputationAtom → Except NumericComputationElabError Unit
  | .atom (.numeric (.field reference)) => do
      let target ← (model.resolveNonrepeatableDeclarationById targetField).mapError .resolve
      if target.fieldValueReadRefusal?.isNone then
        let source ←
          (model.resolveComputationFieldValueRead declaringGroup target.groupPath reference).mapError
            .resolve
        if let some refusal := target.copyComparisonRefusal? source then
          throw (.copyComparison target.path source.path refusal)
  | _ => pure ()

/-- Resolve and check the complete numeric computation surface, including checked entity-list atoms and the distinct row-aligned `SumOfProducts` source, through the one shared numeric expression tree. -/
def elaborateCompleteNumericComputationOperation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom)
    (suppressExactScaleWarning : Bool := false) :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation model) := do
  match hModel : model.validate with
  | .error error => throw (.resolve error)
  | .ok () => do
      let checkedDeclaringGroup ←
        certifyNumericComputationDeclaringGroup declaringGroup
      model.checkNumericCopyComparison checkedDeclaringGroup.val targetField expression
      let (target, targetGroup) ← model.resolveNumericComputationTarget targetField
      let resolved ← model.resolveNumericComputationAtoms checkedDeclaringGroup.val
        targetGroup expression
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
      -- A read of the target is refused last, after every atom has resolved, so a per-row read's
      -- class answers first
      -- ([checkpoint](../../../docs/sources/group-list-and-capacity-probes.md#src-computation-star-binding-gate)),
      -- and after the authoring and scale gates on every measured shape
      -- ([checkpoint](../../../docs/sources/evaluation-and-application-routes.md#src-join-operators-and-guards)).
      if resolved.anyAtom (CheckedNumericComputationAtom.references model targetField) then
        throw (.targetSelfReference targetField)
      let core : NumericComputationOperation model := {
        target
        expression := resolved
        suppressExactScaleWarning }
      if hCore : core.wellFormedBool = true then
        pure {
          declaringGroup := checkedDeclaringGroup.val
          core
          declaringGroupValid := checkedDeclaringGroup.property
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
