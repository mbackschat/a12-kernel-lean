import A12Kernel.Elaboration.NumericComputation.Atom
import A12Kernel.Elaboration.ComputationCondition

/-! # Numeric computation-expression outcomes

This capsule checks one parser-independent numeric operation with an ordinary Number target against a validated model. Its reading scope is the target's repeatable scope, which binds every operand level it holds ([`spec/09`](../../../spec/09-computations.md) §5), so direct and captured filter reads must fit that scope while star/group operands bind their expanded levels, and it then evaluates the resolved expression. Admission resolves scalar Number-field, numeric-`BaseYear`, Base-Year date-component, direct temporal field-component, UTF-16 String `Length`, checked ordinary String/Enumeration/category `FieldValueAsNumber`, Date-only month/year differences, exact-instant DateTime field/`Now` hour/minute/second differences, concrete-profile Date/DateTime day differences, checked direct/plain-star/filtered-star Number entity-list aggregates and `FirstFilledValue`, typed String/stored-Enumeration and Boolean/Confirm value counts, the distinct row-aligned `SumOfProducts` pair, and fixed distinct disjoint multi-group filled counts through one shared numeric tree. The direct aggregate surface maps into the checked entity-list payload, while the complete surface retains each specialized checked source and the product pair's checked row or independent-selection plan. Target self-reference traversal reaches selected entity-list fields, every `Having` reference, product value and selector dependencies, and every counted group subtree; the Boolean/Confirm count cannot include its Number target by construction. Scale checking uses the selected declarations' union, integral count result, or product of pair scales. Each operand-list Min/Max call independently enforces its immediate-constant budget without flattening nested calls. A rounding or absolute-value node rejects an immediate numeric literal body; numeric `BaseYear` remains a distinct admitted source. The primary checked target entry points construct the complete policy from the validated target declaration and attach it once, so evaluation cannot substitute caller-selected constraints; the lower-level attachment remains an explicit compatibility seam for already-resolved policies and still rejects scale/signedness drift. The one explicit scale-warning suppression bypasses only the result-scale gate and selects the existing warning-suppressed target branch after evaluation. Scalar computation evaluation remains available for direct-only sources, reads dynamic `Now` only from its explicit optional `World`, fails structurally when that input is absent, and rejects repeatable atoms explicitly. Addressed computation evaluation accepts the document, outer environment, and checked readers required by the existing entity-list and product traversals, maps structural addressing failure into the computation-fault domain, and otherwise preserves ordinary values, arithmetic domain failure, inherited computation-read poison, and the fail-closed legacy-calendar boundary. Generated validation narrows direct ordinary aggregates and every direct-only specialized source into its existing nonrepeatable atoms, while repeatable entity-list, token-count, product, and first-filled payloads retain their checked certificates through the full-only addressed validation context; fixed filled-group computation remains an explicit arm-crossing generated-validation boundary. Concrete parsing, partially-known Date policy, constructed-Date legacy execution, application, delta projection, wider whole-rule repeatable generated validation, and scheduling remain outside this module.

The measured arithmetic surface retains the target through scale summarization so it reaches the target-scale gate before self-reference: `+`, `-`, or `*` reading the target on exactly one side, against an immediate literal or a different direct Number field. The gate order rather than the authored shape is what that surface encodes. Every other target read keeps its pre-existing immediate local refusal, including when a later operand would otherwise fail resolution, and receives no projected Kernel class. Both operand kinds are measured at both scale relations: a field operand whose declared scale differs from the target's reports the scale gate first and exposes the self-reference under suppression, exactly as a matching one does.
-/

namespace A12Kernel

/-- One resolved numeric operation before target storage, retaining whether its result-scale warning was explicitly suppressed. -/
structure NumericComputationOperation (model : FlatModel) where
  target : FlatNumberField
  expression : AuthoredNumericExpr (CheckedNumericComputationAtom model)
  suppressExactScaleWarning : Bool := false

/-- The levels an operation's rows bind: its target's repeatable scope, empty for a fixed target. -/
def NumericComputationOperation.readingScope (operation : NumericComputationOperation model) :
    List RepeatableLevel :=
  model.fieldRepeatableScope operation.target.id

/-- Whether one model field's declaration satisfies `admits` and its repeatable levels are bound by
`scope`, the reading scope of the operation reading it. -/
private def FlatModel.admitsDeclarationIn (model : FlatModel) (scope : List RepeatableLevel)
    (field : FieldId) (admits : FlatFieldDecl → Bool) : Bool :=
  match model.lookupUniqueId field with
  | .ok declaration => declaration.repetitionBoundBy scope && admits declaration
  | .error _ => false

/-- Whether every one of a list's direct fields is bound by `scope`. Its starred and group operands
bind their own levels, which the list's shape asked against the same scope. -/
private def FlatModel.directFieldsBoundBy (model : FlatModel) (scope : List RepeatableLevel)
    (fields : List FieldId) : Bool :=
  fields.all fun field => (model.lookupUniqueId field).toOption.all (·.repetitionBoundBy scope)

private def FlatModel.admitsTemporalComputationOperand
    (model : FlatModel) (scope : List RepeatableLevel) (source : FlatTemporalField) (accepts : Bool) :
    Bool :=
  model.admitsDeclarationIn scope source.id fun declaration =>
    declaration.toTemporalField? == some source && accepts

def FlatModel.admitsNumericComputationOperand
    (model : FlatModel) (scope : List RepeatableLevel) : CheckedNumericComputationAtom model → Bool
  | .indexed source => source.toCheckedSemanticIndexSource.bindingScopes.all (·.isPrefixOf scope)
  | .indexedString source => source.selection.bindingScopes.all (·.isPrefixOf scope)
  | .temporalExpression source => source.bindingScopes.all (·.isPrefixOf scope)
  | .filledFieldCount source =>
      !source.operands.isEmpty && source.rowBoundBool scope &&
        source.operands.all fun operand =>
          match operand with
          | .indexed _ | .keyed _ => true
          | operand =>
            let structural : CheckedFieldFillOperand model := match operand with
              | .star source => .star (.plain source.declaringGroup source.source)
              | other => other
            (CheckedFieldFillList.computationSources { operands := [structural] }).toOption.any
              (fun sources => !sources.isEmpty && sources.all (·.admitted model scope))
  | .firstFilled source | .valueCount _ source =>
      source.bindingScopes.all (·.isPrefixOf scope)
  | .tokenDistinctCount source => source.bindingScopes.all (·.isPrefixOf scope)
  | .temporalDistinctCount run =>
      run.source.bindingScopes.all (·.isPrefixOf scope)
  | .tokenValueCount source => source.source.bindingScopes.all (·.isPrefixOf scope)
  | .booleanValueCount source => source.bindingScopes.all (·.isPrefixOf scope)
  | .sumOfProducts source => source.bindingScopes.all (·.isPrefixOf scope)
  -- Every operand carries its own model certificate, so admission is settled at elaboration.
  | .filledGroupCountMixed _ => true
  | .numeric (.field declaration) =>
      model.admitsDeclarationIn scope declaration.id fun admitted =>
        admitted == declaration && declaration.toNumberField?.isSome
  | .numeric (.baseYear year) => model.baseYear == some year
  | .numeric (.fixedCurrentRepetition reference) =>
      reference.scalarRepetitionWellFormedBool model
  | .numeric (.boundCurrentRepetition source) => source.wellFormedIn model scope
  | .numeric (.baseYearDatePart year _ _) => model.baseYear == some year
  | .numeric (.temporalFieldPart source part) =>
      model.admitsTemporalComputationOperand scope source
        (part.admittedBy source model.hasBaseYear)
  | .numeric (.dateRangeBoundPart source _ part) =>
      model.admitsDeclarationIn scope source.id (·.policy.kind.surfaceKind == .dateRange) &&
        model.exposesDateRangeBoundPart source part
  | .numeric (.stringLength source) =>
      model.admitsDeclarationIn scope source.id (·.toStringValueField? == some source)
  | .numeric (.stringRange source start finish) =>
      validStringRange start finish &&
        model.admitsDeclarationIn scope source.id (·.toStringValueField? == some source)
  | .numeric (.fieldValueAsNumber source) =>
      match model.certifiedFieldValueAsNumberDeclaration? source with
      | some declaration => declaration.repetitionBoundBy scope
      | none => false
  | .numeric (.dateDifference unit left right) =>
      let admitted : ResolvedDateDifferenceOperand → Bool
        | .field source =>
            model.admitsTemporalComputationOperand scope source
              (unit.admittedBy model.hasBaseYear source.components)
        | .literal source year => source.admittedIn model year
        | .baseYear year _ => model.baseYear == some year
        | .today profile => ModelZone.ConcreteProfile.ofId? model.timeZoneId == some profile
      admitted left && admitted right &&
        unit.compatible model.hasBaseYear left.components right.components
  | .numeric (.dateTimeDifference unit left right) =>
      let admitted : FlatTemporalOperand → Bool
        | .fieldValue source =>
            model.admitsTemporalComputationOperand scope source
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
            model.admitsTemporalComputationOperand scope source
              (CalendarDayDifference.admittedBy source.components)
        | .literal source year => source.admittedIn model year
        | .baseYear year _ => model.baseYear == some year
        | .today profile => ModelZone.ConcreteProfile.ofId? model.timeZoneId == some profile
      ModelZone.ConcreteProfile.ofId? model.timeZoneId == some profile &&
        admitted left && admitted right &&
        CalendarDayDifference.yearCompatible model.hasBaseYear
          left.components right.components
  | .numeric (.aggregate _ source) => source.bindingScopes.all (·.isPrefixOf scope)
  | .numeric (.filledGroupCount groups) =>
      1 < groups.length &&
        (ResolvedGroupReferences.firstOverlap? groups).isNone &&
        groups.all fun reference =>
          model.hasGroupPath reference.path &&
            reference.origin == .path &&
            (model.repeatableScopeForGroupPath reference.path).all scope.contains

/-- Whether the target is a model Number declaration. Its repeatable scope is the operation's reading
scope, so a scalar executor asks `readingScope` separately. -/
def FlatModel.admitsNumericComputationTarget
    (model : FlatModel) (target : FlatNumberField) : Bool :=
  match model.lookupUniqueId target.id with
  | .ok declaration => declaration.toNumberField? == some target
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
  | .indexed source => NumericScaleSummary.field source.field.info.scale
  | .indexedString source => NumericScaleSummary.field source.projection.scale
  | .firstFilled source => source.scaleSummary
  | .temporalExpression _ | .tokenDistinctCount _ | .temporalDistinctCount _
  | .valueCount _ _ | .filledFieldCount _ => NumericScaleSummary.field 0
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

def CheckedNumericComputationAtom.referencesWith
    (model : FlatModel) (field : FieldId)
    (filterReads : CorrelatedHaving → Bool) :
    CheckedNumericComputationAtom model → Bool
  | .indexed source => source.toCheckedSemanticIndexSource.referencesField field
  | .indexedString source => source.referencesField field
  | .filledFieldCount source => source.referencesField field (fun having _ => filterReads having)
  | .firstFilled source => source.referencesField field (fun having _ => filterReads having)
  | .valueCount _ source => source.referencesField field (fun having _ => filterReads having)
  | .tokenDistinctCount source => source.referencesField field (fun having _ => filterReads having)
  | .temporalExpression source => source.referencesWith field filterReads
  | .temporalDistinctCount run => run.source.referencesField field (fun having _ => filterReads having)
  | .tokenValueCount source => source.referencesField field (fun having _ => filterReads having)
  | .booleanValueCount source => source.referencesField field (fun having _ => filterReads having)
  | .sumOfProducts source =>
      source.referencesField field
  | .filledGroupCountMixed operands =>
      operands.any fun operand => operand.referencesField model field
  | .numeric atom => atom.referencesFieldWith model field (·.referencesField field (fun having _ => filterReads having))

def CheckedNumericComputationAtom.references (model : FlatModel) (field : FieldId)
    (atom : CheckedNumericComputationAtom model) : Bool :=
  atom.referencesWith model field (·.referencesField field)

/-- A filter's complete read inventory does not imply an unconditional self-reference or producer edge (spec/09 §5). -/
def CheckedNumericComputationAtom.forbidsTarget (model : FlatModel) (field : FieldId)
    (atom : CheckedNumericComputationAtom model) : Bool :=
  atom.referencesWith model field (·.forbidsTarget field)

def CheckedNumericComputationAtom.requiresProducer (model : FlatModel) (consumer producer : FieldId)
    (protectedGroup : ResolvedGroupReference → Bool) (atom : CheckedNumericComputationAtom model) : Bool :=
  atom.referencesWith model producer (fun having => having.requiresProducer consumer producer protectedGroup)

def NumericComputationOperation.wellFormedBool
    (operation : NumericComputationOperation model) : Bool :=
  model.admitsNumericComputationTarget operation.target &&
    operation.expression.allAtoms (model.admitsNumericComputationOperand operation.readingScope) &&
    !operation.expression.anyAtom
      (CheckedNumericComputationAtom.forbidsTarget model operation.target.id) &&
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
  bandedRounding : Option ComputationRoundingMode := none

/-- The targets one elaboration admits. A fixed scope admits a nonrepeatable target, which the scalar
executors write at the empty path; a row scope admits a repeatable one, which the repeatable plan runs
at every row. A consumer names the scope its executor addresses, so a fixed executor never receives a
row target. -/
inductive ComputationTargetScope where
  | fixed
  | row
  deriving Repr, DecidableEq

/-- The target's declaration for its scope. A fixed scope refuses a repeatable target as the carrier's
boundary, claiming no class. A row scope requires a repeatable target placed as every repeatable
computation target is, and asks that placement ahead of the copy comparison: a String copied into a row
target outside the declaring group draws the placement class alone
([checkpoint](../../../docs/sources/computation-scheduling-probes.md#src-row-target-boundary)). -/
private def FlatModel.lookupNumericComputationTarget (model : FlatModel)
    (targetScope : ComputationTargetScope) (declaringGroup : GroupPath) (target : FieldId) :
    Except NumericComputationElabError FlatFieldDecl :=
  match targetScope with
  | .fixed => (model.resolveNonrepeatableDeclarationById target).mapError .targetResolve
  | .row => (·.declaration) <$>
      (checkAddressedRepeatableTarget model declaringGroup target).mapError .repeatableTarget

/-- The Number target and the group it lies in, which decides a per-row read's class. -/
private def FlatFieldDecl.numericComputationTarget (declaration : FlatFieldDecl) :
    Except NumericComputationElabError (FlatNumberField × GroupPath) :=
  match declaration.toNumberField? with
  | some field => pure (field, declaration.groupPath)
  | none => throw (.targetNotNumber declaration.id)

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
    (model.resolveComputationOperandUnchecked declaringGroup targetGroup reference).mapError .resolve
  match declaration.toTemporalField? with
  | some field =>
      if accepts field then pure field
      else throw (.incompatibleTemporalSource declaration.path)
  | none => throw (.incompatibleTemporalSource declaration.path)

/-- Refuse an operand that reads per row, for the atoms that are not entity lists: the product
    aggregate and the group count. Each scope lists the repeatable levels one operand leaves for its
    evaluation to bind, and the first that holds a level the target's scope does not hold is refused
    with the class `UnboundOperandLevel` selects. An entity list asks the same question list-wide
    inside its shape, ahead of its duplicate scans
    ([checkpoint](../../../docs/sources/group-list-and-capacity-probes.md#src-computation-star-binding-gate)). -/
def FlatModel.requireOperandLevelsBound (model : FlatModel)
    (declaringGroup targetGroup : GroupPath) (scopes : List (List RepeatableLevel)) :
    Except NumericComputationElabError Unit :=
  match model.firstUnboundComputationLevel? declaringGroup targetGroup scopes with
  | none => pure ()
  | some unbound => throw (.unboundOperandLevel unbound)

def FlatModel.elaborateNumericComputationAtom
    (model : FlatModel) (declaringGroup targetGroup : GroupPath) :
    SurfaceNumericComputationAtom →
      Except NumericComputationElabError (CheckedNumericComputationAtom model)
    | .indexedString source operation =>
        (elaborateIndexedStringNumericSource model declaringGroup source operation
        (some (model.repeatableScopeForGroupPath targetGroup))).map .indexedString |>.mapError .indexedString
    | .indexed source =>
        (elaborateNumericSemanticIndexSource model declaringGroup source
          (some (model.repeatableScopeForGroupPath targetGroup))).map .indexed |>.mapError .semanticIndex
    | .temporalExpression source =>
        (elaborateTemporalNumericOperation model declaringGroup source (some targetGroup)).map .temporalExpression
          |>.mapError .temporalExpression
    | .filledFieldCount source =>
        (elaborateComputationFieldFillList model declaringGroup targetGroup source .count).map .filledFieldCount
          |>.mapError .fieldFill
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
    | .tokenEntityValueCount expected source => do
        let checked ←
          (elaborateTokenEntityValueCountSource model declaringGroup expected source
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
        match checked with
        | .row source =>
            model.requireOperandLevelsBound declaringGroup targetGroup
              [source.left.source.bindingScope, source.right.source.bindingScope]
        | .selected _ => pure ()
        pure (.sumOfProducts checked)
    | .numeric (.field reference) => do
        let declaration ←
          (model.resolveComputationFieldValueRead declaringGroup targetGroup reference).mapError .resolve
        if declaration.toNumberField?.isSome then
          pure (.numeric (.field declaration))
        else
          -- The operand typing refuses a non-Number field first; this is the resolver's own
          -- fail-closed answer for a caller that skips it.
          throw (.operandNotNumber declaration.path)
    | .numeric .baseYear =>
        match model.baseYear with
        | some year => pure (.numeric (.baseYear year))
        | none => throw .baseYearNotDeclared
    | .numeric (.currentRepetition path) => do
        -- A fixed target binds no level, so its group must be fixed; a row target's scope binds the
        -- coordinate of every group it holds.
        let scope := model.repeatableScopeForGroupPath targetGroup
        if scope.isEmpty then
          let reference ← model.resolveFixedGroupReference declaringGroup (.path path)
            |>.mapError .currentRepetitionSource
          pure (.numeric (.fixedCurrentRepetition reference))
        else
          (.numeric ·) <$> (model.resolveNumericCurrentRepetition declaringGroup scope path).mapError
            .currentRepetitionSource
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
          | .literal source =>
              if source.valid then pure (.literal source model.baseYearOrDefault)
              else throw .incompatibleDateDifference
          | .baseYear source =>
              match model.baseYear with
              | some year => pure (.baseYear year source)
              | none => throw .baseYearNotDeclared
          | .now => throw .incompatibleDateDifference
          | .today => match ModelZone.ConcreteProfile.ofId? model.timeZoneId with
              | some profile => pure (.today profile)
              | none => throw (.unsupportedCalendarProfile model.timeZoneId)
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
          | .baseYear _ | .literal _ | .today => throw .incompatibleDateDifference
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
          | .literal source =>
              if source.valid then pure (.literal source model.baseYearOrDefault)
              else throw .incompatibleDateDifference
          | .baseYear source =>
              match model.baseYear with
              | some year => pure (.baseYear year source)
              | none => throw .baseYearNotDeclared
          | .now => throw .incompatibleDateDifference
          | .today => match ModelZone.ConcreteProfile.ofId? model.timeZoneId with
              | some profile => pure (.today profile)
              | none => throw (.unsupportedCalendarProfile model.timeZoneId)
        let resolvedLeft ← resolveOperand left
        let resolvedRight ← resolveOperand right
        if CalendarDayDifference.yearCompatible model.hasBaseYear
            resolvedLeft.components resolvedRight.components then
          pure (.numeric
            (.dayDifference profile resolvedLeft resolvedRight))
        else
          throw .incompatibleDateDifference
    | .numeric (.aggregate .distinctCount source) => do
        match ← (elaborateDistinctCountSource model declaringGroup source
            (some targetGroup)).mapError .aggregate with
        | .number checked => pure (.numeric (.aggregate .distinctCount checked))
        | .token checked => pure (.tokenDistinctCount checked)
        | .temporal run => pure (.temporalDistinctCount run)
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
                    -- ([checkpoint](../../../docs/sources/group-list-and-capacity-probes.md#src-ancestor-starred-group-count-computation)).
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

private def FlatModel.resolveNumericComputationAtoms
    (model : FlatModel) (declaringGroup targetGroup : GroupPath)
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom) :
    Except NumericComputationElabError
      (AuthoredNumericExpr (CheckedNumericComputationAtom model)) :=
  expression.mapM (model.elaborateNumericComputationAtom declaringGroup targetGroup)

/-- The type one operand contributes to the operation's typing walk: a field read by its declaration,
and every other operand, once it elaborates, a Number. -/
def FlatModel.numericComputationAtomType
    (model : FlatModel) (declaringGroup targetGroup : GroupPath) :
    SurfaceNumericComputationAtom → Except NumericComputationElabError NumericOperandType
  | .numeric (.field reference) => do
      let declaration ←
        (model.resolveComputationFieldValueRead declaringGroup targetGroup reference).mapError .resolve
      pure (NumericOperandType.ofDeclaration declaration)
  | atom => (model.elaborateNumericComputationAtom declaringGroup targetGroup atom).map
      fun checked => .number checked.numericScaleSummary

/-- Check the operation's nodes in post-order, typing and then each node's authoring gates, and refuse
it at the first failing node, or where its well-typed result is not a Number, ahead of the scale rule
and the target's read
([checkpoint](../../../docs/sources/computation-placement-and-constant-probes.md#src-number-operation-node-gates)). -/
def FlatModel.checkNumericOperationNodes
    (model : FlatModel) (declaringGroup targetGroup : GroupPath)
    (expression : AuthoredNumericExpr SurfaceNumericComputationAtom) :
    Except NumericComputationElabError Unit :=
  match A12Kernel.checkNumericOperationNodes (model.numericComputationAtomType declaringGroup targetGroup)
      expression with
  | .error (.operand error) => throw error
  | .error (.node diagnostic) => throw (.operationNode diagnostic)
  | .ok (.number _) => pure ()
  | .ok result => throw (.operationNode result.numberTargetDiagnostic?)

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
    (target : FlatFieldDecl) :
    AuthoredNumericExpr SurfaceNumericComputationAtom → Except NumericComputationElabError Unit
  | .atom (.numeric (.field reference)) => do
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
    (suppressExactScaleWarning : Bool := false)
    (targetScope : ComputationTargetScope := .fixed) :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation model) := do
  match hModel : model.validate with
  | .error error => throw (.invalidModel error)
  | .ok () => do
      let checkedDeclaringGroup ←
        certifyNumericComputationDeclaringGroup declaringGroup
      let declaration ←
        model.lookupNumericComputationTarget targetScope checkedDeclaringGroup.val targetField
      model.checkNumericCopyComparison checkedDeclaringGroup.val declaration expression
      let (target, targetGroup) ← declaration.numericComputationTarget
      model.checkNumericOperationNodes checkedDeclaringGroup.val targetGroup expression
      -- The node walk already elaborated every atom by this same function, a field through the same
      -- declaration read, so this pass refuses nothing new and only rebuilds the checked tree.
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
      -- ([checkpoint](../../../docs/sources/computation-scheduling-probes.md#src-join-operators-and-guards)).
      if resolved.anyAtom (CheckedNumericComputationAtom.forbidsTarget model targetField) then
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
