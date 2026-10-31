import A12Kernel.Elaboration.AddressedNumericLeaf

namespace A12Kernel

/-- The one scope rule every field-reading source atom answers to: the declaration must be
    model-owned, must not be the target itself, and must be bound by the target's repeatable scope.
    `certify` re-derives the atom's own payload from that declaration, which is what keeps a forged
    kind, component set, or conversion projection out of a checked operand. -/
def CheckedAddressedNumericTarget.admitsSourceField
    (target : CheckedAddressedNumericTarget model) (id : FieldId)
    (certify : FlatFieldDecl → Bool) : Bool :=
  match model.lookupUniqueId id with
  | .ok owned =>
      certify owned && id != target.targetField &&
        owned.repetitionBoundBy target.targetDeclaration.repeatableScope
  | .error _ => false

/-- One endpoint of a completed-period difference. A field endpoint answers exactly the scope rule
    above; literals and Base-Year endpoints read no cell and retain their model's completion year,
    so a forged anchor cannot enter a checked operand. The unit's own component gate is applied
    once over the pair rather than here, because its year position is satisfiable by the model's
    Base Year and that is a property of the pair's agreement, not of one endpoint. -/
def CheckedAddressedNumericTarget.admitsDateDifferenceEndpoint
    (target : CheckedAddressedNumericTarget model) :
    ResolvedDateDifferenceOperand FlatTemporalField clock → Bool
  | .field source =>
      target.admitsSourceField source.id fun owned => owned.toTemporalField? == some source
  | .literal source year => source.admittedIn model year
  | .baseYear year _ => model.baseYear == some year
  | .today _ | .now _ _ => false

/-- One endpoint of a sub-day difference. Only a field is admitted, because `Now` needs an evaluation
    world this carrier's row read does not carry and every other operand this type carries reads
    outside the row. The sub-day operand type has no Base-Year form, so unlike the completed-period
    endpoint there is no constant arm to certify. -/
def CheckedAddressedNumericTarget.admitsSubdayEndpoint
    (target : CheckedAddressedNumericTarget model) : FlatTemporalOperand → Bool
  | .fieldValue source =>
      target.admitsSourceField source.id fun owned => owned.toTemporalField? == some source
  | _ => false

/-- Source admission retains model-owned fields and structural paths separately. Computation row
    bindings come from the checked target; scalar-only operations keep their existing owners.

    **Mixing with a repetition operand does not narrow the source set.** Every numeric source kind a
    repeatable Number target admits alone is admitted beside `CurrentRepetition`, measured against
    the Kernel on `BaseYear`, `Length`, and `YearFromDate` in both positions, with the
    `FieldValueAsNumber` String/Enumeration pair separating an operand-kind refusal from a mixing
    one ([checkpoint](../../docs/sources/group-and-iteration-probes.md#src-repetition-numeric-source-kinds)).
    The scope rule above is therefore the only additional gate this carrier imposes, and all three
    difference families apply it to each of their two endpoints. Aggregates and group counts
    stay outside: each carries a group operand and a scope of its own that this rule does not
    reach, and a group operand naming the target's own repeatable group is refused by the Kernel's
    calculated-field self-reference gate rather than by anything here. -/
def CheckedAddressedNumericTarget.admitsRepetitionOperand
    (target : CheckedAddressedNumericTarget model) : NumericComputationAtom → Bool
  | .field declaration =>
      match model.lookupUniqueId declaration.id with
      | .ok owned => owned == declaration && declaration.toNumberField?.isSome &&
          declaration.id != target.targetField &&
          declaration.repetitionBoundBy target.targetDeclaration.repeatableScope
      | .error _ => false
  | .fixedCurrentRepetition reference => reference.scalarRepetitionWellFormedBool model
  | .boundCurrentRepetition source =>
      source.wellFormedIn model target.targetDeclaration.repeatableScope
  -- The model's own Base Year reads no cell, so neither constant carries a scope to bind.
  | .baseYear _ => true
  | .baseYearDatePart _ _ _ => true
  | .stringLength source =>
      target.admitsSourceField source.id fun owned => owned.toStringValueField? == some source
  | .stringRange source start finish =>
      validStringRange start finish &&
        target.admitsSourceField source.id fun owned => owned.toStringValueField? == some source
  | .dateRangeBoundPart source _ _ =>
      target.admitsSourceField source.id fun owned => owned.toDateRangeField? == some source
  | .temporalFieldPart source part format =>
      target.admitsSourceField source.id fun _ =>
        model.admitsTemporalNumericPart source part format
  | .fieldValueAsNumber source =>
      match model.certifiedFieldValueAsNumberDeclaration? source with
      | some owned =>
          owned.id != target.targetField &&
            owned.repetitionBoundBy target.targetDeclaration.repeatableScope
      | none => false
  | .dateDifference unit left right =>
      DateDifferenceUnit.compatible unit model.baseYear.isSome left.components right.components &&
        target.admitsDateDifferenceEndpoint left && target.admitsDateDifferenceEndpoint right
  -- The profile is certified against the model's own zone, so a forged calendar cannot ride in on an
  -- otherwise admissible operand pair.
  | .dayDifference profile left right =>
      ModelZone.ConcreteProfile.ofId? model.timeZoneId == some profile &&
        CalendarDayDifference.admittedBy left.components &&
        CalendarDayDifference.admittedBy right.components &&
        CalendarDayDifference.yearCompatible model.baseYear.isSome
          left.components right.components &&
        target.admitsDateDifferenceEndpoint left && target.admitsDateDifferenceEndpoint right
  | .dateTimeDifference unit left right =>
      match left.dateTimeDifferenceComponents?, right.dateTimeDifferenceComponents? with
      | some leftComponents, some rightComponents =>
          DateTimeSubdayUnit.compatible unit leftComponents rightComponents &&
            target.admitsSubdayEndpoint left && target.admitsSubdayEndpoint right
      | _, _ => false
  -- A direct field list answers the same scope rule one field answers, member by member. The
  -- freedom a starred aggregate operand has from the target's scope does not apply here, because
  -- this payload carries no star: the Kernel refuses an unstarred read of a disjoint repeatable
  -- group `MVK_NO_WILDCARD` and admits a nonrepeatable one, which is exactly what the shared rule
  -- decides, since an empty repeatable scope is bound by any scope. The two list gates are the
  -- family's own and carry their own classes.
  | .aggregate _ source =>
      source.hasMultipleFields && source.hasUniqueFields &&
        source.fields.all fun field =>
          target.admitsSourceField field.id fun owned => owned.toNumberField? == some field
  | _ => false

abbrev AddressedRepetitionOperand (target : CheckedAddressedNumericTarget model) :=
  { atom : NumericComputationAtom // target.admitsRepetitionOperand atom = true }

private def hasRepetition (expression : AuthoredNumericExpr (AddressedRepetitionOperand target)) : Bool :=
  expression.anyAtom fun atom => match atom.val with
    | .fixedCurrentRepetition _ | .boundCurrentRepetition _ => true
    | _ => false

private def repetitionOperandSummary (atom : AddressedRepetitionOperand target) : NumericScaleSummary :=
  atom.val.summary FlatFieldDecl.numericScaleSummary

inductive AddressedRepetitionComputationElabError where
  | target (cause : AddressedNumericPlacementElabError)
  | source (cause : ResolveError)
  | repetition (cause : FixedGroupReferenceError)
  | unsupportedExpression
  /-- A `BaseYear` operand in a model declaring none. Kept distinct from `unsupportedExpression`
  because the remedy differs — declare the model's Base Year, rather than rewrite the expression —
  and because this is an elaboration refusal only: which class the Kernel draws for that model was
  not measured, so no diagnostic is claimed here. -/
  | baseYearNotDeclared
  | authoring (result : NumericAuthoringCheck)
  | operationScaleMismatch (targetScale : Nat) (operation : NumericScaleSummary)
  deriving Repr, DecidableEq

/-- One repetition-bearing Number expression. Each atom is certified against the same target;
    the shared expression tree retains authored grouping, literal scale, and evaluation lowering. -/
structure CheckedAddressedRepetitionComputation (model : FlatModel) where
  private mk ::
  target : CheckedAddressedNumericTarget model
  expression : AuthoredNumericExpr (AddressedRepetitionOperand target)
  suppressExactScaleWarning : Bool
  expressionAdmitted : expression.isAdmittedResolvedNumericOperation = true
  authoringAdmitted : expression.numericOperationAuthoringCheck = .accepted
  repetitionPresent : hasRepetition expression = true
  scaleAdmitted : (expression.summary? repetitionOperandSummary).any
    (exactNumericScaleComparisonAllowedWithSuppression suppressExactScaleWarning
      target.targetPolicy.info.staticSummary) = true

/-- Resolve one authored difference endpoint against the target's own declaring group. `Now` and `Today` are
    refused rather than resolved: they need an evaluation world this carrier's row read does not
    carry, and a structural refusal keeps that missing input out of the value domain. -/
private def resolveDateDifferenceEndpoint (target : CheckedAddressedNumericTarget model)
    (surface : SurfaceDateDifferenceOperand) :
    Except AddressedRepetitionComputationElabError (ResolvedDateDifferenceOperand FlatTemporalField clock) := do
  match surface with
  | .field reference => do
      let declaration ← model.resolveFieldDeclarationUnchecked target.declaringGroup reference
        |>.mapError .source
      match declaration.toTemporalField? with
      | some field => pure (.field field)
      | none => throw .unsupportedExpression
  | .literal source =>
      if source.valid then pure (.literal source model.baseYearOrDefault)
      else throw .unsupportedExpression
  | .baseYear source =>
      match model.baseYear with
      | some year => pure (.baseYear year source)
      | none => throw .baseYearNotDeclared
  | .now | .today => throw .unsupportedExpression

/-- Resolve one authored sub-day endpoint. Base Year is not a legal operand of this family and `Now`
    needs an evaluation world, so only a field resolves here. -/
private def resolveSubdayEndpoint (target : CheckedAddressedNumericTarget model)
    (surface : SurfaceDateDifferenceOperand) :
    Except AddressedRepetitionComputationElabError FlatTemporalOperand := do
  match surface with
  | .field reference => do
      let declaration ← model.resolveFieldDeclarationUnchecked target.declaringGroup reference
        |>.mapError .source
      match declaration.toTemporalField? with
      | some field => pure (.fieldValue field)
      | none => throw .unsupportedExpression
  | .baseYear _ | .now | .today | .literal _ => throw .unsupportedExpression

/-- Resolve a field the target's declaring group names, asking the field read's group gate from the
    target's scope, for a bracket read and an operator's field parameter ([checkpoint](../../docs/sources/field-value-read-probes.md#src-field-value-read-predictions)). -/
private def resolveRepetitionEntity (target : CheckedAddressedNumericTarget model)
    (reference : SurfaceFieldPath) :
    Except AddressedRepetitionComputationElabError FlatFieldDecl :=
  model.resolveFieldDeclarationUnchecked target.declaringGroup reference |>.mapError fun cause =>
    .source (displaceGroupMiss cause
      (model.computationGroupRead target.declaringGroup target.targetDeclaration.groupPath reference))

private def resolveRepetitionOperand (target : CheckedAddressedNumericTarget model)
    (surface : SurfaceNumericAtom) :
    Except AddressedRepetitionComputationElabError (AddressedRepetitionOperand target) := do
  let atom ← match surface with
    | .field reference => do
        -- A bracket read: its value gates follow the group gate, ahead of the Number check.
        let declaration ← resolveRepetitionEntity target reference
        if let some refusal := declaration.fieldValueReadRefusal? then
          throw (.source refusal)
        pure (.field declaration)
    | .currentRepetition reference =>
        model.resolveNumericCurrentRepetition target.declaringGroup
          target.targetDeclaration.repeatableScope reference |>.mapError .repetition
    -- The widened kinds resolve against the target's own declaring group, which is what lets a
    -- source in the target's row elaborate here; the shared nonrepeatable scalar resolver refuses
    -- exactly that, so it is not reused. Admission below still applies the one scope rule.
    | .baseYear =>
        match model.baseYear with
        | some year => pure (.baseYear year)
        | none => throw .baseYearNotDeclared
    | .stringLength reference => do
        let declaration ← resolveRepetitionEntity target reference
        match declaration.toStringValueField? with
        | some field => pure (.stringLength field)
        | none => throw .unsupportedExpression
    | .stringRange reference start finish => do
        let declaration ← resolveRepetitionEntity target reference
        -- The interval rule is the shared one; suppression cannot widen it, so it is checked here
        -- rather than left to the target's scale gate.
        if validStringRange start finish then
          match declaration.toStringValueField? with
          | some field => pure (.stringRange field start finish)
          | none => throw .unsupportedExpression
        else throw .unsupportedExpression
    | .baseYearDatePart source part =>
        match model.baseYear with
        | some year => pure (.baseYearDatePart year source part)
        | none => throw .baseYearNotDeclared
    | .dateRangeBoundPart reference bound part => do
        let declaration ← resolveRepetitionEntity target reference
        match declaration.toDateRangeField? with
        | some field => pure (.dateRangeBoundPart field bound part)
        | none => throw .unsupportedExpression
    | .temporalFieldPart reference part => do
        let declaration ← model.resolveFieldDeclarationUnchecked target.declaringGroup reference
          |>.mapError .source
        match declaration.toTemporalField? with
        | some field => pure (.temporalFieldPart field part (model.temporalNumericPartialFormat field.id))
        | none => throw .unsupportedExpression
    | .fieldValueAsNumber source => do
        let declaration ← resolveRepetitionEntity target source.reference
        match declaration.resolveFieldValueAsNumberSource source.projectionRef with
        | .ok resolved => pure (.fieldValueAsNumber resolved)
        | .error _ => throw .unsupportedExpression
    | .aggregate op source => do
        let resolveNumber (reference : SurfaceFieldPath) :
            Except AddressedRepetitionComputationElabError FlatNumberField := do
          let declaration ← model.resolveFieldDeclarationUnchecked target.declaringGroup reference
            |>.mapError .source
          match declaration.toNumberField? with
          | some field => pure field
          | none => throw .unsupportedExpression
        let first ← resolveNumber source.first
        let rest ← source.rest.mapM resolveNumber
        pure (.aggregate op { first, rest })
    | .dateDifference unit left right => do
        let left ← resolveDateDifferenceEndpoint target left
        let right ← resolveDateDifferenceEndpoint target right
        pure (.dateDifference unit left right)
    | .dayDifference left right => do
        let profile ← match ModelZone.ConcreteProfile.ofId? model.timeZoneId with
          | some profile => pure profile
          | none => throw .unsupportedExpression
        let left ← resolveDateDifferenceEndpoint target left
        let right ← resolveDateDifferenceEndpoint target right
        pure (.dayDifference profile left right)
    | .dateTimeDifference unit left right => do
        let left ← resolveSubdayEndpoint target left
        let right ← resolveSubdayEndpoint target right
        pure (.dateTimeDifference unit left right)
    | _ => throw .unsupportedExpression
  if admitted : target.admitsRepetitionOperand atom = true then
    pure ⟨atom, admitted⟩
  else throw .unsupportedExpression

def checkAddressedRepetitionComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (expression : AuthoredNumericExpr SurfaceNumericAtom)
    (suppressExactScaleWarning : Bool := false) :
    Except AddressedRepetitionComputationElabError
      (CheckedAddressedRepetitionComputation model) := do
  let target ← checkAddressedNumericTarget model declaringGroup targetField |>.mapError .target
  let resolved ← expression.mapM (resolveRepetitionOperand target)
  if repetitionPresent : hasRepetition resolved = true then
    if expressionAdmitted : resolved.isAdmittedResolvedNumericOperation = true then
      match authoringAdmitted : resolved.numericOperationAuthoringCheck with
      | .accepted =>
          if scaleAdmitted : (resolved.summary? repetitionOperandSummary).any
              (exactNumericScaleComparisonAllowedWithSuppression suppressExactScaleWarning
                target.targetPolicy.info.staticSummary) = true then
            pure {
              target, expression := resolved, suppressExactScaleWarning
              repetitionPresent, expressionAdmitted, authoringAdmitted, scaleAdmitted }
          else
            match resolved.summary? repetitionOperandSummary with
            | some summary => throw (.operationScaleMismatch target.targetPolicy.info.scale summary)
            | none => throw .unsupportedExpression
      | result => throw (.authoring result)
    else throw .unsupportedExpression
  else throw .unsupportedExpression

/-- Read every cell an atom addresses in this row, each at its own declaration's scope, and then
    evaluate the atom through the shared resolved evaluator. The reads happen **before** evaluation
    so that one operand's row address is resolved from its own declaration rather than from a
    neighbour's, and the context then answers by identity over the retained association: the shared
    evaluator asks only for the ids the atom names, so every id it can ask is present and the
    fallback stands for nothing reachable.

    The association is keyed by id, so an atom that names one field twice reads it once and cannot
    see two different cells for it. -/
private def readAddressedAtom (model : FlatModel) (atom : NumericComputationAtom)
    (fields : List FieldId)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) (environment : Env) :
    Except AddressedNumericLeafFault NumericComputationResult := do
  let cells ← fields.mapM fun id =>
    match model.lookupUniqueId id with
    | .error _ => .error (.evaluation (.fieldKindMismatch id))
    | .ok declaration => do
        let path ← environment.pathForScope declaration.repeatableScope |>.mapError .environment
        let cell ← read { field := id, path } |>.mapError .sourceRead
        pure (id, cell)
  let absent : CheckedCell := { rawPresent := false, parsed := none, findings := [] }
  let context : ScalarComputationContext :=
    { read := fun id => (cells.find? (·.1 == id)).elim absent (·.2) }
  context.readNumericComputationAtom atom |>.mapError .evaluation

/-- The field a difference endpoint addresses, or none for a constant. -/
private def ResolvedDateDifferenceOperand.endpointField? :
    ResolvedDateDifferenceOperand FlatTemporalField clock → Option FieldId
  | .field source => some source.id
  | .baseYear _ _ | .literal _ _ | .today _ | .now _ _ => none

/-- The same projection for a sub-day endpoint. Only the field form is admitted here, so every other
    shape reports no field and would read nothing even if one were reachable. -/
private def FlatTemporalOperand.subdayEndpointField? : FlatTemporalOperand → Option FieldId
  | .fieldValue source => some source.id
  | _ => none

/-- Structural coordinates and addressed fields reuse one ordered arithmetic evaluator while
    preserving the addressed source's own error domain. Rejected atom kinds are unconstructible. -/
def AddressedRepetitionOperand.readAt {model : FlatModel}
    {target : CheckedAddressedNumericTarget model} (source : AddressedRepetitionOperand target)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) (environment : Env) :
    Except AddressedNumericLeafFault NumericComputationResult := by
  rcases source with ⟨atom, admitted⟩
  cases atom
  case field declaration =>
    exact do
      let path ← environment.pathForScope declaration.repeatableScope |>.mapError .environment
      let cell ← read { field := declaration.id, path } |>.mapError .sourceRead
      let context : ScalarComputationContext := { read := fun _ => cell }
      context.readNumeric declaration |>.mapError .evaluation
  case fixedCurrentRepetition reference => exact .ok (.value 1)
  case boundCurrentRepetition source =>
    exact (source.coordinateAt environment).map (fun coordinate => .value coordinate)
      |>.mapError .environment
  -- Both Base Year constants are model state, so they read no cell and cannot fail in a row.
  case baseYear year => exact .ok (.value year)
  case baseYearDatePart year source part =>
    exact .ok (.value (baseYearDateSourceNumericPart year source part))
  case stringRange source start finish =>
    exact readAddressedAtom model (.stringRange source start finish) [source.id] read environment
  case dateRangeBoundPart source bound part =>
    exact readAddressedAtom model (.dateRangeBoundPart source bound part) [source.id] read environment
  case stringLength source =>
    exact readAddressedAtom model (.stringLength source) [source.id] read environment
  case temporalFieldPart source part format =>
    exact readAddressedAtom model (.temporalFieldPart source part format) [source.id] read environment
  case fieldValueAsNumber source =>
    exact readAddressedAtom model (.fieldValueAsNumber source) [source.fieldId] read environment
  case dateDifference unit left right =>
    exact readAddressedAtom model (.dateDifference unit left right)
      ([left.endpointField?, right.endpointField?].filterMap id) read environment
  case dayDifference profile left right =>
    exact readAddressedAtom model (.dayDifference profile left right)
      ([left.endpointField?, right.endpointField?].filterMap id) read environment
  case dateTimeDifference unit left right =>
    exact readAddressedAtom model (.dateTimeDifference unit left right)
      ([left.subdayEndpointField?, right.subdayEndpointField?].filterMap id) read environment
  case aggregate op source =>
    exact readAddressedAtom model (.aggregate op source) (source.fields.map (·.id)) read environment
  all_goals simp [CheckedAddressedNumericTarget.admitsRepetitionOperand] at admitted

namespace CheckedAddressedRepetitionComputation

/-- Whether this operation reads a field. It answers through the shared atom walk rather than a
    local match, because a local one silently reported `false` for every source kind added after it
    was written — a dependency query that forgets a kind fails nothing and hands a consumer a
    missing edge as a fact. -/
def referencesField (operation : CheckedAddressedRepetitionComputation model)
    (field : FieldId) : Bool :=
  operation.expression.anyAtom fun atom => atom.val.referencesField model field

def evaluateAtEnvironmentWithRead
    (operation : CheckedAddressedRepetitionComputation model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) (environment : Env) :
    Except AddressedNumericLeafFault NumericComputationResult :=
  operation.expression.lowerForEvaluation.evalComputation (·.readAt read environment)

def executeWithRead (operation : CheckedAddressedRepetitionComputation model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except AddressedNumericLeafFault (List (SourcedNumericTargetOutcome CellAddr)) :=
  if operation.suppressExactScaleWarning then
    operation.target.executeAtEnvironmentScaleWarningSuppressed input
      (operation.evaluateAtEnvironmentWithRead read)
  else
    operation.target.executeAtEnvironment input (operation.evaluateAtEnvironmentWithRead read)

def execute (operation : CheckedAddressedRepetitionComputation model)
    (input : CheckedDocument model) :
    Except AddressedNumericLeafFault (List (SourcedNumericTargetOutcome CellAddr)) :=
  operation.executeWithRead input input.read

end CheckedAddressedRepetitionComputation
end A12Kernel
