import A12Kernel.Elaboration.NumericComputation.Core
import A12Kernel.Semantics.ComputationSelfValidation

/-! # Checked numeric-computation evaluation and fault projection -/

namespace A12Kernel

def NumericOperand.toComputationResult : NumericOperand → NumericComputationResult
  | .value amount _ => .value amount
  | .unknown cause => .poison cause

private def CheckedFieldFillOperand.countComputation (operand : CheckedFieldFillOperand model)
    (context : ScalarComputationContext) (filterRead? : Option (Env → FieldId → CheckedCell))
    (indexColumn? : Option SemanticIndexColumnReader) :
    Except NumericComputationFault (Except FormalCause Nat) := do
  match operand with
  | .indexed source => do
      let some readColumn := indexColumn? | throw .repeatableContextRequired
      let column ← readColumn source.group source.targetDeclaration.id context.row
        |>.mapError .indexSelection
      let key ← source.observeCurrentKey .computation context.read context.storedText
        |>.mapError (NumericComputationFault.indexSelection ∘ CheckedAddressingError.semanticIndex)
      return match column.lookupObservationForIndex .computation source.numericIndex key with
        | .value _ => .ok 1
        | .empty => .ok 0
        | .unknown cause | .poison cause => .error cause
  | .star source =>
      if let some filter := source.filter then
        let some addressed := context.addressed
          | throw (.guardBinding (.fieldFill .contextRequired))
        let resolved ← (source.source.path.resolveInCapacity addressed.document context.row).mapError
          (NumericComputationFault.guardBinding ∘ ComputationConditionError.fieldFill ∘ ComputationFillError.addressing)
        let result ← (filter.condition.scanComputationResolving
          { read := fun row field => pure ((filterRead?.getD addressed.read) row field)
            bindingError := fun error => ComputationFillError.addressing error.toStarAddressingError }
          context.row (fun count row => pure (match observeCell .computation
              (addressed.read row source.source.declaration.id) with
            | .value _ => Sum.inl (count + 1)
            | .empty => Sum.inl count
            | .unknown cause | .poison cause => Sum.inr cause))
          resolved.environments 0).mapError
          (NumericComputationFault.guardBinding ∘ ComputationConditionError.fieldFill)
        return match result with
          | .exhausted count => .ok count
          | .terminated cause | .poison cause => .error cause
  | _ => pure ()
  let sources ← (CheckedFieldFillList.computationSources { operands := [operand] }).mapError
    NumericComputationFault.fieldFillSource
  let slots ← (sources.mapM fun (source : ComputationFillSource) =>
    source.slots context.read context.row context.addressed).mapError
    (NumericComputationFault.guardBinding ∘ ComputationConditionError.fieldFill)
  pure (numberOfFilledFieldsForComputation slots.flatten)

/-- Each filtered operand reuses the computation iterator's lookahead and poison timing
(spec/09 §5). Finish its selected count before reaching the next authored operand. -/
def CheckedFieldFillList.evaluateComputationCount (source : CheckedFieldFillList model)
    (context : ScalarComputationContext) (filterRead? : Option (Env → FieldId → CheckedCell) := none)
    (indexColumn? : Option SemanticIndexColumnReader := none) :
    Except NumericComputationFault NumericComputationResult := do
  let mut total := 0
  for operand in source.operands do
    match ← operand.countComputation context filterRead? indexColumn? with
    | .error cause => return .poison cause
    | .ok count => total := total + count
  pure (.value total)

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

/-- Read either direct temporal component family through one computation-phase empty/value/poison
boundary. A value is held by its format's family, not its declared kind, as every flat temporal read
tests it ([`FlatTemporalField.holdsValue`](../../Semantics/FlatValidation.lean)). -/
def readTemporalNumeric (context : ScalarComputationContext)
    (field : FlatTemporalField) (project : TemporalValue → Option Rat) :
    Except NumericComputationFault NumericComputationResult :=
  match observeCell .computation (context.read field.id) with
  | .empty => pure (.value 0)
  | .value (.temporal value) =>
      if !field.holdsValue value then
        throw (.fieldKindMismatch field.id)
      else
        match project value with
        | some amount => pure (.value amount)
        | none => throw (.fieldKindMismatch field.id)
  | .value _ => throw (.fieldKindMismatch field.id)
  | .unknown cause | .poison cause => pure (.poison cause)

/-- Read one certified DateRange endpoint's numeric Date component in computation phase. The endpoint
owner performs both the profile selection and the component extraction, so a computed component and a
validating one cannot disagree about which runtime carrier is exact. Empty substitutes zero and
formal unavailability propagates, exactly as every other component read in this family does. -/
def readDateRangeBoundNumeric (context : ScalarComputationContext)
    (field : FlatDateRangeField) (bound : DateRangeBound)
    (part : DateNumericPart) :
    Except NumericComputationFault NumericComputationResult := do
  let observed ←
    (CheckedDateRangeSource.observeRange field.id .computation
      (context.read field.id)).mapError fun _ => .fieldKindMismatch field.id
  match observed with
  | .empty => pure (.value 0)
  | .value value => pure (.value (part.extract (value.selectBoundParts bound)))
  | .unknown cause | .poison cause => pure (.poison cause)

def readDateDifferenceOperand (context : ScalarComputationContext) :
    ResolvedDateDifferenceOperand → DateDifferenceOperand
  | .literal source year => .value (source.parts year)
  | .field source => DateDifferenceOperand.ofObservation
      (observeCell .computation (context.read source.id))
  | .baseYear year source => .value (source.parts year)

def readCalendarDayDifferenceOperand (context : ScalarComputationContext)
    (profile : ModelZone.ConcreteProfile) :
    ResolvedDateDifferenceOperand → CalendarDayDifferenceOperand
  | .literal source year => CalendarDayDifferenceOperand.ofParts profile (source.parts year)
  | .field source => CalendarDayDifferenceOperand.ofObservation
      (observeCell .computation (context.read source.id))
  | .baseYear year source =>
      CalendarDayDifferenceOperand.ofBaseYear profile year source

/-- Resolve one checked sub-day operand through computation-phase field reads or the explicit evaluation world. Unsupported temporal comparison shapes fail structurally rather than becoming field poison. -/
def readDateTimeDifferenceOperand (context : ScalarComputationContext) :
    FlatTemporalOperand →
      Except NumericComputationFault DateTimeDifferenceOperand
  | .fieldValue source =>
      pure (.ofObservation (observeCell .computation (context.read source.id)))
  | .nowValue =>
      match context.world with
      | some world => pure (.value world.now)
      | none => throw .worldRequired
  | _ => throw .unsupportedDateTimeDifferenceOperand

/-- Observe one fixed group's descendant cells in the computation arm.

The reads go through this same context, so the count observes the same cells the surrounding
computation observes; it deliberately interprets them differently, since a poisoned cell is
present here while an ordinary numeric read of it poisons the result. A group outside the
admitted scalar boundary refuses explicitly rather than observing as absent. The addressed
group-count route takes this step wherever it answers, which is what
`readGroupCountOperand_fixed_eq_scalarDescendants` turns into a statement about the two routes;
where it refuses, that route answers from row topology this context does not carry. -/
def readGroupDescendants (context : ScalarComputationContext) (model : FlatModel)
    (reference : ResolvedGroupReference) :
    Except NumericComputationFault (List CellObservation) :=
  match reference.computationDescendants? model with
  | none => throw (NumericComputationFault.unsupportedGroupCount reference.path)
  | some descendants =>
      pure (descendants.map fun declaration =>
        observeCell .computation (context.read declaration.id))

/-- Count one resolved fixed multi-group operand list in the computation arm, each group decided
by its own descendant observation. -/
def readFilledGroupCount (context : ScalarComputationContext) (model : FlatModel)
    (groups : List ResolvedGroupReference) :
    Except NumericComputationFault NumericComputationResult := do
  let observed ← groups.mapM (context.readGroupDescendants model)
  pure (.value (numberOfFilledGroupsForComputation observed))

/-- Share every non-aggregate computation atom branch while allowing the direct and addressed evaluators to supply their own aggregate projection and group-count projection. Group presence is supplied rather than shared because only a model-carrying caller can enumerate a group's descendants. -/
def readNumericComputationAtomWith
    (context : ScalarComputationContext)
    (readAggregate : NumericAggregateOp → Aggregate →
      Except NumericComputationFault NumericComputationResult)
    (readGroupCount : List ResolvedGroupReference →
      Except NumericComputationFault NumericComputationResult) :
    ResolvedNumericAtom FlatFieldDecl Aggregate →
      Except NumericComputationFault NumericComputationResult
  | .field declaration => context.readNumeric declaration
  | .baseYear year => pure (.value year)
  | .fixedCurrentRepetition _ => pure (.value 1)
  -- The row's own coordinate at the group's level, measured at a repeatable Number target
  -- ([checkpoint](../../../docs/sources/group-and-iteration-probes.md#src-repetition-source-kinds-runtime));
  -- a context whose row does not bind the group's scope has no coordinate to give.
  | .boundCurrentRepetition source =>
      match source.coordinateAt context.row with
      | .ok coordinate => pure (.value coordinate)
      | .error _ => throw .repeatableContextRequired
  | .baseYearDatePart year source part =>
      pure (.value (baseYearDateSourceNumericPart year source part))
  | .temporalFieldPart field part =>
      context.readTemporalNumeric field part.project?
  | .dateRangeBoundPart field bound part =>
      context.readDateRangeBoundNumeric field bound part
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
  | .dateTimeDifference unit left right => do
      let leftOperand ← context.readDateTimeDifferenceOperand left
      let rightOperand ← context.readDateTimeDifferenceOperand right
      pure ((DateTimeDifferenceOperand.evaluate unit
        leftOperand rightOperand).toComputationResult)
  | .dayDifference profile left right =>
      match CalendarDayDifferenceOperand.evaluate profile
          (context.readCalendarDayDifferenceOperand profile left)
          (context.readCalendarDayDifferenceOperand profile right) with
      | .error _ => throw .unsupportedDateCalendar
      | .ok operand => pure operand.toComputationResult
  | .aggregate op source => readAggregate op source
  | .filledGroupCount groups => readGroupCount groups

/-- Preserve the direct-only resolved evaluator used by low-level proofs and callers. It carries no model, so a group operand's descendants are unknowable here and the group count refuses. -/
def readNumericComputationAtom (context : ScalarComputationContext) :
    NumericComputationAtom →
      Except NumericComputationFault NumericComputationResult :=
  context.readNumericComputationAtomWith
    (fun op source =>
      pure ((source.evaluate op fun field =>
        observeCell .computation (context.read field)).toComputationResult))
    (fun _ => throw .groupCountNeedsModel)

/-- Numeric extraction consumes the temporal source's computation observation before discarding
validation-only fillability; formal poison and calendar faults remain distinct. -/
def readTemporalNumericExpression (context : ScalarComputationContext)
    (source : CheckedTemporalNumericExpression model) :
    Except NumericComputationFault NumericComputationResult := do
  let result ← match source.evalResult .computation {
      read := context.read, storedText := context.storedText, world := context.world } with
    | .ok result => pure result
    | .error .dateTimeLabelUnresolved => return .domainFailure
    | .error fault => throw (.temporalExpression fault)
  match result with
  | .ok (.value amount _) => pure (.value amount)
  | .ok .notEvaluated | .error .nonRelevant | .error .silentlyUnavailable => pure .domainFailure
  | .error (.formal cause) => pure (.poison cause)
  | .error .groupState => throw .unsupportedDateCalendar

/-- Evaluate a checked computation atom without a repeatable document only when its entity-list payload narrows exactly to direct fields. A repeatable operand fails explicitly rather than silently observing an empty synthetic document. -/
def readCheckedNumericComputationAtom (context : ScalarComputationContext) :
    CheckedNumericComputationAtom model →
      Except NumericComputationFault NumericComputationResult
  | .temporalPart source => context.readTemporalNumericExpression source
  | .filledFieldCount source => source.evaluateComputationCount context
  | .firstFilled source =>
      match source.evaluateDirectComputationFirstFilled? context.read with
      | some result => pure result.asComputationResult
      | none => throw .repeatableContextRequired
  | .valueCount expected source =>
      match source.evaluateDirectValueCountAt? expected .computation
          { read := context.read } with
      | some result => pure result.toComputationResult
      | none => throw .repeatableContextRequired
  | .tokenDistinctCount source => do
      if source.directFields?.isNone then throw .repeatableContextRequired
      (source.evaluateDistinctComputation { instantiatedRows := [], rawCells := fun _ => none } {} context.read (fun _ => context.read)
        (fun _ => context.read)).map NumericOperand.toComputationResult
          |>.mapError .repeatableAddressing
  | .temporalDistinctCount run => do
      if !run.source.isDirectOnly then throw .repeatableContextRequired
      (run.evaluateComputation { instantiatedRows := [], rawCells := fun _ => none } {} context.read (fun _ => context.read)
        (fun _ => context.read)).map NumericOperand.toComputationResult
          |>.mapError .repeatableAddressing
  | .tokenValueCount source =>
      match source.evaluateDirectAt? .computation context.read with
      | some result => pure result.toComputationResult
      | none => throw .repeatableContextRequired
  | .booleanValueCount source =>
      match source.evaluateDirectAt? .computation context.read with
      | some result => pure result.toComputationResult
      | none => throw .repeatableContextRequired
  | .sumOfProducts _ => throw .repeatableContextRequired
  -- A starred operand contributes an in-capacity row count, which this context cannot read:
  -- its whole input is `FieldId → CheckedCell`. The refusal is the same one a repeatable
  -- aggregate gets here, for the same reason, and it is correct rather than incomplete.
  | .filledGroupCountMixed _ => throw .repeatableContextRequired
  | .numeric source =>
      context.readNumericComputationAtomWith (Aggregate := CheckedNumberEntitySource model)
        (fun op aggregate =>
          match aggregate.directAggregateFields? with
          | some direct =>
              pure ((direct.evaluate op fun field =>
                observeCell .computation
                  (context.read field)).toComputationResult)
          | none => throw .repeatableContextRequired)
        (context.readFilledGroupCount model) source

end ScalarComputationContext

namespace NumericComputationEvaluationContext

/-- Read one instance of a fixed group whose own scope `environment` binds: its cells at that scope,
    and whether a repeatable descendant holds a row under that instance's address, decided by the
    shared `ResolvedComputationGroupSource`. -/
def readGroupInstanceAt (context : NumericComputationEvaluationContext) (model : FlatModel)
    (groupPath : GroupPath) (environment : Env) :
    Except NumericComputationFault (List CellObservation × Bool) := do
  (model.computationGroupSource groupPath).read context.document context.starRead environment
    |>.mapError (fun error => .repeatableAddressing error.toStarAddressingError)

/-- A fixed group-count operand's content, with the row constituent the scalar reader cannot express.

    Content has **two constituents and either suffices**: an admitted descendant cell outside every
    repeatable row, or an instantiated row in a repeatable descendant. Where the scalar reader
    answers, this takes exactly its extent and reads, so the routes agree there; only the shape it
    refuses reaches the second branch.

    The row constituent counts **any** instantiated row, over-limit ones included. That follows the
    recorded structural rule — an over-limit row stays in the physical topology and still supplies
    group content ([§7](../../../spec/07-repetition-and-iteration.md)) — rather than the starred
    count's in-capacity domain, which is a numeric evaluation domain and not a presence question.

    The choice is inherited rather than measured here, but the two accounts are **indistinguishable**
    on this carrier, so nothing observable rides on it. They differ only where a shell's rows are all
    over-limit, and the nearest repeatable descendant level cannot be in that state: the checked
    document rejects a gap in a row sequence, so a level holding any row holds row 1
    ([case](../../Conformance/CheckedDocument.lean)), and a declared repeatability is a positive
    integer, so row 1 is in capacity ([checkpoint](../../../docs/SOURCES.md#src-repeatability-domain-peer-measurement)).
    What remains is the enclosing binding, which the arm excludes separately when it is over-limit.
    This is a property of this project's own types rather than a Kernel observation, so it is
    provable and not measurable; it is unproved only because `CheckedDocument` checks the
    predecessor rule without retaining it as a certificate a proof could use. -/
def readGroupContent (context : NumericComputationEvaluationContext) (model : FlatModel)
    (reference : ResolvedGroupReference) :
    Except NumericComputationFault (List CellObservation × Bool) :=
  match reference.computationDescendants? model with
  | some descendants =>
      .ok (descendants.map (fun declaration =>
        observeCell .computation (context.scalar.read declaration.id)), false)
  | none =>
      if reference.boundInstanceOperand model then
        context.readGroupInstanceAt model reference.path context.outer
      else match reference.repeatableDescendantShape? model with
        | none => .error (NumericComputationFault.unsupportedGroupCount reference.path)
        | some repeatables =>
            .ok (((model.groupSubtreeFields reference.path).filter
                (·.repeatableScope.isEmpty)).map (fun declaration =>
                  observeCell .computation (context.scalar.read declaration.id)),
              repeatables.any fun group =>
                context.document.instantiatedRows.any fun row => row.group == group.level)

/-- Read a fixed group below a starred level once in each in-capacity environment of its starred
    ancestry, each instance exactly as `readGroupContent` reads a fixed operand's two constituents:
    its cells at that environment's own scope, and whether a repeatable descendant holds a row under
    that environment's address, decided by the shared `ResolvedComputationGroupSource`. An over-limit
    ancestor row supplies no environment, so its instance is not read
    ([checkpoint](../../../docs/SOURCES.md#src-ancestor-starred-group-count-computation)). -/
def readGroupInstances (context : NumericComputationEvaluationContext) (model : FlatModel)
    (source : CheckedStarredGroupPresenceSource model) :
    Except NumericComputationFault (List (List CellObservation × Bool)) := do
  let environments ← (source.inCapacityEnvironments context.document context.outer).mapError
    NumericComputationFault.repeatableAddressing
  environments.mapM (context.readGroupInstanceAt model source.groupPath)

/-- Read one group-count operand into its contribution.

    A **fixed** operand takes the same descendant extent and cell reads the scalar fixed-only reader
    takes wherever that reader answers, which is what keeps the two forms agreeing on any list they
    can both hold. Where it refuses for a repeatable descendant, this route answers instead, using
    the row constituent the scalar projection cannot express. A **starred** operand takes the
    in-capacity instantiated row count, the quantity this route carries the document topology for,
    and a fixed group below a star takes one fixed reading per in-capacity environment. -/
def readGroupCountOperand
    (context : NumericComputationEvaluationContext) (model : FlatModel) :
    CheckedGroupCountOperand model →
      Except NumericComputationFault GroupCountOperandReading
  | .fixed reference =>
      (context.readGroupContent model reference).map fun content =>
        .fixed content.1 content.2
  | .starred source =>
      match source.inCapacityRowCount context.document context.outer with
      | .error error => .error (NumericComputationFault.repeatableAddressing error)
      | .ok rows => .ok (GroupCountOperandReading.starredRows rows)
  | .starredPresence source =>
      (context.readGroupInstances model source).map GroupCountOperandReading.instances

/-- Count an all-fixed group-count operand list on the route that carries the document.

    The addressed evaluator reaches this atom for a list with no star, and the scalar reader it
    would otherwise delegate to must refuse a repeatable-descendant operand because a cell list
    cannot express row instantiation. Delegating anyway would make one operand's admissibility a
    function of whether some *other* operand in the list happened to be starred, since only a
    starred sibling routes the list to the mixed atom. Both atom shapes therefore share
    `readGroupCountOperand` and the operand fold; `readCheckedNumericComputationAtom_filledGroupCount_eq_mixed`
    states the resulting agreement. -/
def readFilledGroupCount
    (context : NumericComputationEvaluationContext) (model : FlatModel)
    (groups : List ResolvedGroupReference) :
    Except NumericComputationFault NumericComputationResult := do
  let readings ← groups.mapM fun reference =>
    context.readGroupCountOperand model (.fixed reference)
  pure (.value (numberOfFilledGroupsForComputationOperands readings))

/-- Read one group-count operand as the growth channel its contribution still offers.

    This is the same operand list the value reading traverses, seen through the other question the
    Kernel asks of it — `computedNumberSelfValidation` types the target's implicit message from
    these. A **fixed** operand can gain content while its subtree is empty; a **starred** one can
    gain a row while its declared capacity is not exhausted; a fixed group below a star can gain
    content in any of its declared instances, an instantiated but empty one included. Whether the
    message exists at all is `groupCountOperandsDecided`'s question, not this one's.

    A starred group whose model retains no finite extent yields no channel rather than an assumed
    unbounded one, matching `numberOfFilledGroupsOperand?`'s refusal on the validation arm: a
    movement rule for that shape is unmeasured on either arm. -/
def growthOfGroupCountOperand
    (context : NumericComputationEvaluationContext) (model : FlatModel) :
    CheckedGroupCountOperand model →
      Except NumericComputationFault (Option ComputationOperandGrowth)
  | .fixed reference =>
      (context.readGroupContent model reference).map fun content =>
        some (.fixedGroup (groupPresentForComputation content.1 || content.2))
  | .starred source =>
      match source.inCapacityRowCount context.document context.outer with
      | .error error => .error (NumericComputationFault.repeatableAddressing error)
      | .ok rows => .ok (source.group.repeatability.map (.starredGroupCount rows ·))
  | .starredPresence source =>
      (context.readGroupInstances model source).map fun instances =>
        (CheckedGroupCountOperand.starredPresence source).declaredExtent?.map fun extent =>
          .fixedGroupInstances (GroupCountOperandReading.instances instances).contribution extent

/-- The whole operand list's growth, refusing as soon as one operand has no retained extent.

    Refusing the list rather than dropping the operand is deliberate: a missing channel would read
    as a closed one and silently type the message VALUE. -/
def growthOfGroupCountOperands
    (context : NumericComputationEvaluationContext) (model : FlatModel)
    (operands : List (CheckedGroupCountOperand model)) :
    Except NumericComputationFault (Option (List ComputationOperandGrowth)) := do
  let channels ← operands.mapM (context.growthOfGroupCountOperand model)
  pure (channels.mapM id)

/-- Whether validation's own reading of one group-count operand still answers, from the reads its
    value takes.

    The implicit message is a generated validation rule
    ([§6](../../../spec/09-computations.md#6-the-implicit-validation-rule-precisely)), so it has no
    answer where validation leaves the count unavailable, although this arm writes a count. What
    this reader can see is the one cause measured on this carrier: a fixed group, or one instance of
    a fixed group below a star, whose reads show only unparseable content
    ([checkpoint](../../../docs/SOURCES.md#src-ancestor-starred-group-count-computation)). A starred
    row count adds no unknown of its own on validation, measured at the
    [unavailability checkpoint](../../../docs/SOURCES.md#src-group-count-unavailability). One
    undecided instance decides the whole below-star operand, measured beside a filled one. An
    instance in an over-limit row is not read, and suppresses nothing where the Kernel reports its
    cell only as over-limit. -/
def groupCountOperandDecided
    (context : NumericComputationEvaluationContext) (model : FlatModel) :
    CheckedGroupCountOperand model → Except NumericComputationFault Bool
  | .fixed reference =>
      (context.readGroupContent model reference).map fun content =>
        !groupPresenceUndecided content.1 content.2
  | .starred _ => .ok true
  | .starredPresence source =>
      (context.readGroupInstances model source).map fun instances =>
        !instances.any fun reading => groupPresenceUndecided reading.1 reading.2

/-- Whether validation's reading of the whole operand list still answers: every operand must. -/
def groupCountOperandsDecided
    (context : NumericComputationEvaluationContext) (model : FlatModel)
    (operands : List (CheckedGroupCountOperand model)) :
    Except NumericComputationFault Bool := do
  pure ((← operands.mapM (context.groupCountOperandDecided model)).all id)

/-- Evaluate one model-checked atom against its complete direct/repeatable computation inputs. Addressing failures stay explicit and cannot collapse into a numeric value, clean absence, or formal poison. -/
def readCheckedNumericComputationAtom
    (context : NumericComputationEvaluationContext) :
    CheckedNumericComputationAtom model →
      Except NumericComputationFault NumericComputationResult
  | .temporalPart source => context.scalar.readTemporalNumericExpression source
  | .filledFieldCount source =>
      source.evaluateComputationCount { context.scalar with
        row := context.outer
        addressed := some { document := context.document, read := context.starRead } } (some context.filterRead) context.indexColumn?
  | .firstFilled source => do
      let result ←
        (source.evaluateComputationFirstFilled context.document context.outer
          context.scalar.read context.filterRead context.starRead).mapError
            NumericComputationFault.repeatableAddressing
      pure result.asComputationResult
  | .valueCount expected source =>
      (source.evaluateValueCountComputation expected context.document
        context.outer context.scalar.read context.filterRead
        context.starRead).map NumericOperand.toComputationResult
          |>.mapError NumericComputationFault.repeatableAddressing
  | .tokenDistinctCount source =>
      (source.evaluateDistinctComputation context.document context.outer
        context.scalar.read context.filterRead context.starRead).map NumericOperand.toComputationResult
          |>.mapError .repeatableAddressing
  | .temporalDistinctCount run =>
      (run.evaluateComputation context.document context.outer
        context.scalar.read context.filterRead context.starRead).map NumericOperand.toComputationResult
          |>.mapError .repeatableAddressing
  | .tokenValueCount source =>
      (source.evaluateComputation context.document context.outer
        context.scalar.read context.filterRead context.starRead).map
          NumericOperand.toComputationResult
        |>.mapError NumericComputationFault.repeatableAddressing
  | .booleanValueCount source =>
      (source.evaluateComputation context.document context.outer
        context.scalar.read context.filterRead context.starRead).map
          NumericOperand.toComputationResult
        |>.mapError NumericComputationFault.repeatableAddressing
  | .sumOfProducts source =>
      (source.evaluateComputation context.document context.outer
        context.starRead).mapError NumericComputationFault.repeatableAddressing
  | .filledGroupCountMixed operands => do
      let readings ← operands.mapM (context.readGroupCountOperand model)
      pure (.value (numberOfFilledGroupsForComputationOperands readings))
  | .numeric source =>
      context.scalar.readNumericComputationAtomWith
        (fun op aggregate =>
          (aggregate.evaluateComputation op context.document context.outer
            context.scalar.read context.filterRead context.starRead).mapError
              NumericComputationFault.repeatableAddressing)
        (context.readFilledGroupCount model) source

end NumericComputationEvaluationContext

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
  | .fixedCurrentRepetition _ => none
  | .boundCurrentRepetition _ => none
  | .baseYearDatePart _ _ _ => none
  | .temporalFieldPart _ _ => none
  | .dateRangeBoundPart _ _ _ => none
  | .stringLength _ => none
  | .stringRange _ _ _ => none
  | .fieldValueAsNumber _ => none
  -- Each difference arm preflights through the SAME predicate its checked owner gates with, rather
  -- than restating the rule, so the two cannot drift. All three previously tested the declared
  -- kind, which is not what the Kernel reads: the declared format is
  -- ([checkpoint](../../../docs/sources/computation-placement-and-constant-probes.md#src-temporal-difference-gates-read-the-format)).
  -- `hasBaseYear` is unavailable on this model-free route, so the completed-period arm passes the
  -- permissive value; a preflight must never be stricter than the gate it guards.
  | .dateDifference unit left right =>
      let fault? : ResolvedDateDifferenceOperand → Option NumericComputationFault
        | .field source =>
            if unit.admittedBy true source.components then none
            else some (.fieldKindMismatch source.id)
        | .baseYear _ _ | .literal _ _ => none
      match fault? left with
      | some fault => some fault
      | none => fault? right
  | .dateTimeDifference unit left right =>
      let fault? : FlatTemporalOperand → Option NumericComputationFault
        | .fieldValue source =>
            if unit.admittedBy source.components then none
            else some (.fieldKindMismatch source.id)
        | .nowValue => none
        | _ => some .unsupportedDateTimeDifferenceOperand
      match fault? left with
      | some fault => some fault
      | none => fault? right
  | .dayDifference _ left right =>
      let fault? : ResolvedDateDifferenceOperand → Option NumericComputationFault
        | .field source =>
            if CalendarDayDifference.admittedBy source.components then none
            else some (.fieldKindMismatch source.id)
        | .baseYear _ _ | .literal _ _ => none
      match fault? left with
      | some fault => some fault
      | none => fault? right
  | .aggregate _ _ => none
  -- No model is available on this route, so no single operand can be named.
  | .filledGroupCount _ => some .groupCountNeedsModel

/-- The structural fault a fixed group-count operand carries, if any.

    Shared by both group-count atoms so the pre-read gate cannot end up narrower than the reader
    on one of them; `readGroupCountOperand_fixed_error_iff_notAdmitted` ties it to the reader. -/
def fixedGroupCountOperandFault? (model : FlatModel) (reference : ResolvedGroupReference) :
    Option NumericComputationFault :=
  if reference.computationOperandAdmitted model then none
  else some (.unsupportedGroupCount reference.path)

def CheckedNumericComputationAtom.numericComputationFault? :
    CheckedNumericComputationAtom model → Option NumericComputationFault
  | .filledFieldCount source => source.operands.findSome? fun operand =>
      match operand with
      | .indexed _ => none
      | operand => if operand.hasHaving then none else
        match CheckedFieldFillList.computationSources { operands := [operand] } with
        | .ok _ => none
        | .error error => some (.fieldFillSource error)
  | .temporalPart _ | .firstFilled _ => none
  | .valueCount _ _ => none
  | .tokenDistinctCount _ | .temporalDistinctCount _ => none
  | .tokenValueCount _ => none
  | .booleanValueCount _ => none
  -- A group operand's boundary is model-structural, so it is decided here rather than left
  -- to the reading branch, where a data-dependent poison could otherwise hide it: `evalOrdered`
  -- stops at a left poison, so an ungated atom's structural fault is never reached. It must be the
  -- reader's own admission and not a narrower copy: refusing here what the reader would count
  -- makes the gate, rather than the operand, decide the answer.
  | .numeric (.filledGroupCount groups) =>
      groups.findSome? (fixedGroupCountOperandFault? model)
  | .numeric source =>
      NumericComputationAtom.numericComputationFault? source
  | .sumOfProducts _ => none
  -- The same gate, because this atom holds the same `fixed` operand form. Only the fixed operands
  -- are pre-decided: a starred operand's refusal is a `StarAddressingError` over the document's
  -- own row topology, which no model-structural pass can answer.
  | .filledGroupCountMixed operands =>
      operands.findSome? fun operand =>
        match operand with
        | .fixed reference => fixedGroupCountOperandFault? model reference
        | .starred _ => none
        | .starredPresence _ => none

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

end A12Kernel
