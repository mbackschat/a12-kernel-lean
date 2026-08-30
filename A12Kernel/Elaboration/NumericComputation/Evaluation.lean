import A12Kernel.Elaboration.NumericComputation.Core
import A12Kernel.Semantics.ComputationSelfValidation

/-! # Checked numeric-computation evaluation and fault projection -/

namespace A12Kernel

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
  | .field source => DateDifferenceOperand.ofObservation
      (observeCell .computation (context.read source.id))
  | .baseYear year source => .value (source.parts year)

def readCalendarDayDifferenceOperand (context : ScalarComputationContext)
    (profile : ModelZone.ConcreteProfile) :
    ResolvedDateDifferenceOperand → CalendarDayDifferenceOperand
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
admitted scalar boundary refuses explicitly rather than observing as absent. Both group-count
readers share this step, which is what `filledGroupCountMixed_fixed_eq_scalarCount` turns into a
statement about the two counts. -/
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

/-- Evaluate a checked computation atom without a repeatable document only when its entity-list payload narrows exactly to direct fields. A repeatable operand fails explicitly rather than silently observing an empty synthetic document. -/
def readCheckedNumericComputationAtom (context : ScalarComputationContext) :
    CheckedNumericComputationAtom model →
      Except NumericComputationFault NumericComputationResult
  | .firstFilled source =>
      match source.evaluateDirectComputationFirstFilled? context.read with
      | some result => pure result.asComputationResult
      | none => throw .repeatableContextRequired
  | .valueCount expected source =>
      match source.evaluateDirectValueCountAt? expected .computation
          { read := context.read } with
      | some result => pure result.toComputationResult
      | none => throw .repeatableContextRequired
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

/-- Read one group-count operand into its contribution.

    A **fixed** operand takes exactly the descendant extent and cell reads the scalar fixed-only
    reader takes, which is what makes the two forms agree on any list they can both hold — stated
    as `filledGroupCountMixed_fixed_eq_scalarCount` rather than left to this comment. A **starred**
    operand takes the in-capacity instantiated row count, the quantity this route carries the
    document topology for. -/
def readGroupCountOperand
    (context : NumericComputationEvaluationContext) (model : FlatModel) :
    CheckedGroupCountOperand model →
      Except NumericComputationFault GroupCountOperandReading
  | .fixed reference =>
      (context.scalar.readGroupDescendants model reference).map GroupCountOperandReading.fixed
  | .starred source =>
      match source.inCapacityRowCount context.document context.outer with
      | .error error => .error (NumericComputationFault.repeatableAddressing error)
      | .ok rows => .ok (GroupCountOperandReading.starredRows rows)

/-- Read one group-count operand as the growth channel its contribution still offers.

    This is the same operand list the value reading traverses, seen through the other question the
    Kernel asks of it — `computedNumberSelfValidation` types the target's implicit message from
    these. A **fixed** operand can gain content while its subtree is empty; a **starred** one can
    gain a row while its declared capacity is not exhausted.

    A starred group whose model retains no finite extent yields no channel rather than an assumed
    unbounded one, matching `numberOfFilledGroupsOperand?`'s refusal on the validation arm: a
    movement rule for that shape is unmeasured on either arm. -/
def growthOfGroupCountOperand
    (context : NumericComputationEvaluationContext) (model : FlatModel) :
    CheckedGroupCountOperand model →
      Except NumericComputationFault (Option ComputationOperandGrowth)
  | .fixed reference =>
      (context.scalar.readGroupDescendants model reference).map fun cells =>
        some (.fixedGroup (groupPresentForComputation cells))
  | .starred source =>
      match source.group.repeatability with
      | none => .ok none
      | some capacity =>
          match source.inCapacityRowCount context.document context.outer with
          | .error error => .error (NumericComputationFault.repeatableAddressing error)
          | .ok rows => .ok (some (.starredGroupCount rows capacity))

/-- The whole operand list's growth, refusing as soon as one operand has no retained extent.

    Refusing the list rather than dropping the operand is deliberate: a missing channel would read
    as a closed one and silently type the message VALUE. -/
def growthOfGroupCountOperands
    (context : NumericComputationEvaluationContext) (model : FlatModel)
    (operands : List (CheckedGroupCountOperand model)) :
    Except NumericComputationFault (Option (List ComputationOperandGrowth)) := do
  let channels ← operands.mapM (context.growthOfGroupCountOperand model)
  pure (channels.mapM id)

/-- Evaluate one model-checked atom against its complete direct/repeatable computation inputs. Addressing failures stay explicit and cannot collapse into a numeric value, clean absence, or formal poison. -/
def readCheckedNumericComputationAtom
    (context : NumericComputationEvaluationContext) :
    CheckedNumericComputationAtom model →
      Except NumericComputationFault NumericComputationResult
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
        (context.scalar.readFilledGroupCount model) source

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
  | .dateRangeBoundPart _ _ _ => none
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
  | .dateTimeDifference _ left right =>
      let fault? : FlatTemporalOperand → Option NumericComputationFault
        | .fieldValue source =>
            if source.kind == .dateTime then none
            else some (.fieldKindMismatch source.id)
        | .nowValue => none
        | _ => some .unsupportedDateTimeDifferenceOperand
      match fault? left with
      | some fault => some fault
      | none => fault? right
  | .dayDifference _ left right =>
      let fault? : ResolvedDateDifferenceOperand → Option NumericComputationFault
        | .field source =>
            if CalendarDayDifference.admitsKind source.kind then none
            else some (.fieldKindMismatch source.id)
        | .baseYear _ _ => none
      match fault? left with
      | some fault => some fault
      | none => fault? right
  | .aggregate _ _ => none
  -- No model is available on this route, so no single operand can be named.
  | .filledGroupCount _ => some .groupCountNeedsModel

def CheckedNumericComputationAtom.numericComputationFault? :
    CheckedNumericComputationAtom model → Option NumericComputationFault
  | .firstFilled _ => none
  | .valueCount _ _ => none
  | .tokenValueCount _ => none
  | .booleanValueCount _ => none
  -- A group operand's boundary is model-structural, so it is decided here rather than left
  -- to the reading branch, where a data-dependent poison could otherwise hide it.
  | .numeric (.filledGroupCount groups) =>
      match groups.find? fun reference =>
          (reference.computationDescendants? model).isNone with
      | some reference => some (.unsupportedGroupCount reference.path)
      | none => none
  | .numeric source =>
      NumericComputationAtom.numericComputationFault? source
  | .sumOfProducts _ => none
  | .filledGroupCountMixed _ => none

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

end A12Kernel
