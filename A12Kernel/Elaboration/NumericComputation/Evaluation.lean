import A12Kernel.Elaboration.NumericComputation.Core

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
  | .dateTimeDifference unit left right =>
      pure ((DateTimeDifferenceOperand.evaluate unit
        (.ofObservation (observeCell .computation (context.read left.id)))
        (.ofObservation (observeCell .computation (context.read right.id))))
        |>.toComputationResult)
  | .dayDifference profile left right =>
      match CalendarDayDifferenceOperand.evaluate profile
          (context.readCalendarDayDifferenceOperand profile left)
          (context.readCalendarDayDifferenceOperand profile right) with
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
  | .dateTimeDifference _ left right =>
      if left.kind != .dateTime then
        some (.fieldKindMismatch left.id)
      else if right.kind != .dateTime then
        some (.fieldKindMismatch right.id)
      else
        none
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
  | .filledGroupCount _ => some .unsupportedGroupCount

def CheckedNumericComputationAtom.numericComputationFault? :
    CheckedNumericComputationAtom model → Option NumericComputationFault
  | .firstFilled _ => none
  | .valueCount _ _ => none
  | .tokenValueCount _ => none
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

end A12Kernel
