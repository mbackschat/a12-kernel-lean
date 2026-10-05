import A12Kernel.Semantics.FlatComparisonInputs
import A12Kernel.Semantics.Condition
import A12Kernel.Semantics.Iteration
import A12Kernel.Semantics.NumericExpression
import A12Kernel.Semantics.NumericConversion

/-! Correlated operand identities, binding frames and phase-specific checked reads. -/

namespace A12Kernel

/-- Origin of one reference inside a correlated `Having` condition. -/
inductive HavingOrigin where
  | inner
  | outer
  deriving Repr, DecidableEq

/-- Resolve exactly one positive binding for a repeatable level. Missing, duplicate, and zero bindings fail closed; correlation must never guess a first row or substitute row zero. -/
def Env.uniqueRowAt? (env : Env) (level : RepeatableLevel) : Option RowIndex :=
  (env.bindingAt level).toOption

/-- A filter leaf's comparison operator. A filter body is the ordinary condition production, so all
six ordinary operators are admitted on its Number and repetition leaves
([checkpoint](../../docs/sources/having-filter-probes.md#src-having-number-leaf-grid)). -/
inductive CorrelationComparisonOp where
  | equal
  | notEqual
  | lessThan
  | lessEqual
  | greaterThan
  | greaterEqual
  deriving Repr, DecidableEq

/-- The ordinary Number comparison operator a filter leaf's operator is. -/
def CorrelationComparisonOp.toNumeric : CorrelationComparisonOp → NumericComparisonOp
  | .equal => .equal
  | .notEqual => .notEqual
  | .lessThan => .less
  | .lessEqual => .lessEqual
  | .greaterThan => .greater
  | .greaterEqual => .greaterEqual

structure HavingNumberRef where
  origin : HavingOrigin
  field : FlatNumberField
  deriving Repr, DecidableEq

/-- A text filter reference retains its domain because String empty-literal suppression and
    Enumeration projection use distinct comparison semantics. -/
structure HavingStringRef where
  origin : HavingOrigin
  operand : FlatTextFieldOperand
  deriving Repr, DecidableEq

def HavingStringRef.field (reference : HavingStringRef) : FlatField := reference.operand.field

/-- Direct String comparison suppresses an empty literal; Enumeration comparisons retain their
checked projection's literal domain (`FlatComparison`'s separate String/Enumeration branches). -/
def HavingStringRef.compareResolved (reference : HavingStringRef)
    (value : SimpleComparisonOperand String) (op : EqualityOp) (expected : String) : Verdict :=
  match reference.operand with
  | .string _ => value.evalDirectString op expected
  | .enumeration _ => op.evalSimple (· == ·) value expected

def HavingOrigin.availableLevels (origin : HavingOrigin)
    (candidateLevels outerLevels : List RepeatableLevel) : List RepeatableLevel :=
  match origin with
  | .inner => candidateLevels
  | .outer => outerLevels

/-- A presence filter reference. Presence reads only whether a cell carries a value, so it is
    kind-neutral and needs the field id alone rather than a typed field. -/
structure HavingPresenceRef where
  origin : HavingOrigin
  field : FieldId
  deriving Repr, DecidableEq

/-- Which presence predicate a filter leaf carries. `FieldNotFilled` is a genuine predicate here
    rather than a negation of the other: only a clean empty cell makes it true, so both polarities
    are non-true on a formally unavailable cell. -/
inductive HavingPresencePolarity where
  | filled
  | notFilled
  deriving Repr, DecidableEq

/-- Fixed groups retain their path because admission still depends on its repeatable ancestors,
    even though the group's own index is one. -/
inductive HavingRepetitionSource where
  | repeatable (level : RepeatableLevel)
  | fixed (path : List String)
  deriving Repr, DecidableEq

structure HavingRepetitionRef where
  origin : HavingOrigin
  source : HavingRepetitionSource
  deriving Repr, DecidableEq

/-- Model constants carry no row origin, so arithmetic cannot make them satisfy a filter reference requirement (spec/07 §3). Field and repetition atoms retain their own origins. -/
inductive HavingNumericAtom where
  | baseYear (year : Int)
  | baseYearDatePart (year : Int) (source : BaseYearDateSource) (part : DateNumericPart)
  | fieldValueAsNumber (origin : HavingOrigin) (source : ResolvedFieldValueAsNumberSource)
  | field (reference : HavingNumberRef)
  | stringLength (origin : HavingOrigin) (field : FlatStringField)
  | stringRange (origin : HavingOrigin) (source : FlatStringField) (start finish : Nat)
  | dateRangeBoundPart (origin : HavingOrigin) (source : FlatDateRangeField) (bound : DateRangeBound) (part : DateNumericPart)
  | temporalPart (origin : HavingOrigin) (source : FlatTemporalField) (part : TemporalNumericPart)
  | repetition (reference : HavingRepetitionRef)
  deriving Repr, DecidableEq

def HavingNumericAtom.origin? : HavingNumericAtom → Option HavingOrigin
  | .baseYear _ | .baseYearDatePart _ _ _ => none
  | .field reference => some reference.origin
  | .dateRangeBoundPart origin _ _ _ | .fieldValueAsNumber origin _ | .stringLength origin _ | .stringRange origin _ _ _ | .temporalPart origin _ _ => some origin
  | .repetition reference => some reference.origin

def HavingNumericAtom.fieldId? : HavingNumericAtom → Option FieldId
  | .baseYear _ | .baseYearDatePart _ _ _ => none
  | .dateRangeBoundPart _ source _ _ => some source.id
  | .fieldValueAsNumber _ source => some source.fieldId
  | .field reference => some reference.field.id
  | .stringLength _ source | .stringRange _ source _ _ => some source.id
  | .temporalPart _ source _ => some source.id
  | .repetition _ => none

def HavingNumericAtom.summary : HavingNumericAtom → NumericScaleSummary
  | .baseYear _ | .baseYearDatePart _ _ _ => .field 0
  | .fieldValueAsNumber _ source => .field source.scale
  | .field reference => .field reference.field.info.scale
  | .dateRangeBoundPart _ _ _ _ | .repetition _ | .stringLength _ _ | .stringRange _ _ _ _ | .temporalPart _ _ _ => .field 0

/-- One correlated filter frame. Both candidate and captured rule environments are
    explicit full repetition contexts. -/
structure CorrelationFrame where
  innerEnv : Env
  outerEnv : Env
  deriving Repr, DecidableEq

def CorrelationFrame.envAt (frame : CorrelationFrame) : HavingOrigin → Env
  | .inner => frame.innerEnv
  | .outer => frame.outerEnv

def CorrelationFrame.rowAt? (frame : CorrelationFrame)
    (reference : HavingRepetitionRef) : Option RowIndex :=
  match reference.source with
  | .repeatable level => (frame.envAt reference.origin).uniqueRowAt? level
  | .fixed _ => some 1

/-- One correlated filter frame: both row identities are explicit and neither is an
    ambient implicit "current" row. This remains the one-group adapter. -/
structure SingleGroupFilterFrame where
  innerRow : RowIndex
  outerRow : RowIndex
  deriving Repr, DecidableEq

def SingleGroupFilterFrame.toCorrelationFrame (frame : SingleGroupFilterFrame)
    (context : SingleGroupValidationContext) : CorrelationFrame :=
  { innerEnv := context.envAt frame.innerRow
    outerEnv := context.envAt frame.outerRow }

structure CapturedSingleGroupContext where
  rows : SingleGroupValidationContext
  outerRow : RowIndex

def CapturedSingleGroupContext.frame (context : CapturedSingleGroupContext)
    (innerRow : RowIndex) : SingleGroupFilterFrame :=
  { innerRow, outerRow := context.outerRow }

inductive CorrelatedNumberOperand where
  | value (amount : Rat)
  | unknown (cause : FormalCause)
  deriving Repr, DecidableEq

/-- The only document operation needed by the shared correlation evaluator. Topology
    adapters construct environments; this seam reads a checked field through one. -/
structure CorrelationContext where
  read : Env → FieldId → CheckedCell

/-- The addressed counterpart of `CorrelationContext`. It preserves caller-owned field-read failures and maps invalid repetition bindings into that same structural channel. -/
structure ResolvingCorrelationContext (Error : Type) where
  read : Env → FieldId → Except Error CheckedCell
  bindingError : EnvBindingError → Error

/-- Resolve one numeric filter reference through the selected environment and caller-selected phase. Empty-to-zero is local to numeric comparison; formal invalidity retains its cause for the consuming phase projection. -/
def HavingNumberRef.resolveInAt (reference : HavingNumberRef) (phase : Phase)
    (context : CorrelationContext) (frame : CorrelationFrame) :
    CorrelatedNumberOperand :=
  let rowContext : FlatContext :=
    { read := context.read (frame.envAt reference.origin) }
  match rowContext.resolveNumberComparisonOperandAt phase reference.field with
  | .value amount _ => .value amount
  | .unknown cause => .unknown cause

/-- Resolve the same numeric reference without collapsing a structural addressed-read failure into a formal cell observation. -/
def HavingNumberRef.resolveInAtResolving (reference : HavingNumberRef)
    (phase : Phase) (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) : Except Error CorrelatedNumberOperand := do
  let cell ← context.read (frame.envAt reference.origin) reference.field.id
  let rowContext : FlatContext := { read := fun _ => cell }
  pure (match rowContext.resolveNumberComparisonOperandAt phase reference.field with
    | .value amount _ => .value amount
    | .unknown cause => .unknown cause)

/-- Resolve text through the selected environment and phase using its owning domain's observation
    projection, preserving unavailable values and formal invalidity. -/
def HavingStringRef.resolveInAt (reference : HavingStringRef) (phase : Phase)
    (context : CorrelationContext) (frame : CorrelationFrame) :
    SimpleComparisonOperand String :=
  let rowContext : FlatContext :=
    { read := context.read (frame.envAt reference.origin) }
  match reference.operand with
  | .string field => rowContext.resolveStringComparisonOperandAt phase field
  | .enumeration operand => operand.projection.resolveOperand (rowContext.observeAt phase operand.field.id)

/-- Resolve the same text reference without collapsing a structural addressed-read failure into a formal cell observation. -/
def HavingStringRef.resolveInAtResolving (reference : HavingStringRef)
    (phase : Phase) (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) :
    Except Error (SimpleComparisonOperand String) := do
  let cell ← context.read (frame.envAt reference.origin) reference.field.id
  let rowContext : FlatContext := { read := fun _ => cell }
  pure (reference.resolveInAt phase { read := fun _ => rowContext.read } frame)

/-- Observe one presence reference's cell at a chosen phase. Presence needs the observation itself,
    not a comparison operand, so it reads the phase view directly. -/
def HavingPresenceRef.observeInAt (reference : HavingPresenceRef) (phase : Phase)
    (context : CorrelationContext) (frame : CorrelationFrame) : CellObservation :=
  let rowContext : FlatContext :=
    { read := context.read (frame.envAt reference.origin) }
  rowContext.observeAt phase reference.field

/-- Observe the same presence reference without collapsing a structural addressed-read failure. -/
def HavingPresenceRef.observeInAtResolving (reference : HavingPresenceRef)
    (phase : Phase) (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) : Except Error CellObservation := do
  let cell ← context.read (frame.envAt reference.origin) reference.field
  pure (observeCell phase cell)

/-- Both presence polarities delegate to the shared validation observation consumers, so this leaf
    adds no second account of what "filled" means. Neither polarity fires on a formally unavailable
    cell, which is why they are complements only over clean cells. -/
def HavingPresencePolarity.evalObservation :
    HavingPresencePolarity → CellObservation → Verdict
  | .filled => CellObservation.evalValidationFilled
  | .notFilled => CellObservation.evalValidationNotFilled

/-- Resolve one repetition reference through the structural addressed channel. -/
def CorrelationFrame.rowAtResolving (frame : CorrelationFrame)
    (context : ResolvingCorrelationContext Error)
    (reference : HavingRepetitionRef) : Except Error RowIndex :=
  match reference.source with
  | .repeatable level =>
      (frame.envAt reference.origin).bindingAt level |>.mapError context.bindingError
  | .fixed _ => .ok 1

/-- Validation specialization retained for established filter consumers. -/
def HavingNumberRef.resolveIn (reference : HavingNumberRef)
    (context : CorrelationContext) (frame : CorrelationFrame) :
    CorrelatedNumberOperand :=
  reference.resolveInAt .validation context frame

private def malformedCorrelationCell : CheckedCell :=
  { rawPresent := true, parsed := none, findings := [.malformed] }

def SingleGroupValidationContext.asCorrelationContext
    (context : SingleGroupValidationContext) : CorrelationContext where
  read env field :=
    match env.uniqueRowAt? context.group with
    | some row => context.read row field
    | none => malformedCorrelationCell

/-- Backwards-compatible one-group numeric resolution. -/
def HavingNumberRef.resolve (reference : HavingNumberRef)
    (context : SingleGroupValidationContext) (frame : SingleGroupFilterFrame) :
    CorrelatedNumberOperand :=
  reference.resolveIn context.asCorrelationContext (frame.toCorrelationFrame context)

private def havingArithmetic : NumericOperand → Except Unit NumericArithmeticOutcome
  | .value amount fillability => .ok (.value amount fillability)
  | .unknown _ => .error ()

/-- Filter Number atoms apply comparison-local empty zero before ordinary arithmetic. Missing raw
    repetition bindings remain unknown; checked addressed readers report them structurally. -/
def HavingNumericAtom.readValidation (context : CorrelationContext) (frame : CorrelationFrame) :
    HavingNumericAtom → Except Unit NumericArithmeticOutcome
  | .dateRangeBoundPart origin source bound part =>
      havingArithmetic ((observeCell .validation (context.read (frame.envAt origin) source.id)).asDateRangeBoundNumericOperand bound part)
  | .baseYear year => .ok (.value year .fixed)
  | .baseYearDatePart year source part => .ok (.value (baseYearDateSourceNumericPart year source part) .fixed)
  | .fieldValueAsNumber origin source =>
      havingArithmetic (source.observeOperand (observeCell .validation (context.read (frame.envAt origin) source.fieldId)))
  | .stringLength origin source =>
      havingArithmetic ((observeCell .validation (context.read (frame.envAt origin) source.id)).asStringLengthOperand)
  | .stringRange origin source start finish =>
      havingArithmetic ((observeCell .validation (context.read (frame.envAt origin) source.id)).asStringRangeOperand start finish)
  | .temporalPart origin source part =>
      havingArithmetic ((observeCell .validation (context.read (frame.envAt origin) source.id)).asTemporalNumericOperand source part.project?)
  | .field reference =>
      match reference.resolveIn context frame with
      | .value amount => .ok (.value amount .fixed)
      | .unknown _ => .error ()
  | .repetition reference =>
      match frame.rowAt? reference with
      | some row => .ok (.value row .fixed)
      | none => .error ()

def HavingNumericAtom.readValidationResolving (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) :
    HavingNumericAtom → Except Error (Except Unit NumericArithmeticOutcome)
  | .dateRangeBoundPart origin source bound part => do
      let cell ← context.read (frame.envAt origin) source.id
      pure (havingArithmetic ((observeCell .validation cell).asDateRangeBoundNumericOperand bound part))
  | .baseYear year => pure (.ok (.value year .fixed))
  | .baseYearDatePart year source part => pure (.ok (.value (baseYearDateSourceNumericPart year source part) .fixed))
  | .fieldValueAsNumber origin source => do
      let cell ← context.read (frame.envAt origin) source.fieldId
      pure (havingArithmetic (source.observeOperand (observeCell .validation cell)))
  | .stringLength origin source => do
      let cell ← context.read (frame.envAt origin) source.id
      pure (havingArithmetic ((observeCell .validation cell).asStringLengthOperand))
  | .stringRange origin source start finish => do
      let cell ← context.read (frame.envAt origin) source.id
      pure (havingArithmetic ((observeCell .validation cell).asStringRangeOperand start finish))
  | .temporalPart origin source part => do
      let cell ← context.read (frame.envAt origin) source.id
      pure (havingArithmetic ((observeCell .validation cell).asTemporalNumericOperand source part.project?))
  | .field reference => do
      pure (match ← reference.resolveInAtResolving .validation context frame with
        | .value amount => .ok (.value amount .fixed)
        | .unknown _ => .error ())
  | .repetition reference => do
      pure (.ok (.value (← frame.rowAtResolving context reference) .fixed))

def HavingNumericAtom.readComputation (context : CorrelationContext) (frame : CorrelationFrame) :
    HavingNumericAtom → NumericComputationResult
  | .dateRangeBoundPart origin source bound part =>
      ((observeCell .computation (context.read (frame.envAt origin) source.id)).asDateRangeBoundNumericOperand bound part).toComputationResult
  | .baseYear year => .value year
  | .baseYearDatePart year source part => .value (baseYearDateSourceNumericPart year source part)
  | .fieldValueAsNumber origin source =>
      (source.observeOperand (observeCell .computation (context.read (frame.envAt origin) source.fieldId))).toComputationResult
  | .stringLength origin source =>
      (observeCell .computation (context.read (frame.envAt origin) source.id)).asStringLengthOperand.toComputationResult
  | .stringRange origin source start finish =>
      ((observeCell .computation (context.read (frame.envAt origin) source.id)).asStringRangeOperand start finish).toComputationResult
  | .temporalPart origin source part =>
      ((observeCell .computation (context.read (frame.envAt origin) source.id)).asTemporalNumericOperand source part.project?).toComputationResult
  | .field reference =>
      match reference.resolveInAt .computation context frame with
      | .value amount => .value amount
      | .unknown cause => .poison cause
  | .repetition reference =>
      match frame.rowAt? reference with
      | some row => .value row
      | none => .domainFailure

def HavingNumericAtom.readComputationResolving (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) : HavingNumericAtom → Except Error NumericComputationResult
  | .dateRangeBoundPart origin source bound part => do
      let cell ← context.read (frame.envAt origin) source.id
      pure (((observeCell .computation cell).asDateRangeBoundNumericOperand bound part).toComputationResult)
  | .baseYear year => pure (.value year)
  | .baseYearDatePart year source part => pure (.value (baseYearDateSourceNumericPart year source part))
  | .fieldValueAsNumber origin source => do
      let cell ← context.read (frame.envAt origin) source.fieldId
      pure ((source.observeOperand (observeCell .computation cell)).toComputationResult)
  | .stringLength origin source => do
      let cell ← context.read (frame.envAt origin) source.id
      pure ((observeCell .computation cell).asStringLengthOperand.toComputationResult)
  | .stringRange origin source start finish => do
      let cell ← context.read (frame.envAt origin) source.id
      pure (((observeCell .computation cell).asStringRangeOperand start finish).toComputationResult)
  | .temporalPart origin source part => do
      let cell ← context.read (frame.envAt origin) source.id
      pure (((observeCell .computation cell).asTemporalNumericOperand source part.project?).toComputationResult)
  | .field reference => do
      pure (match ← reference.resolveInAtResolving .computation context frame with
        | .value amount => .value amount
        | .unknown cause => .poison cause)
  | .repetition reference => do
      pure (.value (← frame.rowAtResolving context reference))

end A12Kernel
