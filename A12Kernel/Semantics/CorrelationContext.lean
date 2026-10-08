import A12Kernel.Semantics.FlatComparisonInputs
import A12Kernel.Semantics.Condition
import A12Kernel.Semantics.Iteration
import A12Kernel.Semantics.NumericExpression
import A12Kernel.Semantics.NumericConversion
import A12Kernel.Semantics.DateDifferenceSource
import A12Kernel.Semantics.DateTimeDifference
import A12Kernel.Semantics.NumericAggregate
import A12Kernel.Semantics.LegacyCalendarExpression
import A12Kernel.Semantics.ComputationCondition

/-! Correlated operand identities, binding frames and caller-owned read capabilities. -/

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

/-- Group filters retain ordinary group identity, content and dependency classification alongside
their candidate/captured origin (spec/07 §3 and the containing-group checkpoint). -/
inductive HavingGroupOperand where
  | field (reference : HavingPresenceRef)
  | group (origin : HavingOrigin) (source : ComputationGroupOperand)
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

structure HavingTemporalRef where
  origin : HavingOrigin
  field : FlatTemporalField
  deriving Repr, DecidableEq

inductive HavingClockSource where
  | today
  | now
  deriving Repr, DecidableEq

def HavingClockSource.components : HavingClockSource → TemporalComponents
  | .today => TemporalComponents.fullDate
  | .now => TemporalComponents.now

def HavingClockSource.admits (source : HavingClockSource) : TemporalNumericPart → Bool
  | .date part => part.admittedBy false source.components
  | .time part => part.admittedBy source.components

/-- Clock extraction follows the ordinary temporal source account: Today uses the resolved local civil date,
while Now projects the legacy calendar label (spec/05 §7 and TemporalNumericPart.projectScalar).
Both decode the caller's exact clock, without caching a label or substituting zero. -/
def HavingClockSource.numericPart? (source : HavingClockSource)
    (profile : ModelZone.ConcreteProfile) (world : Option World) (part : TemporalNumericPart) : Option Rat := do
  let world ← world
  match source with
  | .today =>
      let date ← profile.localDate? world.now
      let _ ← profile.resolveLocal? {
        date, time := { hour := 0, minute := 0, second := 0, valid := by decide } }
      match part with
      | .date part => pure (part.extract date.civil.parts)
      | .time _ => none
  | .now =>
      let label ← profile.calendarLabel? world.now
      pure (match part with
        | .date part => part.extract label.parts
        | .time part => part.extract label.time)

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

/-- A reached runtime value failure differs from a missing calendar capability (spec/07 §3). -/
inductive CorrelationRuntimeFault where
  | calendarUnavailable
  | valueFailure
  | worldUnavailable
  | typeValidityValueFailure
  | groupUnavailable (path : GroupPath)
  | storedTextUnavailable (field : FieldId)
  deriving Repr, DecidableEq

/-- Both phases reuse their ordinary group inputs. Callers retain physical row content and the
current read view; a missing reader is not an empty group (spec/07 §5). Each field extent pairs
in-capacity environments with whether declared but uninstantiated capacity remains. -/
structure CorrelationGroupReads (Error : Type) where
  validation : Env → ResolvedGroupReference → Except Error GroupPresenceState
  computation : Env → ComputationGroupOperand →
    Except Error (List CellObservation × Bool)
  fieldExtent : GroupPath → Env → Nat → FieldId → Except Error (List Env × Bool)
  groupExtent? : Option (GroupPath → Env → StarPath → Except Error (List Env)) := none

/-- Topology adapters supply environments; the shared evaluator reads their checked fields and the caller-owned evaluation clock. Retaining one World prevents candidate and captured reads from sampling different dates (spec/05 §7, clock-source semantics). -/
structure CorrelationContext where
  read : Env → FieldId → CheckedCell
  storedText : Env → FieldId → Option String := fun _ _ => none
  world : Option World := none
  groups : Option (CorrelationGroupReads CorrelationRuntimeFault) := none

/-- The addressed counterpart of `CorrelationContext`. It preserves caller-owned field-read failures and maps repetition-binding and calendar-support failures into that same explicit error channel. -/
structure ResolvingCorrelationContext (Error : Type) where
  read : Env → FieldId → Except Error CheckedCell
  storedText : Env → FieldId → Option String := fun _ _ => none
  bindingError : EnvBindingError → Error
  unsupportedDateCalendar : Error
  temporalValueFailure : Error
  worldUnavailable : Error
  typeValidityValueFailure : Error
  groupUnavailable : GroupPath → Error
  storedTextUnavailable : FieldId → Error
  world : Option World := none
  groups : Option (CorrelationGroupReads Error) := none

def CorrelationContext.asResolving (context : CorrelationContext) :
    ResolvingCorrelationContext CorrelationRuntimeFault := {
  read := fun env field => .ok (context.read env field)
  storedText := context.storedText
  world := context.world
  bindingError := fun _ => .calendarUnavailable
  unsupportedDateCalendar := .calendarUnavailable
  temporalValueFailure := .valueFailure
  worldUnavailable := .worldUnavailable
  typeValidityValueFailure := .typeValidityValueFailure
  groupUnavailable := .groupUnavailable
  storedTextUnavailable := .storedTextUnavailable
  groups := context.groups }

end A12Kernel
