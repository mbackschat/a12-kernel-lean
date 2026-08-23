import A12Kernel.Elaboration.DateRangeBound
import A12Kernel.Semantics.DateNumeric

/-! # Unconfigured yearless DateRange bound extraction

A model with no Base Year cannot complete a yearless DATE_RANGE declaration, and the Kernel
still admits `StartOfDateRange` and `EndOfDateRange` on one: the extraction is legal and the
*consumers* are gated instead. This capsule owns that route separately from the exact-valued
one, because the two retain different domains — the completed route yields a resolved Date and
this one must never manufacture a year.

An extracted endpoint therefore carries exactly the components its declaration retains, so a
numeric component is admitted only where that set exposes it. The absent halves are the same
literal zeroes a partially known Date uses, and no consumer can observe them, because the
static gate refuses every extractor that would read one. Comparison against a full Date, the
bound-versus-bound comparison, and every configured profile keep their existing owners.
-/

namespace A12Kernel

/-- One extracted endpoint of a yearless range: only the labels the declaration retains. -/
inductive YearlessDateRangeBoundValue where
  | month (month : Nat)
  | monthDay (value : MonthDayValue)
  deriving Repr, DecidableEq

namespace YearlessDateRangeBoundValue

/-- Project the retained labels into the shared calendar-part carrier. An absent component is
the literal zero a partially known Date uses; the static component gate keeps it unobservable. -/
def parts : YearlessDateRangeBoundValue → DateParts
  | .month value => { year := 0, month := value, day := 0 }
  | .monthDay value => { year := 0, month := value.month, day := value.day }

/-- Complete one retained endpoint label into a comparable yearless date by its authored
position. A month-only label completes to the first day at a start and to the greatest day that
month can ever have at a finish, which is the same asymmetric rule `YearlessInterval` already
uses for a whole range; a day-bearing label keeps its authored day at either position. -/
def completed (bound : DateRangeBound) :
    YearlessDateRangeBoundValue → MonthDayValue
  | .month value =>
      let interval := YearlessInterval.ofMonthPair value value
      match bound with
      | .start => interval.start
      | .finish => interval.finish
  | .monthDay value => value

end YearlessDateRangeBoundValue

/-- Select one endpoint's retained labels from a yearless checked cell value. An exact value
belongs to the completed route and has no yearless projection here. -/
def DateRangeCellValue.selectYearlessBound (bound : DateRangeBound) :
    DateRangeCellValue → Option YearlessDateRangeBoundValue
  | .yearlessMonth start finish =>
      some (.month (match bound with | .start => start | .finish => finish))
  | .yearlessMonthDay start finish =>
      some (.monthDay (match bound with | .start => start | .finish => finish))
  | .exact _ => none

/-- Static refusal while checking an unconfigured yearless DateRange bound. -/
inductive YearlessDateRangeBoundElabError where
  | source (cause : DirectDateRangeElabError)
  | notYearless (source : FieldId) (format separator : String)
  | baseYearConfigured (source : FieldId)
  | componentNotExposed (source : FieldId) (part : DateNumericPart)
  deriving Repr, DecidableEq

namespace YearlessDateRangeBoundElabError

/-- Only the component refusal has an established Kernel diagnostic. The other three are local
routing facts: a configured or year-bearing declaration belongs to the exact owner. -/
def diagnostic? : YearlessDateRangeBoundElabError → Option KernelStaticDiagnostic
  | .componentNotExposed _ _ => some .wrongDateFormatForOp
  | .source cause => cause.diagnostic?
  | .notYearless _ _ _ | .baseYearConfigured _ => none

end YearlessDateRangeBoundElabError

/-- One selected endpoint of a yearless DateRange field in a model with no Base Year. The source
carries its own reading scope, so this certificate serves a scalar read and a read at a rule's row
without a second structure. -/
structure CheckedYearlessDateRangeBound (model : FlatModel)
    extends CheckedDateRangeSource model where
  private mk ::
  bound : DateRangeBound
  sourceYearless : toCheckedDateRangeSource.format.includesYear = false
  modelUnconfigured : model.baseYear = none

/-- Certify one endpoint at a reading scope: the declaration must be yearless and the model must
supply no Base Year, because a configured model completes the value and belongs to the exact owner. -/
def elaborateYearlessDateRangeBoundIn (model : FlatModel)
    (scope : List RepeatableLevel) (sourceField : FieldId)
    (bound : DateRangeBound) :
    Except YearlessDateRangeBoundElabError
      (CheckedYearlessDateRangeBound model) := do
  let source ← elaborateDateRangeSourceIn model scope sourceField
    |>.mapError .source
  if hYearless : source.format.includesYear = false then
    if hModel : model.baseYear = none then
      pure {
        toCheckedDateRangeSource := source
        bound
        sourceYearless := hYearless
        modelUnconfigured := hModel }
    else
      throw (.baseYearConfigured sourceField)
  else
    throw (.notYearless sourceField source.policy.format source.policy.separator)

/-- The scalar instance: an endpoint read where the reading rule iterates no level. -/
def elaborateYearlessDateRangeBound (model : FlatModel) (sourceField : FieldId)
    (bound : DateRangeBound) :
    Except YearlessDateRangeBoundElabError
      (CheckedYearlessDateRangeBound model) :=
  elaborateYearlessDateRangeBoundIn model [] sourceField bound

/-- One checked yearless endpoint composed with the existing typed Date-component consumer. -/
structure CheckedYearlessDateRangeBoundComponent (model : FlatModel)
    extends CheckedYearlessDateRangeBound model where
  part : DateNumericPart
  partExposed :
    part.admittedBy false toCheckedYearlessDateRangeBound.format.components = true

/-- Certify one numeric component of a yearless endpoint. The gate is the established direct
extractor admission over the declaration's own component set, with no Base Year to supplement
the year, so a month-only declaration exposes month and quarter alone. -/
def elaborateYearlessDateRangeBoundComponent (model : FlatModel)
    (sourceField : FieldId) (bound : DateRangeBound) (part : DateNumericPart) :
    Except YearlessDateRangeBoundElabError
      (CheckedYearlessDateRangeBoundComponent model) := do
  let source ← elaborateYearlessDateRangeBound model sourceField bound
  if hExposed : part.admittedBy false source.format.components = true then
    pure { toCheckedYearlessDateRangeBound := source, part, partExposed := hExposed }
  else
    throw (.componentNotExposed sourceField part)

/-- Defensive failure while reading one yearless endpoint. -/
inductive YearlessDateRangeBoundFault where
  | source (cause : DirectDateRangeFault)
  | sourceValueProfile (source : FieldId) (value : DateRangeCellValue)
  deriving Repr, DecidableEq

/-- One-read result retaining the retained endpoint labels beside their numeric component. -/
structure YearlessDateRangeBoundComponentResult where
  selected : CellObservation YearlessDateRangeBoundValue
  component : NumericOperand
  deriving Repr, DecidableEq

namespace CheckedYearlessDateRangeBound

/-- Select the endpoint's retained labels from one already-read range observation. Every read route
shares this, so an addressed read and a keyed lookup cannot disagree about emptiness, unavailability,
or which end they took. An exact runtime carrier still fails defensively if a malformed checked
document crosses the static boundary. -/
def projectYearless (source : FieldId) (bound : DateRangeBound) :
    CellObservation DateRangeCellValue →
    Except YearlessDateRangeBoundFault
      (CellObservation YearlessDateRangeBoundValue)
  | .empty => .ok .empty
  | .value value =>
      match value.selectYearlessBound bound with
      | some selected => .ok (.value selected)
      | none => .error (.sourceValueProfile source value)
  | .unknown cause => .ok (.unknown cause)
  | .poison cause => .ok (.poison cause)

/-- Read the range once at the row the environment binds and select the endpoint's retained labels. -/
def evaluateAt (operation : CheckedYearlessDateRangeBound model)
    (environment : Env) (phase : Phase) (input : CheckedDocument model) :
    Except YearlessDateRangeBoundFault
      (CellObservation YearlessDateRangeBoundValue) := do
  let observed ←
    operation.toCheckedDateRangeSource.evaluateAt environment phase input
      |>.mapError .source
  projectYearless operation.source.id operation.bound observed

/-- The scalar instance: a read at the document root. -/
def evaluate (operation : CheckedYearlessDateRangeBound model) (phase : Phase)
    (input : CheckedDocument model) :
    Except YearlessDateRangeBoundFault
      (CellObservation YearlessDateRangeBoundValue) :=
  operation.evaluateAt [] phase input

end CheckedYearlessDateRangeBound

namespace CheckedYearlessDateRangeBoundComponent

/-- Project one already-selected yearless endpoint through the established typed component
semantics, so empty substitutes symmetric zero and formal unavailability keeps its cause. -/
def evaluateSelected (operation : CheckedYearlessDateRangeBoundComponent model)
    (selected : CellObservation YearlessDateRangeBoundValue) :
    YearlessDateRangeBoundComponentResult := {
  selected
  component := operation.part.fromObservation (·.parts) selected
}

/-- Read the certified source once in validation phase, then project the selected endpoint's
numeric component. -/
def evaluate (operation : CheckedYearlessDateRangeBoundComponent model)
    (input : CheckedDocument model) :
    Except YearlessDateRangeBoundFault
      YearlessDateRangeBoundComponentResult := do
  let selected ←
    operation.toCheckedYearlessDateRangeBound.evaluate .validation input
  pure (operation.evaluateSelected selected)

end CheckedYearlessDateRangeBoundComponent

end A12Kernel
