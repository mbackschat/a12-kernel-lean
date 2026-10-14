import A12Kernel.Semantics.TemporalFormat
import A12Kernel.Semantics.FlatComparisonInputs
import A12Kernel.Semantics.DateDifference

namespace A12Kernel

/-- A date literal keeps written year presence apart from its model-dependent completion.
The omitted-year calendar gate uses a common year (spec/05 §1), even in a leap Base Year. -/
structure AuthoredDateLiteral where
  year : Option Int
  month : Nat
  day : Nat
  deriving Repr, DecidableEq

namespace AuthoredDateLiteral

def valid (literal : AuthoredDateLiteral) : Bool :=
  (CivilDate.ofYmd? (literal.year.getD 2023) literal.month literal.day).isSome

def components (literal : AuthoredDateLiteral) : TemporalComponents :=
  { TemporalComponents.fullDate with year := literal.year.isSome }

def parts (literal : AuthoredDateLiteral) (anchorYear : Int) : DateParts :=
  { year := literal.year.getD anchorYear, month := literal.month, day := literal.day }

end AuthoredDateLiteral

/-- One checked operand of a calendar difference. `clock` admits `Now`, which only the day difference
accepts: `DifferenceInMonths` and `DifferenceInYears` refuse it with `MVK_WRONG_DATE_FORMAT_FOR_OP` on
every route, as they refuse a DateTime field
([checkpoint](../../docs/sources/having-filter-probes.md#src-having-now-day-difference)). -/
inductive ResolvedDateDifferenceOperand (Field : Type := FlatTemporalField) (clock : Bool := false) where
  | literal (source : AuthoredDateLiteral) (anchorYear : Int)
  | field (source : Field)
  | baseYear (year : Int) (source : BaseYearDateSource)
  | today (profile : ModelZone.ConcreteProfile)
  | now (profile : ModelZone.ConcreteProfile) (admitted : clock = true)
  deriving Repr, DecidableEq

namespace ResolvedDateDifferenceOperand

/-- Read the model-local civil day from this evaluation's clock, as required by spec/05 §7.
No instant is cached in the checked operand. -/
def todayParts? (profile : ModelZone.ConcreteProfile) (world? : Option World) : Option DateParts := do
  let world ← world?
  pure (← profile.localDate? world.now).civil.parts


def fields : ResolvedDateDifferenceOperand Field clock → List Field
  | .field source => [source]
  | .literal _ _ | .baseYear _ _ | .today _ | .now _ _ => []

def componentsWith (fieldComponents : Field → TemporalComponents) :
    ResolvedDateDifferenceOperand Field clock → TemporalComponents
  | .literal source _ => source.components
  | .field source => fieldComponents source
  | .baseYear _ _ => TemporalComponents.baseYear
  | .today _ => TemporalComponents.fullDate
  | .now _ _ => TemporalComponents.now

def readDateOperand [Monad m] (read : Field → m CellObservation)
    (today : ModelZone.ConcreteProfile → m DateDifferenceOperand) :
    ResolvedDateDifferenceOperand Field → m DateDifferenceOperand
  | .literal source year => pure (.value (source.parts year))
  | .field source => DateDifferenceOperand.ofObservation <$> read source
  | .baseYear year source => pure (.value (source.parts year))
  | .today profile => today profile
  | .now _ admitted => nomatch admitted

/-- `Now` is the evaluation's exact instant, read at its local wall label in the model zone. -/
def readDayOperand [Monad m] (profile : ModelZone.ConcreteProfile)
    (read : Field → m CellObservation) (today : ModelZone.ConcreteProfile → m CalendarDayDifferenceOperand)
    (now : ModelZone.ConcreteProfile → m CalendarDayDifferenceOperand) :
    ResolvedDateDifferenceOperand Field clock → m CalendarDayDifferenceOperand
  | .literal source year => pure (.ofParts profile (source.parts year))
  | .field source => CalendarDayDifferenceOperand.ofObservation <$> read source
  | .baseYear year source => pure (.ofBaseYear profile year source)
  | .today sourceProfile => today sourceProfile
  | .now sourceProfile _ => now sourceProfile

end ResolvedDateDifferenceOperand

end A12Kernel
