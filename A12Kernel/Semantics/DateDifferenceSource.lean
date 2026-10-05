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

inductive ResolvedDateDifferenceOperand (Field : Type := FlatTemporalField) where
  | literal (source : AuthoredDateLiteral) (anchorYear : Int)
  | field (source : Field)
  | baseYear (year : Int) (source : BaseYearDateSource)
  | today (profile : ModelZone.ConcreteProfile)
  deriving Repr, DecidableEq

namespace ResolvedDateDifferenceOperand

def fields : ResolvedDateDifferenceOperand Field → List Field
  | .field source => [source]
  | .literal _ _ | .baseYear _ _ | .today _ => []

def componentsWith (fieldComponents : Field → TemporalComponents) :
    ResolvedDateDifferenceOperand Field → TemporalComponents
  | .literal source _ => source.components
  | .field source => fieldComponents source
  | .baseYear _ _ => TemporalComponents.baseYear
  | .today _ => TemporalComponents.fullDate

def readDateOperand [Monad m] (read : Field → m CellObservation)
    (today : ModelZone.ConcreteProfile → m DateDifferenceOperand) :
    ResolvedDateDifferenceOperand Field → m DateDifferenceOperand
  | .literal source year => pure (.value (source.parts year))
  | .field source => DateDifferenceOperand.ofObservation <$> read source
  | .baseYear year source => pure (.value (source.parts year))
  | .today profile => today profile

def readDayOperand [Monad m] (profile : ModelZone.ConcreteProfile)
    (read : Field → m CellObservation) (today : ModelZone.ConcreteProfile → m CalendarDayDifferenceOperand) :
    ResolvedDateDifferenceOperand Field → m CalendarDayDifferenceOperand
  | .literal source year => pure (.ofParts profile (source.parts year))
  | .field source => CalendarDayDifferenceOperand.ofObservation <$> read source
  | .baseYear year source => pure (.ofBaseYear profile year source)
  | .today sourceProfile => today sourceProfile

end ResolvedDateDifferenceOperand

end A12Kernel
