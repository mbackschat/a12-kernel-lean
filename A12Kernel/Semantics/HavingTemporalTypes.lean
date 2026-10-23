import A12Kernel.Semantics.HavingNumericAtom
import A12Kernel.Semantics.TimeConstructionInputs
import A12Kernel.Semantics.HavingDateValidity
import A12Kernel.Semantics.ScalarTemporalValue
import A12Kernel.Semantics.TemporalExpression
import A12Kernel.Semantics.HavingTemporalSelection
import A12Kernel.Semantics.PartialDateInput
import A12Kernel.Semantics.NumericExpressionStructure

namespace A12Kernel

/-- Recursive constructor projections preserve the direct leaf's declaration and capture origin
while reusing the ordinary temporal expression tree (spec/05 §§3,6). -/
inductive HavingTemporalComponent (Source Part Temporal : Type) where
  | direct (origin : HavingOrigin) (source : Source)
  | expression (part : Part) (source : Temporal)
  deriving Repr, DecidableEq

inductive HavingTemporalOperation where
  | constructor (operation : ScalarTemporalConstructorOp)
  | extremum (operator : TemporalExtremumOp)
  deriving Repr, DecidableEq

/-- Partial-Date completion retains the declaration profile and authored interval endpoint (spec/05 §3). -/
structure HavingPartialDateSource where
  reference : HavingTemporalRef
  format : FullDateTargetFormat
  mode : TemporalPartialMode
  youngerThan1900Check : Bool
  endpoint : ValueAsDateEndpoint
  deriving Repr, DecidableEq

inductive HavingTemporalAtom where
  | shift (unit : TemporalOperationUnit) (source : TemporalExpressionOf HavingTemporalAtom HavingTemporalOperation)
      (amount : AuthoredNumericExpr (HavingNumericAtomOf (TemporalExpressionOf HavingTemporalAtom HavingTemporalOperation)))
  | partialDate (source : HavingPartialDateSource)
  | selection (kind : HavingTemporalSelection) (slots : List (HavingFieldListSlot HavingTemporalSelectionRef))
  | field (reference : HavingTemporalRef)
  | rangeBound (origin : HavingOrigin) (source : FlatDateRangeField) (components : TemporalComponents) (bound : DateRangeBound)
  | timeConstruction (components : TimeComponentPrefix (HavingTemporalComponent ResolvedTimeConstructionSource TimeNumericPart (TemporalExpressionOf HavingTemporalAtom HavingTemporalOperation)))
  | dateConstruction (components : ResolvedConstructedDateComponents (HavingTemporalComponent ResolvedConstructedDateSource DateNumericPart (TemporalExpressionOf HavingTemporalAtom HavingTemporalOperation)))
  | dateLiteral (value : DateParts) (yearPresent : Bool)
  | timeLiteral (value : TimeOfDay)
  | dateTimeLiteral (value : LegacyCalendarLabel)
  | today
  | now
  | baseYearBound (bound : BaseYearRangeEndpoint)

abbrev HavingTemporalCore := TemporalExpressionOf HavingTemporalAtom HavingTemporalOperation
abbrev HavingTemporalAmount := AuthoredNumericExpr (HavingNumericAtomOf HavingTemporalCore)

abbrev HavingDateComponent := HavingTemporalComponent ResolvedConstructedDateSource DateNumericPart HavingTemporalCore
abbrev HavingTimeComponent := HavingTemporalComponent ResolvedTimeConstructionSource TimeNumericPart HavingTemporalCore
abbrev HavingDateComponents := ResolvedConstructedDateComponents HavingDateComponent
abbrev HavingTimeComponents := TimeComponentPrefix HavingTimeComponent

namespace HavingTemporalAtom
mutual
private def format : HavingTemporalAtom → Std.Format
  | .selection kind slots => "selection " ++ repr kind ++ " " ++ repr slots
  | .field ref => "field " ++ repr ref
  | .partialDate source => "partialDate " ++ repr source
  | .shift unit source amount => "shift " ++ repr unit ++ " (" ++ formatCore source ++ ") (" ++ formatAmount amount ++ ")"
  | .rangeBound origin source components bound => "rangeBound " ++ repr (origin, source, components, bound)
  | .dateConstruction components => formatDate components
  | .timeConstruction components => formatTime components
  | .dateLiteral value year => "dateLiteral " ++ repr (value, year)
  | .timeLiteral value => "timeLiteral " ++ repr value
  | .dateTimeLiteral value => "dateTimeLiteral " ++ repr value
  | .today => "today"
  | .now => "now"
  | .baseYearBound bound => "baseYearBound " ++ repr bound
termination_by value => sizeOf value
decreasing_by all_goals first | decreasing_tactic | (simp_all +arith; omega)
private def formatCore : HavingTemporalCore → Std.Format
  | .atom atom => format atom
  | .apply op first rest => "apply " ++ repr op ++ " (" ++ formatCore first ++ ") [" ++
      Std.Format.joinSep (rest.map formatCore) ", " ++ "]"
termination_by value => sizeOf value
decreasing_by all_goals first | decreasing_tactic | (simp_all +arith; omega)
private def formatAmount (amount : HavingTemporalAmount) : Std.Format :=
  amount.formatWithSubterm fun atom hAtom => atom.formatWithSubterm fun source hSource =>
    have _ : sizeOf source < sizeOf amount := Nat.lt_trans hSource hAtom
    formatCore source
termination_by sizeOf amount
decreasing_by all_goals first | decreasing_tactic | (simp_all +arith; omega)
private def formatDateComponent : HavingDateComponent → Std.Format
  | .direct origin source => "direct " ++ repr (origin, source)
  | .expression part source => "expression " ++ repr part ++ " (" ++ formatCore source ++ ")"
termination_by value => sizeOf value
decreasing_by all_goals first | decreasing_tactic | (simp_all +arith; omega)
private def formatTimeComponent : HavingTimeComponent → Std.Format
  | .direct origin source => "direct " ++ repr (origin, source)
  | .expression part source => "expression " ++ repr part ++ " (" ++ formatCore source ++ ")"
termination_by value => sizeOf value
decreasing_by all_goals first | decreasing_tactic | (simp_all +arith; omega)
private def formatDate : HavingDateComponents → Std.Format
  | ⟨day, month, year, profile⟩ => "Date " ++ repr profile ++ " (" ++ formatDateComponent day ++ ") (" ++ formatDateComponent month ++ ") (" ++
      (match year with
      | .complete year => formatDateComponent year
      | .baseYear year => "baseYear " ++ repr year
      | .centuryAndShortYear century shortYear => formatDateComponent century ++ ", " ++ formatDateComponent shortYear) ++ ")"
termination_by value => sizeOf value
decreasing_by all_goals first | decreasing_tactic | (simp_all +arith; omega)
private def formatTime : HavingTimeComponents → Std.Format
  | .empty => "Time"
  | .hour hour => "Time " ++ formatTimeComponent hour
  | .minute hour minute => "Time " ++ formatTimeComponent hour ++ ", " ++ formatTimeComponent minute
  | .second hour minute second => "Time " ++ formatTimeComponent hour ++ ", " ++ formatTimeComponent minute ++ ", " ++ formatTimeComponent second
termination_by value => sizeOf value
decreasing_by all_goals first | decreasing_tactic | (simp_all +arith; omega)

end
instance : Repr HavingTemporalAtom where
  reprPrec source _ := format source

mutual
private def decideEqual (left right : HavingTemporalAtom) : Decidable (left = right) := by
  cases left <;> cases right
  all_goals first | (apply isFalse; intro h; cases h; done) | skip
  case selection.selection kind slots other next =>
    exact decidable_of_iff (kind = other ∧ slots = next) (by simp)
  case field.field ref next => exact decidable_of_iff (ref = next) (by simp)
  case rangeBound.rangeBound origin source components bound nextOrigin nextSource nextComponents nextBound =>
    exact decidable_of_iff (origin = nextOrigin ∧ source = nextSource ∧ components = nextComponents ∧ bound = nextBound) (by simp)
  case dateConstruction.dateConstruction first next =>
    letI := decideDateEqual first next
    exact decidable_of_iff (first = next) (by simp)
  case timeConstruction.timeConstruction first next =>
    letI := decideTimeEqual first next
    exact decidable_of_iff (first = next) (by simp)
  case dateLiteral.dateLiteral value year next other =>
    exact decidable_of_iff (value = next ∧ year = other) (by simp)
  case timeLiteral.timeLiteral value next => exact decidable_of_iff (value = next) (by simp)
  case dateTimeLiteral.dateTimeLiteral value next => exact decidable_of_iff (value = next) (by simp)
  case baseYearBound.baseYearBound value next => exact decidable_of_iff (value = next) (by simp)
  case shift.shift unit source amount nextUnit nextSource nextAmount =>
    letI := decideCoreEqual source nextSource
    letI := decideAmountEqual amount nextAmount
    exact decidable_of_iff (unit = nextUnit ∧ source = nextSource ∧ amount = nextAmount) (by simp)
  case partialDate.partialDate source next => exact decidable_of_iff (source = next) (by simp)
  case today.today => exact isTrue rfl
  case now.now => exact isTrue rfl
private def decideCoreEqual (left right : HavingTemporalCore) : Decidable (left = right) :=
  match left, right with
  | .atom first, .atom next =>
      letI := decideEqual first next
      decidable_of_iff (first = next) (by simp)
  | .atom _, .apply _ _ _ | .apply _ _ _, .atom _ => isFalse (by intro h; cases h)
  | .apply op first rest, .apply other next remaining =>
      letI := decideCoreEqual first next
      letI := decideCoreListEqual rest remaining
      decidable_of_iff (op = other ∧ first = next ∧ rest = remaining) (by simp)
private def decideCoreListEqual (left right : List HavingTemporalCore) : Decidable (left = right) :=
  match left, right with
  | [], [] => isTrue rfl
  | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
  | first :: rest, next :: remaining =>
      letI := decideCoreEqual first next
      letI := decideCoreListEqual rest remaining
      decidable_of_iff (first = next ∧ rest = remaining) (by simp)
private def decideDateComponentEqual (left right : HavingDateComponent) : Decidable (left = right) :=
  match left, right with
  | .direct origin source, .direct nextOrigin nextSource =>
      decidable_of_iff (origin = nextOrigin ∧ source = nextSource) (by simp)
  | .direct _ _, .expression _ _ | .expression _ _, .direct _ _ => isFalse (by intro h; cases h)
  | .expression part source, .expression nextPart nextSource =>
      letI := decideCoreEqual source nextSource
      decidable_of_iff (part = nextPart ∧ source = nextSource) (by simp)
private def decideTimeComponentEqual (left right : HavingTimeComponent) : Decidable (left = right) :=
  match left, right with
  | .direct origin source, .direct nextOrigin nextSource =>
      decidable_of_iff (origin = nextOrigin ∧ source = nextSource) (by simp)
  | .direct _ _, .expression _ _ | .expression _ _, .direct _ _ => isFalse (by intro h; cases h)
  | .expression part source, .expression nextPart nextSource =>
      letI := decideCoreEqual source nextSource
      decidable_of_iff (part = nextPart ∧ source = nextSource) (by simp)
private def decideAmountEqual (left right : HavingTemporalAmount) : Decidable (left = right) :=
  left.decideEqWithSubterm right fun a b _ _ =>
    a.decideEqWithSubterm b fun left right _ _ => decideCoreEqual left right

private def decideDateYearEqual (left right : ResolvedConstructedDateYear HavingDateComponent) : Decidable (left = right) := by
  cases left <;> cases right
  all_goals first | (apply isFalse; intro h; cases h; done) | skip
  case complete.complete source next =>
    letI := decideDateComponentEqual source next
    exact decidable_of_iff (source = next) (by simp)
  case baseYear.baseYear source next => exact decidable_of_iff (source = next) (by simp)
  case centuryAndShortYear.centuryAndShortYear century year other next =>
    letI := decideDateComponentEqual century other
    letI := decideDateComponentEqual year next
    exact decidable_of_iff (century = other ∧ year = next) (by simp)
private def decideDateEqual (left right : HavingDateComponents) : Decidable (left = right) := by
  cases left with | mk day month year profile =>
    cases right with | mk nextDay nextMonth nextYear nextProfile =>
      letI := decideDateComponentEqual day nextDay
      letI := decideDateComponentEqual month nextMonth
      letI := decideDateYearEqual year nextYear
      exact decidable_of_iff (day = nextDay ∧ month = nextMonth ∧ year = nextYear ∧ profile = nextProfile) (by simp)
private def decideTimeEqual (left right : HavingTimeComponents) : Decidable (left = right) := by
  cases left <;> cases right
  all_goals first | (apply isFalse; intro h; cases h; done) | skip
  case empty.empty => exact isTrue rfl
  case hour.hour source next =>
    letI := decideTimeComponentEqual source next
    exact decidable_of_iff (source = next) (by simp)
  case minute.minute hour minute nextHour nextMinute =>
    letI := decideTimeComponentEqual hour nextHour
    letI := decideTimeComponentEqual minute nextMinute
    exact decidable_of_iff (hour = nextHour ∧ minute = nextMinute) (by simp)
  case second.second hour minute second nextHour nextMinute nextSecond =>
    letI := decideTimeComponentEqual hour nextHour
    letI := decideTimeComponentEqual minute nextMinute
    letI := decideTimeComponentEqual second nextSecond
    exact decidable_of_iff (hour = nextHour ∧ minute = nextMinute ∧ second = nextSecond) (by simp)
end
instance : DecidableEq HavingTemporalAtom := decideEqual
end HavingTemporalAtom

mutual
def HavingTemporalCore.allAtoms : HavingTemporalCore → List HavingTemporalAtom
  | .atom source => source :: constructorAtoms source
  | .apply _ first rest => HavingTemporalCore.allAtoms first ++ rest.flatMap HavingTemporalCore.allAtoms
termination_by value => sizeOf value
decreasing_by all_goals first | decreasing_tactic | (simp_all +arith; omega)
private def constructorAtoms : HavingTemporalAtom → List HavingTemporalAtom
  | .shift _ source amount => HavingTemporalCore.allAtoms source ++ amountAtoms amount
  | .dateConstruction source => dateAtoms source
  | .timeConstruction source => timeAtoms source
  | _ => []
termination_by value => sizeOf value
decreasing_by all_goals first | decreasing_tactic | (simp_all +arith; omega)
private def amountAtoms (amount : HavingTemporalAmount) : List HavingTemporalAtom :=
  amount.flatMapAtomsSubterm fun atom hAtom => atom.flatMapTemporalSubterm fun source hSource =>
    have _ : sizeOf source < sizeOf amount := Nat.lt_trans hSource hAtom
    HavingTemporalCore.allAtoms source
termination_by sizeOf amount
decreasing_by all_goals first | decreasing_tactic | (simp_all +arith; omega)
private def dateOperandAtoms : HavingDateComponent → List HavingTemporalAtom
  | .expression _ source => HavingTemporalCore.allAtoms source
  | .direct _ _ => []
termination_by value => sizeOf value
decreasing_by all_goals first | decreasing_tactic | (simp_all +arith; omega)
private def timeOperandAtoms : HavingTimeComponent → List HavingTemporalAtom
  | .expression _ source => HavingTemporalCore.allAtoms source
  | .direct _ _ => []
termination_by value => sizeOf value
decreasing_by all_goals first | decreasing_tactic | (simp_all +arith; omega)
private def dateAtoms : HavingDateComponents → List HavingTemporalAtom
  | ⟨day, month, year, _⟩ => dateOperandAtoms day ++ dateOperandAtoms month ++ match year with
      | .complete year => dateOperandAtoms year
      | .baseYear _ => []
      | .centuryAndShortYear century shortYear => dateOperandAtoms century ++ dateOperandAtoms shortYear
termination_by value => sizeOf value
decreasing_by all_goals first | decreasing_tactic | (simp_all +arith; omega)
private def timeAtoms : HavingTimeComponents → List HavingTemporalAtom
  | .empty => []
  | .hour hour => timeOperandAtoms hour
  | .minute hour minute => timeOperandAtoms hour ++ timeOperandAtoms minute
  | .second hour minute second => timeOperandAtoms hour ++ timeOperandAtoms minute ++ timeOperandAtoms second
termination_by value => sizeOf value
decreasing_by all_goals first | decreasing_tactic | (simp_all +arith; omega)

end

structure HavingConstructedDate where
  components : HavingDateComponents
  baseYear : Option Int
  deriving Repr, DecidableEq

structure HavingTemporalExpression where
  core : TemporalExpressionOf HavingTemporalAtom HavingTemporalOperation
  profile : ModelZone.ConcreteProfile
  baseYear : Option Int
  grouped : Bool := false
  deriving Repr, DecidableEq

end A12Kernel
