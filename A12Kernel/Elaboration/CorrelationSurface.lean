import A12Kernel.Elaboration.CorrelationError
import A12Kernel.Elaboration.CustomCondition
/-! Authored correlated-filter forms and binding reads. -/

namespace A12Kernel

structure SurfaceHavingNumberRef where
  origin : HavingOrigin
  field : SurfaceFieldPath
  deriving Repr, DecidableEq

structure SurfaceHavingRepetitionRef where
  origin : HavingOrigin
  group : SurfaceGroupReference
  deriving Repr, DecidableEq

/-- A surface text filter reference. The path is kind-neutral; the consuming leaf decides which
    declaration projection must accept it. -/
structure SurfaceHavingStringRef where
  origin : HavingOrigin
  field : SurfaceFieldPath
  projectionRef : EnumerationProjectionRef := .stored
  deriving Repr, DecidableEq

/-- A surface presence filter reference. Presence accepts any declared field, so no kind projection
    stands between this path and the checked reference. -/
structure SurfaceHavingPresenceRef where
  origin : HavingOrigin
  field : SurfaceFieldPath
  deriving Repr, DecidableEq

structure SurfaceHavingTemporalRef where
  origin : HavingOrigin
  field : SurfaceFieldPath
  deriving Repr, DecidableEq

inductive SurfaceHavingDateComponent (Temporal : Type := Empty) where
  | field (reference : SurfaceHavingPresenceRef)
  | constant (source : String)
  | extractor (part : DateNumericPart) (reference : SurfaceHavingPresenceRef)
  | baseYearExtractor (source : BaseYearDateSource) (part : DateNumericPart)
  | clockExtractor (point : ConstructedDatePointInTime) (part : DateNumericPart)
  | expression (part : DateNumericPart) (source : Temporal)
  deriving Repr, DecidableEq

inductive SurfaceHavingTimeComponent (Temporal : Type := Empty) where
  | field (reference : SurfaceHavingPresenceRef)
  | constant (value : String)
  | extractor (part : TimeNumericPart) (reference : SurfaceHavingPresenceRef)
  | nowExtractor (part : TimeNumericPart)
  | expression (part : TimeNumericPart) (source : Temporal)
  deriving Repr, DecidableEq

inductive SurfaceHavingCollectionCount where
  | filledFields (source : SurfaceHavingEntitySource)
  | numberValue (expected : Rat) (source : SurfaceHavingEntitySource)
  | tokenValue (expected : String) (source : SurfaceHavingEntitySource)
  | booleanValue (expected : Bool) (source : SurfaceHavingEntitySource)
  deriving Repr, DecidableEq

def SurfaceHavingCollectionCount.source : SurfaceHavingCollectionCount → SurfaceHavingEntitySource
  | .filledFields source | .numberValue _ source | .tokenValue _ source | .booleanValue _ source => source

inductive SurfaceHavingNumericAtomOf (Temporal : Type) where
  | temporalDifference (unit : TemporalOperationUnit) (left right : Temporal)
  | firstFilled (source : SurfaceHavingEntitySource)
  | groupCount (source : SurfaceHavingEntitySource)
  | product (source : SurfaceHavingEntitySource)
  | collectionCount (source : SurfaceHavingCollectionCount)
  | aggregate (op : NumericAggregateOp) (source : SurfaceHavingEntitySource)
  | dateDifference (unit : DateDifferenceUnit) (left right : SurfaceDateDifferenceOperand SurfaceHavingTemporalRef)
  | dayDifference (left right : SurfaceDateDifferenceOperand SurfaceHavingTemporalRef)
  | dateTimeDifference (unit : DateTimeSubdayUnit) (left right : SurfaceDateDifferenceOperand SurfaceHavingTemporalRef)
  | baseYear
  | baseYearDatePart (source : BaseYearDateSource) (part : DateNumericPart)
  | clockPart (source : HavingClockSource) (part : TemporalNumericPart)
  | fieldValueAsNumber (reference : SurfaceHavingStringRef)
  | field (reference : SurfaceHavingNumberRef)
  | stringLength (origin : HavingOrigin) (field : SurfaceFieldPath)
  | stringRange (origin : HavingOrigin) (field : SurfaceFieldPath) (start finish : Nat)
  | dateRangeBoundPart (origin : HavingOrigin) (field : SurfaceFieldPath) (bound : DateRangeBound) (part : DateNumericPart)
  | temporalExpressionPart (part : TemporalNumericPart) (source : Temporal)
  | temporalPart (origin : HavingOrigin) (field : SurfaceFieldPath) (part : TemporalNumericPart)
  | repetition (reference : SurfaceHavingRepetitionRef)
  deriving Repr, DecidableEq


namespace SurfaceHavingNumericAtomOf

def formatWithSubterm [SizeOf Temporal] (atom : SurfaceHavingNumericAtomOf Temporal)
    (format : (source : Temporal) → sizeOf source < sizeOf atom → Std.Format) : Std.Format :=
  match atom with
  | .temporalDifference a0 a1 a2 => "temporalDifference" ++ " " ++ (repr a0) ++ " " ++ (format a1 (by simp_all; omega)) ++ " " ++ (format a2 (by simp_all; omega))
  | .firstFilled a0 => "firstFilled" ++ " " ++ (repr a0)
  | .groupCount a0 => "groupCount" ++ " " ++ (repr a0)
  | .product a0 => "product" ++ " " ++ (repr a0)
  | .collectionCount a0 => "collectionCount" ++ " " ++ (repr a0)
  | .aggregate a0 a1 => "aggregate" ++ " " ++ (repr a0) ++ " " ++ (repr a1)
  | .dateDifference a0 a1 a2 => "dateDifference" ++ " " ++ (repr a0) ++ " " ++ (repr a1) ++ " " ++ (repr a2)
  | .dayDifference a0 a1 => "dayDifference" ++ " " ++ (repr a0) ++ " " ++ (repr a1)
  | .dateTimeDifference a0 a1 a2 => "dateTimeDifference" ++ " " ++ (repr a0) ++ " " ++ (repr a1) ++ " " ++ (repr a2)
  | .baseYear  => "baseYear"
  | .baseYearDatePart a0 a1 => "baseYearDatePart" ++ " " ++ (repr a0) ++ " " ++ (repr a1)
  | .clockPart a0 a1 => "clockPart" ++ " " ++ (repr a0) ++ " " ++ (repr a1)
  | .fieldValueAsNumber a0 => "fieldValueAsNumber" ++ " " ++ (repr a0)
  | .field a0 => "field" ++ " " ++ (repr a0)
  | .stringLength a0 a1 => "stringLength" ++ " " ++ (repr a0) ++ " " ++ (repr a1)
  | .stringRange a0 a1 a2 a3 => "stringRange" ++ " " ++ (repr a0) ++ " " ++ (repr a1) ++ " " ++ (repr a2) ++ " " ++ (repr a3)
  | .dateRangeBoundPart a0 a1 a2 a3 => "dateRangeBoundPart" ++ " " ++ (repr a0) ++ " " ++ (repr a1) ++ " " ++ (repr a2) ++ " " ++ (repr a3)
  | .temporalExpressionPart a0 a1 => "temporalExpressionPart" ++ " " ++ (repr a0) ++ " " ++ (format a1 (by simp_all; omega))
  | .temporalPart a0 a1 a2 => "temporalPart" ++ " " ++ (repr a0) ++ " " ++ (repr a1) ++ " " ++ (repr a2)
  | .repetition a0 => "repetition" ++ " " ++ (repr a0)

def decideEqWithSubterm [SizeOf Temporal] (left right : SurfaceHavingNumericAtomOf Temporal)
    (equal : (a b : Temporal) → sizeOf a < sizeOf left → sizeOf b < sizeOf right → Decidable (a = b)) :
    Decidable (left = right) := by
  cases left <;> cases right
  all_goals first | (apply isFalse; intro h; cases h; done) | skip
  case temporalDifference.temporalDifference a0 a1 a2 b0 b1 b2 =>
    letI := equal a1 b1 (by simp; omega) (by simp; omega)
    letI := equal a2 b2 (by simp; omega) (by simp; omega)
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
  case firstFilled.firstFilled a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp)
  case groupCount.groupCount a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp)
  case product.product a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp)
  case collectionCount.collectionCount a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp)
  case aggregate.aggregate a0 a1 b0 b1 =>
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
  case dateDifference.dateDifference a0 a1 a2 b0 b1 b2 =>
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
  case dayDifference.dayDifference a0 a1 b0 b1 =>
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
  case dateTimeDifference.dateTimeDifference a0 a1 a2 b0 b1 b2 =>
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
  case baseYear.baseYear  =>
    exact isTrue rfl
  case baseYearDatePart.baseYearDatePart a0 a1 b0 b1 =>
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
  case clockPart.clockPart a0 a1 b0 b1 =>
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
  case fieldValueAsNumber.fieldValueAsNumber a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp)
  case field.field a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp)
  case stringLength.stringLength a0 a1 b0 b1 =>
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
  case stringRange.stringRange a0 a1 a2 a3 b0 b1 b2 b3 =>
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) (by simp)
  case dateRangeBoundPart.dateRangeBoundPart a0 a1 a2 a3 b0 b1 b2 b3 =>
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) (by simp)
  case temporalExpressionPart.temporalExpressionPart a0 a1 b0 b1 =>
    letI := equal a1 b1 (by simp; omega) (by simp; omega)
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
  case temporalPart.temporalPart a0 a1 a2 b0 b1 b2 =>
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
  case repetition.repetition a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp)

def flatMapTemporalSubterm [SizeOf Temporal] (atom : SurfaceHavingNumericAtomOf Temporal)
    (visit : (source : Temporal) → sizeOf source < sizeOf atom → List Result) : List Result :=
  match atom with
  | .temporalDifference _ left right => visit left (by simp; omega) ++ visit right (by simp; omega)
  | .temporalExpressionPart _ source => visit source (by simp; omega)
  | _ => []

end SurfaceHavingNumericAtomOf

/-- Constructor operands retain an origin at every field, including mixed captured/candidate reads. -/
inductive SurfaceHavingTemporalExpression where
  | shift (unit : TemporalOperationUnit) (source : SurfaceHavingTemporalExpression)
      (amount : AuthoredNumericExpr (SurfaceHavingNumericAtomOf SurfaceHavingTemporalExpression))
  | partialDate (reference : SurfaceHavingTemporalRef) (endpoint : ValueAsDateEndpoint)
  | selection (kind : HavingTemporalSelection) (source : SurfaceHavingEntitySource)
  | combine (operator : TemporalExtremumOp) (first : SurfaceHavingTemporalExpression) (rest : List SurfaceHavingTemporalExpression)
  | field (reference : SurfaceHavingTemporalRef)
  | rangeBound (reference : SurfaceHavingTemporalRef) (bound : DateRangeBound)
  | timeConstruction (components : TimeComponentPrefix (SurfaceHavingTimeComponent SurfaceHavingTemporalExpression))
  | dateConstruction (components : SurfaceConstructedDateComponents (SurfaceHavingDateComponent SurfaceHavingTemporalExpression))
  | dateLiteral (source : AuthoredDateLiteral)
  | timeLiteral (value : TimeOfDay)
  | dateTimeLiteral (value : LocalDateTime)
  | today
  | now
  | baseYearBound (bound : BaseYearRangeEndpoint)
  | grouped (source : SurfaceHavingTemporalExpression)
  | dateTime (date time : SurfaceHavingTemporalExpression)
  | dateFromDateTime (source : SurfaceHavingTemporalExpression)
  | timeFromDateTime (source : SurfaceHavingTemporalExpression)

abbrev SurfaceHavingTemporalAmount := AuthoredNumericExpr (SurfaceHavingNumericAtomOf SurfaceHavingTemporalExpression)

abbrev SurfaceHavingDateComponents := SurfaceConstructedDateComponents (SurfaceHavingDateComponent SurfaceHavingTemporalExpression)
abbrev SurfaceHavingTimeComponents := TimeComponentPrefix (SurfaceHavingTimeComponent SurfaceHavingTemporalExpression)

namespace SurfaceHavingTemporalExpression

private def formatNode (name : String) (arguments : List Std.Format) : Std.Format :=
  name ++ " (" ++ Std.Format.joinSep arguments ") (" ++ ")"

-- The nested-list deriving handler emits an opaque printer; TemporalExpressionOf's total
-- structural printer preserves the trusted elaboration boundary.
mutual
private def format : SurfaceHavingTemporalExpression → Std.Format
  | .selection kind source => formatNode "selection" [repr kind, repr source]
  | .combine operator first rest => formatNode "combine" [repr operator, format first,
      "[" ++ Std.Format.joinSep (rest.map format) ", " ++ "]"]
  | .field reference => formatNode "field" [repr reference]
  | .shift unit source amount => formatNode "shift" [repr unit, format source, formatAmount amount]
  | .partialDate reference endpoint => formatNode "partialDate" [repr reference, repr endpoint]
  | .rangeBound reference bound => formatNode "rangeBound" [repr reference, repr bound]
  | .timeConstruction components => formatNode "timeConstruction" [formatTime components]
  | .dateConstruction components => formatNode "dateConstruction" [formatDate components]
  | .dateLiteral source => formatNode "dateLiteral" [repr source]
  | .timeLiteral value => formatNode "timeLiteral" [repr value]
  | .dateTimeLiteral value => formatNode "dateTimeLiteral" [repr value]
  | .today => "today"
  | .now => "now"
  | .baseYearBound bound => formatNode "baseYearBound" [repr bound]
  | .grouped source => formatNode "grouped" [format source]
  | .dateTime date time => formatNode "dateTime" [format date, format time]
  | .dateFromDateTime source => formatNode "dateFromDateTime" [format source]
  | .timeFromDateTime source => formatNode "timeFromDateTime" [format source]
termination_by value => sizeOf value
decreasing_by all_goals first | decreasing_tactic | omega | (simp_all +arith; omega)
private def formatAmount (amount : SurfaceHavingTemporalAmount) : Std.Format :=
  amount.formatWithSubterm fun atom hAtom => atom.formatWithSubterm fun source hSource =>
    have _ : sizeOf source < sizeOf amount := Nat.lt_trans hSource hAtom
    format source
termination_by sizeOf amount
decreasing_by all_goals first | decreasing_tactic | omega | (simp_all +arith; omega)
private def formatDateComponent : SurfaceHavingDateComponent SurfaceHavingTemporalExpression → Std.Format
  | .field ref => formatNode "field" [repr ref]
  | .constant value => formatNode "constant" [repr value]
  | .extractor part ref => formatNode "extractor" [repr part, repr ref]
  | .baseYearExtractor source part => formatNode "baseYearExtractor" [repr source, repr part]
  | .clockExtractor source part => formatNode "clockExtractor" [repr source, repr part]
  | .expression part source => formatNode "expression" [repr part, format source]
termination_by value => sizeOf value
decreasing_by all_goals first | decreasing_tactic | omega | (simp_all +arith; omega)
private def formatDate : SurfaceHavingDateComponents → Std.Format
  | ⟨day, month, year⟩ => formatNode "Date" [formatDateComponent day, formatDateComponent month,
    match year with
    | .complete year => formatDateComponent year
    | .baseYear => "baseYear"
    | .centuryAndShortYear century shortYear => formatNode "splitYear" [formatDateComponent century, formatDateComponent shortYear]]
termination_by value => sizeOf value
decreasing_by all_goals first | decreasing_tactic | omega | (simp_all +arith; omega)
private def formatTimeComponent : SurfaceHavingTimeComponent SurfaceHavingTemporalExpression → Std.Format
  | .field ref => formatNode "field" [repr ref]
  | .constant value => formatNode "constant" [repr value]
  | .extractor part ref => formatNode "extractor" [repr part, repr ref]
  | .nowExtractor part => formatNode "nowExtractor" [repr part]
  | .expression part source => formatNode "expression" [repr part, format source]
termination_by value => sizeOf value
decreasing_by all_goals first | decreasing_tactic | omega | (simp_all +arith; omega)
private def formatTime : SurfaceHavingTimeComponents → Std.Format
  | .empty => "Time"
  | .hour hour => formatNode "Time" [formatTimeComponent hour]
  | .minute hour minute => formatNode "Time" [formatTimeComponent hour, formatTimeComponent minute]
  | .second hour minute second => formatNode "Time" [formatTimeComponent hour, formatTimeComponent minute, formatTimeComponent second]
termination_by value => sizeOf value
decreasing_by all_goals first | decreasing_tactic | omega | (simp_all +arith; omega)

end

instance : Repr SurfaceHavingTemporalExpression where
  reprPrec source _ := format source

/-- Temporal source slots exclude value-list selectors, extrema and grouping (spec/05 §§3,6;
ordinary SurfaceScalarTemporalExpression.admittedSourceSlot). -/
def admittedSourceSlot (source : SurfaceHavingTemporalExpression) (withPartialDate : Bool := false) : Bool :=
  match source with
  | .partialDate _ _ => withPartialDate
  | .selection _ _ | .combine _ _ _ | .grouped _ => false
  | _ => true

-- As for TemporalExpressionOf, recursive operand lists need structural equality: the pinned
-- Lean deriving handler does not support DecidableEq for nested inductives.
mutual
private def decideEqual (left right : SurfaceHavingTemporalExpression) : Decidable (left = right) := by
  cases left <;> cases right
  all_goals first | (apply isFalse; intro h; cases h; done) | skip
  case combine.combine op first rest other next remaining =>
    letI := decideEqual first next
    letI := decideListEqual rest remaining
    exact decidable_of_iff (op = other ∧ first = next ∧ rest = remaining) (by simp)
  case grouped.grouped first next =>
    letI := decideEqual first next
    exact decidable_of_iff (first = next) (by simp)
  case dateTime.dateTime first rest next remaining =>
    letI := decideEqual first next
    letI := decideEqual rest remaining
    exact decidable_of_iff (first = next ∧ rest = remaining) (by simp)
  case dateFromDateTime.dateFromDateTime first next =>
    letI := decideEqual first next
    exact decidable_of_iff (first = next) (by simp)
  case timeFromDateTime.timeFromDateTime first next =>
    letI := decideEqual first next
    exact decidable_of_iff (first = next) (by simp)
  case selection.selection kind source other next =>
    exact decidable_of_iff (kind = other ∧ source = next) (by simp)
  case shift.shift unit source amount nextUnit nextSource nextAmount =>
    letI := decideEqual source nextSource
    letI := decideAmountEqual amount nextAmount
    exact decidable_of_iff (unit = nextUnit ∧ source = nextSource ∧ amount = nextAmount) (by simp)
  case partialDate.partialDate first endpoint next other =>
    exact decidable_of_iff (first = next ∧ endpoint = other) (by simp)
  case field.field first next => exact decidable_of_iff (first = next) (by simp)
  case rangeBound.rangeBound source bound next other =>
    exact decidable_of_iff (source = next ∧ bound = other) (by simp)
  case timeConstruction.timeConstruction first next =>
    letI := decideTimeEqual first next
    exact decidable_of_iff (first = next) (by simp)
  case dateConstruction.dateConstruction first next =>
    letI := decideDateEqual first next
    exact decidable_of_iff (first = next) (by simp)
  case dateLiteral.dateLiteral first next => exact decidable_of_iff (first = next) (by simp)
  case timeLiteral.timeLiteral first next => exact decidable_of_iff (first = next) (by simp)
  case dateTimeLiteral.dateTimeLiteral first next => exact decidable_of_iff (first = next) (by simp)
  case baseYearBound.baseYearBound first next => exact decidable_of_iff (first = next) (by simp)
  case today.today => exact isTrue rfl
  case now.now => exact isTrue rfl
private def decideListEqual (left right : List SurfaceHavingTemporalExpression) : Decidable (left = right) :=
  match left, right with
  | [], [] => isTrue rfl
  | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
  | first :: rest, next :: remaining =>
      letI := decideEqual first next
      letI := decideListEqual rest remaining
      decidable_of_iff (first = next ∧ rest = remaining) (by simp)
private def decideDateComponentEqual (left right : SurfaceHavingDateComponent SurfaceHavingTemporalExpression) : Decidable (left = right) := by
  cases left <;> cases right
  all_goals first | (apply isFalse; intro h; cases h; done) | skip
  case expression.expression part source other next =>
    letI := decideEqual source next
    exact decidable_of_iff (part = other ∧ source = next) (by simp)
  case field.field source next => exact decidable_of_iff (source = next) (by simp)
  case constant.constant source next => exact decidable_of_iff (source = next) (by simp)
  case extractor.extractor part source other next =>
    exact decidable_of_iff (part = other ∧ source = next) (by simp)
  case baseYearExtractor.baseYearExtractor source part next other =>
    exact decidable_of_iff (source = next ∧ part = other) (by simp)
  case clockExtractor.clockExtractor source part next other =>
    exact decidable_of_iff (source = next ∧ part = other) (by simp)

private def decideTimeComponentEqual (left right : SurfaceHavingTimeComponent SurfaceHavingTemporalExpression) : Decidable (left = right) := by
  cases left <;> cases right
  all_goals first | (apply isFalse; intro h; cases h; done) | skip
  case expression.expression part source other next =>
    letI := decideEqual source next
    exact decidable_of_iff (part = other ∧ source = next) (by simp)
  case field.field source next => exact decidable_of_iff (source = next) (by simp)
  case constant.constant source next => exact decidable_of_iff (source = next) (by simp)
  case extractor.extractor part source other next =>
    exact decidable_of_iff (part = other ∧ source = next) (by simp)
  case nowExtractor.nowExtractor source next => exact decidable_of_iff (source = next) (by simp)

private def decideAmountEqual (left right : SurfaceHavingTemporalAmount) : Decidable (left = right) :=
  left.decideEqWithSubterm right fun a b _ _ =>
    a.decideEqWithSubterm b fun left right _ _ => decideEqual left right
decreasing_by all_goals first | decreasing_tactic | omega | (simp_all +arith; omega)
private def decideDateYearEqual (left right : SurfaceConstructedDateYear (SurfaceHavingDateComponent SurfaceHavingTemporalExpression)) : Decidable (left = right) := by
  cases left <;> cases right
  all_goals first | (apply isFalse; intro h; cases h; done) | skip
  case complete.complete source next =>
    letI := decideDateComponentEqual source next
    exact decidable_of_iff (source = next) (by simp)
  case baseYear.baseYear => exact isTrue rfl
  case centuryAndShortYear.centuryAndShortYear century year other next =>
    letI := decideDateComponentEqual century other
    letI := decideDateComponentEqual year next
    exact decidable_of_iff (century = other ∧ year = next) (by simp)
private def decideDateEqual (left right : SurfaceHavingDateComponents) : Decidable (left = right) := by
  cases left with | mk day month year =>
    cases right with | mk nextDay nextMonth nextYear =>
      letI := decideDateComponentEqual day nextDay
      letI := decideDateComponentEqual month nextMonth
      letI := decideDateYearEqual year nextYear
      exact decidable_of_iff (day = nextDay ∧ month = nextMonth ∧ year = nextYear) (by simp)
private def decideTimeEqual (left right : SurfaceHavingTimeComponents) : Decidable (left = right) := by
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

instance : DecidableEq SurfaceHavingTemporalExpression := decideEqual

end SurfaceHavingTemporalExpression

mutual
def SurfaceHavingTemporalExpression.fields : SurfaceHavingTemporalExpression → List SurfaceHavingTemporalRef
  | .shift _ source amount => source.fields ++ amountFields amount
  | .field reference | .rangeBound reference _ | .partialDate reference _ => [reference]
  | .timeConstruction components => timeFields components
  | .dateConstruction components => dateFields components
  | .grouped source | .dateFromDateTime source | .timeFromDateTime source => source.fields
  | .dateTime date time => date.fields ++ time.fields
  | .combine _ first rest => first.fields ++ rest.flatMap (·.fields)
  | _ => []
private def amountFields (amount : SurfaceHavingTemporalAmount) : List SurfaceHavingTemporalRef :=
  amount.flatMapAtomsSubterm fun atom _ => match atom with
    | .temporalExpressionPart _ source => source.fields
    | .temporalDifference _ left right => left.fields ++ right.fields
    | .field ref => [{ origin := ref.origin, field := ref.field }]
    | .fieldValueAsNumber ref => [{ origin := ref.origin, field := ref.field }]
    | .dateRangeBoundPart origin field _ _ | .temporalPart origin field _
    | .stringLength origin field | .stringRange origin field _ _ => [{ origin, field }]
    | .dateDifference _ left right | .dayDifference left right | .dateTimeDifference _ left right => left.fields ++ right.fields
    | _ => []
decreasing_by all_goals first | decreasing_tactic | omega | (simp_all +arith; omega)
private def dateComponentFields : SurfaceHavingDateComponent SurfaceHavingTemporalExpression → List SurfaceHavingTemporalRef
  | .field ref | .extractor _ ref => [{ origin := ref.origin, field := ref.field }]
  | .expression _ source => source.fields
  | _ => []
private def dateFields : SurfaceHavingDateComponents → List SurfaceHavingTemporalRef
  | ⟨day, month, year⟩ => dateComponentFields day ++ dateComponentFields month ++ match year with
    | .complete year => dateComponentFields year
    | .baseYear => []
    | .centuryAndShortYear century shortYear => dateComponentFields century ++ dateComponentFields shortYear
private def timeComponentFields : SurfaceHavingTimeComponent SurfaceHavingTemporalExpression → List SurfaceHavingTemporalRef
  | .field ref | .extractor _ ref => [{ origin := ref.origin, field := ref.field }]
  | .expression _ source => source.fields
  | _ => []
private def timeFields : SurfaceHavingTimeComponents → List SurfaceHavingTemporalRef
  | .empty => []
  | .hour hour => timeComponentFields hour
  | .minute hour minute => timeComponentFields hour ++ timeComponentFields minute
  | .second hour minute second => timeComponentFields hour ++ timeComponentFields minute ++ timeComponentFields second
end

def SurfaceHavingDateComponents.sources (source : SurfaceHavingDateComponents) : List (SurfaceHavingDateComponent SurfaceHavingTemporalExpression) :=
  [source.day, source.month] ++ match source.year with
    | .complete year => [year]
    | .baseYear => []
    | .centuryAndShortYear century shortYear => [century, shortYear]

def SurfaceHavingDateComponents.references (source : SurfaceHavingDateComponents) : List SurfaceHavingPresenceRef :=
  dateFields source |>.map fun ref => { origin := ref.origin, field := ref.field }

mutual
def SurfaceHavingTemporalExpression.entitySources : SurfaceHavingTemporalExpression → List SurfaceHavingEntitySource
  | .selection _ source => [source]
  | .shift _ source amount => source.entitySources ++ amountEntitySources amount
  | .grouped source | .dateFromDateTime source | .timeFromDateTime source => source.entitySources
  | .dateTime date time => date.entitySources ++ time.entitySources
  | .combine _ first rest => first.entitySources ++ rest.flatMap (·.entitySources)
  | .dateConstruction ⟨day, month, year⟩ =>
      dateComponentEntitySources day ++ dateComponentEntitySources month ++ match year with
      | .complete year => dateComponentEntitySources year
      | .baseYear => []
      | .centuryAndShortYear century shortYear => dateComponentEntitySources century ++ dateComponentEntitySources shortYear
  | .timeConstruction components => timeEntitySources components
  | _ => []
private def amountEntitySources (amount : SurfaceHavingTemporalAmount) : List SurfaceHavingEntitySource :=
  amount.flatMapAtomsSubterm fun atom _ => match atom with
    | .temporalExpressionPart _ source => source.entitySources
    | .temporalDifference _ left right => left.entitySources ++ right.entitySources
    | .collectionCount source => [source.source]
    | .aggregate _ source | .firstFilled source | .groupCount source | .product source => [source]
    | .repetition reference => [{ first := .group reference.origin reference.group, rest := [] }]
    | _ => []
decreasing_by all_goals first | decreasing_tactic | omega | (simp_all +arith; omega)
private def dateComponentEntitySources : SurfaceHavingDateComponent SurfaceHavingTemporalExpression → List SurfaceHavingEntitySource
  | .expression _ source => source.entitySources
  | _ => []
private def timeComponentEntitySources : SurfaceHavingTimeComponent SurfaceHavingTemporalExpression → List SurfaceHavingEntitySource
  | .expression _ source => source.entitySources
  | _ => []
private def timeEntitySources : SurfaceHavingTimeComponents → List SurfaceHavingEntitySource
  | .empty => []
  | .hour hour => timeComponentEntitySources hour
  | .minute hour minute => timeComponentEntitySources hour ++ timeComponentEntitySources minute
  | .second hour minute second => timeComponentEntitySources hour ++ timeComponentEntitySources minute ++ timeComponentEntitySources second

end

abbrev SurfaceHavingNumericAtom := SurfaceHavingNumericAtomOf SurfaceHavingTemporalExpression

namespace SurfaceHavingNumericAtom
export SurfaceHavingNumericAtomOf (temporalDifference firstFilled groupCount product collectionCount aggregate dateDifference dayDifference dateTimeDifference baseYear baseYearDatePart clockPart fieldValueAsNumber field stringLength stringRange dateRangeBoundPart temporalExpressionPart temporalPart repetition)
end SurfaceHavingNumericAtom

/-- Temporal operands preserve grouping for the ordinary constant-pair gate (spec/04). -/
inductive SurfaceHavingTemporalOperand where
  | field (reference : SurfaceHavingStringRef)
  | constant (source : SurfaceDateDifferenceOperand Empty)
  | timeLiteral (value : TimeOfDay)
  | dateTimeLiteral (value : LocalDateTime)
  | grouped (source : SurfaceHavingTemporalOperand)
  deriving Repr, DecidableEq

def SurfaceHavingTemporalOperand.fields : SurfaceHavingTemporalOperand → List SurfaceHavingStringRef
  | .field reference => [reference]
  | .grouped source => source.fields
  | _ => []

inductive SurfaceHavingSelectedOperand where
  | field (reference : SurfaceHavingStringRef)
  | firstFilled (source : SurfaceHavingEntitySource)
  | text (value : String)
  | boolean (value : Bool)
  deriving Repr, DecidableEq

def SurfaceHavingSelectedOperand.entities : SurfaceHavingSelectedOperand → List SurfaceHavingEntityOperand
  | .field reference => [.entity {
      origin := reference.origin, field := reference.field
      form := match reference.projectionRef with | .stored => .stored | .category name => .projected name }]
  | .firstFilled source => source.first :: source.rest
  | .text _ | .boolean _ => []

inductive SurfaceHavingDateRangeOperand where
  | stored (reference : SurfaceHavingPresenceRef)
  | constructed (start finish : SurfaceHavingPresenceRef)
  deriving Repr, DecidableEq

def SurfaceHavingDateRangeOperand.references : SurfaceHavingDateRangeOperand → List SurfaceHavingPresenceRef
  | .stored reference => [reference]
  | .constructed start finish => [start, finish]

inductive SurfaceHavingDateRangePredicate where
  | compare (operator : SurfaceComparisonOp) (left right : SurfaceHavingDateRangeOperand)
  | overlap (scalar : Option SurfaceHavingPresenceRef) (source : SurfaceHavingEntitySource)
  deriving Repr, DecidableEq

def SurfaceHavingDateRangePredicate.entities : SurfaceHavingDateRangePredicate → List SurfaceHavingEntityOperand
  | .compare _ left right => (left.references ++ right.references).map fun ref =>
      .entity { origin := ref.origin, field := ref.field }
  | .overlap scalar source => (scalar.toList.map fun ref => .entity { origin := ref.origin, field := ref.field }) ++
      source.first :: source.rest

inductive SurfaceCorrelatedHaving where
  | customCondition (name : CheckedCustomConditionName)
  | repetitionNotUnique (keys : SurfaceHavingEntitySource) (scope : Option SurfaceHavingEntityOperand)
  | dateRange (source : SurfaceHavingDateRangePredicate)
  | compareStringExpression (op : SurfaceComparisonOp) (left right : StringExpr SurfaceHavingSelectedOperand String)
  | compareSelected (op : SurfaceComparisonOp) (left right : SurfaceHavingSelectedOperand)
  | compareBoolean (op : SurfaceComparisonOp) (reference : SurfaceHavingStringRef) (expected : Bool)
  | compareFields (op : SurfaceComparisonOp) (left right : SurfaceHavingStringRef)
  | compareTemporalExpression (op : SurfaceComparisonOp) (left right : SurfaceHavingTemporalExpression)
  | compareTemporal (op : SurfaceComparisonOp) (left right : SurfaceHavingTemporalOperand)
  | tolerance (range : NumericToleranceRange)
      (left right : AuthoredNumericExpr SurfaceHavingNumericAtom)
  | numeric (op : SurfaceComparisonOp)
      (left right : AuthoredNumericExpr SurfaceHavingNumericAtom)
  /-- Retain the authored operator until operand reads and the comparison-entry gate have run;
      only equality/inequality can reach the checked text comparison (spec/04). -/
  | compareStrings (op : SurfaceComparisonOp) (reference : SurfaceHavingStringRef)
      (expected : String)
  | literalList (quantifier : ValueListQuantifier) (subjects : SurfaceHavingEntitySource)
      (values : List String)
  | dateValidity (operation : ConstructedDateValidityOp) (source : SurfaceHavingDateComponents)
  | uniqueness (source : SurfaceHavingEntitySource)
  | fieldMembership (operator : ComputationValueListOperator)
      (subjects members : SurfaceHavingEntitySource)
  | literalMembership (operator : ValueListMembershipOp) (reference : SurfaceHavingStringRef)
      (values : Sum (List Int) (List String))
  | fieldFill (operator : FieldFillQuantifier) (source : SurfaceHavingEntitySource)
  /-- `FieldFilled` or `FieldNotFilled`. The negative polarity is authorable here because the
      kernel admits it inside a filter without the iteration-negativity refusal that governs a
      rule's own condition. -/
  | presence (polarity : HavingPresencePolarity)
      (reference : SurfaceHavingPresenceRef)
  | stringPattern (operation : StringPatternOp) (reference : SurfaceHavingPresenceRef) (source : String)
  | typeValidity (operation : CustomFieldValidityOp) (reference : SurfaceHavingPresenceRef) (name : String)
  | groupPresence (operator : GroupPresenceOperator) (origin : HavingOrigin)
      (reference : SurfaceGroupReference)
  | groupFill (operator : GroupFillQuantifier)
      (first : SurfaceHavingEntityOperand) (rest : List SurfaceHavingEntityOperand)
  | and (left right : SurfaceCorrelatedHaving)
  /-- Disjunction inside a filter. The filter's condition is the ordinary condition production, so
      this is a strong-Kleene `Or` and a true disjunct dominates an unavailable one, keeping its
      row. The legacy one-group route still refuses it; only the star route admits it. -/
  | or (left right : SurfaceCorrelatedHaving)
  deriving Repr, DecidableEq

def SurfaceCorrelatedHaving.compareNumbers (op : SurfaceComparisonOp)
    (left right : SurfaceHavingNumberRef) : SurfaceCorrelatedHaving :=
  .numeric op (.atom (.field left)) (.atom (.field right))

def SurfaceCorrelatedHaving.compareRepetitions (op : SurfaceComparisonOp)
    (left right : SurfaceHavingRepetitionRef) : SurfaceCorrelatedHaving :=
  .numeric op (.atom (.repetition left)) (.atom (.repetition right))

def SurfaceCorrelatedHaving.compareNumberLiteral (op : SurfaceComparisonOp)
    (reference : SurfaceHavingNumberRef) (literal : DecodedNumericLiteral) : SurfaceCorrelatedHaving :=
  .numeric op (.atom (.field reference)) (.literal literal)

/-- The exact admitted validation shape: the error target is the outer Number guard, and the starred consumer is filtered by a genuinely correlated `Having`. Requiring `errorField = guardField` is this capsule's routing boundary, not a claim that every kernel rule has that shape. -/
structure SurfaceSingleCorrelatedRule where
  errorField : SurfaceFieldPath
  guardField : SurfaceFieldPath
  valueField : SurfaceSingleStarFieldPath
  having : SurfaceCorrelatedHaving
  deriving Repr, DecidableEq



/-- The first marked reference of an authored filter, in authored order, crossing a level the
    reading rule does not bind, with the level the walk refuses. A marked reference reads the rule's
    own environment, so it meets the walk like any read and its class is placed by the error field:
    measured on a keyed and an unkeyed level beside the error field's group
    ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-walk-batch-reading-scope)).
    A reference that does not resolve is left to the filter's own resolution. -/
def SurfaceCorrelatedHaving.unboundOuterReference? (model : FlatModel)
    (declaringGroup writtenGroup : GroupPath)
    (bound : List RepeatableLevel := model.repeatableScopeForGroupPath declaringGroup) :
    SurfaceCorrelatedHaving → Option (List String × UnboundOperandLevel)
  | .customCondition _ => none
  | .repetitionNotUnique keys scope => (keys.first :: keys.rest ++ scope.toList).findSome? entity
  | .numeric _ left right | .tolerance _ left right =>
      (left.atoms ++ right.atoms).findSome? fun
        | .collectionCount count => (count.source.first :: count.source.rest).findSome? entity
        | .firstFilled source | .groupCount source | .product source | .aggregate _ source => (source.first :: source.rest).findSome? entity
        | .dateDifference _ left right | .dayDifference left right =>
            (left.fields ++ right.fields).findSome? fun reference => field reference.origin reference.field
        | .dateTimeDifference _ left right =>
            (left.fields ++ right.fields).findSome? fun reference => field reference.origin reference.field
        | .temporalDifference _ left right =>
            (((left.entitySources ++ right.entitySources).flatMap fun source => source.first :: source.rest).findSome? entity).orElse fun _ =>
              (left.fields ++ right.fields).findSome? fun reference => field reference.origin reference.field
        | .temporalExpressionPart _ source =>
            ((source.entitySources.flatMap fun source => source.first :: source.rest).findSome? entity).orElse fun _ =>
              source.fields.findSome? fun reference => field reference.origin reference.field
        | .baseYear | .baseYearDatePart _ _ | .clockPart _ _ => none
        | .fieldValueAsNumber reference => field reference.origin reference.field
        | .field reference => field reference.origin reference.field
        | .dateRangeBoundPart origin reference _ _ | .stringLength origin reference | .stringRange origin reference _ _ | .temporalPart origin reference _ => field origin reference
        | .repetition reference => group reference.origin reference.group
  | .compareFields _ left right =>
      (field left.origin left.field).orElse fun _ => field right.origin right.field
  | .compareBoolean _ reference _ | .compareStrings _ reference _ => field reference.origin reference.field
  | .dateRange source => source.entities.findSome? entity
  | .compareStringExpression _ left right =>
      ((left.fields ++ right.fields).flatMap SurfaceHavingSelectedOperand.entities).findSome? entity
  | .compareSelected _ left right => (left.entities ++ right.entities).findSome? entity
  | .compareTemporalExpression _ left right =>
      (((left.entitySources ++ right.entitySources).flatMap fun source => source.first :: source.rest).findSome? entity).orElse fun _ =>
        (left.fields ++ right.fields).findSome? fun reference => field reference.origin reference.field
  | .compareTemporal _ left right =>
      (left.fields ++ right.fields).findSome? fun reference => field reference.origin reference.field
  | .literalMembership _ reference _ => field reference.origin reference.field
  | .fieldMembership _ subjects members =>
      (subjects.first :: subjects.rest ++ members.first :: members.rest).findSome? entity
  | .dateValidity _ source => source.references.findSome? fun ref => field ref.origin ref.field
  | .uniqueness source | .fieldFill _ source | .literalList _ source _ =>
      (source.first :: source.rest).findSome? entity
  | .presence _ reference | .typeValidity _ reference _ | .stringPattern _ reference _ => field reference.origin reference.field
  | .groupPresence _ origin reference => group origin reference
  | .groupFill _ first rest => (first :: rest).findSome? entity
  | .and left right | .or left right =>
      (left.unboundOuterReference? model declaringGroup writtenGroup bound).orElse fun _ =>
        right.unboundOuterReference? model declaringGroup writtenGroup bound
where
  entity (ref : SurfaceHavingEntityOperand) : Option (List String × UnboundOperandLevel) := do
    guard (ref.origin == .outer)
    let (path, scope) ← ref.bindingRead? model declaringGroup
    let unbound ← model.unboundReadLevel? declaringGroup writtenGroup scope bound
    pure (path, unbound)
  field (origin : HavingOrigin) (reference : SurfaceFieldPath) :
      Option (List String × UnboundOperandLevel) := do
    guard (origin == .outer)
    let declaration ← (model.resolveFieldDeclarationUnchecked declaringGroup reference).toOption
    let unbound ← model.unboundReadLevel? declaringGroup writtenGroup declaration.repeatableScope bound
    pure (declaration.path, unbound)
  group (origin : HavingOrigin) (reference : SurfaceGroupReference) :
      Option (List String × UnboundOperandLevel) := do
    guard (origin == .outer)
    let resolved ← (reference.resolveAgainst declaringGroup).toOption
    let unbound ← model.unboundReadLevel? declaringGroup writtenGroup
      (model.repeatableScopeForGroupPath resolved.path) bound
    pure (resolved.path, unbound)

/-- Refuse a filter whose marked reference the walk refuses. Callers ask it before the filter's own
    checks; no row measures a filter failing both, so that order is this project's choice. -/
def SurfaceCorrelatedHaving.requireOuterReferencesBound (model : FlatModel)
    (declaringGroup writtenGroup : GroupPath) (having : SurfaceCorrelatedHaving)
    (bound : List RepeatableLevel := model.repeatableScopeForGroupPath declaringGroup) :
    Except CorrelationElabError Unit :=
  match having.unboundOuterReference? model declaringGroup writtenGroup bound with
  | some (path, unbound) => throw (.outerLevelUnbound path unbound)
  | none => pure ()

end A12Kernel
