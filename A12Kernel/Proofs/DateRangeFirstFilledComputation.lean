import A12Kernel.Elaboration.DateRangeFirstFilledComputation
import A12Kernel.Semantics.TemporalApplication

/-! # Bounded DateRange `FirstFilledValue` computation laws -/

namespace A12Kernel

/-- A clean checked DateRange cell retains its exact or yearless typed identity before target rendering. -/
theorem dateRangeFirstFilledCellAt_value
    (addressed : CheckedAddressedCell) (range : DateRangeCellValue)
    (observed : observeCell .computation addressed.cell =
      .value (.dateRange range)) :
    dateRangeFirstFilledCellAt addressed = .value range := by
  simp [dateRangeFirstFilledCellAt, observed]

/-- A reached formal rejection retains its exact cause at the DateRange selection boundary. -/
theorem dateRangeFirstFilledCellAt_poison
    (addressed : CheckedAddressedCell) (cause : FormalCause)
    (observed : observeCell .computation addressed.cell = .poison cause) :
    dateRangeFirstFilledCellAt addressed = .poison cause := by
  simp [dateRangeFirstFilledCellAt, observed]

/-- A present head terminates the DateRange scan before every suffix cell. -/
theorem evalDateRangeFirstFilledCells_present_head
    (addressed : CheckedAddressedCell) (remaining : List CheckedAddressedCell)
    (range : DateRangeCellValue)
    (selected : dateRangeFirstFilledCellAt addressed = .value range) :
    evalDateRangeFirstFilledCells (addressed :: remaining) = .value range := by
  simp [evalDateRangeFirstFilledCells, selected]

/-- Exhausting the checked direct source list keeps the no-value identity. -/
theorem scanDirectDateRangeFirstFilled_nil :
    scanDirectDateRangeFirstFilled ([] :
      List (Unit → Except ε (CellObservation DateRangeCellValue))) =
        .ok .noValue := by
  rfl

/-- An empty direct head delegates to the complete checked suffix. -/
theorem scanDirectDateRangeFirstFilled_empty
    (remaining : List
      (Unit → Except ε (CellObservation DateRangeCellValue))) :
    scanDirectDateRangeFirstFilled ((fun _ => .ok .empty) :: remaining) =
      scanDirectDateRangeFirstFilled remaining := by
  rfl

/-- A present direct head terminates without consulting any suffix observation. -/
theorem scanDirectDateRangeFirstFilled_value
    (range : DateRangeCellValue)
    (remaining : List
      (Unit → Except ε (CellObservation DateRangeCellValue))) :
    scanDirectDateRangeFirstFilled
      ((fun _ => .ok (.value range)) :: remaining) =
      .ok (.value range) := by
  rfl

/-- A reached direct formal cause terminates without consulting any suffix observation. -/
theorem scanDirectDateRangeFirstFilled_poison
    (cause : FormalCause)
    (remaining : List
      (Unit → Except ε (CellObservation DateRangeCellValue))) :
    scanDirectDateRangeFirstFilled
      ((fun _ => .ok (.poison cause)) :: remaining) =
      .ok (.poison cause) := by
  rfl

/-- An interpreted month-only source and target use the dotted carrier and supply day one at both endpoints, independently of either ordinary month spelling. -/
theorem evaluateDateRangeFirstFilledTarget_interpreted_yearlessMonth
    (sourceInterpretation targetInterpretation : DateRangeYearInterpretation)
    (format : DateRangeInputFormat) (start finish : Nat) :
    evaluateDateRangeFirstFilledTarget (some sourceInterpretation)
        (some targetInterpretation) format
        (.value (.yearlessMonth start finish)) =
      .ok (.accepted (DateRangeInputFormat.renderYearlessDayMonthDotted
        { month := start, day := 1 } { month := finish, day := 1 })) := by
  rfl

/-- A standard month-only source presented through an interpreted target spans from the first day of its start month through the yearless last day of its finish month. -/
theorem evaluateDateRangeFirstFilledTarget_standard_yearlessMonth
    (targetInterpretation : DateRangeYearInterpretation)
    (format : DateRangeInputFormat) (start finish : Nat) :
    evaluateDateRangeFirstFilledTarget none (some targetInterpretation) format
        (.value (.yearlessMonth start finish)) =
      .ok (.accepted (DateRangeInputFormat.renderYearlessDayMonthDotted
        (YearlessInterval.ofMonthPair start finish).start
        (YearlessInterval.ofMonthPair start finish).finish)) := by
  rfl

/-- Every interpretation-bearing month/day result uses the dotted carrier and remains accepted even when its endpoint labels wrap the year. -/
theorem evaluateDateRangeFirstFilledTarget_interpreted_yearlessMonthDay
    (sourceInterpretation : Option DateRangeYearInterpretation)
    (targetInterpretation : DateRangeYearInterpretation)
    (format : DateRangeInputFormat) (start finish : MonthDayValue) :
    evaluateDateRangeFirstFilledTarget sourceInterpretation
        (some targetInterpretation) format
        (.value (.yearlessMonthDay start finish)) =
      .ok (.accepted
        (DateRangeInputFormat.renderYearlessDayMonthDotted start finish)) := by
  rfl

/-- Applying an accepted DateRange stores the exact rendered target value independently of prior placement. -/
theorem dateRangeTargetAccepted_applyTo
    (stored : StoredDateRange)
    (prior : TemporalTargetState StoredDateRange) :
    (DateRangeTargetOutcome.accepted stored).applyTo prior =
      .presentValue stored := by
  rfl

end A12Kernel
