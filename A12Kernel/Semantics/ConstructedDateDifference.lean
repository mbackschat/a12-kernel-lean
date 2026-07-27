import A12Kernel.Semantics.ConstructedDateShift
import A12Kernel.Semantics.DateConstructionNumeric
import A12Kernel.Semantics.DateDifference

/-! # Constructed-Date legacy-hybrid completed periods

This capsule counts completed months and years between two reason-bearing `Date(...)` results under the same bounded default-cutover profile as `ConstructedDateShift`. It orders two real labels, tests one fresh landing from the earlier source, and restores authored sign. The result reuses `ConstructedDateNumericResult`, so incomplete and unreal operands both yield zero while retaining missing versus fixed provenance, and formal unavailability dominates both.

Exact day differences, checked authoring, other zone-local discontinuities, DateTime, and target storage remain separate.
-/

namespace A12Kernel

namespace DateParts.LegacyHybrid

/-- Completed months for an already ordered pair, using one fresh legacy-hybrid landing from the earlier source. -/
def wholeMonthsForward? (earlier later : DateParts) : Option Int := do
  let candidate :=
    DateParts.Difference.monthCoordinate later -
      DateParts.Difference.monthCoordinate earlier
  let landing ← DateParts.LegacyHybrid.addMonths? earlier candidate
  pure (if decide (later.Before landing) then candidate - 1 else candidate)

/-- Completed years for an already ordered pair, including the constructed-Date February correction in the candidate landing. -/
def wholeYearsForward? (earlier later : DateParts) : Option Int := do
  let candidate := later.year - earlier.year
  let landing ← DateParts.LegacyHybrid.addYears? earlier candidate
  pure (if decide (later.Before landing) then candidate - 1 else candidate)

/-- Restore authored operand order after one nonnegative completed-period calculation. Both labels must be real in the bounded legacy profile. -/
def signedWholePeriods?
    (forward : DateParts → DateParts → Option Int)
    (first second : DateParts) : Option Int :=
  if !DateParts.LegacyHybrid.isReal first ||
      !DateParts.LegacyHybrid.isReal second then
    none
  else if decide (first.Before second) then
    forward first second
  else
    (forward second first).map (fun amount => -amount)

end DateParts.LegacyHybrid

namespace DateDifferenceUnit

/-- Apply the selected completed-period operation to two real constructed-Date labels in the bounded legacy profile. -/
def betweenLegacy? (unit : DateDifferenceUnit)
    (first second : DateParts) : Option Int :=
  match unit with
  | .months =>
      DateParts.LegacyHybrid.signedWholePeriods?
        DateParts.LegacyHybrid.wholeMonthsForward? first second
  | .years =>
      DateParts.LegacyHybrid.signedWholePeriods?
        DateParts.LegacyHybrid.wholeYearsForward? first second

end DateDifferenceUnit

namespace DateConstructionResult

/-- Apply one concrete difference to two constructed results without collapsing unavailable, incomplete, and unreal operands. -/
def differenceWith?
    (between : DateParts → DateParts → Option Int)
    (first second : DateConstructionResult) :
    Option ConstructedDateNumericResult :=
  match first, second with
  | .unknown, _ | _, .unknown => some .unavailable
  | .incomplete, _ | _, .incomplete => some (.value 0 true)
  | .unreal, _ | _, .unreal => some (.value 0 false)
  | .real firstParts, .real secondParts =>
      (between firstParts secondParts).map
        (fun amount => .value amount false)

/-- Evaluate a constructed-Date month/year difference in the bounded legacy profile. `none` is reserved for a caller-supplied real label outside that profile. -/
def differenceLegacy? (first : DateConstructionResult)
    (unit : DateDifferenceUnit) (second : DateConstructionResult) :
    Option ConstructedDateNumericResult :=
  differenceWith? unit.betweenLegacy? first second

end DateConstructionResult

end A12Kernel
