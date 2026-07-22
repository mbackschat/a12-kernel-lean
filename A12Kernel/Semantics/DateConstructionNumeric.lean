import A12Kernel.Semantics.DateConstruction
import A12Kernel.Semantics.NumericComparison

/-! # Constructed-Date numeric component projection

This capsule implements the resolved `DayFromDate`, `MonthFromDate`, `QuarterFromDate`, and `YearFromDate` consumer from [`spec/05-dates-and-time.md` §3](../../spec/05-dates-and-time.md#3-constructing-dates-and-checking-validity) for an already-classified three-part `Date(...)` result. A real construction exposes its supplied component. Incomplete and unreal constructions both expose numeric zero, but retain not-given versus present provenance so validation polarity remains observable. Formal unavailability stays UNKNOWN.

The supplied real `DateParts` are authoritative: this projection does not repeat calendar resolution. DateTime composition, date differences, authored lowering, computation consumers, and target application remain separate boundaries.
-/

namespace A12Kernel

/-- The four direct numeric components supported by this resolved capsule. -/
inductive DateNumericPart where
  | day
  | month
  | quarter
  | year
  deriving Repr, DecidableEq

namespace DateNumericPart

/-- Select the named numeric component from calendar-resolved parts. -/
def extract (part : DateNumericPart) (parts : DateParts) : Rat :=
  match part with
  | .day => parts.day
  | .month => parts.month
  | .quarter =>
      if parts.month = 0 then 0
      else (((parts.month - 1) / 3 + 1 : Nat) : Rat)
  | .year => parts.year

end DateNumericPart

/-- The cause-free result retained by a direct constructed-Date numeric component. `notGiven` is symmetric date missingness, not unsigned numeric growth. -/
inductive ConstructedDateNumericResult where
  | value (amount : Rat) (notGiven : Bool)
  | unavailable
  deriving Repr, DecidableEq

namespace DateConstructionResult

/-- Project one already-classified construction into a direct numeric component without re-running calendar reality. -/
def numericPart (result : DateConstructionResult)
    (part : DateNumericPart) : ConstructedDateNumericResult :=
  match result with
  | .real parts => .value (part.extract parts) false
  | .incomplete => .value 0 true
  | .unreal => .value 0 false
  | .unknown => .unavailable

end DateConstructionResult

namespace ConstructedDateNumericResult

/-- Compare the projected component with a fixed numeric literal. Available date missingness is symmetric; formal unavailability remains UNKNOWN without inventing a discarded cause. -/
def evalFixedRight (result : ConstructedDateNumericResult)
    (op : NumericComparisonOp) (expected : Rat) : Verdict :=
  match result with
  | .value amount notGiven =>
      op.evalFixedRight
        (.value amount (if notGiven then .both else .fixed)) expected
  | .unavailable => .unknown

end ConstructedDateNumericResult

end A12Kernel
