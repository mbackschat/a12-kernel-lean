import A12Kernel.Semantics.DateConstructionNumeric

/-! # Base-Year Date source projection

This capsule resolves the configured Base Year after authored source checking has established that the model contains it and that a date-extraction or date-range-extraction position consumes it. A direct date source is January 1; the two range endpoints are January 1 and December 31.

The result deliberately remains decoded `DateParts`. It is model configuration rather than a stored or computed field value, so applying the separate 1583-10-16 `FullDate` value floor here would reject legal configured years before the consuming operation sees them. Exact-instant comparison, model-zone resolution, missing-configuration checking, authored wrappers, and range comparison remain separate consumers.
-/

namespace A12Kernel

/-- The endpoint selected by a date-range extraction over Base Year. -/
inductive BaseYearRangeEndpoint where
  | start
  | finish
  deriving Repr, DecidableEq

/-- Resolve Base Year as the January 1 calendar label used by direct date consumers. -/
def baseYearDateParts (year : Int) : DateParts :=
  { year, month := 1, day := 1 }

/-- Resolve Base Year as the full-year endpoint selected by a range extraction. -/
def baseYearRangeParts (year : Int) : BaseYearRangeEndpoint → DateParts
  | .start => baseYearDateParts year
  | .finish => { year, month := 12, day := 31 }

/-- Apply one direct date component extractor to the Base-Year date source. -/
def baseYearNumericPart (year : Int) (part : DateNumericPart) : Rat :=
  part.extract (baseYearDateParts year)

end A12Kernel
