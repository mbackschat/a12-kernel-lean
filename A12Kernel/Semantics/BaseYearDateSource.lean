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

/-- The two authored source shapes from which a direct numeric date component may be extracted. -/
inductive BaseYearDateSource where
  | direct
  | range (endpoint : BaseYearRangeEndpoint)
  deriving Repr, DecidableEq

namespace BaseYearDateSource

/-- Select the floor-free calendar label denoted by an already-checked Base-Year source. -/
def parts (year : Int) : BaseYearDateSource → DateParts
  | .direct => { year, month := 1, day := 1 }
  | .range .start => { year, month := 1, day := 1 }
  | .range .finish => { year, month := 12, day := 31 }

end BaseYearDateSource

/-- Resolve Base Year as the January 1 calendar label used by direct date consumers. -/
def baseYearDateParts (year : Int) : DateParts :=
  BaseYearDateSource.direct.parts year

/-- Resolve Base Year as the full-year endpoint selected by a range extraction. -/
def baseYearRangeParts (year : Int) : BaseYearRangeEndpoint → DateParts
  | endpoint => (BaseYearDateSource.range endpoint).parts year

/-- Apply one direct numeric date-component extractor after selecting its Base-Year source label. -/
def baseYearDateSourceNumericPart (year : Int) (source : BaseYearDateSource)
    (part : DateNumericPart) : Rat :=
  part.extract (source.parts year)

/-- Apply one direct date component extractor to the Base-Year date source. -/
def baseYearNumericPart (year : Int) (part : DateNumericPart) : Rat :=
  baseYearDateSourceNumericPart year .direct part

/-- Apply one direct numeric date-component extractor to a selected Base-Year range endpoint. -/
def baseYearRangeNumericPart (year : Int) (endpoint : BaseYearRangeEndpoint)
    (part : DateNumericPart) : Rat :=
  baseYearDateSourceNumericPart year (.range endpoint) part

end A12Kernel
