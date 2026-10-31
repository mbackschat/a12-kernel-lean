import A12Kernel.Semantics.FullDateInputFormat
import A12Kernel.Semantics.PartialDate
import A12Kernel.Semantics.ConstructedDateShift
import A12Kernel.Semantics.Observation

namespace A12Kernel

/-- One classified stored cell of a partial-Date declaration. The admitted case carries its precision
witness, so a consumer cannot pair a value with a declaration that does not allow it. -/
inductive PartialDateInputCell (mode : TemporalPartialMode) where
  | presentEmpty
  | rejected (cause : BaseFormalCause)
  | admitted (value : AdmittedPartiallyKnownDate mode)
  deriving Repr

/-- Classify stored partial-Date text against the three declaration facts that decide it, with no
certificate required. This is the **single owner** of the decision: every consumer that reads a
partial-Date cell routes here rather than repeating the ladder, so the measured cause cannot drift
between two implementations of it. Every formal text failure is a successful classification carrying
its cause; no model zone is consulted, because an admitted partial value denotes an interval and
resolves to an instant only when an endpoint is selected. -/
def classifyPartialDateStored (format : FullDateTargetFormat)
    (mode : TemporalPartialMode) (youngerThan1900Check : Bool) (text : String) :
    PartialDateInputCell mode :=
  if text.isEmpty then
    .presentEmpty
  else
    match format.parseComponents? text with
    | none => .rejected .dateFormat
    | some parts =>
        -- The gates run in the measured order (spec/05 §6.2): a zero pattern that is not a monotone
        -- suffix is refused first, then the *reality* of the present components, then their
        -- *position in time*, and only then the declaration's precision. Reality before the floor
        -- keeps an impossible month beside a legally omitted day a format failure, and the pattern
        -- before reality keeps one beside an omitted year a date failure (`d5-3`).
        if parts.day = 0 && parts.month = 0 && parts.year = 0 then
          -- Nothing is present, so there is no calendar and no position to judge.
          gateByPrecision .omittedYear
        else if parts.year = 0 then
          -- A present month or day beside an omitted year is no monotone suffix.
          .rejected .dateInvalid
        else if parts.day = 0 && parts.month = 0 then
          guardCompletion { year := parts.year, month := 1, day := 1 }
            (OmittedMonthDate.ofYear? (parts.year : Int) |>.map .omittedMonth)
        else if parts.day = 0 then
          guardCompletion { year := parts.year, month := parts.month, day := 1 }
            (OmittedDayDate.ofYearMonth? (parts.year : Int) parts.month
              |>.map .omittedDay)
        else if parts.month = 0 then
          -- A present day beside an omitted month: the zeros are not a monotone suffix, so this is
          -- an omission failure, not a spelling one.
          .rejected .dateInvalid
        else
          guardCompletion parts
            (FullDate.ofYmd? (parts.year : Int) parts.month parts.day |>.map .full)
where
  /-- Apply the declaration's precision gate to one structurally legal shape. -/
  gateByPrecision (value : PartiallyKnownDateValue) : PartialDateInputCell mode :=
    if h : mode.admitsPartiallyKnownValue value = true then
      .admitted { value, admitted := h }
    else
      .rejected .dateInvalid
  /-- Judge one shape's earliest completion, then its precision. `earliest` is that completion's
  components and `build` the value it denotes. An unreal completion is a calendar failure; one below
  the universal floor, or below the enabled pre-1900 boundary, is a position-in-time failure. The
  builders apply the floor internally too, so `build` is consulted only after the floor has already
  passed and its `none` can mean nothing but unreality. -/
  guardCompletion (earliest : DateParts)
      (build : Option PartiallyKnownDateValue) : PartialDateInputCell mode :=
    if !DateParts.LegacyHybrid.isReal earliest then
      .rejected .dateFormat
    else if decide (earliest.Before CivilDate.gregorianFloor.parts) ||
        (youngerThan1900Check &&
          decide (earliest.Before FullDate.year1900Start.civil.parts)) then
      .rejected .dateInvalid
    else
      match build with
      | none => .rejected .dateFormat
      | some value => gateByPrecision value

end A12Kernel
