import A12Kernel.Semantics.RuntimeFormalMessageKey
import A12Kernel.Semantics.FullDateInputFormat
import A12Kernel.Semantics.ConstructedDateShift
import A12Kernel.Semantics.ModelZone

/-! # Runtime formal-error message keys of the date families

A stored Date, partially known Date or DateRange refusal draws its code from the formal check and its
message key from a finer reading of the same text: which component failed, and whether the value
failed as a spelling or as a date. This capsule owns that selection over the three fixed-width
formats `FullDateInputFormat` admits. It returns a key, never text
([`RuntimeFormalMessageKey`](RuntimeFormalMessageKey.lean) states the licence boundary).

Basis: the 30.8.1 runtime date format's validation and its partially-known-part check, read for the
mechanism and calibrated row by row by rendered text at measurement
([checkpoint](../../docs/sources/domain-ingestion-probes.md#src-date-message-keys-k22)), whose
retained artifact redacts the text. -/

namespace A12Kernel

/-- Which component reading a calendar-unreal date fails, the detail the date keys split on. -/
inductive DateComponentDefect where
  | format
  | month
  | february29
  | day
  deriving Repr, DecidableEq

namespace DateParts

/-- Classify a syntactically well-formed date the legacy calendar rejects. The order is the Kernel's
and is not a calendar order: a zero component is a spelling defect before the month. Only an exact
29 February is the leap-day defect; every other day defect, the October 1582 gap day included (row
`d1-11`), is the day's. -/
def componentDefect (parts : DateParts) : DateComponentDefect :=
  if parts.day == 0 || parts.month == 0 || parts.year == 0 then .format
  else if 12 < parts.month then .month
  else if parts.day == 29 && parts.month == 2 then .february29
  else .day

end DateParts

/-- Which endpoint of a DateRange a component defect belongs to. -/
inductive DateRangeEndpoint where
  | start
  | finish
  deriving Repr, DecidableEq

namespace DateComponentDefect

/-- The key a stored Date's component defect selects. -/
def dateKey : DateComponentDefect → RuntimeFormalMessageKey
  | .format => .textDatumFormat
  | .month => .textDatumMonatFehler
  | .february29 => .textDatumFebruar29Fehler
  | .day => .textDatumTagFehler

/-- The key a DateRange endpoint's component defect selects: the range's own format key, and an
endpoint-specific key for each component. -/
def rangeKey (endpoint : DateRangeEndpoint) : DateComponentDefect → RuntimeFormalMessageKey
  | .format => .textDatumBereichFormat
  | .month => if endpoint == .start then .textDatumBereichStartMonatFehler else .textDatumBereichEndMonatFehler
  | .february29 =>
      if endpoint == .start then .textDatumBereichStartFebruar29Fehler else .textDatumBereichEndFebruar29Fehler
  | .day => if endpoint == .start then .textDatumBereichStartTagFehler else .textDatumBereichEndTagFehler

end DateComponentDefect

/-- The key the omission check of a partially known Date selects, or `none` when its zero parts are
consistent with the declared precision. Over these two-digit formats a lone `0` cannot pass the
syntax gate, so only the all-zero spellings `00` and `0000` reach this table. The keys carry the
code `datum`, not the spelling code. -/
def TemporalPartialMode.omissionMessageKey? (mode : TemporalPartialMode) (parts : DateParts) :
    Option RuntimeFormalMessageKey :=
  let yearUnknown := parts.year == 0
  let monthUnknown := parts.month == 0
  let dayUnknown := parts.day == 0
  match mode with
  | .full => none
  | .dayOptional =>
      if monthUnknown then some .textDatumMonatFehlt
      else if yearUnknown then some .textDatumJahrFehlt
      else none
  | .monthOptional =>
      if monthUnknown && !dayUnknown then some .textDatumMonatoptionalTagAngegeben
      else if yearUnknown then some .textDatumJahrFehlt
      else none
  | .yearOptional =>
      if yearUnknown && (!monthUnknown || !dayUnknown) then some .textDatumJahroptionalMonatOderTagAngegeben
      else if monthUnknown && !dayUnknown then some .textDatumMonatoptionalTagAngegeben
      else none

namespace FullDateInputFormat

/-- The key a stored Date's text selects, or `none` when the text is an admitted date. A partially
known declaration first meets its omission check, then reads an unknown day or month as `01` and an
unknown year as `2000` for the remaining checks. Past the syntax gate a calendar-unreal date selects
its component key; a real one fails only as a date, below the universal floor, and this key carries the
code `datum`. -/
def dateMessageKey? (format : FullDateInputFormat) (profile : ModelZone.ConcreteProfile)
    (mode : TemporalPartialMode) (text : String) : Option RuntimeFormalMessageKey :=
  match format.parseComponents? text with
  | none => some .textDatumFormat
  | some written =>
      match mode.omissionMessageKey? written with
      | some key => some key
      | none =>
          let parts : DateParts :=
            if mode == .full then written
            else {
              year := if written.year == 0 then 2000 else written.year
              month := if written.month == 0 then 1 else written.month
              day := if written.day == 0 then 1 else written.day }
          if !profile.storedLabelReal parts then
            some parts.componentDefect.dateKey
          else if decide (parts.Before CivilDate.gregorianFloor.parts) then some .textDatum
          else none

/-- The key a stored DateRange's text selects, or `none` when both endpoints are admitted dates in
order. A missing separator and a split that is not two nonempty endpoints select the range's format
key; the start endpoint is read before the end. An inverted range answers before the date check,
which reads the start alone against the floor. -/
def dateRangeMessageKey? (format : FullDateInputFormat) (profile : ModelZone.ConcreteProfile)
    (separator : String) (text : String) : Option RuntimeFormalMessageKey :=
  match text.splitOn separator with
  | [start, finish] =>
      if start.isEmpty || finish.isEmpty then some .textDatumBereichFormat
      else
        match format.parseComponents? start, format.parseComponents? finish with
        | some first, some last =>
            if !profile.storedLabelReal first then
              some (first.componentDefect.rangeKey .start)
            else if !profile.storedLabelReal last then
              some (last.componentDefect.rangeKey .finish)
            else if decide (last.Before first) then some .textDatumBereichNichtGueltig
            else if decide (first.Before CivilDate.gregorianFloor.parts) then some .textDatumBereichDatum
            else none
        | _, _ => some .textDatumBereichFormat
  | _ => some .textDatumBereichFormat

end FullDateInputFormat

end A12Kernel
