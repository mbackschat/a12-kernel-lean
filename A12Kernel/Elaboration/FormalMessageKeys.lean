import A12Kernel.Elaboration.AddressFormalLegality
import A12Kernel.Elaboration.DateTimeInput
import A12Kernel.Elaboration.OmittingDateInput
import A12Kernel.Semantics.DateFormalMessageKey

/-! # Runtime formal-error message keys of the classifier-owned families

The [date key capsule](../Semantics/DateFormalMessageKey.lean) selects the keys of the three complete
Date formats. This module selects them for the formats whose classifiers live here: the eight
component-omitting Date formats, the DateTime format and the clock format, and it pairs the addressing
codes with their keys. It returns keys, never text
([`RuntimeFormalMessageKey`](../Semantics/RuntimeFormalMessageKey.lean) states the licence boundary).

**One mechanism serves every date-bearing format.** A text the strict parse refuses is read again for
its day, month and year; a format that does not carry a day, or a text whose parts cannot be read, takes
the format key, and readable parts take the component reading `DateParts.componentDefect` already owns
for the complete formats. That is why month `13` is a format defect for `yyyy-MM` and `MM` but a month
defect for `MM-dd`, and why a DateTime whose clock fails on a sound date takes the day key.

Basis: the 30.8.1 runtime date format's validation and its component-detail path, read for the
mechanism, and the addressing codes' pairing in its formal checker; calibrated row by row by rendered
text at measurement ([checkpoint](../../docs/sources/domain-ingestion-probes.md#src-k22-formal-keys-wider)),
whose retained artifacts redact the text. -/

namespace A12Kernel

private def twoDigits? (part : String) : Option Nat :=
  if part.length == 2 then parseAsciiNatural? part else none

namespace OmittingDateFormat

/-- The day and month a day-bearing format's text spells, read for shape alone: widths, digits and the
literal separators, with neither component bounded. `none` for a malformed text and for the formats
that carry no day. -/
def writtenDayMonth? : OmittingDateFormat → String → Option (Nat × Nat)
  | .monthDay, text => match text.splitOn "-" with
    | [monthText, dayText] => do pure ((← twoDigits? dayText), (← twoDigits? monthText))
    | _ => none
  | .monthDayConcatenated, text =>
      if text.length == 4 then do
        pure ((← twoDigits? (text.drop 2).toString), (← twoDigits? (text.take 2).toString))
      else none
  | .dayMonthConcatenated, text =>
      if text.length == 4 then do
        pure ((← twoDigits? (text.take 2).toString), (← twoDigits? (text.drop 2).toString))
      else none
  | .dayMonthDotted, text => match text.splitOn "." with
    | [dayText, monthText, ""] => do pure ((← twoDigits? dayText), (← twoDigits? monthText))
    | _ => none
  | .year, _ | .yearMonthDashed, _ | .yearMonthConcatenated, _ | .month, _ => none

/-- The key a stored component-omitting Date's text selects, or `none` when the classifier admits it.
A real date before 1900 under the check and before the universal floor take the date keys. A refused
day-bearing text is completed with the Base Year, `2000` when none is declared, before its component
reading, so `02-29` takes the leap-day key only under a common Base Year. -/
def messageKey? (format : OmittingDateFormat) (baseYear : Option Int) (youngerThan1900Check : Bool)
    (text : String) : Option RuntimeFormalMessageKey :=
  match format.classifyStored baseYear youngerThan1900Check text with
  | .ok _ => none
  | .error .before1900 => some .textDatumAdditionalCheck
  | .error .beforeGregorianFloor => some .textDatum
  | .error (.renderingRejected _) =>
      match format.writtenDayMonth? text with
      | some (writtenDay, writtenMonth) => some (DateParts.componentDefect youngerThan1900Check
          { year := baseYear.getD 2000, month := writtenMonth, day := writtenDay }).dateKey
      | none => some .textDatumFormat

end OmittingDateFormat

namespace DateTimeTargetFormat

/-- The key a refused DateTime text selects once the floor is excluded: its date half's component
reading when the whole label is well shaped, whatever the clock holds, and the format key otherwise. -/
private def refusalKey (format : DateTimeTargetFormat) (text : String) : RuntimeFormalMessageKey :=
  let clockShaped := fun (clock : String) => match clock.splitOn ":" with
    | [hour, minute, second] => (twoDigits? hour).isSome && (twoDigits? minute).isSome && (twoDigits? second).isSome
    | _ => false
  match format.splitLabel? text with
  | some (dateText, timeText) =>
      match format.dateHalf.parseComponents? dateText with
      | some parts => if clockShaped timeText then (parts.componentDefect false).dateKey else .textDatumFormat
      | none => .textDatumFormat
  | none => .textDatumFormat

/-- The key a stored DateTime's text selects, or `none` when the classifier admits it. An unsupported
or unresolvable model context stays an error rather than a key. -/
def messageKey? (format : DateTimeTargetFormat) (profile : ModelZone.ConcreteProfile) (text : String) :
    Except DateTimeInputError (Option RuntimeFormalMessageKey) := do
  match ← format.classifyStoredIn profile text with
  | .rejected .dateInvalid => pure (some .textDatum)
  | .rejected _ => pure (some (format.refusalKey text))
  | .empty | .presentEmpty | .parsed _ => pure none

end DateTimeTargetFormat

/-- The key a stored clock-format text selects, on any date-bearing kind: the format carries no day, so
every refusal takes the format key. -/
def clockFormatMessageKey? (text : String) : Option RuntimeFormalMessageKey :=
  if text.isEmpty || (decodeTimeLiteral? text).isSome then none else some .textDatumFormat

namespace AddressRefusal

/-- The key each addressing code renders with. The over-maximum row and context arms are measured; the
other ten pairings are read from the formal checker and no route this project drives has produced them,
an unknown member of a JSON document drawing no message at all. -/
def messageKey : AddressRefusal → RuntimeFormalMessageKey
  | .fieldUnknown => .textFehlerFeldUnbekannt
  | .indexCountWrong => .textFalscheAnzahlIndicesFmText
  | .serialTooSmall => .textFehlerLaufendeNrFmText
  | .serialTooLarge => .textFehlerLaufendeNrZuGrossFmText
  | .contextTooSmall => .textKontextnummerZuKleinFmText
  | .contextTooLarge => .textFehlerKontextnummerZuGrossFmText
  | .rowTooSmall => .textFehlerZeileFmText
  | .rowTooLarge => .textFehlerZeilennummerZuGrossFmText
  | .usbMissing => .textFehlerKeinUsbFmText
  | .usbTooSmall => .textFehlerUsbFmText
  | .usbTooLarge => .textFehlerUsbZuGrossFmText
  | .usbUnexpected => .textFehlerUsbAngegebenFmText

end AddressRefusal

end A12Kernel
