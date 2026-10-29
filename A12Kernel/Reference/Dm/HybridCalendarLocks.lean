import A12Kernel.Reference.Dm.Replay
import A12Kernel.Reference.Dm.LoneSurrogate
import A12Kernel.Reference.Dm.EntryFrameFixture

/-! # Clock and constant rows on the hybrid calendar

`Today`, `Now`, a date or date-time constant and a Base Year before the 1582 cutover are Julian
instants, so their components, comparisons, shifts and day differences read the Julian calendar
([October 21 letter](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), §1.2,
§1.12, §2.15). Each row runs `FieldFilled(Reference) And (…)` on the letter's `/Policy` host, whose
stored values are `Inception` 2024-01-01, `Day` 29, `Month` 2, `Year` 1500 and the `MM` range
`Season` `02/02`, and reads `fires`, `silent` or `refused`. -/

namespace A12Kernel.Dm.HybridCalendarLocks

open Lean A12Kernel

private def field (name typeName body : String) : String :=
  s!"\{\"type\":\"Field\",\"name\":\"{name}\",\"Field\":\{\"fieldType\":\{\"type\":\"{typeName}\",\"{typeName}\":{body}}}}"

private def rule (index : Nat) (condition : String) : String :=
  s!"\{\"type\":\"Rule\",\"name\":\"R{index}\",\"Rule\":\{\"errorEntityRelPath\":\"../Reference\",\"errorCode\":\"R{index}\",\"errorCondition\":{(toJson ("FieldFilled(Reference) And (" ++ condition ++ ")")).compress},\"severity\":\"ERROR\",\"errorMessage\":[\{\"locale\":\"en_US\",\"text\":\"m\"}]}}"

private def policy (zone : String) (baseYear : Int) (conditions : List String) : Option DmModel := do
  let number (name : String) (maximum : Nat) :=
    field name "NumberType" s!"\{\"maxFractionalDigits\":0,\"minValue\":0,\"maxValue\":{maximum}}"
  let elements := [field "Reference" "StringType" "{}", field "Inception" "DateType" "{\"format\":\"yyyy-MM-dd\"}",
    number "Day" 31, number "Month" 12, number "Year" 9999,
    field "Season" "DateRangeType" "{\"format\":\"MM\",\"rangeSeparator\":\"/\"}"] ++
    conditions.zipIdx.map fun (condition, index) => rule index condition
  let text := "{\"content\":{\"modelInfo\":{\"baseYear\":" ++ toString baseYear ++
    "},\"modelConfig\":{\"conditionLanguage\":{\"code\":\"en_US\"},\"timeZone\":\"" ++ zone ++
    "\"},\"modelRoot\":{\"rootGroups\":[{\"type\":\"Group\",\"name\":\"Policy\",\"Group\":{\"elements\":[" ++
    ",".intercalate elements ++ "]}}]}}}"
  let model ← (((parseModelJson text).map checkedEntryFrame).bind readModel).toOption
  if model.refusals.isEmpty then some model else none

/-- Each condition's outcome under the model zone, Base Year and pinned clock. -/
private def outcomes (zone : String) (baseYear : Int) (now : Int) (conditions : List String)
    (inception := "2024-01-01") : Option (List String) := do
  let model ← policy zone baseYear conditions
  let world : World := { now := { epochMillis := now }, modelZoneRules := ModelZone.concreteRules }
  let input ← (readDocument model (Json.mkObj [("Policy", Json.mkObj [("Reference", "x"),
    ("Inception", Json.str inception), ("Day", "29"), ("Month", "2"), ("Year", "1500"), ("Season", "02/02")])])).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model.flat).toOption
  let document ← ((checkDocument prepared "en_US" input.data).toOption.bind (·.fullValidationDocument.toOption))
  model.rules.mapM fun definition =>
    match checkValidationRule model .english definition world with
    | .error _ => some "refused"
    | .ok checked => (runValidationRule world document checked).toOption.map fun messages =>
        if messages.isEmpty then "silent" else "fires"

private def expect (zone : String) (baseYear now : Int) (rows : List (String × String)) : Bool :=
  outcomes zone baseYear now (rows.map (·.1)) == some (rows.map (·.2))

/- §1.2: under Europe/Berlin a clock pinned at 1500-03-10T12:00Z reads 29 February 1500 and one at
   1582-10-14T12:00Z reads 4 October, for `Today` and `Now` alike; `Today` then compares as that
   Julian date. The proleptic reading would see 1 March and 14 October. -/
example : expect "Europe/Berlin" 2024 (-14825851200000) [
    ("DayFromDate(Today) == 29", "fires"), ("MonthFromDate(Today) == 2", "fires"),
    ("YearFromDate(Today) == 1500", "fires"), ("DayFromDate(Now) == 29", "fires"),
    ("Today < \"01.03.1500\"", "fires"), ("Today == \"29.02.1500\"", "fires")] = true := by
  native_decide

example : [(-12219336000000, 4, 10), (-12219249600000, 15, 10), (1750672800000, 23, 6)].all
    (fun (now, day, month) => expect "Europe/Berlin" 2024 now [
      (s!"DayFromDate(Today) == {day}", "fires"), (s!"MonthFromDate(Today) == {month}", "fires"),
      (s!"DayFromDate(Now) == {day}", "fires"),
      ("Today < \"01.03.1500\"", "silent"), ("Today == \"29.02.1500\"", "silent")]) = true := by
  native_decide

/- The §1.2 control: at 2025-06-23T10:00Z a stored date of that day equals `Today`. -/
example : outcomes "Europe/Berlin" 2024 1750672800000 ["[Inception] == Today", "[Inception] > Today"]
    (inception := "2025-06-23") = some ["fires", "silent"] := by
  native_decide

/- §1.12: a constant before the cutover counts no skipped label, so the hybrid count fires and the
   proleptic one does not; a Base Year of 1500 starts its year on the Julian calendar; a Julian leap
   day in that year is two days from 1 March and a constructed one before it; a `MM` range escapes
   the floor and ends on the Base Year's 29 February; and a date-time constant stepped over the
   cutover lands on the same day as the first Gregorian one. -/
example : expect "UTC" 2024 0 [
    ("DifferenceInDays(\"04.10.1582\", Inception) == 161151", "fires"),
    ("DifferenceInDays(\"04.10.1582\", Inception) == 161161", "silent"),
    ("[Inception] == AddDays(\"04.10.1582\", 161151)", "fires"),
    ("[Inception] == AddDays(\"04.10.1582\", 161161)", "silent"),
    ("DifferenceInDays(AddHours(\"04.10.1582T23:00:00\", 1), \"15.10.1582T12:00:00\") == 0", "fires")] = true := by
  native_decide

example : expect "UTC" 1500 0 [
    ("DifferenceInDays(BaseYear, Inception) == 191378", "fires"),
    ("DifferenceInDays(BaseYear, Inception) == 191387", "silent"),
    ("Date(Day, Month, Year) == \"01.03.1500\"", "silent"),
    ("Date(Day, Month, Year) < \"01.03.1500\"", "fires"),
    ("EndOfDateRange(Season) == Date(Day, Month, Year)", "fires"),
    ("DifferenceInDays(\"28.02.\", \"01.03.\") == 2", "fires")] = true := by
  native_decide

/- §2.15 with §1.12's comparison rows: a real hybrid constant is admitted as a comparison operand
   and as a shift source, an unreal one is refused, and a year-less 29 February is refused. -/
example : expect "UTC" 2024 0 ((["04.10.1582", "15.10.1582", "29.02.1500", "29.02.1300"].flatMap fun constant =>
      [(s!"[Inception] > \"{constant}\"", "fires"), (s!"[Inception] > AddDays(\"{constant}\", 7)", "fires")]) ++
    (["05.10.1582", "14.10.1582", "29.02.1700"].flatMap fun constant =>
      [(s!"[Inception] > \"{constant}\"", "refused"), (s!"[Inception] > AddDays(\"{constant}\", 7)", "refused")]) ++
    [("[Inception] > AddDays(\"29.02.\", 7)", "refused")]) = true := by
  native_decide

end A12Kernel.Dm.HybridCalendarLocks
