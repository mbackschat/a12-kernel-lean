import A12Kernel.Reference.Dm.Replay
import A12Kernel.Reference.Dm.LoneSurrogate
import A12Kernel.Reference.Dm.EntryFrameFixture

/-! # Clock and constant rows before the 1582 cutover

Kernel 31.1.1 reads `Today`, `Now`, a date or date-time constant, a constructed Date and a Base Year on
the proleptic ISO calendar, while static admission of a constant keeps the hybrid Julian–Gregorian
calendar ([spec/05 §2.7 and §1](../../../spec/05-dates-and-time.md)). Each row runs
`FieldFilled(Reference) And (…)` on a `/Policy` host whose stored values are `Inception` 2024-01-01,
`Day` 29, `Month` 2, `Year` 1500 and the `MM` range `Season` `02/02`, and reads `fires`, `silent` or
`refused`. The clock rows are locked by `HybridCalendarClockDiffTest` of a12-dmkits at its
simplification revision `1124b523f`; the constant and Base Year rows follow the same account and are
unmeasured on 31.1.1. -/

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

/- Locked by `HybridCalendarClockDiffTest`: under Europe/Berlin a clock pinned at 1500-03-10T12:00Z reads
   10 March 1500 and one at 1582-10-14T12:00Z reads 14 October, for `Today` and `Now` alike, where kernel
   30.8.1 read the Julian 29 February and 4 October. `Today` compares with constants as that proleptic
   date. The Julian leap day is no constant here: a rule over `"29.02.1500"` fails at evaluation under
   Europe/Berlin ([spec/05 §1](../../../spec/05-dates-and-time.md)). -/
example : expect "Europe/Berlin" 2024 (-14825851200000) [
    ("DayFromDate(Today) == 10", "fires"), ("MonthFromDate(Today) == 3", "fires"),
    ("YearFromDate(Today) == 1500", "fires"), ("DayFromDate(Now) == 10", "fires"),
    ("DayFromDate(Today) == 29", "silent"),
    ("Today < \"11.03.1500\"", "fires"), ("Today == \"10.03.1500\"", "fires")] = true := by
  native_decide

example : [(-12219336000000, 14, 10), (-12219249600000, 15, 10), (1750672800000, 23, 6)].all
    (fun (now, day, month) => expect "Europe/Berlin" 2024 now [
      (s!"DayFromDate(Today) == {day}", "fires"), (s!"MonthFromDate(Today) == {month}", "fires"),
      (s!"DayFromDate(Now) == {day}", "fires"),
      ("Today < \"01.03.1500\"", "silent"), ("Today == \"10.03.1500\"", "silent")]) = true := by
  native_decide

/- The control: at 2025-06-23T10:00Z a stored date of that day equals `Today`. -/
example : outcomes "Europe/Berlin" 2024 1750672800000 ["[Inception] == Today", "[Inception] > Today"]
    (inception := "2025-06-23") = some ["fires", "silent"] := by
  native_decide

/- A constant before the cutover is read on the proleptic calendar, so `DifferenceInDays("04.10.1582",
   Inception)` is 161161 (spec/05 §1 states this value; the 30.8.1 count of 161151 skipped the ten
   missing labels). The `AddDays` and `AddHours` rows apply the same reading to a shift source and are
   unmeasured on 31.1.1: 4 October 1582 plus 161161 days is `Inception`, and 4 October 23:00 plus an hour
   is 5 October, ten whole days before 15 October noon. -/
example : expect "UTC" 2024 0 [
    ("DifferenceInDays(\"04.10.1582\", Inception) == 161161", "fires"),
    ("DifferenceInDays(\"04.10.1582\", Inception) == 161151", "silent"),
    ("[Inception] == AddDays(\"04.10.1582\", 161161)", "fires"),
    ("[Inception] == AddDays(\"04.10.1582\", 161151)", "silent"),
    ("DifferenceInDays(AddHours(\"04.10.1582T23:00:00\", 1), \"15.10.1582T12:00:00\") == 10", "fires"),
    ("DifferenceInDays(AddHours(\"04.10.1582T23:00:00\", 1), \"15.10.1582T12:00:00\") == 0", "silent")] = true := by
  native_decide

/- A Base Year of 1500 starts its year on the proleptic calendar, which has 191387 days to `Inception`
   and a 28-day February, so the constructed Julian leap day `Date(29, 2, 1500)` is unreal and compares
   with nothing (spec/05 §3.1; `ConstructedDateCalendarDiffTest` locks the unreality), while the real
   `Date("28", Month, Year)` equals its own constant and a yearless `28.02.` is one day from `01.03.`
   (spec/05's omitted-year section: two days under a leap Base Year, one under 2023). The remaining
   values are unmeasured on 31.1.1. An `MM` range ending in the Base Year's February is deliberately
   absent: its endpoint still completes on the hybrid calendar. -/
example : expect "UTC" 1500 0 [
    ("DifferenceInDays(BaseYear, Inception) == 191387", "fires"),
    ("DifferenceInDays(BaseYear, Inception) == 191378", "silent"),
    ("Date(Day, Month, Year) == \"01.03.1500\"", "silent"),
    ("Date(Day, Month, Year) < \"01.03.1500\"", "silent"),
    ("Date(\"28\", Month, Year) == \"28.02.1500\"", "fires"),
    ("DifferenceInDays(\"28.02.\", \"01.03.\") == 1", "fires"),
    ("DifferenceInDays(\"28.02.\", \"01.03.\") == 2", "silent")] = true := by
  native_decide

/- Static admission keeps the hybrid calendar ([spec/05 §1](../../../spec/05-dates-and-time.md)): a real
   hybrid constant is admitted as a comparison operand and as a shift source, an unreal one is refused,
   and a year-less 29 February is refused. -/
example : expect "UTC" 2024 0 ((["04.10.1582", "15.10.1582", "29.02.1500", "29.02.1300"].flatMap fun constant =>
      [(s!"[Inception] > \"{constant}\"", "fires"), (s!"[Inception] > AddDays(\"{constant}\", 7)", "fires")]) ++
    (["05.10.1582", "14.10.1582", "29.02.1700"].flatMap fun constant =>
      [(s!"[Inception] > \"{constant}\"", "refused"), (s!"[Inception] > AddDays(\"{constant}\", 7)", "refused")]) ++
    [("[Inception] > AddDays(\"29.02.\", 7)", "refused")]) = true := by
  native_decide

end A12Kernel.Dm.HybridCalendarLocks
