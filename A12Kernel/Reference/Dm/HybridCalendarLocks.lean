import A12Kernel.Reference.Dm.Replay
import A12Kernel.Reference.Dm.LoneSurrogate
import A12Kernel.Reference.Dm.EntryFrameFixture

/-! # Clock and constant rows before the 1582 cutover

Kernel 31.1.1 reads `Today`, `Now`, a date or date-time constant, a constructed Date and a Base Year on
the proleptic ISO calendar, while static admission of a constant keeps the hybrid Julian–Gregorian
calendar ([spec/05 §2.7 and §1](../../../spec/05-dates-and-time.md)). Each row runs
`FieldFilled(Reference) And (…)` on a `/Policy` host whose stored values are `Inception` 2024-01-01,
`Day` 29, `Month` 2, `Year` 1500 and the `MM` range `Season` `02/02`, and reads `fires`, `silent`, `fails` (the rule's runtime
failure) or `refused`. The clock rows are locked by `HybridCalendarClockDiffTest` and the stored-date and
pre-cutover value rows named in their comments by `StoredDateCalendarDiffTest`, both of a12-dmkits at its
simplification revision `1124b523f`; the rows their comments mark unmeasured follow the same account. -/

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

/-- Each condition's outcome under the model zone, Base Year and pinned clock: `fires` on its condition,
`fails` when evaluation raised the rule's runtime failure instead, `silent` or `refused`. -/
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
        if messages.isEmpty then "silent"
        else if messages.any (·.origin == .runtimeFailure) then "fails" else "fires"

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

/- A label real only on the Julian side resolves at runtime to its Julian instant under UTC, the proleptic
   10 March 1500, and has no instant under Europe/Berlin, where reaching it fails the evaluation
   (spec/05 §1). A clock one day later separates the two UTC readings from a failure that would fire on
   every clock; the Berlin rows must not fire at all. -/
example : expect "UTC" 2024 (-14825851200000) [
    ("Today == \"29.02.1500\"", "fires"), ("Today == \"10.03.1500\"", "fires"), ("Today == \"09.03.1500\"", "silent"),
    ("DifferenceInDays(\"29.02.1500\", \"10.03.1500\") == 0", "fires"),
    ("DifferenceInDays(\"29.02.1500\", \"11.03.1500\") == 1", "fires")] = true := by
  native_decide

example : expect "UTC" 2024 (-14825764800000) [
    ("Today == \"29.02.1500\"", "silent"), ("Today == \"10.03.1500\"", "silent"),
    ("Today == \"11.03.1500\"", "fires")] = true := by
  native_decide

example : expect "Europe/Berlin" 2024 (-14825851200000) [
    ("Today == \"29.02.1500\"", "fails"), ("Today == \"10.03.1500\"", "fires")] = true := by
  native_decide

/- Locked by `StoredDateCalendarDiffTest.aJulianLeapDayConstantIsAnEvaluationFaultUnderEuropeBerlin`: a
   stored-date comparison with the Julian leap day fails under Europe/Berlin, and the labels beside the
   cutover, `04.10.1582` and `15.10.1582`, compare as ordinary dates. -/
example : expect "Europe/Berlin" 2024 0 [
    ("[Inception] > \"29.02.1500\"", "fails"), ("[Inception] > \"04.10.1582\"", "fires"),
    ("[Inception] > \"15.10.1582\"", "fires")] = true := by
  native_decide

/- Locked by `StoredDateCalendarDiffTest.aJulianLeapDayConstantIsItsJulianInstantUnderUtc`: under UTC the
   constant `29.02.1500` is its Julian instant, 191319 days before `Inception`, where the proleptic
   1 March would be 191328. -/
example : expect "UTC" 2024 0 [
    ("DifferenceInDays(\"29.02.1500\", Inception) == 191319", "fires"),
    ("DifferenceInDays(\"29.02.1500\", Inception) == 191328", "silent")] = true := by
  native_decide

/- A date constant without an instant fails the evaluation of a difference it is an operand of, in either
   position and for every unit, where a real label beside it counts normally: `28.02.1500` is 191329 days
   from `Inception`. Derived from spec/05 §1, whose statement for the comparison carrier the lock above
   measures. Unmeasured on 31.1.1. -/
example : expect "Europe/Berlin" 2024 0 [
    ("DifferenceInDays(\"29.02.1500\", Inception) == 191319", "fails"),
    ("DifferenceInDays(Inception, \"29.02.1500\") == -191319", "fails"),
    ("DifferenceInMonths(\"29.02.1500\", Inception) == 6285", "fails"),
    ("DifferenceInYears(\"29.02.1500\", \"01.03.2024\") == 523", "fails"),
    ("DifferenceInDays(\"28.02.1500\", Inception) == 191329", "fires")] = true := by
  native_decide

/- Under UTC month and year differences read the constant as its Julian instant, the proleptic 10 March
   1500, as the day difference does: 6285 completed months to `Inception` where the written 29 February
   would count 6286, and 523 completed years to 1 March 2024 where it would count 524. Derived from
   spec/05 §1 and unmeasured on 31.1.1. -/
example : expect "UTC" 2024 0 [
    ("DifferenceInMonths(\"29.02.1500\", Inception) == 6285", "fires"),
    ("DifferenceInMonths(\"29.02.1500\", Inception) == 6286", "silent"),
    ("DifferenceInYears(\"29.02.1500\", \"01.03.2024\") == 523", "fires"),
    ("DifferenceInYears(\"29.02.1500\", \"01.03.2024\") == 524", "silent")] = true := by
  native_decide

/- An empty `timeZone` reads as an absent one, which is UTC (spec/05 §5): the model carries `UTC`, and
   `Now` reads hour 10 at 10:00Z where Europe/Berlin reads hour 12. -/
example : (policy "" 2024 []).map (·.flat.timeZoneId) = some "UTC" ∧
    expect "" 2024 1750672800000 [
      ("HoursFromTime(TimeFromDateTime(Now)) == 10", "fires"),
      ("HoursFromTime(TimeFromDateTime(Now)) == 12", "silent")] = true ∧
    expect "Europe/Berlin" 2024 1750672800000 [
      ("HoursFromTime(TimeFromDateTime(Now)) == 10", "silent"),
      ("HoursFromTime(TimeFromDateTime(Now)) == 12", "fires")] = true := by
  native_decide

/- The control: at 2025-06-23T10:00Z a stored date of that day equals `Today`. -/
example : outcomes "Europe/Berlin" 2024 1750672800000 ["[Inception] == Today", "[Inception] > Today"]
    (inception := "2025-06-23") = some ["fires", "silent"] := by
  native_decide

/- A constant before the cutover is read on the proleptic calendar, so `DifferenceInDays("04.10.1582",
   Inception)` is 161161 where the 30.8.1 count of 161151 skipped the ten missing labels, and 4 October
   1582 plus 161161 days is `Inception`: locked under Europe/Berlin by
   `StoredDateCalendarDiffTest.aPreCutoverConstantCountsOnTheProlepticCalendar`, its UTC twin unmeasured on
   31.1.1. Under UTC 4 October 23:00 plus an hour is 5 October, ten whole days before 15 October noon,
   locked by `everyPreCutoverValueCountsOnTheProlepticCalendar`. -/
example : expect "Europe/Berlin" 2024 0 [
    ("DifferenceInDays(\"04.10.1582\", Inception) == 161161", "fires"),
    ("DifferenceInDays(\"04.10.1582\", Inception) == 161151", "silent"),
    ("[Inception] == AddDays(\"04.10.1582\", 161161)", "fires"),
    ("[Inception] == AddDays(\"04.10.1582\", 161151)", "silent")] = true := by
  native_decide

example : expect "UTC" 2024 0 [
    ("DifferenceInDays(\"04.10.1582\", Inception) == 161161", "fires"),
    ("DifferenceInDays(\"04.10.1582\", Inception) == 161151", "silent"),
    ("[Inception] == AddDays(\"04.10.1582\", 161161)", "fires"),
    ("[Inception] == AddDays(\"04.10.1582\", 161151)", "silent"),
    ("DifferenceInDays(AddHours(\"04.10.1582T23:00:00\", 1), \"15.10.1582T12:00:00\") == 10", "fires"),
    ("DifferenceInDays(AddHours(\"04.10.1582T23:00:00\", 1), \"15.10.1582T12:00:00\") == 0", "silent")] = true := by
  native_decide

/- A Base Year of 1500 starts its year on the proleptic calendar, which has a 28-day February, so under
   UTC the constructed Julian leap day `Date(29, 2, 1500)` is unreal and compares with nothing, the `MM`
   range `Season` ends on 28 February and not on the constant `"29.02.1500"`, and a yearless `28.02.` is one
   day from `01.03.`: locked by `StoredDateCalendarDiffTest.everyPreCutoverValueCountsOnTheProlepticCalendar`
   (UTC, Base Year 1500). `BaseYear` is 191387 days before `Inception`, locked under Europe/Berlin by
   `aPreCutoverBaseYearCountsOnTheProlepticCalendar` and unmeasured under UTC; the real `Date("28", Month,
   Year)` rows are unmeasured on 31.1.1. -/
example : expect "Europe/Berlin" 1500 0 [
    ("DifferenceInDays(BaseYear, Inception) == 191387", "fires"),
    ("DifferenceInDays(BaseYear, Inception) == 191378", "silent")] = true := by
  native_decide

example : expect "UTC" 1500 0 [
    ("DifferenceInDays(BaseYear, Inception) == 191387", "fires"),
    ("DifferenceInDays(BaseYear, Inception) == 191378", "silent"),
    ("Date(Day, Month, Year) == \"01.03.1500\"", "silent"),
    ("Date(Day, Month, Year) < \"01.03.1500\"", "silent"),
    ("Date(\"28\", Month, Year) == \"28.02.1500\"", "fires"),
    ("EndOfDateRange(Season) == Date(\"28\", Month, Year)", "fires"),
    ("EndOfDateRange(Season) == \"29.02.1500\"", "silent"),
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
