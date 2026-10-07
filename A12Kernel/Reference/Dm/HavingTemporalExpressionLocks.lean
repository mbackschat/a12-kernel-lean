import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingTemporalExpressionLocks
open Lean A12Kernel

private def model : FlatModel := { HavingFixture.model with fields := HavingFixture.model.fields.map fun field =>
  if field.id == 2 || field.id == 3 then { field with
    policy := { kind := .temporal .dateTime TemporalComponents.now }
    temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } } else field }
private def run (filter selected : String) (outer : String := "2024-04-12T12:30:00")
    (first : String := "2024-04-12T11:30:00") (second : String := "2024-04-12T12:30:00")
    (fixture : FlatModel := model) (fresh : Bool := false) (producer : String := "\"drop\"") :=
  HavingFixture.runModel fixture filter fresh outer first second producer (ruleExpected := selected)

example : run "DateTime(DateFromDateTime(Rows/Tag),TimeFromDateTime($Expected)) == [Rows/Tag]" "5" =
    some (.fired .omission, ["value 5"]) ∧
    run "HoursFromTime(TimeFromDateTime(Rows/Tag)) == 12" "5" =
      some (.fired .omission, ["value 5"]) := by native_decide

example : [
    "DateFromDateTime(Rows/Tag) == DateFromDateTime($Expected)",
    "DateFromDateTime($Expected) == DateFromDateTime(Rows/Tag)"].all (fun filter =>
      run filter "5" "2024-04-12T12:30:00" "2024-04-11T11:30:00" ==
        some (.fired .omission, ["value 5"])) = true ∧
    ["TimeFromDateTime(Rows/Tag) == TimeFromDateTime($Expected)",
      "TimeFromDateTime($Expected) == TimeFromDateTime(Rows/Tag)",
      "[Rows/Tag] == DateTime(DateFromDateTime(Rows/Tag),TimeFromDateTime($Expected))"].all (fun filter =>
      run filter "5" == some (.fired .omission, ["value 5"])) = true := by native_decide

example : ["TimeFromDateTime(Rows/Tag) < TimeFromDateTime($Expected)",
    "TimeFromDateTime($Expected) > TimeFromDateTime(Rows/Tag)",
    "DateTime(DateFromDateTime(Rows/Tag),TimeFromDateTime(Rows/Tag)) < [$Expected]",
    "[$Expected] > DateTime(DateFromDateTime(Rows/Tag),TimeFromDateTime(Rows/Tag))"].all (fun filter =>
      run filter "9" == some (.fired .omission, ["value 9"])) = true := by native_decide

private def projections := [
  ("YearFromDate(DateFromDateTime(Rows/Tag))", "2024", "14"),
  ("MonthFromDate(DateFromDateTime(Rows/Tag))", "4", "14"),
  ("QuarterFromDate(DateFromDateTime(Rows/Tag))", "2", "14"),
  ("DayFromDate(DateFromDateTime(Rows/Tag))", "12", "5"),
  ("HoursFromTime(TimeFromDateTime(Rows/Tag))", "12", "5"),
  ("MinutesFromTime(TimeFromDateTime(Rows/Tag))", "34", "5"),
  ("SecondsFromTime(TimeFromDateTime(Rows/Tag))", "56", "5")]
example : projections.all (fun (source, amount, selected) => [false, true].all fun reverse =>
    let filter := if reverse then amount ++ " == " ++ source else source ++ " == " ++ amount
    run filter selected "2024-04-12T12:34:56" "2024-04-11T11:30:15" "2024-04-12T12:34:56" ==
      some (.fired .omission, ["value " ++ selected])) = true ∧
    run "HoursFromTime(TimeFromDateTime(DateTime(DateFromDateTime(Rows/Tag),TimeFromDateTime($Expected)))) + DayFromDate(DateFromDateTime(Rows/Tag)) == 24"
      "5" "2024-04-12T12:30:00" "2024-04-11T11:30:00" = some (.fired .omission, ["value 5"]) := by
  native_decide

private def splitModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 2 then { field with
    policy := { kind := .temporal .time TemporalComponents.time }
    temporalTargetPolicy := some { format := "HH:mm:ss" } }
  else if field.id == 3 then { field with
    policy := { kind := .temporal .date TemporalComponents.fullDate }
    temporalTargetPolicy := some { format := "yyyy-MM-dd" } } else field }
example : run "DateTime(Rows/Tag,$Expected) == \"12.04.2024T12:30:00\"" "5" "12:30:00"
      "2024-04-11" "2024-04-12" splitModel = some (.fired .omission, ["value 5"]) := by native_decide

example : ["DateFromDateTime", "TimeFromDateTime"].all (fun operator =>
    let filter := operator ++ "(Rows/Tag) == " ++ operator ++ "($Expected)"
    run filter "5" (first := "") == some (.fired .omission, ["value 5"]) &&
      run filter "5" (first := "bad") == some (.fired .omission, [])) = true ∧
    run "DateTime(DateFromDateTime(Rows/Tag),TimeFromDateTime($Expected)) == [Rows/Tag]" "5"
      (first := "") = some (.fired .omission, ["value 5"]) ∧
    run "DateTime(DateFromDateTime(Rows/Tag),TimeFromDateTime($Expected)) == [Rows/Tag]" "5"
      (first := "bad") = some (.fired .omission, []) := by native_decide

example : run "HoursFromTime(TimeFromDateTime(Rows/Tag)) == 0" "9" (first := "") =
      some (.fired .omission, ["value 9"]) ∧
    run "HoursFromTime(TimeFromDateTime(Rows/Tag)) == 12" "5" (first := "bad") =
      some (.fired .omission, []) ∧
    run "HoursFromTime(TimeFromDateTime(DateTime(DateFromDateTime(Rows/Tag),TimeFromDateTime($Expected)))) == 0"
      "14" (outer := "") = some (.fired .omission, ["value 14"]) ∧
    run "HoursFromTime(TimeFromDateTime(DateTime(DateFromDateTime(Rows/Tag),TimeFromDateTime($Expected)))) == 0"
      "0" (outer := "bad") = some (.fired .omission, []) := by native_decide

private def pointerModel : FlatModel := { model with fields := model.fields ++ [{
  id := 6, name := "Token", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } }] }
example : ["DateFromDateTime", "TimeFromDateTime"].all (fun operator =>
    HavingFixture.referencesFor (operator ++ "(/Form/Rows/Tag) == " ++ operator ++ "($/Form/Rows/Tag)")
      pointerModel "Token" == some (true, true)) = true ∧
    HavingFixture.referencesFor
      "DateTime(DateFromDateTime(/Form/Rows/Tag),TimeFromDateTime($/Form/Rows/Tag)) == [/Form/Rows/Tag]"
      pointerModel "Token" = some (true, true) ∧
    HavingFixture.referencesFor
      "HoursFromTime(TimeFromDateTime(/Form/Rows/Tag)) == HoursFromTime(TimeFromDateTime($/Form/Rows/Tag))"
      pointerModel "Token" = some (true, true) := by native_decide

private def sameField : Option (List Bool × List String) := do
  let fixture := { model with fields := model.fields.map fun field =>
    if field.id == 5 then { field with groupPath := ["Form", "Rows"], repeatableScope := [10] } else field }
  let world : World := { now := { epochMillis := 0 } }
  let dm : DmModel := { flat := fixture, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let row (n stamp : String) := Json.mkObj [("N", .str n), ("Tag", .str stamp), ("Out", .str "99")]
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [("Rows", .arr #[
    row "2" "2024-04-12T11:30:00", row "5" "2024-04-12T12:30:00", row "7" "2024-04-12T11:30:00"])])])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler fixture).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let operation := "Sum(/Form/Rows*/N Having TimeFromDateTime(/Form/Rows/Tag) == TimeFromDateTime($/Form/Rows/Tag))"
  let rule ← (checkRule dm .english {
    group := ["Form", "Rows"], name := "Same", errorCode := "SAME"
    errorEntityRelPath := "../N", condition := "FieldFilled(N) And " ++ operation ++ " > 0", severity := "ERROR" } world).toOption
  let verdicts ← (rule.evalOrdinaryRepeatableFull document (some world)).toOption
  let (_, computation) ← (lowerComputation fixture .english {
    group := ["Form", "Rows"], name := "Same"
    targetRelPath := "../Out", commonPrecondition := none, alternatives := [{ precondition := none, operation }]
    errorCodesToSuppress := [] }).toOption
  let outcomes ← (runComputations world prepared document [computation]).toOption
  pure (verdicts.map (fun result => result.2.verdict.keepsHaving), outcomes.map (·.outcome))
example : sameField = some ([true, true, true], ["value 9", "value 5", "value 9"]) := by native_decide

example : run "TimeFromDateTime(Rows/Tag) == TimeFromDateTime($Expected)" "5" (fresh := true)
    (producer := "\"12.04.2024T11:30:00\"") =
      some (.fired .omission, ["value 2024-04-12T11:30:00", "value 9"]) := by native_decide

private def accepted (filter : String) (fixture : FlatModel := model) : Bool :=
  ((parseText .english ("Sum(Rows*/N Having " ++ filter ++ ") > 0")).toOption.bind fun parsed =>
    (lowerCondition fixture ["Form"] false parsed.body).toOption).isSome
example : ["DateFromDateTime(Rows/Tag) == DateFromDateTime($Expected)",
    "TimeFromDateTime(Rows/Tag) == TimeFromDateTime($Expected)",
    "DateTime(DateFromDateTime(Rows/Tag),TimeFromDateTime($Expected)) == [Rows/Tag]"].all accepted = true ∧
    ["DateTime(Rows/Tag,$Expected) == [Rows/Tag]", "DateFromDateTime(Rows/N) == DateFromDateTime($Expected)",
      "TimeFromDateTime(Rows/N) == TimeFromDateTime($Expected)",
      "DateTime(DateFromDateTime(Rows/Tag)) == [Rows/Tag]",
      "DateTime(DateFromDateTime(Rows/Tag),TimeFromDateTime($Expected),Rows/Tag) == [Rows/Tag]",
      "DateFromDateTime(Rows/Tag,$Expected) == DateFromDateTime($Expected)",
      "TimeFromDateTime() == TimeFromDateTime(Rows/Tag)",
      "DateFromDateTime([Rows/Tag]) == DateFromDateTime($Expected)",
      "TimeFromDateTime([Rows/Tag]) == TimeFromDateTime($Expected)",
      "DateFromDateTime({Rows/Tag}) == DateFromDateTime($Expected)",
      "TimeFromDateTime({Rows/Tag}) == TimeFromDateTime($Expected)",
      "DateTime(DateFromDateTime(Rows/Tag),TimeFromDateTime([$Expected])) == [Rows/Tag]",
      "DateTime(DateFromDateTime(Rows/Tag),TimeFromDateTime($Expected)) == Rows/Tag",
      "TimeFromDateTime($Rows/Tag) == TimeFromDateTime($Expected)",
      "TimeFromDateTime($Expected) == \"12:30:00\"",
      "DayFromDate(TimeFromDateTime(Rows/Tag)) == 12",
      "HoursFromTime(DateFromDateTime(Rows/Tag)) == 12"].all (fun filter => !accepted filter) = true := by native_decide

private def restricted (partialPolicy : Bool) : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 3 then { field with
    policy := { kind := .temporal .dateTime (TemporalComponents.ofFormat (if partialPolicy then "yyyy-MM-dd'T'HH:mm:ss" else "yyyy-MM-dd'T'HH:mm")) }
    temporalTargetPolicy := some {
      format := if partialPolicy then "yyyy-MM-dd'T'HH:mm:ss" else "yyyy-MM-dd'T'HH:mm"
      partialMode := if partialPolicy then .dayOptional else .full } } else field }
example : [false, true].all (fun partialPolicy =>
    ["DateFromDateTime", "TimeFromDateTime"].all fun operator =>
      !accepted (operator ++ "(Rows/Tag) == " ++ operator ++ "($Expected)") (restricted partialPolicy)) = true := by native_decide

example : [("UTC", "0"), ("Europe/Berlin", "1")].all (fun (zone, hour) =>
    run ("HoursFromTime(TimeFromDateTime(Now)) == " ++ hour ++ " And FieldFilled(Rows/N)") "14"
      (fixture := { model with timeZoneId := zone }) == some (.fired .omission, ["value 14"])) = true := by native_decide

example : run "{TimeFromDateTime(Rows/Tag)} == {TimeFromDateTime($Expected)}" "5" =
      some (.fired .omission, ["value 5"]) ∧
    run "DateTime(\"12.04.\",TimeFromDateTime(Rows/Tag)) == \"12.04.2024T12:30:00\"" "5"
      (fixture := { model with baseYear := some 2024 }) = some (.fired .omission, ["value 5"]) ∧
    accepted "DateTime(\"12.04.\",TimeFromDateTime(Rows/Tag)) == \"12.04.2024T12:30:00\"" = false ∧
    accepted "TimeFromDateTime(Rows/Tag) == TimeFromDateTime($Expected)"
      { model with timeZoneId := "unsupported" } = false := by native_decide

example : run "HoursFromTime(TimeFromDateTime(DateTime(Rows/Tag,$Expected))) == 0" "5"
      "02:30:00" "2024-03-30" "2024-03-31" { splitModel with timeZoneId := "Europe/Berlin" } =
      some (.fired .omission, ["value 5"]) := by native_decide

end A12Kernel.Dm.HavingTemporalExpressionLocks
