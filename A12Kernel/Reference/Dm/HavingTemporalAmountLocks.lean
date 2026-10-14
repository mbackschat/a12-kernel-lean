import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingTemporalAmountLocks
open Lean A12Kernel

private def model : FlatModel := {
  HavingFixture.model with
  baseYear := some 2024
  timeZoneId := "Europe/Berlin"
  fields := (HavingFixture.model.fields.map fun field =>
    if field.id == 3 then { field with
      policy := { kind := .temporal .date TemporalComponents.fullDate }
      temporalTargetPolicy := some { format := "yyyy-MM-dd" } }
    else field) ++ [
      { id := 6, groupPath := ["Form", "Rows"], name := "Amount", repeatableScope := [10]
        policy := { kind := .number { scale := 0, signed := true } } },
      { id := 7, groupPath := ["Form", "Rows"], name := "Text", repeatableScope := [10]
        policy := { kind := .string }, stringPatternSource := some "[0-9]+"
        stringPolicy := { maxLength := some 15 } },
      { id := 8, groupPath := ["Form", "Rows"], name := "OtherAmount", repeatableScope := [10]
        policy := { kind := .number { scale := 0, signed := true } } }] }

private def amounts : List (String × String) := [
  ("BaseYear-2023", "2"), ("Length(Rows/Text)", "2"),
  ("FieldValueAsNumber(Rows/Text)", "2"), ("RangeAsNumber(Rows/Text,1,1)", "2"),
  ("Sum(Rows/Amount,Rows/OtherAmount)", "3"), ("FirstFilledValue(Rows/Amount,Rows/OtherAmount)", "2"),
  ("NumberOfFilledFields(Rows/Amount,Rows/OtherAmount)", "3"),
  ("DifferenceInDays(\"01.01.2024\",Date(\"02\",\"01\",\"2024\"))", "2")]

private def run (amount expectedDay : String) (number text : String := "1")
    (date : String := "2024-01-01") (selected : String := "7") :=
  HavingFixture.runModel model
    ("DayFromDate(AddDays(Rows/Tag," ++ amount ++ ")) == " ++ expectedDay)
    false "ready" date date (ruleExpected := selected) (zoneRules := ModelZone.concreteRules)
    (extra := [("Out", .str "99")])
    (rowsOverride := some #[Json.mkObj [
      ("Tag", .str date), ("N", .str "7"), ("Amount", .str number), ("OtherAmount", .str number), ("Text", .str text)]])

example : amounts.all (fun (amount, day) => run amount day ==
    some (.fired .omission, ["value 7"])) = true := by native_decide

example : [("NumberOfFilledGroups(Rows*)", "2"),
    ("SumOfProducts(Rows*/Amount,Rows*/OtherAmount)", "2"),
    ("NumberOfValueInFields(1 In Rows/Amount,Rows/OtherAmount)", "3"),
    ("NumberOfValueInFields(\"1\" In Rows/Text,$Expected)", "2"),
    ("NumberOfDifferentValues(Rows/Text,$Expected)", "3"),
    ("MinValue(Rows/Amount,Rows/OtherAmount)", "2"),
    ("MaxValue(Rows/Amount,Rows/OtherAmount)", "2"),
    ("DifferenceInDays(Rows/Tag,Rows/Tag)", "1"),
    ("DifferenceInMonths(Rows/Tag,Rows/Tag)", "1"),
    ("DifferenceInYears(Rows/Tag,Rows/Tag)", "1"),
    ("DayFromDate(BaseYear)", "2"), ("DayFromDate(StartOfDateRange(BaseYear))", "2"),
    ("HoursFromTime(Now)", "2")].all (fun (amount, day) =>
      run amount day == some (.fired .omission, ["value 7"])) = true := by native_decide




example : (amounts.zipIdx).all (fun ((amount, day), index) =>
    let empty := [4, 5, 6].contains index
    run amount day "" "1" (selected := if empty then "0" else "7") ==
      some (.fired .omission, [if empty then "value 0" else "value 7"])) = true := by native_decide

example : (amounts.zipIdx).all (fun ((amount, day), index) =>
    let empty := [1, 2, 3].contains index
    run amount day "1" "" (selected := if empty then "0" else "7") ==
      some (.fired .omission, [if empty then "value 0" else "value 7"])) = true := by native_decide

example : (amounts.zipIdx).all (fun ((amount, day), index) =>
    let poisoned := [4, 5, 6].contains index
    run amount day "bad" "1" (selected := if poisoned then "0" else "7") ==
      some (.fired .omission, [if poisoned then "cleared" else "value 7"])) = true := by native_decide

example : (amounts.zipIdx).all (fun ((amount, day), index) =>
    let poisoned := [1, 2, 3].contains index
    run amount day "1" "bad" (selected := if poisoned then "0" else "7") ==
      some (.fired .omission, [if poisoned then "cleared" else "value 7"])) = true := by native_decide

example : amounts.all (fun (amount, day) => run amount day "1" "1" "bad" "0" ==
    some (.fired .omission, ["cleared"])) = true := by native_decide


example : HavingFixture.runModel model
    "DayFromDate(AddDays(Date(\"01\",\"01\",\"2024\"),CurrentRepetition(Rows))) == 2"
    false "ready" "2024-01-01" "2024-01-01" (ruleExpected := "2")
    (zoneRules := ModelZone.concreteRules) = some (.fired .omission, ["value 2"]) := by native_decide

private def unitRun (unit extractor source expected : String) (amount : String) :=
  let fixture := if ["AddHours", "AddMinutes", "AddSeconds"].contains unit then
    { model with fields := model.fields.map fun field => if field.id == 3 then
        { field with
          policy := { kind := .temporal .dateTime TemporalComponents.now }
          temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } } else field }
    else model
  HavingFixture.runModel fixture
    (extractor ++ "(" ++ unit ++ "(Rows/Tag," ++ amount ++ ")) == " ++ expected)
    false "ready" source source (ruleExpected := "7") (zoneRules := ModelZone.concreteRules)
    (rowsOverride := some #[Json.mkObj [
      ("Tag", .str source), ("N", .str "7"), ("Amount", .str "1"),
      ("OtherAmount", .str "1"), ("Text", .str "1")]])

example : [("AddDays", "DayFromDate", "2024-01-01", "2", "3"),
    ("AddMonths", "MonthFromDate", "2024-01-01", "2", "3"),
    ("AddYears", "YearFromDate", "2024-01-01", "2025", "2026"),
    ("AddHours", "HoursFromTime", "2024-01-01T08:10:20", "9", "10"),
    ("AddMinutes", "MinutesFromTime", "2024-01-01T08:10:20", "11", "12"),
    ("AddSeconds", "SecondsFromTime", "2024-01-01T08:10:20", "21", "22")].all
    (fun (unit, extractor, source, one, two) => amounts.all fun (amount, day) =>
      unitRun unit extractor source (if day == "3" then two else one) amount ==
        some (.fired .omission, ["value 7"])) = true := by native_decide

private def ordinaryModel : FlatModel := { model with
  fields := model.fields ++ ((model.fields.filter fun field => [3, 6, 7, 8].contains field.id).map fun field =>
    { field with id := field.id + 10, groupPath := ["Form"], repeatableScope := [] }) }

private def ordinaryRun (amount expected : String) (number text : String := "1") (date : String := "2024-01-01") :=
  let operation := "DayFromDate(AddDays(Tag," ++ amount.replace "Rows/" "" ++ "))"
  HavingFixture.runModel ordinaryModel "" false "ready" date date
    (operationOverride := some operation) (ruleExpected := expected) (zoneRules := ModelZone.concreteRules)
    (extra := [("Out", .str "99"), ("Tag", .str date), ("Amount", .str number),
      ("OtherAmount", .str "1"), ("Text", .str text)])

example : amounts.all (fun (amount, day) => ordinaryRun amount day ==
    some (.fired .value, ["value " ++ day])) = true := by native_decide

example : (amounts.zipIdx).all (fun ((amount, day), index) =>
    let affected := [4, 5, 6].contains index
    ordinaryRun amount (if affected then "2" else day) "" "1" ==
      some (.fired (if affected then .omission else .value), ["value " ++ (if affected then "2" else day)])) = true := by native_decide

example : (amounts.zipIdx).all (fun ((amount, day), index) =>
    let affected := [1, 2, 3].contains index
    ordinaryRun amount (if affected then "1" else day) "1" "" ==
      some (.fired (if affected then .omission else .value), ["value " ++ (if affected then "1" else day)])) = true := by native_decide

example : (amounts.zipIdx).all (fun ((amount, day), index) =>
    let poisoned := [4, 5, 6].contains index
    ordinaryRun amount day "bad" "1" ==
      some (if poisoned then .unknown else .fired .value, [if poisoned then "cleared" else "value " ++ day])) = true := by native_decide

example : (amounts.zipIdx).all (fun ((amount, day), index) =>
    let poisoned := [1, 2, 3].contains index
    ordinaryRun amount day "1" "bad" ==
      some (if poisoned then .unknown else .fired .value, [if poisoned then "cleared" else "value " ++ day])) = true := by native_decide

example : amounts.all (fun (amount, day) => ordinaryRun amount day "1" "1" "bad" ==
    some (.unknown, ["cleared"])) = true := by native_decide

private def partialAmount (amount : String) (unavailable fault : Option FieldId := none) :
    Option (Sum ScalarTemporalEvaluationFault (Sum NumericValidationUnavailable NumericArithmeticOutcome)) := do
  let world : World := { now := { epochMillis := 0 }, modelZoneRules := ModelZone.concreteRules }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler ordinaryModel).toOption
  let input ← (readDocument { flat := ordinaryModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (Json.mkObj [("Form", Json.mkObj [("Tag", .str "2024-01-01"), ("Amount", .str "1"), ("OtherAmount", .str "1")])])).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let parsed ← (parseText .english ("AddDays(Tag," ++ amount ++ ")")).toOption
  let surface ← (lowerScalarTemporalExpression ordinaryModel ["Form"] parsed.body).toOption
  let checked ← (elaborateTemporalNumericExpression ordinaryModel ["Form"] surface (.date .day)).toOption
  let partialRead : TemporalPartialReadContext ordinaryModel := {
    document, scope := .full
    read := fun row field => if fault == some field then .error (.checkedDocumentRequired ["injected"])
      else if unavailable == some field then pure none
      else (fun (addressed : CheckedAddressedCell) => some addressed.cell) <$> document.addressedCell row field }
  pure (match checked.evalResult .validation document.flatContext (partialRead? := some partialRead) with
    | .error fault => Sum.inl fault
    | .ok (.error unavailable) => .inr (.inl unavailable)
    | .ok (.ok value) => .inr (.inr value))

example : partialAmount "FirstFilledValue(Amount,OtherAmount)" none (some 18) =
      some (.inr (.inr (.value 2 .fixed))) ∧
    partialAmount "FirstFilledValue(Amount,OtherAmount)" (some 16) =
      some (.inr (.inl .nonRelevant)) ∧
    partialAmount "Sum(Amount,OtherAmount)" none (some 18) =
      some (.inl (.addressing (.checkedDocumentRequired ["injected"]))) ∧
    partialAmount "Sum(Amount,OtherAmount)" (some 18) =
      some (.inr (.inl .nonRelevant)) := by native_decide

private def baseYearExpressions : List (String × String) := [
  ("DifferenceInDays(BaseYear,AddDays(Rows/Tag,1))", "1"),
  ("DifferenceInDays(AddDays(Rows/Tag,1),BaseYear)", "-1"),
  ("DifferenceInMonths(BaseYear,AddMonths(Rows/Tag,1))", "1"),
  ("DifferenceInYears(AddYears(Rows/Tag,1),BaseYear)", "-1"),
  ("DayFromDate(AddDays(BaseYear,[Rows/Amount]))", "2"),
  ("MonthFromDate(AddMonths(BaseYear,[Rows/Amount]))", "2"),
  ("YearFromDate(AddYears(BaseYear,[Rows/Amount]))", "2025"),
  ("HoursFromTime(AddHours(DateTime(BaseYear,Time(\"08\")),[Rows/Amount]))", "9"),
  ("MinutesFromTime(AddMinutes(DateTime(BaseYear,Time(\"08\",\"10\")),[Rows/Amount]))", "11"),
  ("SecondsFromTime(AddSeconds(DateTime(BaseYear,Time(\"08\",\"10\",\"20\")),[Rows/Amount]))", "21"),
  ("DifferenceInHours(DateTime(BaseYear,Time(\"08\")),AddHours(DateTime(Rows/Tag,Time(\"08\")),1))", "1"),
  ("DifferenceInSeconds(AddSeconds(DateTime(Rows/Tag,Time(\"08\")),1),DateTime(BaseYear,Time(\"08\")))", "-1")]

private def baseYearRun (having : Bool) (expression expected : String) (number : String := "1")
    (date : String := "2024-01-01") (fixture : FlatModel := ordinaryModel) :=
  let operation := if having then "Sum(Rows*/N Having " ++ expression ++ " == " ++ expected ++ ")"
    else expression.replace "Rows/" ""
  HavingFixture.runModel fixture "" false "ready" date date
    (operationOverride := some operation) (ruleExpected := if having then "7" else expected)
    (zoneRules := ModelZone.concreteRules)
    (extra := [("Out", .str "99"), ("Tag", .str date), ("Amount", .str number)])
    (rowsOverride := some #[Json.mkObj [("Tag", .str date), ("Amount", .str number), ("N", .str "7")]])

example : baseYearExpressions.all (fun (expression, expected) =>
    baseYearRun true expression expected == some (.fired .omission, ["value 7"]) &&
    baseYearRun false expression expected == some (.fired .value, ["value " ++ expected])) = true := by native_decide

example : (baseYearExpressions.zipIdx).all (fun ((expression, expected), index) =>
    let emptyValue := (["1", "1", "2024", "8", "10", "20"][index - 4]?).getD expected
    let shifted := 4 ≤ index && index < 10
    baseYearRun true expression expected "" ==
      some (if shifted then .notFired else .fired .omission, [if shifted then "value 0" else "value 7"]) &&
    baseYearRun false expression (if shifted then emptyValue else expected) "" ==
      some (.fired (if shifted then .omission else .value),
        ["value " ++ (if shifted then emptyValue else expected)])) = true := by native_decide

example : (baseYearExpressions.zipIdx).all (fun ((expression, expected), index) =>
    let sourceRead := index < 4 || 10 ≤ index
    baseYearRun true expression expected "1" "bad" ==
      some (if sourceRead then .notFired else .fired .omission, [if sourceRead then "cleared" else "value 7"]) &&
    baseYearRun false expression expected "1" "bad" ==
      some (if sourceRead then .unknown else .fired .value,
        [if sourceRead then "cleared" else "value " ++ expected])) = true := by native_decide

example : [true, false].all (fun having =>
    baseYearExpressions.all (fun (expression, expected) =>
      (baseYearRun having expression expected (fixture := { ordinaryModel with baseYear := none })).isNone) &&
    ["HoursFromTime(AddHours(BaseYear,1))", "MinutesFromTime(AddMinutes(BaseYear,1))",
      "SecondsFromTime(AddSeconds(BaseYear,1))"].all (fun expression =>
        (baseYearRun having expression "1").isNone)) = true := by native_decide

example : (!(lowerHavingTemporalExpression false (.constant "BaseYear")).isOk) &&
    (lowerHavingTemporalExpression true (.constant "BaseYear")).isOk = true := by native_decide


example : HavingFixture.runModel ordinaryModel
    "DayFromDate(AddDays(Rows/Tag,Length($Expected))) == 3" true "a"
    "2024-01-01" "2024-01-01" "\"xx\"" (ruleExpected := "0")
    (zoneRules := ModelZone.concreteRules)
    (rowsOverride := some #[Json.mkObj [("Tag", .str "2024-01-01"), ("N", .str "7")]]) =
      some (.fired .omission, ["value xx", "value 7"]) ∧
    HavingFixture.runModel ordinaryModel "" true "a" "2024-01-01" "2024-01-01" "\"xx\""
      (operationOverride := some "DayFromDate(AddDays(Tag,Length(Expected)))") (ruleExpected := "2")
      (zoneRules := ModelZone.concreteRules) (extra := [("Tag", .str "2024-01-01")]) =
      some (.fired .value, ["value xx", "value 3"]) := by native_decide

example : HavingFixture.referencesFor
    "DayFromDate(AddDays(Date(\"01\",\"01\",\"2024\"),Length(/Form/Rows/Tag)+Length($/Form/Rows/Tag))) == 3"
    HavingFixture.model = some (true, true) := by native_decide

private def amountCondition (amount : String) (filtered : Bool) : String :=
  let expression := "DayFromDate(AddDays(Date(\"01\",\"01\",\"2024\")," ++ amount ++ ")) == 2"
  if filtered then "Sum(/Form/Rows*/N Having " ++ expression ++ ") > 0" else expression

private def amountReferences (amount : String) (filtered : Bool) :
    Option (Option Bool × Option Bool × Option Bool) := do
  let parsed ← (parseText .english (amountCondition amount filtered)).toOption
  let checked ← (lowerCondition HavingFixture.model ["Form"] false parsed.body
    (bindingGroup := ["Form", "Rows"])).toOption
  pure (checked.core.authoredErrorReference? 3,
    checked.core.errorReferenceAt? 3 10, checked.core.formOnlyErrorReference? 3)

private def amountAdmission (amount : String) (filtered : Bool) : Bool :=
  let dm : DmModel := {
    flat := HavingFixture.model, rules := [], computations := []
    conditionLanguage := "en_US", refusals := [] }
  (checkRule dm .english {
    group := ["Form"], name := "Amount", errorCode := "AMOUNT", severity := "ERROR"
    errorEntityRelPath := "../Rows/Tag", condition := amountCondition amount filtered }).isOk

example : [
    ("Length(/Form/Rows/Tag)", true, false, false, false, false),
    ("Length($/Form/Rows/Tag) + Length(/Form/Rows/Tag)", true, true, true, false, true),
    ("NumberOfFilledFields($/Form/Rows) + Length(/Form/Rows/Tag)", true, true, true, false, true)
  ].all (fun (amount, filtered, member, bound, rootOnly, admitted) =>
    amountReferences amount filtered == some (some member, some bound, some rootOnly) &&
      amountAdmission amount filtered == admitted) = true := by native_decide

/-- An ordinary shift amount may count the iterated group or its star, and never the root group.
Kernel oracle: static rows `y01`–`y03` of the retained expanded-shift-amount capture. -/
example : amountAdmission "NumberOfFilledFields(Rows)" false &&
    amountAdmission "NumberOfFilledFields(Rows*)" false &&
    !amountAdmission "NumberOfFilledFields(/Form)" false = true := by native_decide

private def partialSourceModel : FlatModel := { ordinaryModel with
  fields := ordinaryModel.fields.map fun field => if field.id == 3 || field.id == 13 then
    { field with temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .yearOptional } }
    else field }

example : ["DayFromDate(AddDays(BaseYear,DayFromDate(Rows/Tag)))",
    "MonthFromDate(AddMonths(BaseYear,MonthFromDate(Rows/Tag)))",
    "DayFromDate(AddDays(BaseYear,DifferenceInDays(Rows/Tag,Rows/Tag)))",
    "MonthFromDate(AddMonths(BaseYear,DifferenceInMonths(Rows/Tag,Rows/Tag)))"].all (fun expression =>
      [true, false].all fun having =>
        (baseYearRun having expression "2" (fixture := partialSourceModel)).isNone) = true := by native_decide

private def amountCertificate (part : DateNumericPart) : HavingTemporalExpression := {
  profile := .utc, baseYear := some 2024
  core := .atom (.shift .days (.atom (.baseYearBound .start)) (.atom
    (.temporalPart .inner { id := 13, kind := .date, components := .fullDate } (.date part)))) }

example : [DateNumericPart.day, .month].all (fun part =>
    (amountCertificate part).wellFormed { ordinaryModel with timeZoneId := "UTC" } [] [] &&
    !(amountCertificate part).wellFormed { partialSourceModel with timeZoneId := "UTC" } [] []) = true := by native_decide

end A12Kernel.Dm.HavingTemporalAmountLocks
