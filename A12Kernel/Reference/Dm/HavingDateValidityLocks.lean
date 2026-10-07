import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingDateValidityLocks
open A12Kernel Lean

private def number (id : FieldId) (name : String) (maximum : Rat) : FlatFieldDecl := {
  id, name, groupPath := ["Form", "Rows"], repeatableScope := [10]
  policy := { kind := .number { scale := 0, signed := false } }
  numericTargetConstraints := { maximum := some maximum } }

private def model : FlatModel := { HavingFixture.model with
  timeZoneId := "UTC", baseYear := some 2024
  fields := HavingFixture.model.fields ++
    [number 6 "D" 31, number 7 "M" 12, number 8 "Y" 9999,
      number 9 "C" 99, number 10 "S" 99,
      { (number 11 "OuterY" 9999) with groupPath := ["Form"], repeatableScope := [] },
      { id := 12, name := "TextD", groupPath := ["Form", "Rows"], repeatableScope := [10],
        policy := { kind := .string }, stringPolicy := { maxLength := some 2 },
        stringPatternSource := some "[0-9]+" },
      { id := 13, name := "Year", groupPath := ["Form", "Rows"], repeatableScope := [10],
        policy := { kind := .temporal .time (TemporalComponents.ofFormat "yyyy") },
        temporalTargetPolicy := some { format := "yyyy" } },
      { id := 14, name := "Stamp", groupPath := ["Form", "Rows"], repeatableScope := [10],
        policy := { kind := .temporal .time TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "yyyy-MM-dd" } }] }

private def run (filter : String) (expected : String) (outerYear : String := "2024")
    (fixture : FlatModel := model) (fresh : Bool := false)
    (producerOperation : String := "\"drop\"") (century : String := "20") (stamp : String := "2024-02-29") : Option (Verdict × List String) :=
  let row (n d m y : String) := Json.mkObj [
    ("N", .str n), ("D", .str d), ("M", .str m), ("Y", .str y),
    ("C", .str century), ("S", .str "24"), ("TextD", .str d),
    ("Year", .str y), ("Stamp", .str stamp)]
  HavingFixture.runModel fixture filter fresh outerYear "" "" producerOperation (zoneRules := ModelZone.concreteRules) (ruleExpected := expected) (extra := [("OuterY", .str outerYear)])
    (rowsOverride := some #[row "2" "29" "2" "2024", row "5" "30" "2" "2024",
      row "7" "" "2" "2024"])

example : run "FieldFilled(Rows/D)" "7" = some (.fired .omission, ["value 7"]) := by native_decide

example : run "Valid(Date(Rows/D, Rows/M, Rows/Y))" "2" =
    some (.fired .omission, ["value 2"]) ∧
    run "Invalid(Date(Rows/D, Rows/M, Rows/Y))" "12" =
      some (.fired .omission, ["value 12"]) ∧
    run "Valid(Date(Rows/D, Rows/M))" "2" = some (.fired .omission, ["value 2"]) ∧
    run "Valid(Date(Rows/D, Rows/M, Rows/C, Rows/S))" "2" =
      some (.fired .omission, ["value 2"]) := by native_decide

example : run "Valid(Date(Rows/TextD, Rows/M, Rows/Year))" "2" = some (.fired .omission, ["value 2"]) ∧
    run "Valid(Date(DayFromDate(Rows/Stamp), Rows/M, Rows/Y))" "14" = some (.fired .omission, ["value 14"]) ∧
    run "Valid(Date(Rows/D, MonthFromDate(Today), YearFromDate(Now)))" "7" = some (.fired .omission, ["value 7"]) ∧
    run "Valid(Date(Rows/D, MonthFromDate(EndOfDateRange(BaseYear)), YearFromDate(BaseYear)))" "7" =
      some (.fired .omission, ["value 7"]) ∧
    run "Valid(Date(Rows/D, \"02\", $OuterY))" "2" = some (.fired .omission, ["value 2"]) ∧
    run "Valid(Date(Rows/D, \"02\", $OuterY))" "0" "2023" = some (.fired .omission, ["value 0"]) := by native_decide

example : run "Valid(Date(Rows/D, Rows/M, Rows/C, Rows/S))" "0" (century := "0") =
      some (.fired .omission, ["value 0"]) ∧
    run "Invalid(Date(Rows/D, Rows/M, Rows/C, Rows/S))" "14" (century := "0") =
      some (.fired .omission, ["value 14"]) := by native_decide

private inductive Admission where
  | reader | operand | refused (code : Option KernelStaticDiagnostic) | admitted
  deriving Repr, DecidableEq
private def admission (filter : String) (fixture : FlatModel := model) : Admission :=
  match (parseText .english filter).toOption.bind (fun parsed => (lowerHaving parsed.body).toOption) with
  | none => .reader
  | some authored => match elaborateStarFieldPath fixture ["Form"] {
      base := .relative 0, groups := [{ name := "Rows", starred := true }], field := "N" } with
    | .error _ => .operand
    | .ok source => match elaborateStarHavingCore fixture ["Form"] source authored with
      | .error error => .refused error.diagnostic?
      | .ok _ => .admitted

example : admission "Valid(Date(\"29\", \"02\", \"2024\"))" = .refused (some .onlyConstantsUsed) ∧
    admission "Valid(Date(DayFromDate(Rows/Stamp), MonthFromDate(Rows/Stamp), YearFromDate(Rows/Stamp)))" =
      .refused (some .onlyConstantsUsed) ∧
    admission "Valid(Date(Rows/D, Rows/M))" { model with baseYear := none } ≠ .admitted ∧
    admission "Valid(Date(Rows/D, Rows/M, MonthFromDate(Rows/Stamp)))" ≠ .admitted ∧
    admission "Valid(Date(Rows/D, Rows/M, \"24\"))" ≠ .admitted ∧
    admission "Valid(Date(Rows*/D, Rows/M, Rows/Y))" ≠ .admitted ∧
    admission "Valid(Date(Rows/D, Rows/M, $Rows/Y))" = .refused (some .noWildcard) := by native_decide

example : admission "Valid(Date(Rows/M, Rows/M, Rows/Y))" ≠ .admitted ∧
    admission "Valid(Date(Rows/TextD, Rows/M, Rows/Y))" = .admitted ∧
    admission "Valid(Date(Rows/TextD, Rows/M, Rows/Y))"
      { model with fields := model.fields.map fun field =>
        if field.id == 12 then { field with stringPolicy := { maxLength := some 3 } } else field } ≠ .admitted ∧
    admission "Valid(Date(Rows/D, Rows/M, Rows/Year))" = .admitted := by native_decide

private def pointerModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 3 then { field with stringPolicy := { maxLength := some 2 }, stringPatternSource := some "[0-9]+" }
  else field }
example : HavingFixture.referencesFor
      "Valid(Date(Tag, \"02\", \"2024\")) And Invalid(Date($Tag, \"02\", \"2023\"))" pointerModel = some (true, true) ∧
    HavingFixture.referencesFor "Valid(Date(Tag, \"02\", \"2024\"))" pointerModel = some (true, false) := by native_decide

private def freshModel : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id == 2 then { field with
    policy := { kind := .temporal .date (TemporalComponents.ofFormat "yyyy") }
    temporalTargetPolicy := some { format := "yyyy" } } else field }

example : run "Valid(Date(Rows/D, \"02\", $Expected))" "0" "2023" freshModel true "Date(\"01\", \"01\", \"2024\")" =
    some (.fired .omission, ["value 2024", "value 2"]) ∧
    run "Valid(Date(Rows/D, \"02\", $Expected))" "2" "2024" freshModel true "Date(\"01\", \"01\", \"2023\")" =
      some (.fired .omission, ["value 2023", "value 0"]) := by native_decide

private def rows (operation : String) (guard : Option String := none)
    (partialCheck : Bool := false) : Option (List Verdict × List String) := do
  let model := { model with fields := model.fields.map fun field =>
    if field.id == 5 then { field with groupPath := ["Form", "Rows"], repeatableScope := [10] } else field }
  let world : World := { now := { epochMillis := 0 }, modelZoneRules := ModelZone.concreteRules }
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let row (n d y : String) := Json.mkObj [("N", .str n), ("D", .str d), ("Y", .str y), ("Out", .str "99")]
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Rows", .arr #[row "2" "29" "2024", row "5" "30" "2023", row "7" "" "2024"])])])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let rule ← (checkRule dm .english {
    group := ["Form"], name := "Selected", errorCode := "SELECTED", errorEntityRelPath := "../Rows/N",
    condition := if guard.isSome then "FieldFilled(Rows/N)" else "FieldFilled(Rows/N) And " ++ operation ++ " > 0",
    severity := "ERROR" } world).toOption
  let verdicts ← (rule.evalOrdinaryRepeatableFull document (some world)).toOption
  if partialCheck then
    return ← match rule.evalOrdinaryRepeatablePartial document .full with
      | .ok .skipped => some ([], [])
      | _ => none
  let (_, computation) ← (lowerComputation model .english {
    group := ["Form"], name := "Selected", targetRelPath := "../Rows/Out", commonPrecondition := none,
    alternatives := [{ precondition := guard, operation }], errorCodesToSuppress := [] }).toOption
  let results ← (runComputations world prepared document [computation]).toOption
  pure (verdicts.map (·.2.verdict), results.map (·.outcome))

private def rowFilter := "Valid(Date(Rows/D, \"02\", $Rows/Y))"
example : rows ("Sum(Rows*/N Having " ++ rowFilter ++ ")") =
      some ([.fired .omission, .notFired, .fired .omission], ["value 2", "value 0", "value 2"]) ∧
    rows ("FirstFilledValue(Rows*/N Having " ++ rowFilter ++ ")") =
      some ([.fired .omission, .notFired, .fired .omission], ["value 2", "value 0", "value 2"]) ∧
    rows "77" (some ("AtLeastOneFieldFilled(Rows*/N Having " ++ rowFilter ++ ")")) =
      some (List.replicate 3 (.fired .value), ["value 77", "cleared", "value 77"]) ∧
    rows ("Sum(Rows*/N Having " ++ rowFilter ++ ")") (partialCheck := true) = some ([], []) := by native_decide

private def partialModel (mode : TemporalPartialMode) (format : String := "yyyy-MM-dd") : FlatModel := { model with
  fields := model.fields.map fun field => if field.id == 14 then { field with
    policy := { kind := .temporal .date TemporalComponents.fullDate }
    temporalTargetPolicy := some { format, partialMode := mode } } else field }

example : admission "Valid(Date(DayFromDate(Rows/Stamp), Rows/M, Rows/Y))" (partialModel .full) = .admitted ∧
    admission "Valid(Date(DayFromDate(Rows/Stamp), Rows/M, Rows/Y))" (partialModel .dayOptional) = .refused (some .invalidDateType) ∧
    admission "Valid(Date(Rows/D, MonthFromDate(Rows/Stamp), Rows/Y))" (partialModel .dayOptional) = .admitted ∧
    admission "Valid(Date(Rows/D, MonthFromDate(Rows/Stamp), Rows/Y))" (partialModel .monthOptional) = .refused (some .invalidDateType) ∧
    admission "Valid(Date(Rows/D, Rows/M, YearFromDate(Rows/Stamp)))" (partialModel .monthOptional) = .admitted ∧
    admission "Valid(Date(Rows/D, Rows/M, YearFromDate(Rows/Stamp)))" (partialModel .yearOptional) = .refused (some .invalidDateType) := by native_decide

example : run "Valid(Date(Rows/D, MonthFromDate(Rows/Stamp), Rows/Y))" "2"
      (fixture := partialModel .dayOptional) (stamp := "2024-02-00") = some (.fired .omission, ["value 2"]) ∧
    run "Valid(Date(Rows/D, Rows/M, YearFromDate(Rows/Stamp)))" "2"
      (fixture := partialModel .monthOptional) (stamp := "2024-00-00") = some (.fired .omission, ["value 2"]) ∧
    run "Invalid(Date(Rows/D, Rows/M, YearFromDate(Rows/Stamp)))" "14"
      (fixture := partialModel .monthOptional) (stamp := "") = some (.fired .omission, ["value 14"]) := by native_decide

example : (elaborateConstructedDateExtractorField (partialModel .dayOptional) .day .day 14 [10]).isOk = false ∧
    (elaborateConstructedDateExtractorField (partialModel .dayOptional) .month .month 14 [10]).isOk = true ∧
    (elaborateConstructedDateExtractorField (partialModel .monthOptional) .month .month 14 [10]).isOk = false := by native_decide

example : run "Valid(Date(Rows/D, MonthFromDate(Rows/Stamp), Rows/Y))" "2"
      (fixture := partialModel .dayOptional "dd.MM.yyyy") (stamp := "00.02.2024") = some (.fired .omission, ["value 2"]) ∧
    run "Valid(Date(Rows/D, Rows/M, YearFromDate(Rows/Stamp)))" "2"
      (fixture := partialModel .monthOptional "dd.MM.yyyy") (stamp := "00.00.2024") = some (.fired .omission, ["value 2"]) := by native_decide

example : ((elaborateConstructedDateExtractorField (partialModel .dayOptional) .month .month 14 [10]).toOption.bind
      fun checked => (checked.classify (.value (.partialDate "2024-02-00"))).toOption) = some (.value 2) ∧
    ((elaborateConstructedDateExtractorField (partialModel .monthOptional "dd.MM.yyyy") .year .year 14 [10]).toOption.bind
      fun checked => (checked.classify (.value (.partialDate "00.00.2024"))).toOption) = some (.value 2024) ∧
    (elaborateConstructedDateExtractorField { model with fields := model.fields.map fun field =>
      if field.id == 14 then { field with temporalTargetPolicy := none } else field }
      .day .day 14 [10]).isOk = true := by native_decide

end A12Kernel.Dm.HavingDateValidityLocks
