import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.StampConstructionLocks

private def model : FlatModel := {
  fields := [
    { id := 0, groupPath := ["Form"], name := "D",
      policy := { kind := .temporal .date TemporalComponents.fullDate }
      temporalTargetPolicy := some { format := "yyyy-MM-dd" } },
    { id := 1, groupPath := ["Form"], name := "P",
      policy := { kind := .temporal .date TemporalComponents.fullDate }
      temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .yearOptional } },
    { id := 2, groupPath := ["Form"], name := "T",
      policy := { kind := .temporal .time TemporalComponents.time }
      temporalTargetPolicy := some { format := "HH:mm:ss" } },
    { id := 3, groupPath := ["Form"], name := "Z",
      policy := { kind := .temporal .dateTime TemporalComponents.now }
      temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } },
    { id := 4, groupPath := ["Form"], name := "H",
      policy := { kind := .number { scale := 0, signed := false } }
      numericTargetConstraints := { maxStoredLength := some 2 } },
    { id := 5, groupPath := ["Form"], name := "After", policy := { kind := .number { scale := 0, signed := true } } }]
  timeZoneId := "Europe/Berlin" }

private def expression? (source : String) (model : FlatModel := model) : Option (CheckedScalarTemporalExpression model) := do
  let parsed ← (parseText .english source).toOption
  let surface ← (lowerScalarTemporalExpression model ["Form"] parsed.body).toOption
  (elaborateScalarTemporalExpression model ["Form"] surface).toOption

example : ["DateTime(D,T)", "DateTime(ValueAsDate(P,FirstDay),Time(H))",
    "DateTime(ValueAsDate(P,LastDay),TimeFromDateTime(Z))",
    "ValueAsDate(P,FirstDay)", "AddDays(ValueAsDate(P,LastDay),1)"].all
      (fun source => (expression? source).isSome) := by native_decide

example : [none, some 2024].all (fun year =>
    ["DateTime(D,T)", "Min(Time(H),[T])", "DateTime(ValueAsDate(P,LastDay),T)"].all
      (fun source => (expression? source { model with baseYear := year }).isSome)) := by native_decide


-- The static matrix separates bracket syntax, source family and partial-Date interpretation.
example : ["DateTime([D],T)", "DateTime(D,[T])", "DateTime(T,T)", "DateTime(D,D)",
    "DateTime(P,T)", "DateTime(Z,T)", "DateTime(D,Z)", "ValueAsDate([P],FirstDay)",
    "ValueAsDate(D,FirstDay)"].all (fun source => (expression? source).isNone) := by native_decide

private def checkedInput (date partialText clock hour : String) (model : FlatModel := model) :
    Option (CheckedDocument model) := do
  let dm : DmModel := { flat := model, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Lean.Json.mkObj [("Form", Lean.Json.mkObj
    ([("D", date), ("P", partialText), ("T", clock), ("H", hour),
      ("Z", "2001-01-01T00:00:00"), ("After", "9")].map fun (name, value) =>
        (name, Lean.Json.str value)))])).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" input.data).toOption

private def observed (source date partialText clock hour : String) (baseYear : Option Int := none) :
    Option (Sum ScalarTemporalEvaluationFault (SimpleComparisonOperand ScalarTemporalValue)) := do
  let model := { model with baseYear }
  let input ← checkedInput date partialText clock hour model
  let expression ← expression? source model
  pure (match expression.evalResult .computation input.flatContext with
    | .ok value => .inr value
    | .error fault => .inl fault)

-- The runtime grid separates fixed impossibility, missingness and cause-free non-relevance.
example :
    observed "Time(H)" "2024-03-31" "2024-03-00" "02:30:00" "24" =
      some (.inr (.value .noValue true)) ∧
    observed "Time(H)" "2024-03-31" "2024-03-00" "02:30:00" "" =
      some (.inr (.value .noValue false)) ∧
    observed "DateTime(D,T)" "2024-03-31" "2024-03-00" "02:30:00" "2" =
      some (.inr (.value .noValue true)) ∧
    observed "DateTime(D,T)" "" "2024-03-00" "02:30:00" "2" =
      some (.inr (.value .noValue false)) ∧
    observed "DateTime(ValueAsDate(P,FirstDay),T)" "2024-03-31" "0000-00-00" "02:30:00" "2" =
      some (.inr (.value .nonRelevant true)) := by native_decide

-- Non-relevance absorbs a selector rather than substituting the other, present operand.
example : observed "Min(ValueAsDate(P,FirstDay),[D])" "2024-03-31" "0000-00-00" "02:30:00" "2" =
    some (.inr (.value .nonRelevant true)) := by native_decide

example : ["AddDays(D,DayFromDate(ValueAsDate(P,FirstDay)))",
    "AddSeconds(Z,DayFromDate(ValueAsDate(P,FirstDay)))"].all
    (fun source => (expression? source).isNone) := by native_decide

example : ["AddDays(D,DayFromDate(AddDays(ValueAsDate(P,FirstDay),1)))",
    "AddSeconds(Z,DayFromDate(AddDays(ValueAsDate(P,FirstDay),1)))"].all
    (fun source => observed source "2024-03-31" "0000-00-00" "02:30:00" "2" ==
      some (.inr (.value .nonRelevant true))) := by native_decide

private def given (source hour : String) (baseYear : Option Int := none) : Option Bool := do
  let result ← observed source "2024-03-31" "2024-03-00" "02:30:00" hour baseYear
  match result with
  | .inr (.value _ given) => pure given
  | _ => none

example : ["Min", "Max"].all (fun op =>
    given s!"{op}(Time(H),[T])" "24" == some true &&
    given s!"{op}(Time(H),[T])" "" == some false) := by native_decide

-- A successful absent/non-relevant first argument still reaches the failing second argument.
example : ["", "0000-00-00"].all (fun partialText =>
    decide (observed "DateTime(ValueAsDate(P,FirstDay),TimeFromDateTime(\"31.03.2024T02:30:00\"))"
      "2024-03-31" partialText "02:30:00" "2" = some (.inl .dateTimeLabelUnresolved))) := by native_decide

example : (do
    let expression ← expression? "DateTime(ValueAsDate(P,LastDay),Time(H))"
    pure expression.fieldIds) = some [1, 4] := by native_decide

private def run (source date partialText clock : String) (baseYear : Option Int := none) : Option (List String) := do
  let model := { model with baseYear }
  let input ← checkedInput date partialText clock "2" model
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let steps ← [("After", "1", some "FieldNotFilled(Z)"), ("Z", source, none)].mapM
    fun (name, operation, guard) =>
      (lowerComputation model .english {
        group := ["Form"], name := name ++ "Comp"
        targetRelPath := "../" ++ name, commonPrecondition := guard,
        alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption.map (·.2)
  pure ((← (runComputations world prepared input steps).toOption).map
    (fun result => result.pointer ++ ":" ++ result.outcome)).mergeSort

-- The guard distinguishes clean clearing from poisoned clearing; target order exercises scheduling.
example :
    run "DateTime(D,T)" "2024-03-31" "2024-03-00" "02:30:00" =
      some ["Form/After:value 1", "Form/Z:cleared"] ∧
    run "DateTime(D,T)" "" "" "bad" =
      some ["Form/After:cleared", "Form/Z:cleared"] ∧
    run "AddHours(DateTime(D,T),1)" "2024-10-27" "2024-10-00" "02:30:00" =
      some ["Form/After:cleared", "Form/Z:value 2024-10-27T03:30:00"] ∧
    run "DateTime(ValueAsDate(P,LastDay),T)" "2024-03-31" "2024-02-00" "12:30:00" =
      some ["Form/After:cleared", "Form/Z:value 2024-02-29T12:30:00"] := by native_decide

-- Configured and unconfigured runtime rows separate a clock from Base-Year-completed Dates.
example : [none, some 2024].all (fun year =>
    run "DateTime(D,T)" "2024-03-30" "2024-03-00" "12:30:00" year ==
      some ["Form/After:cleared", "Form/Z:value 2024-03-30T12:30:00"]) := by native_decide

example : [none, some 2024].all (fun year =>
    given "Min(Time(H),[T])" "2" year == some true) := by native_decide

end A12Kernel.Dm.StampConstructionLocks
