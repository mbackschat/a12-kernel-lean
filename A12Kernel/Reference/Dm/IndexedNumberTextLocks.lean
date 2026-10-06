import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.LowerValidation
import A12Kernel.Elaboration.ScalarComputationRun

namespace A12Kernel.Dm.IndexedNumberTextLocks

private def model : FlatModel := {
  fields := [
    { id := 1, name := "Key", groupPath := ["Form"], policy := { kind := .string } },
    { id := 2, name := "Out", groupPath := ["Form"], policy := { kind := .string } },
    { id := 3, name := "Code", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } },
    { id := 4, name := "Amount", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .number { scale := 2, signed := true } },
      numericTargetConstraints := { minFractionalDigits := 2, leadingZerosAllowed := true } },
    { id := 5, name := "Out", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } },
    { id := 6, name := "Flag", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 3 }] }

private structure Scenario where
  amount : Lean.Json := .str "01.50"
  key : String := "R1"
  secondCode : String := "R2"
  repeated : Bool := false
  numberTarget : Bool := false
  scalarPlan : Bool := false
  producer : Option (String × String) := none

private def input (scenario : Scenario) : Lean.Json :=
  let row (code : String) (amount : Lean.Json) := Lean.Json.mkObj [
    ("Code", .str code), ("Amount", amount), ("Out", .str "old")]
  Lean.Json.mkObj [("Form", Lean.Json.mkObj [("Key", .str scenario.key), ("Out", .str "old"), ("Flag", .str "99"),
    ("Rows", .arr #[row "R1" scenario.amount, row scenario.secondCode (.str "02.50")])])]

private def evaluate (expression : String) (computation : Bool)
    (scenario : Scenario := {}) (guard : Option String := none) : Option (Sum Verdict (List String)) := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let data ← (readDocument {
    flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] } (input scenario)).toOption
  let document ← (checkDocument prepared "en_US" data.data).toOption
  if computation then
    let target := if scenario.numberTarget then "Flag" else "Out"
    let step ← (lowerComputation model .english {
      name := "Result", group := ["Form"], targetRelPath := "../" ++ (if scenario.repeated then "Rows/" else "") ++ target,
      commonPrecondition := guard, alternatives := [{ precondition := none, operation := expression }], errorCodesToSuppress := [] }).toOption
    let producers ← scenario.producer.toList.mapM fun (target, operation) =>
      (lowerComputation model .english {
        name := "Producer", group := ["Form"], targetRelPath := "../" ++ target,
        commonPrecondition := none, alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
    if scenario.scalarPlan then
      let scalars ← (step.2 :: producers.map (·.2)).mapM fun step => match step with
        | .number table false => some (CheckedScalarComputationStep.number table)
        | .string table => some (.string table)
        | _ => none
      let plan ← (certifyScalarComputationPlan scalars).toOption
      let results ← (plan.execute world prepared.patterns document).toOption
      pure (.inr (results.filterMap fun result => match result with
        | .number field (.accepted value) => if field == (if scenario.numberTarget then 6 else 2) then some ("value " ++ value.render) else none
        | .string field (.accepted value) => if field == 2 then some ("value " ++ value.text) else none
        | _ => none))
    else
      let results ← (runComputations world prepared document (step.2 :: producers.map (·.2))).toOption
      pure (.inr ((results.filter (·.pointer.endsWith ("/" ++ target))).map (·.outcome)))
  else
    let parsed ← (parseText .english expression).toOption
    let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
    Sum.inl <$> (condition.core.evalAddressed {
      scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable },
      outer := [], input := .checked document }).toOption


example : [(Lean.Json.str "01.50", "01.50"), (.str "1.5", "1.50"),
    (.str "1.5000", "1.50"),
    (.str "-0.00", "0.00")].all (fun (amount, expected) =>
      evaluate ("FieldValueAsString(Rows/Amount For Key) == \"" ++ expected ++ "\"") false { amount } == some (.inl (.fired .value)) &&
      evaluate "FieldValueAsString(Rows/Amount For Key)" true { amount } == some (.inr ["value " ++ expected])) = true := by native_decide

example : evaluate "FieldValueAsString(Rows/Amount For \"R1\") + FieldValueAsString(Rows/Amount For \"R2\")" true =
    some (.inr ["value 01.5002.50"]) := by native_decide

example : [(({ key := "missing" } : Scenario), Verdict.fired .omission, "value !"),
    ({ amount := .str "" }, .fired .omission, "value !"),
    ({ amount := .str "bad" }, .unknown, "cleared"),
    ({ amount := .str "01.5000" }, .unknown, "cleared"),
    ({ secondCode := "R1" }, .unknown, "cleared")].all (fun (scenario, verdict, result) =>
      evaluate "FieldValueAsString(Rows/Amount For Key) + \"!\" == \"!\"" false scenario == some (.inl verdict) &&
      evaluate "FieldValueAsString(Rows/Amount For Key) + \"!\"" true scenario == some (.inr [result])) = true := by native_decide

example : [false, true].all (fun repeated =>
    evaluate "FieldValueAsString(Rows/Amount For Key)" true { repeated } ==
      some (.inr (List.replicate (if repeated then 2 else 1) "value 01.50")) &&
    evaluate "FieldValueAsString(Rows/Amount For Key)" true
      { repeated, amount := .str "bad", producer := some ("Rows/Amount", "2.25") } ==
      some (.inr (List.replicate (if repeated then 2 else 1) "value 2.25"))) = true := by native_decide

example : evaluate "FieldValueAsString(Rows/Amount For Key)" true
    { key := "missing", producer := some ("Key", "\"R2\"") } = some (.inr ["value 02.50"]) := by native_decide

example : [false, true].all (fun scalarPlan =>
    evaluate "\"ok\"" true { scalarPlan } (some "FieldValueAsString(Rows/Amount For Key) == \"01.50\"") ==
      some (.inr ["value ok"]) &&
    evaluate "1" true { scalarPlan, numberTarget := true } (some "FieldValueAsString(Rows/Amount For Key) == \"01.50\"") ==
      some (.inr ["value 1"])) = true := by native_decide

example : ["FieldValueAsString([Rows/Amount For Key])", "FieldValueAsString(Rows/Code For Key)"].all
    (fun expression => (evaluate (expression ++ " == \"x\"") false).isNone &&
      (evaluate expression true).isNone) = true := by native_decide

private def selectedBindings (expression : String) : Option (List FieldId × List FieldId) := do
  let parsed ← (parseText .english expression).toOption
  let surface ← (lowerSelectedStringExpr model ["Form"] parsed.body).toOption
  let checked ← (elaborateSelectedBoundStringExpression model ["Form"] ["Form"] surface).toOption
  pure (checked.declarations.map (·.id), checked.boundDeclarations.map (·.id))

example : selectedBindings "FieldValueAsString(Rows/Amount For Key)" = some ([1, 3, 4], [1]) ∧
    selectedBindings "FieldValueAsString(Rows/Amount For \"R1\")" = some ([3, 4], []) := by native_decide

private def withMissingText (expression : String) (phase : Phase) (scenario : Scenario := {}) :
    Option String := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let data ← (readDocument {
    flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] } (input scenario)).toOption
  let document ← (checkDocument prepared "en_US" data.data).toOption
  let parsed ← (parseText .english expression).toOption
  let surface ← (lowerSelectedStringExpr model ["Form"] parsed.body).toOption
  let checked ← (elaborateSelectedBoundStringExpression model ["Form"] ["Form"] surface).toOption
  let context := document.indexedScalarComputationContext world
  let context := { context with addressed := context.addressed.map fun addressed =>
    { addressed with numberText := fun _ _ => none } }
  pure (match checked.eval phase document.flatContext context.numberText (some context) with
    | .error .indexedReadUnavailable => "unavailable"
    | .error _ => "other fault"
    | .ok .notEvaluated => "empty"
    | .ok (.unknown _) => "unknown"
    | .ok (.value text _) => "value " ++ text)

example : withMissingText "FieldValueAsString(Rows/Amount For Key)" .computation =
    some "unavailable" ∧
    withMissingText "FieldValueAsString(Rows/Amount For Key)" .validation { key := "missing" } =
      some "empty" := by native_decide

example : withMissingText "FieldValueAsString(Rows/Amount For \"R1\") + FieldValueAsString(Rows/Amount For \"R2\")"
      .computation { amount := .str "bad" } = some "unknown" ∧
    withMissingText "FieldValueAsString(Rows/Amount For \"R1\") + FieldValueAsString(Rows/Amount For \"R2\")"
      .validation { amount := .str "bad" } = some "unavailable" := by native_decide

example : ["FieldValueAsString(Flag) == \"1\"",
    "FieldValueAsString(Rows/Amount For Key) + FieldValueAsString(Flag) == \"01.501\""].all
    (fun guard => evaluate "\"ok\"" true { scalarPlan := true, producer := some ("Flag", "1") } (some guard) ==
      some (.inr ["value ok"])) = true := by native_decide

end A12Kernel.Dm.IndexedNumberTextLocks
