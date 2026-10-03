import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.ScalarFieldGuardLocks

private def model : FlatModel := { fields := [
  { id := 0, groupPath := ["Form"], name := "B1", policy := { kind := .boolean } },
  { id := 1, groupPath := ["Form"], name := "B2", policy := { kind := .boolean } },
  { id := 2, groupPath := ["Form"], name := "C1", policy := { kind := .confirm } },
  { id := 3, groupPath := ["Form"], name := "C2", policy := { kind := .confirm } }] }

private def result (text : String) (left right : RawCell) : Option ComputationConditionResult := do
  let expression ← (parseText .english text).toOption
  let surface ← (lowerGuard model ["Form"] false expression.body).toOption
  let checked ← (model.elaborateCheckedComputationCondition ["Form"] ["Form"] surface).toOption
  (checked.evalChecked { read := fun id => formalCheck { kind := if id < 2 then .boolean else .confirm } (if id % 2 == 0 then left else right) }).toOption

example :
    result "[B1] == [B2]" (.parsed (.bool true)) (.parsed (.bool true)) = some .holds ∧
    result "[B1] != [B2]" (.parsed (.bool false)) (.parsed (.bool true)) = some .holds ∧
    result "[B1] != [B2]" .empty (.parsed (.bool true)) = some .notTrue ∧
    result "[C1] != [C2]" .empty (.parsed (.conf true)) = some .holds ∧
    result "[C1] != [C2]" .empty .empty = some .notTrue ∧
    result "[B1] == [B2]" .empty (.rejected .malformed) = some (.poison .malformed) := by
  native_decide

private def runtimeModel : FlatModel := { model with fields := model.fields ++ [
  { id := 4, groupPath := ["Form"], name := "R1", policy := { kind := .dateRange },
    dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } },
  { id := 5, groupPath := ["Form"], name := "R2", policy := { kind := .dateRange },
    dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" } },
  { id := 6, groupPath := ["Form"], name := "T", policy := { kind := .number { scale := 0, signed := false } } },
  { id := 7, groupPath := ["Form"], name := "After", policy := { kind := .number { scale := 0, signed := false } } },
  { id := 8, groupPath := ["Form"], name := "Z1", policy := { kind := .temporal .dateTime TemporalComponents.now },
    temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } },
  { id := 9, groupPath := ["Form"], name := "Z2", policy := { kind := .temporal .dateTime TemporalComponents.now },
    temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } },
  { id := 10, groupPath := ["Form"], name := "Text", policy := { kind := .string } },
  { id := 11, groupPath := ["Form"], name := "Stamp", policy := { kind := .temporal .dateTime TemporalComponents.now },
    temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" } }], timeZoneId := "Europe/Berlin" }

private def runOn (target operation condition : String) (values : List (String × String)) : Option (List String) := do
  let dm : DmModel := {
    flat := runtimeModel, computations := [], rules := []
    conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Lean.Json.mkObj [("Form", Lean.Json.mkObj
    ((values ++ [(target, if target == "Stamp" then "2020-01-01T00:00:00" else "9"), ("After", "9")]).map fun (key, value) => (key, Lean.Json.str value)))])).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler runtimeModel).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let steps ← [(target, condition, operation), ("After", "FieldFilled(" ++ target ++ ") Or FieldNotFilled(" ++ target ++ ")", "1")].mapM fun (name, guard, operation) =>
    (lowerComputation runtimeModel .english {
      group := ["Form"], name := name ++ "Comp", targetRelPath := "../" ++ name,
      commonPrecondition := some guard, alternatives := [{ precondition := none, operation }],
      errorCodesToSuppress := [] }).toOption.map (·.2)
  pure ((← (runComputations world prepared document steps).toOption).map
    (fun result => result.pointer ++ ":" ++ result.outcome)).mergeSort

private def run := runOn "T" "1"

example :
    run "[R1] == [R2]" [("R1", "2024-03-01/2024-03-02"), ("R2", "2024-03-01/2024-03-02")] =
      some ["Form/After:value 1", "Form/T:value 1"] ∧
    run "[R1] != [R2]" [("R1", "2024-03-01/2024-03-02"), ("R2", "2024-04-01/2024-04-02")] =
      some ["Form/After:value 1", "Form/T:value 1"] ∧
    run "[R1] != [R2]" [] = some ["Form/After:value 1", "Form/T:cleared"] ∧
    run "[R1] == [R2]" [("R2", "bad")] = some ["Form/After:cleared", "Form/T:cleared"] ∧
    run "[C1] != [C2]" [("C2", "true")] = some ["Form/After:value 1", "Form/T:value 1"] := by
  native_decide

example :
    run "[Z1] < [Z2]" [("Z1", "2024-03-31T01:00:00"), ("Z2", "2024-03-31T03:00:00")] =
      some ["Form/After:value 1", "Form/T:value 1"] ∧
    run "[Z1] < \"31.03.2024T02:30:00\"" [] =
      some ["Form/After:cleared", "Form/T:cleared"] := by native_decide

example :
    runOn "Text" "\"ok\"" "[Z1] < \"31.03.2024T02:30:00\"" [] =
      some ["Form/After:cleared", "Form/Text:cleared"] ∧
    runOn "Stamp" "\"05.03.2024T12:30:00\"" "[Z1] < \"31.03.2024T02:30:00\"" [] =
      some ["Form/After:cleared", "Form/Stamp:cleared"] := by native_decide

private def rich (target operation condition : String) :
    Option (Sum NumericTargetCheckResult DocumentTargetOutcome) := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler runtimeModel).toOption
  let document ← (checkDocument prepared "en_US" { instantiatedRows := [], cells := [] }).toOption
  let (_, step) ← (lowerComputation runtimeModel .english {
    group := ["Form"], name := target ++ "Comp", targetRelPath := "../" ++ target,
    commonPrecondition := some condition, alternatives := [{ precondition := none, operation }],
    errorCodesToSuppress := [] }).toOption
  let context := document.scalarComputationContext world
  match step with
  | .number table _ => .inl <$> (table.evaluate context).toOption
  | .string table => (.inr ∘ .string) <$>
      (table.evaluateOutcomeWithPattern none { read := context.read } context).toOption
  | .document step => (.inr ∘ Prod.fst) <$> (step.run world (fun _ => none) document).toOption
  | _ => none

example :
    rich "T" "1" "[Z1] < \"31.03.2024T02:30:00\"" =
      some (.inl (.supported (.invalidNoValue .calculationValue))) ∧
    rich "Text" "\"ok\"" "[Z1] < \"31.03.2024T02:30:00\"" =
      some (.inr (.string .invalidNoValue)) ∧
    rich "Stamp" "\"05.03.2024T12:30:00\"" "[Z1] < \"31.03.2024T02:30:00\"" =
      some (.inr (.valueError .dateTime)) ∧
    rich "T" "1" "[B1] == True And [Z1] < \"31.03.2024T02:30:00\"" =
      some (.inl (.supported .noValue)) := by native_decide

private def diagnostic (condition : String) : Option KernelStaticDiagnostic := do
  let parsed ← (parseText .english condition).toOption
  let surface ← (lowerGuard runtimeModel ["Form"] false parsed.body).toOption
  match runtimeModel.elaborateCheckedComputationCondition ["Form"] ["Form"] surface with
  | .ok _ => none
  | .error error => (NumericComputationTableElabError.precondition 1 error).diagnostic?

example :
    diagnostic "[B1] < [B2]" = some .invalidTypeForComparison ∧
    diagnostic "[C1] == [C2]" = some .invalidCompareToYes ∧
    diagnostic "[B1] != [C1]" = some .invalidCompareToYes ∧
    diagnostic "[C1] != [B1]" = some .invalidCompareToYes ∧
    diagnostic "[R1] < [R2]" = some .invalidTypeForComparison := by native_decide


private def rowRuntimeModel : FlatModel := { runtimeModel with
  fields := runtimeModel.fields.map fun field =>
    { field with groupPath := ["Form", "Rows"], repeatableScope := [10] }
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 }] }

private def rowFailure (condition : String) (stamp : String := "") :
    Option (List (CellAddr × DocumentTargetOutcome × CellObservation Unit) × List String) := do
  let dm : DmModel := {
    flat := rowRuntimeModel, computations := [], rules := []
    conditionLanguage := "en_US", refusals := [] }
  let row := Lean.Json.mkObj [("Text", "old"), ("After", "9"), ("Z1", Lean.Json.str stamp)]
  let input ← (readDocument dm (Lean.Json.mkObj [("Form", Lean.Json.mkObj
    [("Rows", Lean.Json.arr #[row])])])).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler rowRuntimeModel).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let steps : List (LoweredComputation rowRuntimeModel) ← [("Text", condition, "\"ok\""),
      ("After", "FieldFilled(Text) Or FieldNotFilled(Text)", "1")].mapM fun (target, guard, operation) =>
    (lowerComputation rowRuntimeModel .english {
      group := ["Form", "Rows"], name := target ++ "Comp", targetRelPath := "../" ++ target
      commonPrecondition := some guard, alternatives := [{ precondition := none, operation }]
      errorCodesToSuppress := [] }).toOption.map (·.2)
  let some (.rows table) := steps.head? | none
  let outcomes ← ((table builtinStringPatternCompiler).run world prepared.patterns document).toOption
  let results ← (runComputations world prepared document steps).toOption
  pure (outcomes.map (fun (address, outcome, cell) =>
      let observation : CellObservation Unit := match observeCell .computation cell with
        | .empty => .empty
        | .value _ => .value ()
        | .unknown cause => .unknown cause
        | .poison cause => .poison cause
      (address, outcome, observation)),
    (results.map fun result => result.pointer ++ ":" ++ result.outcome).mergeSort)

-- Internal composition separator for the row-table branch of spec/09 §3.2; the kernel grid's
-- repeated targets are Number, so this lock adds no String-row calibration claim.
set_option synthInstance.maxSize 512 in
example :
    rowFailure "[Z1] < \"31.03.2024T02:30:00\"" =
      some ([({ field := 10, path := [1] }, .valueError .string, .poison .computedDependency)],
        ["Form/Rows/After:cleared", "Form/Rows/Text:cleared"]) ∧
    rowFailure "[Z1] < \"31.03.2024T02:30:00\"" "bad" =
      some ([({ field := 10, path := [1] }, .string (.poison .dateFormat), .poison .computedDependency)],
        ["Form/Rows/After:cleared", "Form/Rows/Text:cleared"]) ∧
    rowFailure "[Z1] < \"31.03.2024T01:30:00\"" =
      some ([({ field := 10, path := [1] }, .string .noValue, .empty)],
        ["Form/Rows/After:value 1", "Form/Rows/Text:cleared"]) := by native_decide

end A12Kernel.Dm.ScalarFieldGuardLocks
