import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.LowerValidation
import A12Kernel.Elaboration.GeneratedComputationValidation.Assembly

namespace A12Kernel.Dm.IndexedProductLocks

private def model : FlatModel := {
  fields := [
    { id := 1, name := "Key", groupPath := ["Form"], policy := { kind := .string } },
    { id := 2, name := "Out", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 3, name := "Code", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .string } },
    { id := 4, name := "N", groupPath := ["Form", "Rows", "Items"], repeatableScope := [10, 20], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 6, name := "Q", groupPath := ["Form", "Rows", "Items"], repeatableScope := [10, 20], policy := { kind := .number { scale := 0, signed := false } } },
    { id := 7, name := "S", groupPath := ["Form", "Rows", "Items"], repeatableScope := [10, 20], policy := { kind := .string } },
    { id := 5, name := "Out", groupPath := ["Form", "Rows"], repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 3 },
    { level := 20, path := ["Form", "Rows", "Items"], repeatability := some 3 }] }

private structure Scenario where
  key : String := "R1"
  out : String := "99"
  left : List String := ["2", "5"]
  right : List String := ["3"]
  secondCode : String := "R2"
  repeated : Bool := false
  producer : Option (String × String) := none

private def input (scenario : Scenario) : Lean.Json :=
  let row (code : String) (values : List String) := Lean.Json.mkObj [
    ("Code", .str code), ("Items", .arr (values.map (fun value => Lean.Json.mkObj [("N", .str value), ("Q", .str "7"), ("S", .str "text")])).toArray), ("Out", .str "99")]
  Lean.Json.mkObj [("Form", Lean.Json.mkObj [("Key", .str scenario.key), ("Out", .str scenario.out),
    ("Rows", .arr #[row "R1" scenario.left, row scenario.secondCode scenario.right])])]

private def evaluate (expression : String) (computation : Bool)
    (scenario : Scenario := {}) (guard : Option String := none) : Option (Sum Verdict (List String)) := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let data ← (readDocument {
    flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] } (input scenario)).toOption
  let document ← (checkDocument prepared "en_US" data.data).toOption
  if computation then
    let step ← (lowerComputation model .english {
      name := "Result", group := ["Form"], targetRelPath := if scenario.repeated then "../Rows/Out" else "../Out",
      commonPrecondition := guard, alternatives := [{ precondition := none, operation := expression }], errorCodesToSuppress := [] }).toOption
    let producers ← scenario.producer.toList.mapM fun (target, operation) =>
      (lowerComputation model .english {
        name := "Producer", group := ["Form"], targetRelPath := "../" ++ target,
        commonPrecondition := none, alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
    let results ← (runComputations world prepared document (step.2 :: producers.map (·.2))).toOption
    pure (.inr ((results.filter (·.pointer.endsWith "/Out")).map (·.outcome)))
  else
    let parsed ← (parseText .english expression).toOption
    let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
    Sum.inl <$> (condition.core.evalAddressed {
      scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable },
      outer := [], input := .checked document }).toOption

private def product (left right : String) : String :=
  "SumOfProducts(Rows/Items*/N For " ++ left ++ ", Rows/Items*/N For " ++ right ++ ")"

example : [("Key", "Key", "29"), ("Key", "\"R2\"", "6"), ("\"R2\"", "Key", "6")].all
    (fun (left, right, expected) => evaluate (product left right) true == some (.inr ["value " ++ expected]) &&
      evaluate (product left right ++ " == " ++ expected) false == some (.inl (.fired .omission))) = true := by native_decide

example : evaluate (product "Key" "\"R2\"") true { left := ["2", "bad"] } =
    some (.inr ["cleared"]) := by native_decide

example : [product "Key" "\"R2\"", product "\"R2\"" "Key"].all (fun expression =>
    evaluate expression true { left := ["2", "bad"] } == some (.inr ["cleared"]) &&
    evaluate (expression ++ " == 6") false { left := ["2", "bad"] } == some (.inl .unknown)) = true := by native_decide

example : [({ left := ["", "5"] } : Scenario), { right := [] }, { key := "missing" },
    { key := "" }].all (fun scenario =>
      evaluate (product "Key" "\"R2\"") true scenario == some (.inr ["value 0"])) = true := by native_decide

example : evaluate (product "Key" "Key") true { key := "missing" } = some (.inr ["value 0"]) := by native_decide

example : evaluate (product "Key" "\"R2\"") true { secondCode := "R1" } =
    some (.inr ["cleared"]) := by native_decide

example : evaluate (product "Key" "\"R2\"") true { left := ["2", "5", "7", "bad"] } =
    some (.inr ["value 6"]) := by native_decide

example : evaluate (product "Key" "\"R2\"") true { key := "missing", producer := some ("Key", "\"R2\"") } =
    some (.inr ["value 9"]) := by native_decide

example : evaluate (product "Key" "\"R2\"") true { left := ["bad", "5"], producer := some ("Rows/Items/N", "7") } =
    some (.inr ["value 49"]) := by native_decide

example : evaluate (product "Key" "\"R2\"") true { repeated := true } =
    some (.inr ["value 6", "value 6"]) := by native_decide

example : evaluate "1" true {} (some (product "Key" "\"R2\"" ++ " == 6")) =
    some (.inr ["value 1"]) := by native_decide

example : ["SumOfProducts(Rows/Items/N For Key, Rows/Items/N For Key)",
    "SumOfProducts(Rows/Items*/N For Key, Rows/Items*/N)",
    "SumOfProducts(Rows/Items*/N For Key Having [N] > 0, Rows/Items*/N For Key)",
    "SumOfProducts(Rows/Items For Key, Rows/Items For Key)",
    "SumOfProducts(Rows/Items*/N For Key, Rows/Items*/S For Key)"].all (fun expression =>
      (evaluate expression true).isNone && (evaluate (expression ++ " == 0") false).isNone) = true := by native_decide

example : evaluate "SumOfProducts(Rows/Items*/N For Key, Rows/Items*/Q For Key)" true =
    some (.inr ["value 49"]) := by native_decide

example : evaluate (product "Key" "Key" ++ " == 38") false { left := ["2", "3", "5"] } =
    some (.inl (.fired .value)) := by native_decide

private def generated (scenario : Scenario) : Option Verdict := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let data ← (readDocument {
    flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] } (input scenario)).toOption
  let document ← (checkDocument prepared "en_US" data.data).toOption
  let (_, .number table false) ← (lowerComputation model .english {
    name := "Result", group := ["Form"], targetRelPath := "../Out", commonPrecondition := none
    alternatives := [{ precondition := none, operation := product "Key" "\"R2\"" }], errorCodesToSuppress := [] }).toOption | none
  let generated : GeneratedComputationTable (CheckedNumericComputationOperation model) (CheckedComputationCondition model) := {
    targetField := 2, name := "Result", alternatives := .singleton {
      precondition := table.first.precondition, operation := table.first.operation.operation }, messagePlan := { parts := [] } }
  let rule ← (assembleGeneratedNumericOperationTableRule model generated).toOption
  pure (← (rule.evalAddressedFull {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document } true).toOption).verdict

example : generated { out := "6" } = some .notFired ∧
    generated {} = some (.fired .omission) ∧
    generated { left := ["2", "5", "7"], right := ["3", "4", "6"] } = some (.fired .value) ∧
    generated { left := ["2", "bad"] } = some .unknown := by native_decide

end A12Kernel.Dm.IndexedProductLocks
