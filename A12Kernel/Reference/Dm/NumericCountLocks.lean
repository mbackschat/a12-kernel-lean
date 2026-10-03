import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Parser
import A12Kernel.Reference.Dm.Replay

/-! # Filled-field counts inside numeric expressions

These locks distinguish rational comparison from integer truncation and count reads from stale
document reads. Kernel admission is retained in the filled-field count expression checkpoint;
the scheduling and composition examples below are internal execution checks.
-/

namespace A12Kernel.Dm.NumericCountLocks

open A12Kernel A12Kernel.Dm

private def model : FlatModel := { fields := [
  { id := 1, groupPath := ["Form", "Inputs"], name := "A",
    policy := { kind := .number { scale := 0, signed := true } } },
  { id := 2, groupPath := ["Form", "Inputs"], name := "B", policy := { kind := .string } },
  { id := 3, groupPath := ["Form"], name := "Out",
    policy := { kind := .number { scale := 0, signed := true } } },
  { id := 4, groupPath := ["Form"], name := "Down",
    policy := { kind := .number { scale := 0, signed := true } } }] }

private def definition (name target operation : String) : DmComputation := {
  group := ["Form"], name, targetRelPath := target, commonPrecondition := none
  alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }

private def input (a : Option String) (b : Bool) : DocumentData := {
  instantiatedRows := []
  cells := a.toList.map (fun value => {
    address := { field := 1, path := [] }, stored := value
    raw := if value == "bad" then .rejected .malformed else .parsed (.num 1) }) ++
    (if b then [{
      address := { field := 2, path := [] }, stored := "yes"
      raw := .parsed (.str "yes") }] else []) ++
    [3, 4].map fun field => {
      address := { field, path := [] }, stored := "9"
      raw := .parsed (.num 9) } }

private def admitsComparison (expression : String) : Bool :=
  match parseText .english expression with
  | .error _ => false
  | .ok parsed => (lowerCondition model ["Form", "Inputs"] false parsed.body).isOk

example : ["==", "!=", ">", ">=", "<", "<="].all (fun operator =>
    ["1", "1.0", "1.5"].all fun literal =>
      let expected := !(["==", "!="].contains operator) || literal == "1"
      admitsComparison s!"NumberOfFilledFields(/Form/Inputs) {operator} {literal}" == expected &&
      admitsComparison s!"{literal} {operator} NumberOfFilledFields(/Form/Inputs)" == expected) := by
  native_decide

example : ["NumberOfFilledFields(/Form/Inputs) + 1 > 1",
    "1 < NumberOfFilledFields(/Form/Inputs) + 1",
    "NumberOfFilledFields(/Form/Inputs) + 1 < 1.5",
    "NumberOfFilledFields(/Form/Inputs) + [/Form/Inputs/A] >= 0",
    "Abs(NumberOfFilledFields(/Form/Inputs)) == 0",
    "NumberOfFilledFields(/Form/Inputs) + NumberOfFilledFields(/Form/Inputs) >= 0"].all
    admitsComparison := by native_decide

example : ["NumberOfFilledFields(Inputs)", "NumberOfFilledFields(Inputs) + 1",
    "1 + NumberOfFilledFields(Inputs)", "NumberOfFilledFields(Inputs) * 2",
    "Abs(NumberOfFilledFields(Inputs))",
    "NumberOfFilledFields(Inputs) + NumberOfFilledFields(Inputs)",
    "NumberOfFilledFields(Inputs) + [Inputs/A]"].all (fun operation =>
      (lowerComputation model .english (definition "Count" "../Out" operation)).isOk) := by
  native_decide

private def run (operation : String) (a : Option String) (b : Bool)
    (fresh : Bool := false) : Option (List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" (input a b)).toOption
  let authored := [definition "Down" "../Down" "[Out] + 1",
    definition "Count" "../Out" operation] ++
    (if fresh then [definition "Input" "../Inputs/A" "1"] else [])
  let steps ← authored.mapM fun computation =>
    (lowerComputation model .english computation).toOption.map (·.2)
  pure ((← (runComputations world prepared checked steps).toOption).map (·.outcome))

example : run "NumberOfFilledFields(Inputs)" none false = some ["value 0", "value 1"] ∧
    run "NumberOfFilledFields(Inputs)" (some "1") true = some ["value 2", "value 3"] ∧
    run "1 + NumberOfFilledFields(Inputs)" (some "1") false = some ["value 2", "value 3"] := by
  native_decide

example : run "NumberOfFilledFields(Inputs)" (some "bad") true =
    some ["cleared", "cleared"] ∧
    run "NumberOfFilledFields(Inputs)" (some "bad") false true =
    some ["value 1", "value 1", "value 2"] := by
  native_decide

private def comparison (expression : String) (b expected : Bool) : Option (List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" (input (some "1") b)).toOption
  let rule : DmRule := {
    group := ["Form", "Inputs"], name := "Count", errorEntityRelPath := "../A"
    errorCode := "COUNT", condition := expression, severity := "ERROR" }
  let dm : DmModel := {
    flat := model, rules := [rule], computations := [], conditionLanguage := "en_US", refusals := [] }
  let messages := if expected then [{
    code := "COUNT", pointer := "Form/Inputs/A"
    messageType := "OMISSION_ERROR", severity := "ERROR" }] else []
  pure ((replayRules dm .english world checked messages).map (·.status.tier))

example : comparison "NumberOfFilledFields(/Form/Inputs) < 1.5" false true = some ["match"] ∧
    comparison "NumberOfFilledFields(/Form/Inputs) < 1.5" true false = some ["match"] ∧
    comparison "1.5 > NumberOfFilledFields(/Form/Inputs)" false true = some ["match"] ∧
    comparison "NumberOfFilledFields(/Form/Inputs) + 1 < 2.5" false true = some ["match"] := by
  native_decide

example : (lowerComputation model .english
    (definition "Self" "../Out" "NumberOfFilledFields(Inputs, Out)")).isOk = false ∧
    (lowerComputation model .english
      (definition "Other" "../Out" "NumberOfFilledFields(Inputs, Down)")).isOk = true := by
  native_decide

end A12Kernel.Dm.NumericCountLocks
