import A12Kernel.Elaboration.GeneratedComputationValidation.Execution
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

private def capturedAdmission (token : Bool) (operation : String) : Option (List Bool) := do
  let model : FlatModel := {
    fields := [
      { id := 1, name := "A", groupPath := ["Form", "Rows"], repeatableScope := [10]
        policy := { kind := if token then .string else .number { scale := 0, signed := true } } },
      { id := 2, name := "Keep", groupPath := ["Form", "Rows"], repeatableScope := [10]
        policy := { kind := .number { scale := 0, signed := true } } },
      { id := 3, name := "Out", groupPath := ["Form", "Rows"], repeatableScope := [10]
        policy := { kind := .number { scale := 0, signed := true } } }]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }
  let (_, .number table _) ← (lowerComputation model .english
    (definition "Read" "../Rows/Out" operation)).toOption | none
  let .atom atom := table.first.operation.operation.core.expression | none
  pure ([[], [10], [10, 20], [20]].map (model.admitsNumericComputationOperand · atom))

example : ["NumberOfFilledFields(Rows*/A Having CurrentRepetition(Rows) <= [$Rows/Keep])",
    "FirstFilledValue(Rows*/A Having CurrentRepetition(Rows) <= [$Rows/Keep])",
    "NumberOfValueInFields(1 In Rows*/A Having CurrentRepetition(Rows) <= [$Rows/Keep])"].all
    (fun operation => capturedAdmission false operation == some [false, true, true, false]) ∧
    capturedAdmission true
      "NumberOfValueInFields(\"A\" In Rows*/A Having CurrentRepetition(Rows) <= [$Rows/Keep])" =
        some [false, true, true, false] := by native_decide

private def filteredModel : FlatModel := {
  fields := [
    { id := 1, groupPath := ["Form"], name := "Anchor", policy := { kind := .number { scale := 0, signed := true } } },
    { id := 2, groupPath := ["Form", "Rows"], name := "Qty", repeatableScope := [10], policy := { kind := .string } },
    { id := 3, groupPath := ["Form", "Rows"], name := "Keep", repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 4, groupPath := ["Form"], name := "Out", policy := { kind := .number { scale := 0, signed := true } } },
    { id := 5, groupPath := ["Form"], name := "Down", policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 2 }] }

private def filteredInput (keep : String) (badTarget : Bool) : DocumentData := {
  instantiatedRows := [1, 2, 3].map fun row => { group := 10, path := [row] }
  cells := [1, 4, 5].map (fun field => {
    address := { field, path := [] }, stored := "9", raw := .parsed (.num 9) }) ++
    [1, 2, 3].flatMap fun row => [
      { address := { field := 2, path := [row] }, stored := "entry",
        raw := if badTarget && row == 2 then .rejected .malformed else .parsed (.str "entry") },
      { address := { field := 3, path := [row] }, stored := if row == 1 then "1" else keep,
        raw := if row == 1 then .parsed (.num 1) else
          if keep == "bad" then .rejected .malformed else .parsed (.num (if keep == "1" then 1 else 0)) }] }

private def filteredOperation := "NumberOfFilledFields(Anchor, Rows*/Qty Having [Rows/Keep] > 0)"

private def filteredRun (keep : String) (badTarget : Bool) (fresh : Bool := false) : Option (List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler filteredModel).toOption
  let checked ← (checkDocument prepared "en_US" (filteredInput keep badTarget)).toOption
  let definitions := [definition "Down" "../Down" "[Out] + 1", definition "Count" "../Out" filteredOperation] ++
    (if fresh then [definition "Keep" "../Rows/Keep" "1"] else [])
  let steps ← definitions.mapM fun computation =>
    (lowerComputation filteredModel .english computation).toOption.map (·.2)
  pure ((← (runComputations world prepared checked steps).toOption).map (·.outcome))

example : filteredRun "0" true = some ["value 2", "value 3"] ∧
    filteredRun "1" false = some ["value 3", "value 4"] ∧
    filteredRun "1" true = some ["cleared", "cleared"] ∧
    filteredRun "bad" false = some ["cleared", "cleared"] := by native_decide

private def filteredComparison (expression keep : String) (badTarget expected : Bool) : Option (List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler filteredModel).toOption
  let checked ← (checkDocument prepared "en_US" (filteredInput keep badTarget)).toOption
  let rule : DmRule := { group := ["Form"], name := "Count", errorEntityRelPath := "../Anchor", errorCode := "COUNT", condition := expression, severity := "ERROR" }
  let dm : DmModel := { flat := filteredModel, rules := [rule], computations := [], conditionLanguage := "en_US", refusals := [] }
  let messages := if expected then [{ code := "COUNT", pointer := "Form/Anchor", messageType := "OMISSION_ERROR", severity := "ERROR" }] else []
  pure ((replayRules dm .english world checked messages).map (·.status.tier))

example : filteredComparison (filteredOperation ++ " == 2") "0" true true = some ["match"] ∧
    filteredComparison ("2 == " ++ filteredOperation) "bad" false true = some ["match"] ∧
    filteredComparison (filteredOperation ++ " + 1 > 3") "1" false true = some ["match"] ∧
    filteredComparison (filteredOperation ++ " > 0") "1" true false = some ["match"] := by native_decide

example : filteredRun "bad" false true = some ["value 1", "value 1", "cleared", "value 3", "value 4"] ∧
    filteredRun "0" true true = some ["value 1", "value 1", "cleared", "cleared", "cleared"] := by native_decide

example : (do
    let parsed ← (parseText .english (filteredOperation ++ " == 2")).toOption
    let condition ← (lowerCondition filteredModel ["Form"] false parsed.body).toOption
    pure (condition.hasHaving, condition.core.referencesField 3,
      condition.core.referencesErrorField 3)) = some (true, true, false) := by native_decide

example : ["Out", "Down"].map (fun target =>
    (lowerComputation filteredModel .english (definition "Count" "../Out"
      s!"NumberOfFilledFields(Rows*/Qty Having [Rows/Keep] > [{target}])")).isOk) =
    [false, true] := by native_decide

example : [2, 99].all (fun field =>
    let forged : FlatFieldDecl := { id := field, groupPath := ["Form"], name := "Forged", policy := { kind := .string } }
    !(filteredModel.admitsNumericComputationOperand [] (.filledFieldCount { operands := [.field forged] }))) := by native_decide

private def countFault (filteredFirst directPoison : Bool) : Option NumericComputationResult := do
  let selected := "Rows*/Qty Having [Rows/Keep] > 0"
  let operands := if filteredFirst then selected ++ ", Anchor" else "Anchor, " ++ selected
  let (_, .number table _) ← (lowerComputation filteredModel .english
    (definition "Count" "../Out" ("NumberOfFilledFields(" ++ operands ++ ")"))).toOption | none
  let .atom (.filledFieldCount source) := table.first.operation.operation.core.expression | none
  let good : CheckedCell := { rawPresent := true, parsed := some (.num 1), findings := [] }
  let bad (cause : FormalCause) : CheckedCell := { good with findings := [cause] }
  let context : ScalarComputationContext := {
    read := fun _ => if directPoison then bad .malformed else good
    addressed := some {
      document := (filteredInput "1" false).toDocument
      read := fun _ field => if field == 2 then bad .malformed else good } }
  (source.evaluateComputationCount context (some fun row _ =>
    if row.lookup 10 == some 2 then bad .dateFormat else good)).toOption

example : countFault false false = some (.poison .dateFormat) ∧
    countFault false true = some (.poison .malformed) ∧
    countFault true true = some (.poison .dateFormat) := by native_decide

private def indexedModel : FlatModel := {
  filteredModel with repeatableGroups := [{
    level := 10, path := ["Form", "Rows"], repeatability := some 2, indexField := some 3 }] }

private def indexedInput (keep : String) (badTarget : Bool) : DocumentData :=
  let source := filteredInput keep badTarget
  { source with cells := source.cells.map fun cell =>
      if cell.address.field == 3 && cell.address.path != [1] then
        { cell with raw := if keep == "bad" then .rejected .malformed
            else .parsed (.num (if keep == "1" then 1 else 2)) }
      else cell }

private def indexedRun (key keep : String) (badTarget : Bool := false)
    (freshKey : Bool := false) (clearValue : Bool := false)
    (presenceDependent : Bool := false) (skipCount : Bool := false) : Option (List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler indexedModel).toOption
  let checked ← (checkDocument prepared "en_US" (indexedInput keep badTarget)).toOption
  let dependent := if presenceDependent then
    { definition "Down" "../Down" "1" with commonPrecondition := some "FieldFilled(Out) Or FieldNotFilled(Out)" }
    else definition "Down" "../Down" "[Out] + 1"
  let count := { definition "Count" "../Out" s!"NumberOfFilledFields(Anchor, Rows/Qty For {key})" with
    commonPrecondition := if skipCount then some "[Anchor] < 0" else none }
  let authored := [dependent, count] ++
      (if freshKey then [definition "Key" "../Anchor" "1"] else []) ++
      (if clearValue then [definition "Value" "../Rows/Qty" "\"\""] else [])
  let steps ← authored.mapM fun computation =>
    (lowerComputation indexedModel .english computation).toOption.map (·.2)
  let outcomes ← (runComputations world prepared checked steps).toOption
  pure ((outcomes.filter fun outcome => !clearValue ||
    outcome.pointer == "Form/Out" || outcome.pointer == "Form/Down").map (·.outcome))

example : indexedRun "\"1\"" "2" = some ["value 2", "value 3"] := by native_decide
example : indexedRun "\"3\"" "2" = some ["value 1", "value 2"] := by native_decide
example : indexedRun "\"1\"" "bad" = some ["cleared", "cleared"] := by native_decide
example : indexedRun "\"1\"" "1" = some ["cleared", "cleared"] := by native_decide
example : indexedRun "\"2\"" "2" true = some ["cleared", "cleared"] := by native_decide
example : indexedRun "Anchor" "2" = some ["value 1", "value 2"] := by native_decide
example : indexedRun "Anchor" "2" false true = some ["value 1", "value 2", "value 3"] := by native_decide

example : indexedRun "\"1\"" "2" false false true = some ["value 1", "value 2"] := by native_decide

example : indexedRun "\"1\"" "bad" false false false true = some ["cleared", "cleared"] ∧
    indexedRun "\"1\"" "1" false false false true = some ["cleared", "cleared"] ∧
    indexedRun "\"2\"" "2" true false false true = some ["cleared", "cleared"] ∧
    indexedRun "\"1\"" "2" false false false true true = some ["cleared", "value 1"] := by native_decide

private def indexedComparison (keep : String) (badTarget expected : Bool) : Option (List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler indexedModel).toOption
  let checked ← (checkDocument prepared "en_US" (indexedInput keep badTarget)).toOption
  let rule : DmRule := {
    group := ["Form"], name := "Count", errorEntityRelPath := "../Anchor", errorCode := "COUNT",
    condition := "NumberOfFilledFields(Anchor, Rows/Qty For \"1\") == 2", severity := "ERROR" }
  let dm : DmModel := { flat := indexedModel, rules := [rule], computations := [], conditionLanguage := "en_US", refusals := [] }
  let messages := if expected then [{ code := "COUNT", pointer := "Form/Anchor", messageType := "VALUE_ERROR", severity := "ERROR" }] else []
  pure ((replayRules dm .english world checked messages).map (·.status.tier))

example : indexedComparison "2" false true = some ["match"] := by native_decide
example : indexedComparison "bad" false true = some ["match"] := by native_decide
example : indexedComparison "1" false false = some ["match"] := by native_decide

example : (lowerComputation indexedModel .english
    (definition "SelfKey" "../Out" "NumberOfFilledFields(Anchor, Rows/Qty For Out)")).isOk = false := by
  native_decide

example : (lowerComputation indexedModel .english
    (definition "WrongKeyType" "../Out" "NumberOfFilledFields(Anchor, Rows/Qty For Rows/Qty)")).isOk = false := by
  native_decide

private def booleanIndexedModel : FlatModel := {
  indexedModel with fields := indexedModel.fields.map fun declaration =>
    if declaration.id == 1 || declaration.id == 3 then
      { declaration with policy := { kind := .boolean } }
    else declaration }

private def booleanIndexedRun (key : String) : Option (List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler booleanIndexedModel).toOption
  let base := indexedInput "2" false
  let input := { base with cells := base.cells.map fun cell =>
    if cell.address.field == 1 || cell.address.field == 3 then
      let value := cell.address.field == 3 && cell.address.path == [1]
      { cell with stored := if value then "true" else "false", raw := .parsed (.bool value) }
    else cell }
  let checked ← (checkDocument prepared "en_US" input).toOption
  let step ← (lowerComputation booleanIndexedModel .english
    (definition "Count" "../Out" s!"NumberOfFilledFields(Anchor, Rows/Qty For {key})")).toOption
  pure ((← (runComputations world prepared checked [step.2]).toOption).map (·.outcome))

example : booleanIndexedRun "\"false\"" = some ["value 2"] := by native_decide
example : booleanIndexedRun "Anchor" = some ["value 2"] := by native_decide

private def indexedSurface : SurfaceFieldEntitySource := {
  first := .field { base := .absolute, groups := ["Form"], field := "Anchor" }
  rest := [.indexed {
    target := { base := .absolute, groups := ["Form", "Rows"], field := "Qty" }
    key := .literal (.number 1) }] }

private def indexedQuantifierRefused (operator : FieldFillQuantifier) : Option (Bool × Bool) := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler indexedModel).toOption
  let input ← (checkDocument prepared "en_US" (indexedInput "2" false)).toOption
  let source ← (elaborateFieldFillList indexedModel ["Form"] indexedSurface).toOption
  pure (!(CheckedValidationCondition.checkCore indexedModel ["Form"] (.leaf (.fieldFill operator source)) (by native_decide)).isOk,
    !(source.evaluateFill? operator input []).isOk)

example : indexedQuantifierRefused .atLeastOneFieldFilled = some (true, true) ∧
    indexedQuantifierRefused .noFieldFilled = some (true, true) := by native_decide

example : [CheckedSemanticIndexKey.literal (.text "wrong"),
    .field { id := 1, groupPath := ["Form"], name := "Anchor", policy := { kind := .boolean } }].all
    (fun key => !key.agreesWith { id := 3, groupPath := ["Form", "Rows"], name := "Keep", policy := { kind := .number { scale := 0, signed := true } }, repeatableScope := [10] }) = true := by
  native_decide

private def generatedIndexedCount (key : Rat) : Option NumericTargetCheckResult := do
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler indexedModel).toOption
  let input ← (checkDocument prepared "en_US" (indexedInput "2" false)).toOption
  let (_, .number parsed _) ← (lowerComputation indexedModel .english
    (definition "Generated" "../Out" s!"NumberOfFilledFields(Anchor, Rows/Qty For \"{key}\")")).toOption | none
  let operation := parsed.first.operation.operation
  let table : GeneratedComputationTable (CheckedNumericComputationOperation indexedModel)
      (CheckedComputationCondition indexedModel) := {
    targetField := 4, name := "IndexedCount", alternatives := .singleton { operation }
    messagePlan := { parts := [] } }
  let admission ← (admitGeneratedNumericOperationTable indexedModel table (some world)).toOption
  pure (← (admission.executeAddressedTargetResultWithRead world input input.read).toOption).targetCheck

example : generatedIndexedCount 1 = some (.supported (.accepted { unscaled := 2, scale := 0 })) ∧
    generatedIndexedCount 3 = some (.supported (.accepted { unscaled := 1, scale := 0 })) := by native_decide

end A12Kernel.Dm.NumericCountLocks
