import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Elaboration.GeneratedComputationValidation

namespace A12Kernel.Dm.UniquenessGuardLocks

private def number (id : FieldId) (name : String) : FlatFieldDecl := {
  id, name, groupPath := ["Form"]
  policy := { kind := .number { scale := 2, signed := true } } }

private def token : FlatFieldDecl := {
  number 1 "A" with policy := { kind := .string }, stringPolicy := { maxLength := some 1 } }

private def enumeration : FlatFieldDecl := {
  number 1 "A" with
  policy := { kind := .enumeration }
  enumeration := some { storedTokens := ["A", "B"] } }

private def date : FlatFieldDecl := {
  number 1 "A" with
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some { format := "yyyy-MM-dd" } }

private structure Inputs where
  rows : List Lean.Json := []
  pool : List (String × Lean.Json) := []
  poolRows : List Lean.Json := []
  rowTarget : Bool := false
  producer : Bool := false
  stringTarget : Bool := false

private def run (source : FlatFieldDecl) (guard a b bad : String)
    (inputs : Inputs := {}) : Option (List String) := do
  let model : FlatModel := {
    fields := [
    { source with id := 1, name := "A" }, { source with id := 2, name := "B" },
    { source with id := 3, name := "Bad" }, number 4 "Out", number 5 "After",
    { source with id := 6, name := "A", groupPath := ["Form", "Rows"], repeatableScope := [10] },
    { source with id := 7, name := "B", groupPath := ["Form", "Rows"], repeatableScope := [10] },
    { number 8 "Keep" with groupPath := ["Form", "Rows"], repeatableScope := [10] },
    { number 9 "Out" with groupPath := ["Form", "Rows"], repeatableScope := [10] },
    { number 10 "After" with groupPath := ["Form", "Rows"], repeatableScope := [10] },
    { source with id := 11, name := "A", groupPath := ["Form", "Pool"] },
    { source with id := 12, name := "B", groupPath := ["Form", "Pool"] },
    { source with id := 13, name := "A", groupPath := ["Form", "PoolRows"], repeatableScope := [20] },
    { source with id := 14, name := "B", groupPath := ["Form", "PoolRows"], repeatableScope := [20] }]
    repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 4 },
      { level := 20, path := ["Form", "PoolRows"], repeatability := some 4 }] }
  let model := if inputs.stringTarget then { model with fields := model.fields.map fun field =>
    if field.id == 4 then { field with policy := { kind := .string } }
    else if field.id == 5 then { field with policy := { kind := .number { scale := 0, signed := true } } }
    else field } else model
  let dm : DmModel := {
    flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("A", .str a), ("B", .str b), ("Bad", .str bad), ("Out", .str "9"), ("After", .str "9"),
    ("Rows", .arr inputs.rows.toArray), ("Pool", Lean.Json.mkObj inputs.pool), ("PoolRows", .arr inputs.poolRows.toArray)])])).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let definitions : List DmComputation := [
    { name := "Consumer", group := ["Form"], targetRelPath := if inputs.rowTarget then "../Rows/Out" else "../Out"
      commonPrecondition := some guard, alternatives := [{
        precondition := none, operation := if inputs.stringTarget then "\"yes\"" else "1" }]
      errorCodesToSuppress := [] },
    { name := "Dependent", group := ["Form"], targetRelPath := if inputs.rowTarget then "../Rows/After" else "../After"
      commonPrecondition := none, alternatives := [{ precondition := none, operation := if inputs.rowTarget then "[Rows/Out] + 1"
        else if inputs.stringTarget then "Length(Out)" else "[Out] + 1" }]
      errorCodesToSuppress := [] }]
  let producer : DmComputation := {
    name := "Producer", group := ["Form"], targetRelPath := "../Rows/A"
    commonPrecondition := none, alternatives := [{ precondition := none, operation := "[A]" }]
    errorCodesToSuppress := [] }
  let definitions := definitions ++ if inputs.producer then [producer] else []
  let lowered ← definitions.mapM fun definition => (lowerComputation model .english definition).toOption
  pure ((← (runComputations world prepared checked (lowered.map (·.2))).toOption).map (·.outcome))

example : [(number 1 "A", "1", "2", "bad"), (token, "A", "B", "too long"),
    (enumeration, "A", "B", "unknown"), (date, "2024-01-01", "2024-01-02", "2024-02-30")].all
    (fun (source, a, b, bad) =>
      run source "FieldValuesNotUnique(A,B,Bad)" a a bad == some ["value 1", "value 2"] &&
      run source "FieldValuesNotUnique(Bad,A,B)" a a bad == some ["cleared", "cleared"] &&
      run source "FieldValuesNotUnique(A,B)" a b "" == some ["cleared", "value 1"] &&
      run source "FieldValuesNotUnique(A,B)" "" "" "" == some ["cleared", "value 1"]) = true := by native_decide

private def row (a b keep : String) : Lean.Json := Lean.Json.mkObj [
  ("A", .str a), ("B", .str b), ("Keep", .str keep), ("Out", .str "9"), ("After", .str "9")]

example : [(number 1 "A", "1", "2"), (token, "A", "B"), (enumeration, "A", "B"),
    (date, "2024-01-01", "2024-01-02")].all (fun (source, a, b) =>
      run source "FieldValuesNotUnique(Rows*/A)" "" "" ""
        { rows := [row a b "1", row a b "1"] } == some ["value 1", "value 2"] &&
      run source "FieldValuesNotUnique(Pool)" "" "" ""
        { pool := [("A", .str a), ("B", .str a)] } == some ["value 1", "value 2"] &&
      run source "FieldValuesNotUnique(Rows*/A Having [Rows/Keep] > 0)" "" "" ""
        { rows := [row a b "1", row a b "1", row b a "bad", row b a "1"] } ==
          some ["cleared", "cleared"] &&
      run source "FieldValuesNotUnique(Rows*/A Having [Rows/Keep] > 0)" "" "" ""
        { rows := [row a b "1", row a b "1", row b a "1", row b a "bad"] } ==
          some ["value 1", "value 2"]) = true := by native_decide

example : [(number 1 "A", "1", "2"), (token, "A", "B"), (enumeration, "A", "B"),
    (date, "2024-01-01", "2024-01-02")].all (fun (source, a, b) =>
      run source "FieldValuesNotUnique(Rows/A,Rows/B)" "" "" ""
        { rows := [row a a "1", row a b "1"], rowTarget := true } ==
          some ["value 1", "cleared", "value 2", "value 1"] &&
      (run source "FieldValuesNotUnique(Rows*/A)" a "" ""
        { rows := [row a b "1", row b a "1"], producer := true }).map (fun values => values.drop (values.length - 2)) ==
          some ["value 1", "value 2"]) = true := by native_decide

example : [(number 1 "A", "1", "2", "bad"), (token, "A", "B", "too long"),
    (enumeration, "A", "B", "unknown"), (date, "2024-01-01", "2024-01-02", "2024-02-30")].all
    (fun (source, a, b, bad) =>
      run source "FieldValuesNotUnique(PoolRows*)" "" "" ""
        { poolRows := [Lean.Json.mkObj [("A", .str a), ("B", .str bad)],
            Lean.Json.mkObj [("A", .str a), ("B", .str b)]] } == some ["value 1", "value 2"] &&
      run source "FieldValuesNotUnique(PoolRows*)" "" "" ""
        { poolRows := [Lean.Json.mkObj [("A", .str a), ("B", .str a)],
            Lean.Json.mkObj [("A", .str bad), ("B", .str b)]] } == some ["cleared", "cleared"]) = true := by native_decide

example : run (number 1 "A") "FieldFilled(A) Or FieldValuesNotUnique(Bad,A,B)" "1" "2" "bad" =
    some ["value 1", "value 2"] ∧
    run (number 1 "A") "FieldNotFilled(A) And FieldValuesNotUnique(Bad,A,B)" "1" "2" "bad" =
    some ["cleared", "value 1"] ∧
    run (number 1 "A") "FieldValuesNotUnique(A)" "1" "2" "" = none ∧
    run (number 1 "A") "FieldValuesNotUnique(A,A)" "1" "2" "" = none ∧
    run (number 1 "A") "FieldValuesNotUnique(Out,A)" "1" "2" "" = none := by native_decide

example : run date "FieldValuesNotUnique(A,B,Bad)" "2024-01-01" "2024-01-01" "bad"
    { stringTarget := true } = some ["value yes", "value 3"] ∧
    run date "FieldValuesNotUnique(Bad,A,B)" "2024-01-01" "2024-01-01" "bad"
    { stringTarget := true } = some ["cleared", "cleared"] := by native_decide

example : [(number 1 "A", "1"), (token, "A"), (enumeration, "A"),
    (date, "2024-01-01")].all (fun (source, a) =>
      ["", "A, "].all fun leading =>
        let guard := s!"FieldValuesNotUnique({leading}Rows*/A Having CurrentRepetition(Rows) <= [$Rows/Keep])"
        run source guard "" "" "" { rows := [row a a "1", row a a "2"], rowTarget := true } ==
          some ["cleared", "value 1", "value 1", "value 2"] &&
        run source guard "" "" "" { rows := [row a a "1", row a a "bad"], rowTarget := true } ==
          some ["cleared", "cleared", "value 1", "cleared"]) := by native_decide

private def generatedPhase : Option (Bool × Bool) := do
  let model : FlatModel := { fields := [number 1 "A", number 2 "B", number 3 "Bad", number 4 "Out"] }
  let parsed ← (parseText .english "FieldValuesNotUnique(Bad,A,B)").toOption
  let surface ← (lowerGuard model ["Form"] false parsed.body (some ["Form"])).toOption
  let guard ← (model.elaborateCheckedComputationCondition ["Form"] ["Form"] surface).toOption
  let operation ← (elaborateCompleteNumericComputationOperation model ["Form"] 4
    (.literal { value := 1, authoredScale := 0 }) false).toOption
  let table : GeneratedComputationTable (CheckedNumericComputationOperation model) (CheckedComputationCondition model) := {
    targetField := 4, name := "Computed", commonPrecondition := some guard
    alternatives := .singleton { operation }
    messagePlan := { parts := [.text "duplicate"] } }
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let input ← (readDocument {
      flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (Lean.Json.mkObj [("Form", Lean.Json.mkObj [
      ("A", "1"), ("B", "1"), ("Bad", "bad"), ("Out", "9")])])).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let computed ← (table.evaluateNumericTarget (document.scalarComputationContext world)).toOption
  let rule ← (assembleGeneratedNumericOperationTableRule model table).toOption
  let outcome ← (rule.evalAddressedFull {
    scalar := { fields := document.flatContext.withWorld world, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document } true).toOption
  pure (match computed with | .supported (.inheritedPoison _) => true | _ => false,
        match outcome with | .fired _ => true | _ => false)

example : generatedPhase = some (true, true) := by native_decide

end A12Kernel.Dm.UniquenessGuardLocks
