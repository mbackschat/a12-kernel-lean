import A12Kernel.Reference.Dm.HavingFixture
import A12Kernel.Reference.Dm.Validate

namespace A12Kernel.Dm.HavingPatternLocks
open A12Kernel Lean

private def pattern (op : String) (field : String := "Rows/Tag") (source : String := "[0-9]+") : String :=
  "[" ++ field ++ "] " ++ op ++ " \"" ++ source ++ "\""
private def sum (filter : String) : String := "Sum(Rows*/N Having " ++ filter ++ ")"
private def run (filter first second expected : String) : Option (Verdict × List String) :=
  HavingFixture.runModel HavingFixture.model filter false "unused" first second (ruleExpected := expected)

example : run (pattern "PatternMatched") "123" "x" "9" = some (.fired .omission, ["value 9"]) ∧
    run (pattern "PatternViolated") "123" "x" "5" = some (.fired .omission, ["value 5"]) ∧
    run (pattern "PatternMatched") "x123" "x" "0" = some (.fired .omission, ["value 0"]) ∧
    run (pattern "PatternViolated") "x123" "x" "14" = some (.fired .omission, ["value 14"]) ∧
    run (pattern "PatternViolated") "" "x" "5" = some (.fired .omission, ["value 5"]) := by native_decide

example : HavingFixture.runModel { HavingFixture.model with fields := HavingFixture.model.fields.map fun field =>
      if field.id == 3 then { field with stringPolicy := { maxLength := some 2 } } else field }
      (pattern "PatternMatched") false "unused" "123" "7"
      (extra := [("Out", .str "99")]) (ruleExpected := "5") = some (.fired .omission, ["cleared"]) := by native_decide

private def rowModel : FlatModel := { HavingFixture.model with fields := HavingFixture.model.fields.map fun field =>
  if field.id == 5 then { field with groupPath := ["Form", "Rows"], repeatableScope := [10] } else field }

private def rows (operation : String) (guard : Option String := none)
    (partialCheck : Bool := false) : Option (List Verdict × List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let dm : DmModel := { flat := rowModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let row := fun (tag n : String) => Json.mkObj [("Tag", .str tag), ("N", .str n), ("Out", .str "99")]
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj [
    ("Rows", .arr #[row "123" "2", row "x" "5", row "45" "7"])])])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler rowModel).toOption
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
  let (_, computation) ← (lowerComputation rowModel .english {
    group := ["Form"], name := "Selected", targetRelPath := "../Rows/Out", commonPrecondition := none,
    alternatives := [{ precondition := guard, operation }], errorCodesToSuppress := [] }).toOption
  let results ← (runComputations world prepared document [computation]).toOption
  pure (verdicts.map (·.2.verdict), results.map (·.outcome))

example : rows (sum ("[Rows/N] > 0 And " ++ pattern "PatternMatched" "$Rows/Tag")) =
      some ([.fired .omission, .notFired, .fired .omission], ["value 14", "value 0", "value 14"]) ∧
    rows (sum ("[Rows/N] > 0 And " ++ pattern "PatternViolated" "$Rows/Tag")) =
      some ([.notFired, .fired .omission, .notFired], ["value 0", "value 14", "value 0"]) ∧
    rows ("Sum(Rows/N, Rows*/N Having " ++ pattern "PatternMatched" ++ ")") =
      some (List.replicate 3 (.fired .omission), ["value 11", "value 14", "value 16"]) := by native_decide

private inductive Admission where
  | reader | operand | refused (code : Option KernelStaticDiagnostic) | admitted
  deriving Repr, BEq, DecidableEq
private def admission (filter : String) (model : FlatModel := HavingFixture.model) : Admission :=
  match (parseText .english filter).toOption.bind (fun parsed => (lowerHaving parsed.body).toOption) with
  | none => .reader
  | some authored => match elaborateStarFieldPath model ["Form"] {
      base := .relative 0, groups := [{ name := "Rows", starred := true }], field := "N" } with
    | .error _ => .operand
    | .ok source => match elaborateStarHavingCore model ["Form"] source authored with
      | .error error => .refused error.diagnostic?
      | .ok _ => .admitted

example : admission "[Rows/Tag] PatternMatched {\"[0-9]+\"}" = .admitted ∧
    admission "[Rows/N] PatternMatched \"[0-9]+\"" = .refused (some .invalidTypeForPatternComparison) ∧
    admission "[Rows/N] PatternMatched \"[\"" = .refused (some .invalidTypeForPatternComparison) ∧
    -- The built-in compiler cannot judge Java syntax, so `[` is its limit, not the Kernel's class.
    admission "[Rows/Tag] PatternMatched \"[\"" = .refused none ∧
    admission (pattern "PatternMatched" "Expected") = .refused (some .noIterationForWildcard) ∧
    admission (pattern "PatternMatched" "$Rows/Tag") = .refused (some .noWildcard) ∧
    admission "{[Rows/Tag]} PatternMatched \"[0-9]+\"" = .reader ∧
    admission "[Rows*/Tag] PatternMatched \"[0-9]+\"" = .reader ∧
    admission "[Rows/Tag For \"A\"] PatternMatched \"[0-9]+\"" = .reader ∧
    admission "[Rows/Tag -> Label] PatternMatched \"[0-9]+\"" = .reader := by native_decide

private def separateCarrier : FlatModel := { HavingFixture.model with fields := HavingFixture.model.fields ++ [
  { id := 6, groupPath := ["Form", "Rows"], name := "Other", policy := { kind := .string }, repeatableScope := [10] }] }

example : HavingFixture.referencesFor (pattern "PatternMatched" "Tag") separateCarrier "Other" = some (true, false) ∧
    HavingFixture.referencesFor "[N] > 0" separateCarrier "Other" = some (false, false) ∧
    HavingFixture.referencesFor ("[N] > 0 And " ++ pattern "PatternViolated" "$Tag") separateCarrier "Other" =
      some (false, true) := by native_decide

example : HavingFixture.runModel HavingFixture.model (pattern "PatternMatched") false "unused" "123" "x"
      (operationOverride := some ("FirstFilledValue(Rows*/N Having " ++ pattern "PatternMatched" ++ ")"))
      (ruleExpected := "2") = some (.fired .omission, ["value 2"]) ∧
    rows ("FirstFilledValue(Rows*/N Having " ++ pattern "PatternViolated" ++ ")") =
      some (List.replicate 3 (.fired .omission), List.replicate 3 "value 5") ∧
    rows (sum (pattern "PatternMatched")) (partialCheck := true) = some ([], []) := by native_decide

example : HavingFixture.runModel HavingFixture.model (pattern "PatternMatched") false "unused" "123" "x"
      (operationOverride := some "77") (ruleCondition := some "FieldFilled(Error)")
      (computationPrecondition := some ("AtLeastOneFieldFilled(Rows*/N Having " ++ pattern "PatternMatched" ++ ")")) =
      some (.fired .value, ["value 77"]) ∧
    rows "77" (some ("AtLeastOneFieldFilled(Rows*/N Having [Rows/N] > 0 And " ++ pattern "PatternMatched" "$Rows/Tag" ++ ")")) =
      some (List.replicate 3 (.fired .value), ["value 77", "cleared", "value 77"]) := by native_decide

private def compileLiteral : StringPatternCompiler := fun source => .compiled (· == source)
private def library (source actual : String) : Option (K × K) := do
  let path ← (elaborateStarFieldPath HavingFixture.model ["Form"] {
    base := .relative 0, groups := [{ name := "Rows", starred := true }], field := "N" }).toOption
  let field : SurfaceFieldPath := { base := .relative 0, groups := ["Rows"], field := "Tag" }
  let matched ← (elaborateStarHavingCore HavingFixture.model ["Form"] path
    (.stringPattern .matched { origin := .inner, field } source) (compilePattern := compileLiteral)).toOption
  let violated ← (elaborateStarHavingCore HavingFixture.model ["Form"] path
    (.stringPattern .violated { origin := .inner, field } source) (compilePattern := compileLiteral)).toOption
  let context : CorrelationContext := { read := fun _ _ => {
    rawPresent := true, parsed := some (.str actual), findings := [] } }
  let frame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [] }
  pure (matched.condition.evalTruthIn context frame, violated.condition.evalTruthIn context frame)

example : library "abc" "abc" = some (.tru, .fls) ∧
    library "def" "abc" = some (.fls, .tru) ∧
    library "(?<=abc)" "(?<=abc)" = none ∧
    admission "[Rows/Tag] PatternMatched \"abc\"" = .refused none := by native_decide

example : admission (pattern "PatternMatched") { HavingFixture.model with fields := HavingFixture.model.fields.map fun field =>
      if field.id == 3 then { field with stringValueMode := .raw } else field } != .admitted ∧
    admission (pattern "PatternMatched") { HavingFixture.model with fields := HavingFixture.model.fields.map fun field =>
      if field.id == 3 then { field with customType := some { name := "Code" } } else field } = .admitted := by native_decide

example : HavingFixture.runModel HavingFixture.model
      ("[Rows/N] > 0 And " ++ pattern "PatternMatched" "Expected") false "123" "unused" "unused"
      (ruleExpected := "14") = some (.fired .omission, ["value 14"]) ∧
    HavingFixture.runModel HavingFixture.model
      ("[Rows/N] > 0 And " ++ pattern "PatternMatched" "Expected") true "123" "unused" "unused"
      (ruleExpected := "14") = some (.fired .omission, ["value drop", "value 0"]) := by native_decide

private def emptyRows : List (Array Json) := [#[],
  #[Json.mkObj [("Tag", .str "123"), ("N", .str "")]],
  #[Json.mkObj [("Tag", .str "123")]]]

private def emptyRun (op source : String) (rows : Array Json) : Option (Verdict × List String) :=
  HavingFixture.runModel HavingFixture.model (pattern op "Rows/Tag" source) false "unused" "123" "x"
    (extra := [("Out", .str "99")]) (ruleExpected := "0") (rowsOverride := some rows)

example : ["PatternMatched", "PatternViolated"].all (fun op =>
    admission (pattern op "Rows/Tag" "") == .admitted &&
    emptyRows.all (fun rows =>
      emptyRun op "" rows == some (.fired .value, ["cleared"]) &&
      emptyRun op "[0-9]+" rows == some (.fired .omission, ["value 0"]))) = true := by native_decide

end A12Kernel.Dm.HavingPatternLocks
