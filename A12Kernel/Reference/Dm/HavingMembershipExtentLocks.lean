import A12Kernel.Reference.Dm.HavingFixture

namespace A12Kernel.Dm.HavingMembershipExtentLocks
open Lean A12Kernel

private def model : FlatModel := { HavingFixture.model with
  fields := HavingFixture.model.fields ++ [
  { id := 6, groupPath := ["Form", "Rows", "Pair"], name := "A", repeatableScope := [10],
    policy := { kind := .number { scale := 0, signed := true } } },
  { id := 7, groupPath := ["Form", "Rows", "Pair"], name := "B", repeatableScope := [10],
    policy := { kind := .number { scale := 0, signed := true } } },
  { id := 8, groupPath := ["Form", "Allowed"], name := "Value",
    policy := { kind := .number { scale := 0, signed := true } } },
  { id := 9, groupPath := ["Form", "Rows", "Members"], name := "M", repeatableScope := [10],
    policy := { kind := .number { scale := 0, signed := true } } },
  { id := 10, groupPath := ["Form", "Choices"], name := "V", repeatableScope := [30],
    policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := HavingFixture.model.repeatableGroups ++ [
    { level := 30, path := ["Form", "Choices"], repeatability := some 2 }] }
private def row (n a b : String) := Json.mkObj [
  ("N", .str n), ("Tag", .str "x"), ("Members", Json.mkObj [("M", .str b)]), ("Pair", Json.mkObj [("A", .str a), ("B", .str b)])]
private def rows := #[row "2" "1" "2", row "5" "4" "5", row "7" "3" "4"]
private def extra (value : String := "2") := [
  ("Allowed", Json.mkObj [("Value", .str value)]),
  ("Choices", .arr #[Json.mkObj [("V", .str "2")], Json.mkObj [("V", .str "4")]])]
private def run (operator operand expected : String) (valueModel : FlatModel := model)
    (members : String := "Allowed") :=
  HavingFixture.runModel valueModel (operator ++ "(" ++ operand ++ " In " ++ members ++ ") And FieldFilled(Rows/N)")
    false "" "unused" "unused" (ruleExpected := expected)
    (extra := extra) (rowsOverride := some rows)

example : run "AtLeastOneFieldValueIncludedInValueList" "Rows/Pair" "2" =
    some (.fired .omission, ["value 2"]) := by native_decide

private def tokenModel (enumerated : Bool) : FlatModel := { model with fields := model.fields.map fun field =>
  if field.id < 6 then field else { field with
    policy := { kind := if enumerated then .enumeration else .string }
    enumeration := if enumerated then some { storedTokens := ["1", "2", "3", "4", "5"] } else none } }

example : [false, true].all (fun enumerated => decide (
    run "AtLeastOneFieldValueIncludedInValueList" "Rows/Pair" "2" (tokenModel enumerated) =
      some (.fired .omission, ["value 2"]) ∧
    run "AtLeastOneFieldValueIncludedInValueList" "Rows/Pair" "2" (tokenModel enumerated) "\"2\"" =
      some (.fired .omission, ["value 2"]))) = true := by native_decide

private def operators := ["AtLeastOneFieldValueIncludedInValueList", "NoFieldValueIncludedInValueList",
  "NotAllFieldValuesIncludedInValueList"]
private def matrix (fixture : FlatModel) (subjects members : String) (expected : List String) :=
  expected.length == operators.length && (operators.zip expected).all fun (operator, value) =>
    decide (run operator subjects value fixture members = some (.fired .omission, ["value " ++ value]))

example : [model, tokenModel false, tokenModel true].all (fun fixture =>
    matrix fixture "Rows/Pair" "Allowed" ["2", "12", "14"] &&
    matrix fixture "Rows*/Pair" "Allowed" ["14", "0", "14"] &&
    matrix fixture "Rows*/Pair/A" "Allowed" ["0", "14", "14"] &&
    ["Rows*/Members", "Rows*/Members/M"].all (fun members => matrix fixture "Rows/Pair" members ["14", "0", "9"]) &&
    matrix fixture "Rows/Pair" "Choices*" ["14", "0", "14"] &&
    matrix fixture "Choices*" "Allowed" ["14", "0", "14"]) = true := by native_decide

example : [tokenModel false, tokenModel true].all (fun fixture =>
    matrix fixture "Rows/Pair" "\"2\"" ["2", "12", "14"] &&
    matrix fixture "Rows*/Pair" "\"2\"" ["14", "0", "14"]) = true := by native_decide

private def raw (filter : String) (input : Array Json) (value : String := "2") :
    Option (Verdict × ComputationConditionResult) := do
  let world : World := { now := { epochMillis := 0 } }
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj (("Rows", .arr input) :: extra value))])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let parsed ← (parseText .english (filter ++ " And FieldFilled(Rows/N)")).toOption
  let authored ← (lowerHaving parsed.body).toOption
  let path ← (elaborateStarFieldPath model ["Form"] {
    base := .relative 0, groups := [{ name := "Rows", starred := true }], field := "N" }).toOption
  let checked ← (elaborateStarHavingCore model ["Form"] path authored).toOption
  let .and (.leaf (.fieldMembership operator source)) _ := checked.condition | none
  let frame : CorrelationFrame := { innerEnv := [(10, 1)], outerEnv := [] }
  let context := document.resolvingCorrelationContext
  pure (← (source.evalValidationRead operator context frame).toOption,
    ← (source.evalComputationRead operator context frame).toOption)

example : raw "NoFieldValueIncludedInValueList(Rows*/Pair In Allowed)" #[row "2" "1" "1"] =
      some (.fired .omission, .holds) ∧
    raw "NoFieldValueIncludedInValueList(Rows*/Pair In Allowed)"
      #[row "2" "1" "1", row "5" "1" "1", row "7" "1" "1"] = some (.fired .value, .holds) ∧
    raw "NotAllFieldValuesIncludedInValueList(Allowed In Rows*/Pair)" #[row "2" "1" "1"] =
      some (.fired .omission, .holds) ∧
    raw "NotAllFieldValuesIncludedInValueList(Allowed In Rows*/Pair)"
      #[row "2" "1" "1", row "5" "1" "1", row "7" "1" "1"] = some (.fired .value, .holds) := by native_decide

example : raw "NoFieldValueIncludedInValueList(Rows*/Pair In Allowed)" #[row "2" "bad" ""] =
      some (.unknown, .poison .malformed) ∧
    raw "NoFieldValueIncludedInValueList(Rows*/Pair In Allowed)" #[row "2" "" ""] =
      some (.fired .omission, .holds) ∧
    raw "AtLeastOneFieldValueIncludedInValueList(Rows*/Pair In Allowed)"
      #[row "2" "2" "bad", row "5" "bad" "bad"] = some (.fired .value, .holds) ∧
    raw "AtLeastOneFieldValueIncludedInValueList(Allowed In Rows*/Pair)"
      #[row "2" "2" "bad", row "5" "bad" "bad"] = some (.fired .value, .poison .malformed) := by native_decide

private def accepted (filter : String) (fixture : FlatModel := model) : Bool :=
  ((parseText .english ("Sum(Rows*/N Having " ++ filter ++ " And FieldFilled(Rows/N)) > 0")).toOption.bind fun parsed =>
    (lowerCondition fixture ["Form"] false parsed.body).toOption).isSome

example : [
    "AtLeastOneFieldValueIncludedInValueList(Rows/Pair/A In Allowed/Value)",
    "AtLeastOneFieldValueIncludedInValueList(Rows*/Pair, Rows*/Pair In Allowed)",
    "FieldValueIncludedInValueList(Rows/Pair/A, [Allowed/Value])"].all accepted = true ∧
    ["AtLeastOneFieldValueIncludedInValueList(Rows/Pair, Rows/Pair In Allowed)",
    "AtLeastOneFieldValueIncludedInValueList(Rows/Pair In Rows/Pair)",
    "AtLeastOneFieldValueIncludedInValueList(Rows/Pair In Rows/Pair/A)",
    "AtLeastOneFieldValueIncludedInValueList(Rows/Pair/A In Rows/Pair/A)",
    "AtLeastOneFieldValueIncludedInValueList(/Form In Allowed)",
    "AtLeastOneFieldValueIncludedInValueList(Rows/Pair In /Form)",
    "AtLeastOneFieldValueIncludedInValueList(Rows/Pair In Rows/Tag)",
    "FieldValueIncludedInValueList(Rows/Pair, [Allowed/Value])",
    "FieldValueIncludedInValueList(Rows/Pair/A, [Rows*/Members/M])",
    "AtLeastOneFieldValueIncludedInValueList(Rows/Pair/A[1] In Allowed)",
    "AtLeastOneFieldValueIncludedInValueList(Rows*/Pair Having FieldFilled(Rows/N) In Allowed)"].all
      (fun filter => !accepted filter) = true := by native_decide

private def categoryModel : FlatModel := { (tokenModel true) with fields := (tokenModel true).fields.map fun field =>
  if field.id < 6 then field else { field with enumeration := some {
    storedTokens := ["1", "2", "3", "4", "5"], categories := [{ name := "Label", tokens := ["5", "4", "3", "2", "1"] }] } } }
private def unionModel : FlatModel := { (tokenModel true) with fields := (tokenModel true).fields.map fun field =>
  if field.id == 6 then { field with enumeration := some { storedTokens := ["1", "4", "3"] } }
  else if field.id == 7 then { field with enumeration := some { storedTokens := ["2", "5", "4"] } } else field }

example : matrix categoryModel "Rows/Pair" "Allowed/Value -> Label" ["12", "2", "14"] = true ∧
    matrix unionModel "Rows/Pair" "\"2\"" ["2", "12", "14"] = true ∧
    accepted "AtLeastOneFieldValueIncludedInValueList(Rows/Pair/A, Rows/Pair/A -> Label In Allowed)" categoryModel = true ∧
    accepted "AtLeastOneFieldValueIncludedInValueList(Rows/Pair In \"9\")" unionModel = false := by native_decide

example : raw "NoFieldValueIncludedInValueList(Rows*/Pair In Allowed)"
    #[row "2" "1" "1", row "5" "1" "1", row "7" "1" "1", row "11" "bad" "bad"] =
    some (.fired .value, .holds) := by native_decide

private def nestedModel : FlatModel := { model with
  fields := (model.fields.map fun field => if field.id == 5 then
    { field with groupPath := ["Form", "Rows"], repeatableScope := [10] } else field) ++ [{
      id := 11, groupPath := ["Form", "Rows", "Bucket", "Items"], name := "C", repeatableScope := [10, 20],
      policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := model.repeatableGroups ++ [{
    level := 20, path := ["Form", "Rows", "Bucket", "Items"], repeatability := some 2 }] }
private def nestedFilter (operand : String) (memberSide : Bool := false) :=
  "AtLeastOneFieldValueIncludedInValueList(" ++
    (if memberSide then "/Form/Allowed In " ++ operand else operand ++ " In /Form/Allowed") ++ ") And FieldFilled(N)"
private def nestedRun (captured : Bool) (operand : String) (memberSide : Bool := false) : Option (List Bool × List String) := do
  let world : World := { now := { epochMillis := 0 } }
  let dm : DmModel := { flat := nestedModel, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let row (n : String) (values : List String) := Json.mkObj [
    ("N", .str n), ("Tag", .str "x"), ("Out", .str "99"), ("Bucket", Json.mkObj [
      ("Items", .arr ((values.map fun value => Json.mkObj [("C", .str value)]).toArray))])]
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj (
    ("Rows", .arr #[row "2" ["1", "1"], row "5" ["2"], row "7" []]) :: extra "1"))])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler nestedModel).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let operation := "Sum(/Form/Rows*/N Having " ++ nestedFilter ((if captured then "$" else "") ++ operand) memberSide ++ ")"
  let rule ← (checkRule dm .english {
    group := ["Form", "Rows"], name := "Nested", errorCode := "NESTED", errorEntityRelPath := "../N",
    condition := "FieldFilled(N) And " ++ operation ++ " > 0", severity := "ERROR" } world).toOption
  let verdicts ← (rule.evalOrdinaryRepeatableFull document (some world)).toOption
  let (_, computation) ← (lowerComputation nestedModel .english {
    group := ["Form", "Rows"], name := "Nested", targetRelPath := "../Out", commonPrecondition := none,
    alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
  let outcomes ← (runComputations world prepared document [computation]).toOption
  pure (verdicts.map (fun result => result.2.verdict.keepsHaving), outcomes.map (·.outcome))

example : [false, true].all (fun memberSide =>
    ["Bucket", "Bucket/Items*", "Bucket/Items*/C"].all (fun operand => decide (
      nestedRun false operand memberSide = some ([true, true, true], ["value 2", "value 2", "value 2"]) ∧
      nestedRun true operand memberSide = some ([true, false, false], ["value 14", "value 0", "value 0"])))) = true := by native_decide

private def nestedReferences (operand : String) (memberSide : Bool := false) : Option (Option (List RepeatableLevel) × Bool × Bool) := do
  let parsed ← (parseText .english ("FieldValuesNotUnique(/Form/Rows*/Tag Having " ++ nestedFilter operand memberSide ++ ")")).toOption
  let checked ← (lowerCondition nestedModel ["Form", "Rows"] false parsed.body).toOption
  let numeric ← (parseText .english ("Sum(/Form/Rows*/N Having " ++ nestedFilter operand memberSide ++ ") > 0")).toOption
  let numericChecked ← (lowerCondition nestedModel ["Form", "Rows"] false numeric.body).toOption
  let scope ← numericChecked.core.ordinaryIterationScope.toOption
  let pointers ← (checked.core.referencePointers [(10, 2)]).toOption
  pure (scope, pointers.contains { field := 11, coordinates := [.wildcard, .wildcard] },
    pointers.contains { field := 11, coordinates := [.concrete 2, .wildcard] })

example : [false, true].all (fun memberSide =>
    ["Bucket", "Bucket/Items*", "Bucket/Items*/C"].all (fun operand => decide (
      nestedReferences operand memberSide = some (none, true, false) ∧
      nestedReferences ("$" ++ operand) memberSide = some (some [10], false, true)))) = true := by native_decide

private def fresh : Option (Verdict × List String) := do
  let fixture := tokenModel false
  let world : World := { now := { epochMillis := 0 } }
  let dm : DmModel := { flat := fixture, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Json.mkObj [("Form", Json.mkObj (("Error", .str "ready") ::
    ("Rows", .arr rows) :: extra))])).toOption
  if !input.refusals.isEmpty then none
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler fixture).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let operation := "Sum(Rows*/N Having AtLeastOneFieldValueIncludedInValueList(Rows/Pair In $Allowed))"
  let rule ← (checkRule dm .english {
    group := ["Form"], name := "Fresh", errorCode := "FRESH",
    errorEntityRelPath := "../Error", condition := "FieldFilled(Error) And " ++ operation ++ " == 2", severity := "ERROR" } world).toOption
  let context : AddressedValidationEvaluationContext fixture := {
    scalar := { fields := document.flatContext.withWorld world, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document }
  let verdict := (← (rule.evalAddressedFull context true).toOption).verdict
  let computation (name target operation : String) := lowerComputation fixture .english {
    group := ["Form"], name, targetRelPath := target, commonPrecondition := none,
    alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }
  let (_, consumer) ← (computation "Consumer" "../Out" operation).toOption
  let (_, producer) ← (computation "Producer" "../Allowed/Value" "\"5\"").toOption
  let outcomes ← (runComputations world prepared document [consumer, producer]).toOption
  pure (verdict, outcomes.map (·.outcome))

example : fresh = some (.fired .omission, ["value 5", "value 5"]) := by native_decide

example : [model, tokenModel false, tokenModel true].all (fun fixture =>
    matrix fixture "Rows/Pair/A, Choices*" "Rows/Members/M" ["9", "5", "14"] &&
    matrix fixture "Rows/Pair" "Allowed/Value, Choices*/V" ["14", "0", "14"]) = true := by native_decide

private def hollowModel : FlatModel := { model with repeatableGroups := model.repeatableGroups ++ [
  { level := 40, path := ["Form", "Hollow"], repeatability := some 2 },
  { level := 50, path := ["EmptyRoot"], repeatability := some 2 }] }

private def admission (filter : String) : Option (Bool × Option KernelStaticDiagnostic) := do
  let parsed ← (parseText .english (filter ++ " And FieldFilled(Rows/N)")).toOption
  let authored ← (lowerHaving parsed.body).toOption
  let source ← (elaborateStarFieldPath hollowModel ["Form"] {
    base := .relative 0, groups := [{ name := "Rows", starred := true }], field := "N" }).toOption
  pure (match elaborateStarHavingCore hollowModel ["Form"] source authored with
    | .ok _ => (true, none)
    | .error error => (false, error.diagnostic?))

example : operators.all (fun operator =>
    ["Hollow* In Allowed", "Rows/Pair In Hollow*"].all (fun operands =>
      admission (operator ++ "(" ++ operands ++ ")") == some (false, some .groupIsEmpty))) = true ∧
    admission "AtLeastOneFieldValueIncludedInValueList(/EmptyRoot* In Allowed)" =
      some (false, some .rootGroupIsEmpty) ∧
    admission "AtLeastOneFieldValueIncludedInValueList(Choices* In Allowed)" = some (true, none) := by native_decide

end A12Kernel.Dm.HavingMembershipExtentLocks
