import A12Kernel.Elaboration.GeneratedComputationValidation.Assembly
import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.LowerValidation

namespace A12Kernel.Dm.IndexedGroupLocks

private def model : FlatModel := {
  fields := [
    { id := 1, name := "Code", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .string }, stringPolicy := { maxLength := some 2 } },
    { id := 2, name := "A", groupPath := ["Form", "Rows", "Body"], repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 3, name := "B", groupPath := ["Form", "Rows", "Body"], repeatableScope := [10], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 4, name := "C", groupPath := ["Form", "Rows", "Children"], repeatableScope := [10,20], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 5, name := "Key", groupPath := ["Form"], policy := { kind := .string } },
    { id := 6, name := "Out", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 1 },
    { level := 20, path := ["Form", "Rows", "Children"], repeatability := some 2 }] }

private def input (key : String) (firstA : String := "bad") (duplicate : Bool := false)
    (secondCode : String := "R2") (firstB : String := "") : Option (CheckedDocument model) := do
  let row (code a b : String) (children : Array Lean.Json) := Lean.Json.mkObj [
    ("Code", .str code), ("Body", Lean.Json.mkObj [("A", .str a), ("B", .str b)]), ("Children", .arr children)]
  let data := Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("Key", .str key), ("Out", .str "99"), ("Rows", .arr #[
      row "R1" firstA firstB #[], row (if duplicate then "R1" else secondCode) "2" "" #[Lean.Json.mkObj [("C", .str "3")]]])])]
  let dm : DmModel := { flat := model, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }
  let document ← (readDocument dm data).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" document.data).toOption

private def validation (expression : String) (key : String := "R1") (firstA : String := "bad")
    (duplicate : Bool := false) (secondCode : String := "R2")
    (declaringGroup : GroupPath := ["Form"]) : Option Verdict := do
  let document ← input key firstA duplicate secondCode
  let parsed ← (parseText .english expression).toOption
  let condition ← (lowerCondition model declaringGroup false parsed.body).toOption
  (condition.core.evalAddressed {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable },
    outer := [], input := .checked document }).toOption

private def computation (guard : String) (key : String := "R1") (firstA : String := "bad")
    (duplicate : Bool := false) (secondCode : String := "R2")
    (producer : Option (String × String) := none) (target : String := "Out") (firstB : String := "") (suppressScale : Bool := false)
    (declaringGroup : GroupPath := ["Form"]) : Option String := do
  let document ← input key firstA duplicate secondCode firstB
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let lower (target operation : String) (guard : Option String) :=
    (lowerComputation model .english {
      name := "Compute_" ++ (target.replace "/" "_").replace "." "_", group := declaringGroup, targetRelPath := "../" ++ target, commonPrecondition := guard,
      alternatives := [{ precondition := none, operation }],
      errorCodesToSuppress := if suppressScale then ["MVK_INVALID_COMPARE_DEC_PLACES"] else [] }).toOption
  let consumer ← lower target "1" (some guard)
  let producers ← producer.toList.mapM fun (target, operation) => lower target operation none
  let result ← (runComputations world prepared document (consumer.2 :: producers.map (·.2))).toOption
  ((result.filter (fun result => result.pointer.endsWith ("/" ++ (target.splitOn "/").getLast!))).head?).map (·.outcome)

example : validation "GroupFilled(Rows/Body For Key)" = some .notFired ∧
    validation "GroupNotFilled(Rows/Body For Key)" = some .unknown ∧
    computation "GroupFilled(Rows/Body For Key)" = some "value 1" ∧
    computation "GroupNotFilled(Rows/Body For Key)" = some "cleared" := by native_decide

example : validation "GroupFilled(Rows For Key)" = some (.fired .value) ∧
    validation "GroupNotFilled(Rows For Key)" "missing" = some (.fired .omission) ∧
    computation "GroupNotFilled(Rows For Key)" "missing" = some "value 1" ∧
    validation "NoGroupFilled(Rows/Children* For Key)" = some (.fired .omission) ∧
    computation "NoGroupFilled(Rows/Children* For Key)" = some "value 1" := by native_decide

private def groupSignature (compute : Bool) (key firstA : String) : String :=
  String.ofList (["AllGroupsFilled", "NoGroupFilled", "AtLeastOneGroupFilled", "NotAllGroupsFilled", "GroupsNotCollectivelyFilled"].map fun operator =>
    let expression := operator ++ "(Rows/Body For Key, Key)"
    let fired := if compute then computation expression key firstA == some "value 1"
      else (validation expression key firstA).any fun | .fired _ => true | _ => false
    if fired then 'T' else 'F')

example : [false, true].map (groupSignature · "R2" "") = ["TFTFF", "TFTFF"] ∧
    [false, true].map (groupSignature · "R1" "") = ["FFTTT", "FFTTT"] ∧
    [false, true].map (groupSignature · "missing" "") = ["FFTTT", "FFTTT"] ∧
    [false, true].map (groupSignature · "R1" "bad") = ["FFTFF", "TFTFF"] := by native_decide

example : validation "GroupFilled(Rows For Key)" "R1" "bad" false "" = some (.fired .value) ∧
    computation "GroupFilled(Rows For Key)" "R1" "bad" false "" = some "cleared" ∧
    validation "GroupNotFilled(Rows For Key)" "R1" "bad" true = some .unknown ∧
    computation "GroupNotFilled(Rows For Key)" "R1" "bad" true = some "cleared" ∧
    computation "AtLeastOneGroupFilled(Key,Rows/Body For Key)" "R1" "bad" true = some "value 1" ∧
    computation "AtLeastOneGroupFilled(Rows/Body For Key,Key)" "R1" "bad" true = some "cleared" := by native_decide

example : validation "NoGroupFilled(Rows/Children* For Key)" "R2" = some .unknown ∧
    computation "AtLeastOneGroupFilled(Rows/Children* For Key)" "R2" = some "value 1" ∧
    computation "NoGroupFilled(Rows/Children* For Key)" "missing" = some "value 1" ∧
    validation "AllGroupsFilled(Rows For Key)" = none ∧
    computation "AllGroupsFilled(Rows For Key)" = none ∧
    validation "GroupFilled(Rows/Children* For Key)" = none ∧
    computation "GroupFilled(Rows/Children* For Key)" = none ∧
    validation "AllGroupsFilled(Rows/Children* For Key,Key)" = none ∧
    computation "AllGroupsFilled(Rows/Children* For Key,Key)" = none := by native_decide

example : validation "AllGroupsFilled(Rows For Key, Rows For Key)" = none ∧
    computation "AllGroupsFilled(Rows For Key, Rows For Key)" = none ∧
    validation "AllGroupsFilled(Rows For \"R1\", Rows For \"R2\")" = some (.fired .value) ∧
    computation "AllGroupsFilled(Rows For \"R1\", Rows For \"R2\")" = some "value 1" ∧
    validation "NoGroupFilled(Rows For Key, Rows/Body For Key)" = none ∧
    computation "NoGroupFilled(Rows For Key, Rows/Body For Key)" = none := by native_decide

example : computation "GroupFilled(Rows/Body For Key)" "R1" "bad" false "R2" (some ("Rows/Body/A", "7")) = some "value 1" ∧
    computation "GroupNotFilled(Rows/Body For Key)" "R1" "bad" false "R2" (some ("Rows/Body/A", "1 / 0")) "Out" "" true = some "value 1" ∧
    computation "GroupFilled(Rows/Body For Key)" "missing" "2" false "R2" (some ("Key", "\"R1\"")) = some "value 1" := by native_decide

example : computation "GroupFilled(Rows/Body For Key)" "R1" "5" false "R2" none "Rows/Body/A" = some "cleared" ∧
    computation "GroupFilled(Rows/Body For Key)" "R1" "5" false "R2" none "Rows/Body/A" "7" = some "value 1" ∧
    computation "AtLeastOneGroupFilled(Rows/Body For Key)" "R1" "5" false "R2" none "Rows/Body/A" "7" = none ∧
    computation "GroupFilled(Rows/Body For Key)" "R1" "5" false "R2" (some ("Rows/Body/B", "7")) "Rows/Body/A" = some "value 1" := by native_decide

private def conditionalPair : Option (List String) := do
  let document ← input "R1" "5" false "R2" "7"
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let steps ← ["A", "B"].mapM fun field => (lowerComputation model .english {
    name := field, group := ["Form"], targetRelPath := "../Rows/Body/" ++ field,
    commonPrecondition := some "GroupFilled(Rows/Body For Key)",
    alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] }).toOption
  let results ← (runComputations world prepared document (steps.map (·.2))).toOption
  pure (results.map (·.outcome))

example : validation "AllGroupsFilled(Rows/Code For Key,Key)" = some (.fired .value) ∧
    computation "AllGroupsFilled(Rows/Code For Key,Key)" = some "value 1" := by native_decide

example : validation "FieldFilled(Rows/Body/A For Key)" "R2" = some (.fired .value) ∧
    computation "FieldFilled(Rows/Body/A For Key)" "R2" = some "value 1" ∧
    validation "FieldFilled(Rows/Body/A For Key)" = some .unknown ∧
    computation "FieldFilled(Rows/Body/A For Key)" = some "cleared" ∧
    validation "FieldNotFilled(Rows/Body/A For Key)" "missing" = some (.fired .omission) ∧
    computation "FieldNotFilled(Rows/Body/A For Key)" "missing" = some "value 1" := by native_decide

example : validation "[Rows/Body/A For Key] == 2" "R2" = some (.fired .value) ∧
    computation "[Rows/Body/A For Key] == 2" "R2" = some "value 1" ∧
    computation "[Rows/Body/A For Key] == 7" "R1" "bad" false "R2" (some ("Rows/Body/A", "7")) = some "value 1" ∧
    computation "FieldFilled(Rows/Body/A For Key)" "missing" "2" false "R2" (some ("Key", "\"R1\"")) = some "value 1" := by native_decide

example : validation "AllGroupsFilled(Rows/Body/A For Key,Key)" "R2" = some (.fired .value) ∧
    computation "AllGroupsFilled(Rows/Body/A For Key,Key)" "R2" = some "value 1" ∧
    validation "NoGroupFilled(Rows/Body For Key,Rows/Body/A For Key)" = none ∧
    computation "NoGroupFilled(Rows/Body For Key,Rows/Body/A For Key)" = none ∧
    validation "FieldFilled(Rows/Children/C For Key)" = none ∧
    computation "FieldFilled(Rows/Children/C For Key)" = none := by native_decide

private def descendantAggregates := [
  "Sum(Rows/Body/A For Key,Rows/Body/A For \"R2\") == 9",
  "MinValue(Rows/Body/A For Key,Rows/Body/A For \"R2\") == 2",
  "MaxValue(Rows/Body/A For Key,Rows/Body/A For \"R2\") == 7",
  "NumberOfDifferentValues(Rows/Body/A For Key,Rows/Body/A For \"R2\") == 2",
  "FirstFilledValue(Rows/Body/A For Key,Rows/Body/A For \"R2\") == 7",
  "NumberOfValueInFields(2 In Rows/Body/A For Key,Rows/Body/A For \"R2\") == 1"]

example : descendantAggregates.all (fun expression =>
    validation expression "R1" "7" == some (.fired .value) &&
    computation expression "R1" "7" == some "value 1") = true := by native_decide

private def descendantFillOutcomes : List (Option Verdict × Option String) :=
  ["AllFieldsFilled", "NoFieldFilled", "AtLeastOneFieldFilled", "MoreThanOneFieldFilled",
    "NotAllFieldsFilled", "NotExactlyOneFieldFilled", "FieldsNotCollectivelyFilled"].map fun operator =>
    let expression := operator ++ "(Rows/Body/A For Key,Rows/Body/B For Key)"
    (validation expression "R2", computation expression "R2")

example : validation "NumberOfFilledFields(Rows/Body/A For Key,Rows/Body/B For Key) == 1" "R2" = some (.fired .omission) ∧
    computation "NumberOfFilledFields(Rows/Body/A For Key,Rows/Body/B For Key) == 1" "R2" = some "value 1" := by native_decide

example : descendantFillOutcomes = [
    (some .unknown, some "cleared"), (some .unknown, some "cleared"),
    (some (.fired .value), some "value 1"), (some .unknown, some "cleared"),
    (some (.fired .omission), some "value 1"), (some .unknown, some "cleared"),
    (some (.fired .omission), some "value 1")] ∧
    validation "FieldFilled(Rows/Body/A For Key)" "R2" "bad" true = some .unknown ∧
    computation "FieldFilled(Rows/Body/A For Key)" "R2" "bad" true = some "cleared" := by native_decide

private def classification : Option Bool := do
  let parsed ← (parseText .english "GroupFilled(Rows/Body For Key)").toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
  pure (condition.core.anyLeaf ValidationConditionLeaf.requiresClassificationPass)

example : classification = some true := by native_decide

example : conditionalPair = some ["cleared", "cleared", "cleared"] := by native_decide

private def generatedGuard (expression key : String) : Option Bool := do
  let document ← input key
  let parsed ← (parseText .english expression).toOption
  let surface ← (lowerGuard model ["Form"] false parsed.body (some ["Form"])).toOption
  let guard ← (model.elaborateCheckedComputationCondition ["Form"] ["Form"] surface).toOption
  let operation ← (elaborateCompleteNumericComputationOperation model ["Form"] 6
    (.literal { value := 1, authoredScale := 0 }) false).toOption
  let table : GeneratedComputationTable (CheckedNumericComputationOperation model) (CheckedComputationCondition model) := {
    targetField := 6, name := "Computed", commonPrecondition := some guard
    alternatives := .singleton { operation }, messagePlan := { parts := [] } }
  let rule ← (assembleGeneratedNumericOperationTableRule model table).toOption
  let outcome ← (rule.evalAddressedFull {
    scalar := { fields := document.flatContext, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document } true).toOption
  pure (match outcome with | .fired _ => true | _ => false)

example : generatedGuard "GroupFilled(Rows/Body For Key)" "R1" = some false ∧
    generatedGuard "GroupFilled(Rows/Body For Key)" "R2" = some true ∧
    generatedGuard "AtLeastOneGroupFilled(Rows/Children* For Key)" "R1" = some false ∧
    generatedGuard "AtLeastOneGroupFilled(Rows/Children* For Key)" "R2" = some true := by native_decide

private def ruleGroupCondition (operator key : String) (alias : Bool) : String :=
  operator ++ "(" ++ (if alias then "RuleGroup" else "/Form/Rows/Body") ++ " For " ++ key ++ ")"

example : ["GroupFilled", "GroupNotFilled", "AllFieldsFilled", "NoFieldFilled"].all (fun operator =>
    ["\"R1\"", "/Form/Key"].all fun key =>
      let explicit := validation (ruleGroupCondition operator key false) "R1" "7"
        (declaringGroup := ["Form", "Rows", "Body"])
      explicit.isSome && validation (ruleGroupCondition operator key true) "R1" "7"
        (declaringGroup := ["Form", "Rows", "Body"]) == explicit) = true := by native_decide

example : [false, true].all (fun alias =>
    computation (ruleGroupCondition "GroupFilled" "\"R1\"" alias) "R2" "7"
      (target := "A") (firstB := "7") (declaringGroup := ["Form", "Rows", "Body"]) == some "value 1" &&
    computation (ruleGroupCondition "GroupFilled" "/Form/Key" alias) "R1" "7"
      (target := "A") (firstB := "7") (declaringGroup := ["Form", "Rows", "Body"]) == some "value 1" &&
    computation (ruleGroupCondition "GroupFilled" "/Form/Key" alias) "R1" "7"
      (target := "A") (declaringGroup := ["Form", "Rows", "Body"]) == some "cleared" &&
    computation (ruleGroupCondition "GroupFilled" "/Form/Key" alias) "missing" "7"
      (target := "A") (firstB := "7") (declaringGroup := ["Form", "Rows", "Body"]) == some "cleared" &&
    computation (ruleGroupCondition "GroupFilled" "/Form/Key" alias) "R1" "7" true
      (target := "A") (firstB := "7") (declaringGroup := ["Form", "Rows", "Body"]) == some "cleared" &&
    computation (ruleGroupCondition "GroupNotFilled" "/Form/Key" alias) "R1" "7"
      (target := "A") (declaringGroup := ["Form", "Rows", "Body"]) == none) = true := by native_decide

example : [false, true].all (fun alias =>
    validation (ruleGroupCondition "GroupFilled" "/Form/Key" alias) "missing" "7"
      (declaringGroup := ["Form", "Rows", "Body"]) == some .notFired &&
    validation (ruleGroupCondition "GroupFilled" "/Form/Key" alias) "R1" "7" true
      (declaringGroup := ["Form", "Rows", "Body"]) == some .unknown &&
    validation (ruleGroupCondition "GroupFilled" "/Form/Key" alias) "R1" "7" false "bad"
      (declaringGroup := ["Form", "Rows", "Body"]) == some (.fired .value) &&
    computation (ruleGroupCondition "GroupFilled" "/Form/Key" alias) "R1" "7" false "bad"
      (target := "A") (firstB := "7") (declaringGroup := ["Form", "Rows", "Body"]) == some "cleared" &&
    validation (ruleGroupCondition "NumberOfFilledFields" "/Form/Key" alias ++ " == 1") "R1" "7"
      (declaringGroup := ["Form", "Rows", "Body"]) == some (.fired .omission) &&
    computation (ruleGroupCondition "GroupFilled" "/Form/Key" alias) "R1" "7"
      (target := "../../Out") (declaringGroup := ["Form", "Rows", "Body"]) == some "value 1") = true := by native_decide

example : validation "GroupFilled(RuleGroup For \"R1\")" = none ∧
    computation "GroupFilled(RuleGroup For \"R1\")" = none ∧
    ["AllGroupsFilled", "NumberOfFilledGroups"].all (fun operator =>
      [false, true].all fun alias =>
        let expression := ruleGroupCondition operator "/Form/Key" alias ++
          (if operator == "NumberOfFilledGroups" then " > 0" else "")
        validation expression (declaringGroup := ["Form", "Rows", "Body"]) == none &&
        computation expression (target := "../../Out") (declaringGroup := ["Form", "Rows", "Body"]) == none) = true := by native_decide

example : [
    ("GroupNotFilled", "R1", "", "cleared"),
    ("GroupNotFilled", "missing", "", "value 1"),
    ("AllFieldsFilled", "R1", "", "cleared"),
    ("AllFieldsFilled", "R1", "7", "value 1"),
    ("NoFieldFilled", "R1", "", "cleared"),
    ("NoFieldFilled", "missing", "", "value 1"),
    ("NumberOfFilledFields", "R1", "", "value 1")].all (fun (operator, key, firstB, expected) =>
      [false, true].all fun alias =>
        let expression := ruleGroupCondition operator "/Form/Key" alias ++
          (if operator == "NumberOfFilledFields" then " > 0" else "")
        computation expression key "7" (target := "../../Out") (firstB := firstB)
          (declaringGroup := ["Form", "Rows", "Body"]) == some expected) = true ∧
    computation "AllGroupsFilled(RuleGroup For /Form/Key, /Form/Key)" "R1" "7"
      (target := "../../Out") (declaringGroup := ["Form", "Rows", "Body"]) = some "value 1" ∧
    computation "NumberOfFilledGroups(/Form/Rows*) > 0" "R1" "7"
      (target := "../../Out") (declaringGroup := ["Form", "Rows", "Body"]) = some "value 1" := by native_decide

end A12Kernel.Dm.IndexedGroupLocks
