import A12Kernel.Elaboration.GeneratedComputationValidation.Assembly
import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.LowerValidation

namespace A12Kernel.Dm.SemanticIndexLocks

private def number (id : FieldId) (name : String) : FlatFieldDecl := {
  id, name, groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } }

private def model : FlatModel := {
  fields := [number 1 "A", number 2 "Out", number 3 "Key",
    { number 4 "Id" with groupPath := ["Form", "Rows"], repeatableScope := [10] },
    { number 5 "N" with groupPath := ["Form", "Rows"], repeatableScope := [10] },
    { number 6 "Out" with groupPath := ["Form", "Rows"], repeatableScope := [10] }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3, indexField := some 4 }] }

private def modelFor (textIndex : Bool) (stringTarget : Bool := false) : FlatModel :=
  { model with fields := model.fields.map fun field =>
    if (textIndex && (field.id == 3 || field.id == 4)) || (stringTarget && (field.id == 2 || field.id == 6))
    then { field with policy := { kind := .string } } else field }

private def operators := ["AllFieldsFilled", "NoFieldFilled", "AtLeastOneFieldFilled",
  "MoreThanOneFieldFilled", "NotAllFieldsFilled", "NotExactlyOneFieldFilled", "FieldsNotCollectivelyFilled"]

private def input (rows : List (String × String)) (a key : String) (textIndex : Bool := false) (stringTarget : Bool := false) :
    Option (CheckedDocument (modelFor textIndex stringTarget)) := do
  let model := modelFor textIndex stringTarget
  let dm : DmModel := { flat := model, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }
  let data := Lean.Json.mkObj [("Form", Lean.Json.mkObj [
    ("A", .str a), ("Out", .str "99"), ("Key", .str key),
    ("Rows", .arr (rows.map fun (id,n) => Lean.Json.mkObj [("Id", .str id), ("N", .str n)]).toArray)])]
  let input ← (readDocument dm data).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" input.data).toOption

private def validation (operator operands : String) (rows : List (String × String))
    (a : String := "1") (key : String := "1") (textIndex : Bool := false) : Option Verdict := do
  let model := modelFor textIndex
  let checked ← input rows a key textIndex
  let parsed ← (parseText .english (operator ++ "(" ++ operands ++ ")")).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
  (condition.core.evalAddressed {
    scalar := { fields := checked.flatContext, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked checked }).toOption

private def computation (operator operands : String) (rows : List (String × String))
    (a : String := "1") (key : String := "1") (fallback : Bool := false)
    (producer : Option String := none) (textIndex : Bool := false) (stringTarget : Bool := false) (expression : Option String := none) (rowTarget : Bool := false) : Option String := do
  let model := modelFor textIndex stringTarget
  let checked ← input rows a key textIndex stringTarget
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let operation := expression.getD (if stringTarget then "\"x\"" else "1")
  let fallbackOperation := if stringTarget then "\"y\"" else "2"
  let definition : DmComputation := {
    name := "Consumer", group := ["Form"], targetRelPath := if rowTarget then "../Rows/Out" else "../Out",
    commonPrecondition := if fallback then none else some (operator ++ "(" ++ operands ++ ")"),
    alternatives := if fallback then [
      { precondition := some (operator ++ "(" ++ operands ++ ")"), operation },
      { precondition := some "FieldFilled(A)", operation := fallbackOperation }]
      else [{ precondition := none, operation }], errorCodesToSuppress := [] }
  let lowered ← (lowerComputation model .english definition).toOption
  let producers ← producer.toList.mapM fun target =>
    (lowerComputation model .english {
      name := "Producer", group := ["Form"], targetRelPath := "../" ++ target,
      commonPrecondition := none, alternatives := [{ precondition := none, operation := "2" }],
      errorCodesToSuppress := [] }).toOption
  let results ← (runComputations world prepared checked (lowered.2 :: producers.map (·.2))).toOption
  let results := results.filter (·.pointer.endsWith "/Out")
  if rowTarget then pure (",".intercalate (results.map (·.outcome)))
  else (results.head?).map (·.outcome)

private def validationTruthSignature (rows : List (String × String)) (a : String := "1") : Option String := do
  let verdicts ← operators.mapM fun operator => validation operator "Rows/N For Key,A" rows a
  pure (String.ofList (verdicts.map fun
    | .fired _ => 'T'
    | .notFired | .unknown => 'F'))

private def computationSignature (rows : List (String × String)) (a : String := "1") : Option String := do
  let outcomes ← operators.mapM fun operator => computation operator "Rows/N For Key,A" rows a
  pure (String.ofList (outcomes.map fun outcome => if outcome == "value 1" then 'T' else 'F'))

example : validationTruthSignature [("1", "7")] = some "TFTTFTF" ∧
    computationSignature [("1", "7")] = some "TFTTFTF" ∧
    validationTruthSignature [("2", "7")] = some "FFTFTFT" ∧
    computationSignature [("2", "7")] = some "FFTFTFT" ∧
    validationTruthSignature [("2", "7")] "" = some "FTFFTTF" ∧
    computationSignature [("2", "7")] "" = some "FTFFTTF" := by native_decide

example : validation "AllFieldsFilled" "Rows/N For Key,A" [("1", "7"), ("bad", "9")] = some (.fired .value) ∧
    computation "AllFieldsFilled" "Rows/N For Key,A" [("1", "7"), ("bad", "9")] = some "cleared" ∧
    computation "AtLeastOneFieldFilled" "A,Rows/N For Key" [("1", "7"), ("bad", "9")] = some "value 1" := by native_decide

example : validation "AllFieldsFilled" "Rows/N For Key,A" [("1", "7"), ("1", "9")] = some .unknown ∧
    validation "AtLeastOneFieldFilled" "Rows/N For Key,A" [("1", "bad")] = some (.fired .value) ∧
    validation "AllFieldsFilled" "Rows/N For Key,A" [("1", "7")] "1" "bad" = some .unknown ∧
    computation "AtLeastOneFieldFilled" "Rows/N For Key,A" [("1", "7")] "1" "bad" = some "cleared" := by native_decide


example : computation "AllFieldsFilled" "Rows/N For Key,A" [("2", "7")] "1" "1" true = some "value 2" ∧
    computation "AllFieldsFilled" "Rows/N For Key,A" [("1", "bad")] "1" "1" true = some "cleared" ∧
    computation "AllFieldsFilled" "Rows/N For Key,A" [("2", "7")] "1" "bad" false (some "Key") = some "value 1" ∧
    computation "AllFieldsFilled" "Rows/N For Key,A" [("1", "bad")] "1" "1" false (some "Rows/N") = some "value 1" := by native_decide

example : validation "AllFieldsFilled" "Rows/N For \"01\",A" [("1", "7")] = some (.fired .value) ∧
    computation "AllFieldsFilled" "Rows/N For \"01\",A" [("1", "7")] = some "value 1" := by native_decide

example : validation "AllFieldsFilled" "Rows/N For Key,A" [("01", "7")] "1" "1" true = some .unknown ∧
    validation "AllFieldsFilled" "Rows/N For Key,A" [("01", "7")] "1" "01" true = some (.fired .value) ∧
    computation "AllFieldsFilled" "Rows/N For Key,A" [("01", "7")] "1" "1" true none true = some "value 2" ∧
    computation "AllFieldsFilled" "Rows/N For Key,A" [("01", "7")] "1" "01" true none true = some "value 1" := by native_decide

example : computation "AllFieldsFilled" "Rows/N For Key,A" [("1", "7")] "1" "1" false none false true = some "value x" ∧
    computation "AllFieldsFilled" "Rows/N For Key,A" [("1", "bad")] "1" "1" true none false true = some "cleared" := by native_decide

private def numericValidation (expression : String) (rows : List (String × String))
    (key : String := "1") : Option Verdict := do
  let checked ← input rows "1" key
  let parsed ← (parseText .english expression).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
  (condition.core.evalAddressed {
    scalar := { fields := checked.flatContext, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked checked }).toOption

private def numericComputation (expression : String) (rows : List (String × String))
    (key : String := "1") (producer : Option String := none) : Option String :=
  computation "AtLeastOneFieldFilled" "A,Key" rows "1" key false producer false false (some expression)

example : numericValidation "[Rows/N For Key] + 1 == 8" [("1", "7")] = some (.fired .value) ∧
    numericComputation "[Rows/N For Key] + 1" [("1", "7")] = some "value 8" ∧
    numericValidation "[Rows/N For Key] + 1 == 1" [("2", "7")] = some (.fired .omission) ∧
    numericComputation "[Rows/N For Key] + 1" [("2", "7")] = some "value 1" := by native_decide

example : numericValidation "[Rows/N For Key] == 7" [("1", "7"), ("bad", "9")] = some (.fired .value) ∧
    numericComputation "[Rows/N For Key]" [("1", "7"), ("bad", "9")] = some "cleared" ∧
    numericComputation "[Rows/N For Key]" [("1", "bad")] = some "cleared" ∧
    numericComputation "[Rows/N For Key]" [("1", "7")] "bad" = some "cleared" ∧
    numericComputation "[Rows/N For Key]" [("2", "7")] "bad" (some "Key") = some "value 7" ∧
    numericComputation "[Rows/N For Key]" [("1", "bad")] "1" (some "Rows/N") = some "value 2" := by native_decide

example : numericComputation "[Rows/N For Out]" [("1", "7")] = none ∧
    numericComputation "[Rows/N For Rows/Id]" [("1", "7")] = none ∧
    numericComputation "[Rows/N For \"bad\"]" [("1", "7")] = none := by native_decide

private def generatedNumeric (rows : List (String × String)) : Option Verdict := do
  let checked ← input rows "1" "1"
  let lowered ← (lowerComputation model .english {
    name := "Consumer", group := ["Form"], targetRelPath := "../Out", commonPrecondition := none,
    alternatives := [{ precondition := none, operation := "[Rows/N For Key] + 1" }],
    errorCodesToSuppress := [] }).toOption
  let .number table _ := lowered.2 | none
  let rule ← (assembleGeneratedNumericOperationRule model table.first.operation.operation
    "Computed" none { parts := [] }).toOption
  let outcome ← (rule.evalAddressedFull {
    scalar := { fields := checked.flatContext, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked checked } true).toOption
  pure outcome.verdict

example : generatedNumeric [("1", "7")] = some (.fired .value) ∧
    generatedNumeric [("1", "bad")] = some .unknown := by native_decide

example : validation "FieldFilled" "Rows/N For Key" [("1", "7")] = some (.fired .value) ∧
    validation "FieldNotFilled" "Rows/N For Key" [("2", "7")] = some (.fired .omission) ∧
    validation "FieldNotFilled" "Rows/N For Key" [("1", "bad")] = some .unknown ∧
    computation "FieldFilled" "Rows/N For Key" [("1", "7")] = some "value 1" ∧
    computation "FieldNotFilled" "Rows/N For Key" [("2", "7")] = some "value 1" ∧
    computation "FieldNotFilled" "Rows/N For Key" [("1", "bad")] "1" "1" true = some "cleared" := by native_decide

private def classification (operator : String) : Option Bool := do
  let parsed ← (parseText .english (operator ++ "(Rows/N For Key)")).toOption
  let condition ← (lowerCondition model ["Form"] false parsed.body).toOption
  pure (condition.core.anyLeaf ValidationConditionLeaf.requiresClassificationPass)

example : classification "FieldFilled" = some false ∧
    classification "FieldNotFilled" = some true := by native_decide

example : computation "FieldFilled" "Rows/N For Key" [("1", "7"), ("2", "9")]
      "1" "1" false none false false (some "[Rows/N For Key] + 1") true = some "value 8,value 8" ∧
    computation "FieldFilled" "Rows/N For Key" [("1", "7"), ("2", "9")]
      "1" "1" false none false true none true = some "value x,value x" := by native_decide

end A12Kernel.Dm.SemanticIndexLocks
