import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Parser
import A12Kernel.Reference.Dm.ParallelValidation
import A12Kernel.Reference.Dm.Validate

namespace A12Kernel.Dm.NumericFieldFormLocks

private def model : FlatModel := {
  fields := [
    { id := 1, name := "N", groupPath := ["Form"], policy := { kind := .number { scale := 2, signed := true } } },
    { id := 2, name := "Rounded", groupPath := ["Form"], policy := { kind := .number { scale := 0, signed := true } } },
    { id := 3, name := "Absolute", groupPath := ["Form"], policy := { kind := .number { scale := 2, signed := true } } },
    { id := 4, name := "Text", groupPath := ["Form"], policy := { kind := .string } },
    { id := 5, name := "N", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .number { scale := 2, signed := true } } },
    { id := 6, name := "Rounded", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 7, name := "Absolute", groupPath := ["Form", "Rows"], repeatableScope := [10],
      policy := { kind := .number { scale := 2, signed := true } } }]
  repeatableGroups := [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 }] }

private def admitted (text : String) (group : GroupPath := ["Form"]) : Bool :=
  match parseText .english text with
  | .ok parsed => (lowerCondition model group false parsed.body).isOk
  | .error _ => false

private def run (operation input : String) (repeated : Bool := false) : Option (List String) := do
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let row := Lean.Json.mkObj [("N", .str input), ("Rounded", .str "9"), ("Absolute", .str "9")]
  let content := if repeated then Lean.Json.mkObj [("Rows", .arr #[row])] else row
  let document ← (readDocument dm (Lean.Json.mkObj [("Form", content)])).toOption
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" document.data).toOption
  let target := if operation.startsWith "AbsValue" then "Absolute" else "Rounded"
  let (_, step) ← (lowerComputation model .english {
    group := if repeated then ["Form", "Rows"] else ["Form"], name := "Compute", targetRelPath := "../" ++ target, commonPrecondition := none
    alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }).toOption
  pure ((← (runComputations world prepared checked [step]).toOption).map (·.outcome))

/-- KF393 and KF395 distinguish field syntax from operation syntax; arithmetic reuses spec/04. -/
example : ["RoundDownValue", "RoundUpValue", "RoundAccountingValue", "AbsValue"].all
    (fun op => admitted (op ++ "(N) > 0") && admitted (op ++ "(/Form/Rows/N) > 0") ["Form", "Rows"]) := by
  native_decide

example : run "RoundDownValue(N)" "-1.5" = some ["value -2"] ∧
    run "RoundUpValue(N)" "-1.5" = some ["value -1"] ∧
    run "RoundAccountingValue(N)" "-1.5" = some ["value -2"] ∧
    run "AbsValue(N)" "-1.5" = some ["value 1.5"] := by native_decide

example : ["RoundDownValue", "RoundUpValue", "RoundAccountingValue", "AbsValue"].all
    (fun op => run (op ++ "(N)") "" == some ["value 0"] &&
      run (op ++ "(N)") "bad" == some ["cleared"]) := by native_decide

private def refused (operation : String) : Option String :=
  match parseText .english operation with
  | .error error => some error.errorClass.code
  | .ok parsed => match lowerNumericExpr lowerValidationNumericAtom
      (lowerNumericFieldAtom model ["Form"] lowerValidationNumericAtom) parsed.body with
      | .ok _ => none
      | .error error => some error.detail

/-- The class a rule reporting on `N` draws for `operation > 0`. -/
private def ruleClass (operation : String) : Option String :=
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let condition := s!"FieldFilled(N) And {operation} > 0"
  let rule : DmRule := { group := ["Form"], name := "P", errorCode := "P", errorEntityRelPath := "../N", condition, severity := "ERROR" }
  match checkValidationRule dm .english rule with
  | .ok _ => none
  | .error refusal => refusal.kernelClass?

/-- KF393/KF395's source gates are shared by the entire field-form family; a group's class is the
rule's, after the operand's read. -/
example : ["RoundDownValue", "RoundUpValue", "RoundAccountingValue", "AbsValue"].all (fun op =>
    refused (op ++ "([N])") == some "MVK_UNEXPECTED_TOKEN" &&
    ruleClass (op ++ "(/Form)") == some "MVK_NO_GROUPS_ALLOWED" &&
    ruleClass (op ++ "(Rows*)") == some "MVK_NO_GROUPS_ALLOWED" &&
    refused (op ++ "(Rows*/N)") == some "MVK_NO_WILDCARDS_ALLOWED" &&
    refused (op ++ "(N->Code)") == some "MVK_CATEGORY_NOT_ALLOWED" &&
    refused (op ++ "(Text)") == some "MVK_NO_NUMBER" &&
    refused (op ++ "(Rows*/N->Code)") == some "MVK_NO_WILDCARDS_ALLOWED" &&
    refused (op ++ "(Text->Code)") == some "MVK_CATEGORY_NOT_ALLOWED") := by native_decide

/-- GrammarOnly rundenOp/feldOp reject argument shape before their checker runs. -/
example : refused "AbsValue(Text, 0)" = some "MVK_UNEXPECTED_TOKEN" ∧
    refused "RoundUpValue(Text, -1)" = some "MVK_UNEXPECTED_TOKEN" ∧
    refused "RoundUpValue()" = some "MVK_UNEXPECTED_TOKEN" := by native_decide

/-- KF393/KF448 separate source refusal, ordinary precision refusal and overflow. -/
example : ["RoundDownValue", "RoundUpValue", "RoundAccountingValue"].all (fun op =>
    (List.range 15).all (fun places => admitted (op ++ "(N, " ++ toString places ++ ") > 0")) &&
    refused (op ++ "(Text, 99)") == some "MVK_NO_NUMBER" &&
    refused (op ++ "(N, 15)") == some "MVK_INVALID_DIGIT_FOR_ROUNDING" &&
    refused (op ++ "(N, 9223372036854775807)") == some "MVK_INVALID_DIGIT_FOR_ROUNDING" &&
    refused (op ++ "(N, 9223372036854775808)") == some "MVK_INTERNAL_ERROR") := by native_decide

example : ["AbrundenWert", "AufrundenWert", "RundenWert", "AbsWert"].all (fun op =>
    match parseText .german (op ++ "(N) > 0") with
    | .ok parsed => (lowerCondition model ["Form"] false parsed.body).isOk
    | .error _ => false) := by native_decide

/-- Row binding must reach the same checked arithmetic, including empty substitution and poison. -/
example : ["RoundDownValue", "RoundUpValue", "RoundAccountingValue", "AbsValue"].all
    (fun op => ["-1.5", "", "bad"].all (fun input =>
      (run (op ++ "(N)") input true).isSome &&
      run (op ++ "(N)") input true == run (op ++ "(N)") input)) := by native_decide

example : admitted "AbsValue(N) + RoundUpValue(N) > 0" ∧
    admitted "RoundDown(AbsValue(N), 1) > 0" ∧
    !admitted "RoundDownValue(AbsValue(N)) > 0" := by native_decide

end A12Kernel.Dm.NumericFieldFormLocks
