import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Elaboration.GeneratedComputationValidation

namespace A12Kernel.Dm.TypeValidityGuardLocks

private def number (id : FieldId) (name : String) : FlatFieldDecl := {
  id, name, groupPath := ["G"], policy := { kind := .number { scale := 0, signed := true } } }

private def model : FlatModel := { fields := [
  { number 1 "S" with policy := { kind := .string }, stringPolicy := { maxLength := some 1 } },
  number 2 "Out", number 3 "After",
  { number 4 "Fresh" with policy := { kind := .string } }] }

private def world (registered : Bool) : World := {
  now := { epochMillis := 0 }
  customFieldValidator? := fun name =>
    if registered && name == "Code" then some (fun value context =>
      if value == "x" && context == explicitCustomFieldValidationContext then none
      else some { projectCode := "TYPE_REJECTED" }) else none }

private def run (guard value : String) (registered : Bool := false)
    (enumerated : Bool := false) (rows : Bool := false) (producer : Bool := false) : Option (List String) := do
  let model := if enumerated then { model with fields := model.fields.map fun field =>
    if field.id == 1 then { field with
      policy := { kind := .enumeration }
      stringPolicy := {}
      enumeration := some { storedTokens := ["x", "y"] } } else field } else model
  let model := if rows then { model with
    fields := model.fields.map fun field => if field.id <= 3 then
      { field with groupPath := ["G", "Rows"], repeatableScope := [10] } else field
    repeatableGroups := [{ level := 10, path := ["G", "Rows"], repeatability := some 2 }] } else model
  let world := world registered
  let dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm (Lean.Json.mkObj [("G", Lean.Json.mkObj [
    ("S", .str value), ("Out", .str "9"), ("After", .str "9"), ("Fresh", .str "y"),
    ("Rows", .arr #[Lean.Json.mkObj [("S", .str value), ("Out", .str "9"), ("After", .str "9")],
      Lean.Json.mkObj [("S", .str "y"), ("Out", .str "9"), ("After", .str "9")]])])])).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let definitions : List DmComputation := [
    { name := "Dependent", group := ["G"], targetRelPath := if rows then "../Rows/After" else "../After", commonPrecondition := none
      alternatives := [{ precondition := none, operation := if rows then "[Rows/Out] + 1" else "[Out] + 1" }], errorCodesToSuppress := [] },
    { name := "Consumer", group := ["G"], targetRelPath := if rows then "../Rows/Out" else "../Out", commonPrecondition := some guard
      alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] }]
  let definitions := definitions ++ if producer then [{
    name := "Producer", group := ["G"], targetRelPath := "../Rows/S", commonPrecondition := none
    alternatives := [{ precondition := none, operation := "[Fresh]" }], errorCodesToSuppress := [] }] else []
  let lowered : List (FlatFieldDecl × LoweredComputation model) ← definitions.mapM fun definition => (lowerComputation model .english definition).toOption
  pure ((← (runComputations world prepared checked (lowered.map (·.2))).toOption).map (·.outcome))

example : ["Valid", "Invalid"].all (fun op =>
    run s!"{op}(S, \"Code\")" "x" == some ["cleared", "cleared"] &&
    run s!"{op}(S, \"Code\")" "" == some ["cleared", "value 1"] &&
    run s!"{op}(S, \"Code\")" "long" == some ["cleared", "cleared"]) = true := by native_decide

example : run "Valid(S, \"Code\")" "x" true = some ["value 1", "value 2"] ∧
    run "Invalid(S, \"Code\")" "x" true = some ["cleared", "value 1"] ∧
    run "Valid(S, \"Code\")" "y" true = some ["cleared", "value 1"] ∧
    run "Invalid(S, \"Code\")" "y" true = some ["value 1", "value 2"] := by native_decide

example : run "FieldFilled(S) Or Valid(S, \"Code\")" "x" = some ["value 1", "value 2"] ∧
    run "FieldNotFilled(S) And Invalid(S, \"Code\")" "x" = some ["cleared", "value 1"] ∧
    run "Valid(S, \"\")" "x" = none ∧
    run "Valid(Out, \"Code\")" "x" = none := by native_decide

example : run "Valid(S, \"Code\")" "x" true true = some ["value 1", "value 2"] ∧
    run "Invalid(S, \"Code\")" "y" true true = some ["value 1", "value 2"] ∧
    run "Valid(Rows/S, \"Code\")" "x" true false true =
      some ["value 1", "cleared", "value 2", "value 1"] ∧
    run "Invalid(Rows/S, \"Code\")" "x" true false true true =
      some ["value y", "value 1", "value 1", "value 2", "value 2"] := by native_decide

private def generatedPhase (operation : String) (registered : Bool)
    (enumerated : Bool := false) : Option (Bool × Bool) := do
  let shouldHold := operation == "Invalid"
  let model := if enumerated then { model with fields := model.fields.map fun field =>
    if field.id == 1 then { field with
      policy := { kind := .enumeration }
      stringPolicy := {}
      enumeration := some { storedTokens := ["x", "y"] } } else field } else model
  let parsed ← (parseText .english s!"{operation}(S, \"Code\")").toOption
  let surface ← (lowerGuard model ["G"] false parsed.body (some ["G"])).toOption
  let guard ← (model.elaborateCheckedComputationCondition ["G"] ["G"] surface).toOption
  let operation ← (elaborateCompleteNumericComputationOperation model ["G"] 2
    (.literal { value := 1, authoredScale := 0 }) false).toOption
  let table : GeneratedComputationTable (CheckedNumericComputationOperation model) (CheckedComputationCondition model) := {
    targetField := 2, name := "Computed", commonPrecondition := some guard
    alternatives := .singleton { operation }, messagePlan := { parts := [.text "type result"] } }
  let requiresWorld := match assembleGeneratedNumericOperationTableRule model table with
    | .error .typeValidityRequiresWorld => true
    | _ => false
  let world := world registered
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let input ← (readDocument {
      flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
    (Lean.Json.mkObj [("G", Lean.Json.mkObj [("S", "y"), ("Out", "9")])])).toOption
  let document ← (checkDocument prepared "en_US" input.data).toOption
  let agrees := fun actual => match actual with
    | .error (.operation .guardValueFailure) => !registered
    | .ok value => registered && value ==
        (if shouldHold then .supported (.accepted { unscaled := 1, scale := 0 })
         else .supported .noValue)
    | _ => false
  let routedScalar := agrees (table.evaluateNumericTarget (document.scalarComputationContext world))
  let routedDocument := agrees ((table.executeNumericTargetResult world document).map (·.targetCheck))
  let rule ← (assembleGeneratedNumericOperationTableRule model table (some world)).toOption
  let outcome ← (rule.evalAddressedFull {
    scalar := { fields := document.flatContext.withWorld world, groups := GroupPresenceContext.unavailable }
    outer := [], input := .checked document } true).toOption
  pure (requiresWorld && routedScalar && routedDocument, match outcome with | .fired _ => true | _ => false)

example : generatedPhase "Valid" false = some (true, true) ∧
    generatedPhase "Invalid" false = some (true, true) ∧
    generatedPhase "Valid" true = some (true, false) ∧
    generatedPhase "Invalid" true = some (true, true) ∧
    generatedPhase "Invalid" true true = some (true, true) ∧
    generatedPhase "Valid" false true = some (true, true) := by native_decide

end A12Kernel.Dm.TypeValidityGuardLocks
