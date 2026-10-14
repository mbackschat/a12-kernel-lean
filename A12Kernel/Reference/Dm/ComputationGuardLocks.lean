import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Parser
import A12Kernel.Reference.Dm.Replay

/-! # Computation guard context locks

The checked guard needs the current addressed overlay on both mixed scheduled runs and standalone
run policies; rebuilding only its scalar read loses the expanded field-fill operands.
-/

namespace A12Kernel.Dm.ComputationGuardLocks

open A12Kernel A12Kernel.Dm

private def fillGuardFreshRun (repeated : Bool) (stringTarget : Bool := false)
    (legacy : Bool := false) : Option (List String) := do
  let group := if repeated then ["Form", "Rows"] else ["Form", "Inputs"]
  let model : FlatModel := {
    fields := [
      { id := 1, groupPath := group, name := "Value", policy := { kind := .number { scale := 0, signed := true } }
        repeatableScope := if repeated then [10] else [] },
      { id := 2, groupPath := ["Form"], name := "Out", policy := {
        kind := if stringTarget then .string else .number { scale := 0, signed := true } } }]
    repeatableGroups := if repeated then [{ level := 10, path := group, repeatability := some 2 }] else [] }
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let input : DocumentData := {
    instantiatedRows := if repeated then [{ group := 10, path := [1] }, { group := 10, path := [2] }] else []
    cells := (if repeated then [[1], [2]] else [[]]).map fun path =>
      { address := { field := 1, path }, stored := if legacy then "1" else "bad"
        raw := if legacy then .parsed (.num 1) else .rejected .malformed } }
  let checked ← (checkDocument prepared "en_US" input).toOption
  let producer : DmComputation := {
    group := ["Form"], name := "Producer", targetRelPath := if repeated then "../Rows/Value" else "../Inputs/Value"
    commonPrecondition := none, alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] }
  let consumer : DmComputation := {
    group := ["Form"], name := "Consumer", targetRelPath := "../Out"
    commonPrecondition := some (if repeated then "AllFieldsFilled(Rows*)" else "AllFieldsFilled(Inputs)")
    alternatives := [{ precondition := none, operation := if stringTarget then "\"fresh\"" else "2" }], errorCodesToSuppress := [] }
  let guardText := consumer.commonPrecondition.getD ""
  let (_, producer) ← (lowerComputation model .english producer).toOption
  let (_, consumer) ← (lowerComputation model .english consumer).toOption
  if legacy then
    let parsed ← (parseText .english guardText).toOption
    let surface ← (lowerGuard model ["Form"] false parsed.body).toOption
    let guard ← (model.elaborateCheckedComputationCondition ["Form"] ["Form"] surface).toOption
    let context ← match consumer with
      | .number table _ => do
          let run ← (certifyNumericComputationRun [table]).toOption
          pure (run.readPolicy {} checked)
      | .string table => do
          let run ← (certifyStringComputationRun [table]).toOption
          pure (run.readPolicy {} checked)
      | _ => none
    return if (guard.evalChecked context).toOption == some .holds then ["holds"] else ["other"]
  let outcomes ← (runComputations world prepared checked [consumer, producer]).toOption
  pure (outcomes.map (·.outcome))

example : fillGuardFreshRun false = some ["value 1", "value 2"] ∧
    fillGuardFreshRun true = some ["value 1", "value 1", "value 2"] := by native_decide

example : fillGuardFreshRun false true = some ["value 1", "value fresh"] := by native_decide
example : fillGuardFreshRun true true = some ["value 1", "value 1", "value fresh"] := by native_decide
example : fillGuardFreshRun true false true = some ["holds"] := by native_decide
example : fillGuardFreshRun true true true = some ["holds"] := by native_decide


private def refusedTargetIdentity (target : FieldId) : Bool :=
  let model : FlatModel := { fields := [
    { id := 1, groupPath := ["Form"], name := "Y", policy := { kind := .number { scale := 0, signed := true } } },
    { id := 2, groupPath := ["Form", "Other"], name := "Y", policy := { kind := .number { scale := 0, signed := true } } }] }
  let refused : DmComputation := {
    group := ["Form", "Other"], name := "Refused", targetRelPath := "../../Y"
    commonPrecondition := none, alternatives := [], errorCodesToSuppress := [] }
  hasRefusedComputationTarget .english model [refused] target

example : refusedTargetIdentity 1 = true ∧ refusedTargetIdentity 2 = false := by native_decide

private inductive GroupGuardKind where
  | number | string | boolean

private inductive GroupGuardShape where
  | paired | bypass | ordinaryCycle | splitGuardFirst | splitPlainFirst | unconditionalProducer

private inductive GroupGuardResult where
  | cycle
  | outcomes (values : List String)
  deriving Repr, DecidableEq

private def groupGuardRun (seed : Bool) (kind : GroupGuardKind := .number)
    (shape : GroupGuardShape := .paired) : Option GroupGuardResult := do
  let model : FlatModel := { fields := [
    { id := 1, groupPath := ["Form"], name := "Gate", policy := { kind := .number { scale := 0, signed := true } } },
    { id := 2, groupPath := ["Form"], name := "X", policy := { kind := .number { scale := 0, signed := true } } },
    { id := 3, groupPath := ["Form"], name := "Y", policy := { kind := match kind with
      | .number => .number { scale := 0, signed := true } | .string => .string | .boolean => .boolean } }] }
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := [{ address := { field := 2, path := [] }, stored := "bad", raw := .rejected .malformed }] ++
      (if seed then [{ address := { field := 1, path := [] }, stored := "3", raw := .parsed (.num 3) }] else []) }).toOption
  let condition := match shape with
    | .bypass => "GroupFilled(/Form) Or FieldFilled(Gate)"
    | _ => "GroupFilled(/Form)"
  let first : DmComputation := {
    group := ["Form"], name := "First", targetRelPath := "../X", commonPrecondition := some condition
    alternatives := [{ precondition := none, operation := match shape with | .ordinaryCycle => "[Y]" | _ => "1" }]
    errorCodesToSuppress := [] }
  let second : DmComputation := {
    group := ["Form"], name := "Second", targetRelPath := "../Y"
    commonPrecondition := match shape with | .unconditionalProducer => none | _ => some condition
    alternatives := [{ precondition := none, operation := match kind, shape with
      | .number, .ordinaryCycle | .number, .splitGuardFirst | .number, .splitPlainFirst => "[X]"
      | .number, _ => "2" | .string, _ => "\"ready\"" | .boolean, _ => "True" }]
    errorCodesToSuppress := [] }
  let plain : DmComputation := { second with
    commonPrecondition := none
    alternatives := [{ precondition := none, operation := match kind with
      | .number => "2" | .string => "\"fallback\"" | .boolean => "False" }] }
  let authored := match shape with
    | .splitGuardFirst => [first, second, plain]
    | .splitPlainFirst => [plain, first, second]
    | _ => [first, second]
  let lowered ← authored.mapM fun computation => (lowerComputation model .english computation).toOption
  let steps := lowered.map (·.2.toMixedStep builtinStringPatternCompiler)
  match certifyAuthoredMixedComputationPlan steps with
  | .error (.cycle _ _) => pure .cycle
  | .error _ => none
  | .ok _ =>
      let outcomes ← (runComputations world prepared checked (lowered.map (·.2))).toOption
      pure (.outcomes (outcomes.map (·.outcome)))

example : groupGuardRun false = some (.outcomes ["cleared"]) ∧
    groupGuardRun true = some (.outcomes ["value 1", "value 2"]) := by native_decide
example : groupGuardRun true .string = some (.outcomes ["value 1", "value ready"]) ∧
    groupGuardRun true .boolean = some (.outcomes ["value 1", "value true"]) := by native_decide
example : groupGuardRun false .number .bypass = some .cycle ∧
    groupGuardRun false .number .ordinaryCycle = some .cycle := by native_decide
example : groupGuardRun false .number .unconditionalProducer =
    some (.outcomes ["value 2", "value 1"]) := by native_decide
example : groupGuardRun false .number .splitGuardFirst = some (.outcomes ["cleared", "value 2"]) ∧
    groupGuardRun false .number .splitPlainFirst = some (.outcomes ["cleared", "value 2"]) ∧
    groupGuardRun true .number .splitGuardFirst = some (.outcomes ["value 1", "value 1"]) ∧
    groupGuardRun true .number .splitPlainFirst = some (.outcomes ["value 1", "value 2"]) := by native_decide
example : groupGuardRun true .string .splitGuardFirst = some (.outcomes ["value 1", "value ready"]) ∧
    groupGuardRun true .string .splitPlainFirst = some (.outcomes ["value fallback", "value 1"]) := by native_decide

private def standaloneGroupPlans (stringTargets : Bool) : Option Bool := do
  let kind := if stringTargets then FieldKind.string else .number { scale := 0, signed := true }
  let model : FlatModel := { fields := [
    { id := 1, groupPath := ["Form"], name := "X", policy := { kind } },
    { id := 2, groupPath := ["Form"], name := "Y", policy := { kind } }] }
  let definition (name : String) : DmComputation := {
    group := ["Form"], name, targetRelPath := "../" ++ name
    commonPrecondition := some "GroupFilled(/Form)"
    alternatives := [{ precondition := none, operation := if stringTargets then "\"ready\"" else "1" }]
    errorCodesToSuppress := [] }
  let (_, first) ← (lowerComputation model .english (definition "X")).toOption
  let (_, second) ← (lowerComputation model .english (definition "Y")).toOption
  match first, second with
  | .number first _, .number second _ => pure (
      (certifyNumericComputationRun [first, second]).isOk &&
      (certifyRepeatableNumberPlan [first, second]).isOk &&
      (certifyScalarComputationPlan [.number first, .number second]).isOk)
  | .string first, .string second => pure (
      (certifyStringComputationRun [first, second]).isOk &&
      (certifyScalarComputationPlan [.string first, .string second]).isOk)
  | _, _ => none

example : standaloneGroupPlans false = some true ∧ standaloneGroupPlans true = some true := by native_decide

private inductive RepeatableProfileShape where
  | child | rows | common | fixed
  deriving BEq

private def repeatableProfilePlan (shape : RepeatableProfileShape) (plainFirst : Bool) :
    Option Bool := do
  let repeated := shape != .fixed
  let scope := if repeated then [10] else []
  let group := ["Form", "Rows", "Box"]
  let model : FlatModel := {
    fields := [
    { id := 1, groupPath := group, name := "Gate", repeatableScope := scope,
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 2, groupPath := group, name := "X", repeatableScope := scope,
      policy := { kind := .number { scale := 0, signed := true } } },
    { id := 3, groupPath := group, name := "Y", repeatableScope := scope,
      policy := { kind := .number { scale := 0, signed := true } } }]
    repeatableGroups := if repeated then
      [{ level := 10, path := ["Form", "Rows"], repeatability := some 3 }] else [] }
  let definition (name target operation : String) (guard : Option String)
      (common : Bool := false) : DmComputation := {
    group, name, targetRelPath := "../" ++ target
    commonPrecondition := if common then guard else none
    alternatives := [{ precondition := if common then none else guard, operation }]
    errorCodesToSuppress := [] }
  let first := definition "XComp" "X" "1" (some (if shape == .rows then
    "GroupFilled(/Form/Rows)" else "GroupFilled(/Form/Rows/Box)"))
  let guarded := definition "YGuard" "Y" "[/Form/Rows/Box/X]" (some "GroupFilled(/Form/Rows/Box)")
  let plain := definition "YPlain" "Y" "2"
    (if shape == .common then some "GroupFilled(/Form/Rows/Box)" else none) true
  let authored := first :: (if plainFirst then [plain, guarded] else [guarded, plain])
  let steps ← authored.mapM fun computation => do
    let (_, lowered) ← (lowerComputation model .english computation).toOption
    match lowered with
    | .number table _ => some (MixedComputationStep.number (compilePattern := builtinStringPatternCompiler) table)
    | _ => none
  match certifyAuthoredMixedComputationPlan steps with
  | .ok _ => some true
  | .error (.cycle _ _) => some false
  | .error _ => none

example : repeatableProfilePlan .child false = some false ∧
    repeatableProfilePlan .child true = some false := by native_decide

example : [RepeatableProfileShape.rows, .common, .fixed].all (fun shape =>
    repeatableProfilePlan shape false == some true &&
      repeatableProfilePlan shape true == some true) = true := by native_decide

private def standaloneGuardOverlay (stringTargets scalar stored filledList : Bool) :
    Option (Bool × Bool) := do
  let kind := if stringTargets then FieldKind.string else .number { scale := 0, signed := true }
  let model : FlatModel := { fields := [
    { id := 1, groupPath := ["Form"], name := "X", policy := { kind } },
    { id := 2, groupPath := if filledList then ["Form", "Inputs"] else ["Form"], name := "Y", policy := { kind } }] }
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := if stored then [{
      address := { field := if filledList then 2 else 1, path := [] }
      stored := if stringTargets then "old" else "9"
      raw := .parsed (if stringTargets then .str "old" else .num 9) }] else [] }).toOption
  let definition (name target : String) (guard : Option String) : DmComputation := {
    group := ["Form"], name, targetRelPath := "../" ++ target, commonPrecondition := guard
    alternatives := [{ precondition := none, operation := if stringTargets then "\"fresh\"" else "2" }]
    errorCodesToSuppress := [] }
  let (_, producer) ← (lowerComputation model .english
    (definition "Producer" (if filledList then "Inputs/Y" else "Y") none)).toOption
  let (_, consumer) ← (lowerComputation model .english
    (definition "Consumer" "X" (some (if filledList then "AllFieldsFilled(/Form/Inputs)" else "GroupFilled(/Form)")))).toOption
  let holds (guard : CheckedComputationCondition model) (context : ScalarComputationContext) :=
    (guard.evalChecked context).toOption == some .holds
  match producer, consumer with
  | .number producer _, .number consumer _ => do
      let guard ← consumer.first.precondition
      if scalar then
        let run ← (certifyScalarComputationRun [.number producer, .number consumer]).toOption
        let completed ← (run.evaluateStep world prepared.patterns checked {} (.number producer)).toOption
        pure (holds guard (run.numberContext world {} checked),
          holds guard (run.numberContext world { completed := [completed] } checked))
      else
        let run ← (certifyNumericComputationRun [producer, consumer]).toOption
        let completed ← (run.evaluateTable world checked {} producer).toOption
        pure (holds guard (run.readPolicy {} checked),
          holds guard (run.readPolicy { completed := [completed] } checked))
  | .string producer, .string consumer => do
      let guard ← consumer.first.precondition
      if scalar then
        let run ← (certifyScalarComputationRun [.string producer, .string consumer]).toOption
        let completed ← (run.evaluateStep world prepared.patterns checked {} (.string producer)).toOption
        pure (holds guard (run.stringContext {} checked),
          holds guard (run.stringContext { completed := [completed] } checked))
      else
        let run ← (certifyStringComputationRun [producer, consumer]).toOption
        let completed ← (run.evaluateTable prepared.patterns checked {} producer).toOption
        pure (holds guard (run.readPolicy {} checked),
          holds guard (run.readPolicy { completed := [completed] } checked))
  | _, _ => none

example : [false, true].all (fun strings => [false, true].all fun scalar =>
    [false, true].all fun stored => standaloneGuardOverlay strings scalar stored false == some (false, true)) = true := by
  native_decide

example : [false, true].all (fun strings => [false, true].all fun scalar =>
    [false, true].all fun stored => standaloneGuardOverlay strings scalar stored true == some (false, true)) = true := by
  native_decide

private def numericExpressionGuardRun (guard : String) (stringTarget : Bool)
    (produceA : Bool := false) : Option (List String) := do
  let number : FieldKind := .number { scale := 0, signed := true }
  let model : FlatModel := { fields := [
    { id := 1, groupPath := ["Form"], name := "A", policy := { kind := number } },
    { id := 2, groupPath := ["Form"], name := "B", policy := { kind := number } },
    { id := 3, groupPath := ["Form"], name := "Text", policy := { kind := .string }
      stringPatternSource := some "[0-9]+", stringPolicy := { maxLength := some 3 } },
    { id := 4, groupPath := ["Form"], name := "Out", policy := {
      kind := if stringTarget then .string else number } },
    { id := 5, groupPath := ["Form"], name := "After", policy := { kind := number } }] }
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := [
      { address := { field := 1, path := [] }, stored := "bad", raw := .rejected .malformed },
      { address := { field := 2, path := [] }, stored := "0", raw := .parsed (.num 0) },
      { address := { field := 3, path := [] }, stored := "bad", raw := .rejected .malformed },
      { address := { field := 4, path := [] }, stored := "9",
        raw := .parsed (if stringTarget then .str "9" else .num 9) },
      { address := { field := 5, path := [] }, stored := "9", raw := .parsed (.num 9) }] }).toOption
  let producer : DmComputation := {
    group := ["Form"], name := "Producer", targetRelPath := "../A"
    commonPrecondition := none, alternatives := [{ precondition := none, operation := "1" }]
    errorCodesToSuppress := [] }
  let consumer : DmComputation := {
    group := ["Form"], name := "Consumer", targetRelPath := "../Out"
    commonPrecondition := some guard
    alternatives := [{ precondition := none, operation := if stringTarget then "\"ready\"" else "2" }]
    errorCodesToSuppress := [] }
  let dependent : DmComputation := {
    group := ["Form"], name := "Dependent", targetRelPath := "../After"
    commonPrecondition := some "FieldFilled(Out) Or FieldNotFilled(Out)"
    alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] }
  let authored := [dependent, consumer] ++ if produceA then [producer] else []
  let lowered ← authored.mapM fun computation => (lowerComputation model .english computation).toOption
  let outcomes ← (runComputations world prepared checked (lowered.map (·.2))).toOption
  pure (outcomes.map (·.outcome))

-- The dependent separates clean non-selection from reached poison: either clears the guarded
-- target, but only poison clears its reader (spec/09 §1).
example : numericExpressionGuardRun "Sum(A,B) > 0" false true =
    some ["value 1", "value 2", "value 1"] ∧
    numericExpressionGuardRun "Sum(A,B) > 0" true true =
    some ["value 1", "value ready", "value 1"] := by native_decide

example : [false, true].all (fun strings =>
    numericExpressionGuardRun "FieldValueAsNumber(Text) > 0" strings ==
      some ["cleared", "cleared"]) = true := by native_decide

example : [false, true].all (fun strings =>
    numericExpressionGuardRun "NumberOfFilledFields(A,B) == 2" strings true ==
      some ["value 1", if strings then "value ready" else "value 2", "value 1"] &&
    numericExpressionGuardRun "NumberOfFilledFields(A,B) == 2" strings ==
      some ["cleared", "cleared"] &&
    numericExpressionGuardRun "NumberOfFilledFields(A,B) == 0" strings true ==
      some ["value 1", "cleared", "value 1"]) := by native_decide

example : numericExpressionGuardRun "[B] > 0 And FieldValueAsNumber(Text) > 0" false =
    some ["cleared", "value 1"] ∧
    numericExpressionGuardRun "[B] == 0 Or FieldValueAsNumber(Text) > 0" true =
    some ["value ready", "value 1"] := by native_decide

private def containingListAdmitted (guard : String) (target : String := "../C/N") : Bool :=
  let model : FlatModel := {
    fields := [(["G"], "N", 1, []), (["G", "C"], "N", 2, []),
      (["G", "H"], "N", 3, []), (["G", "R"], "N", 4, [10])].map
      fun (group, name, id, scope) => {
        id, name, groupPath := group, repeatableScope := scope
        policy := { kind := .number { scale := 0, signed := true } } }
    repeatableGroups := [{ level := 10, path := ["G", "R"], repeatability := some 5 }] }
  (lowerComputation model .english {
    group := ["G"], name := "Guarded", targetRelPath := target, commonPrecondition := some guard
    alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] }).isOk

example : containingListAdmitted "GroupFilled(/G/C)" ∧
    containingListAdmitted "AtLeastOneGroupFilled(/G)" "../N" ∧
    !containingListAdmitted "AtLeastOneGroupFilled(/G/C)" ∧
    !containingListAdmitted "AtLeastOneGroupFilled(/G/C,/G/H)" ∧
    !containingListAdmitted "AllGroupsFilled(/G/C,/G/H)" ∧
    !containingListAdmitted "NoGroupFilled(/G/C)" ∧
    !containingListAdmitted "AtLeastOneGroupFilled(/G/R*)" "../R/N" ∧
    containingListAdmitted "AtLeastOneGroupFilled(/G/H)" := by native_decide

end A12Kernel.Dm.ComputationGuardLocks
