import A12Kernel.Elaboration.NumericComputation.FormalInput
import A12Kernel.Elaboration.MixedComputationPlan

/-! # Guard-derived computation operand scope

The Number row/fixed-child controls follow `src-computation-guard-operand-scope`.
Nested-row and connective controls distinguish the shared source-derived mechanism from
unconditional target expansion. Operand inclusion does not create scheduling dependencies.
-/

namespace A12Kernel.Conformance.ComputationOperandScope

private def rowPath : GroupPath := ["Form", "Rows"]
private def boxPath : GroupPath := rowPath ++ ["Box"]
private def innerPath : GroupPath := boxPath ++ ["Inner"]
private def number (id : FieldId) (name : String) (groupPath : GroupPath)
    (repeatableScope : List RepeatableLevel) : FlatFieldDecl :=
  { id, name, groupPath, repeatableScope, policy := { kind := .number { scale := 0, signed := true } } }
private def model : FlatModel := {
  fields := [number 0 "RootNoise" ["Form"] [], number 1 "RowNoise" rowPath [10],
    number 2 "Gate" boxPath [10], number 3 "X" boxPath [10],
    number 4 "InnerNoise" innerPath [10, 20], number 5 "Y" innerPath [10, 20], number 6 "FarNoise" (rowPath ++ ["Far"]) [10, 30]]
  repeatableGroups := [{ level := 10, path := rowPath, repeatability := some 3 },
    { level := 20, path := innerPath, repeatability := some 3 },
    { level := 30, path := rowPath ++ ["Far"], repeatability := some 3 }] }

private def guard (path : GroupPath) (operator : GroupPresenceOperator := .filled) : CheckedComputationCondition model :=
  .leaf (.groupPresence operator {
    reference := { path, origin := .path, boundRepeatableScope := model.repeatableScopeForGroupPath path }
    content := model.computationGroupSource path
    members := (model.groupSubtreeFields path).map (·.id) })

private def table? (target : FieldId) (group : GroupPath)
    (condition : Option (CheckedComputationCondition model)) :
    Option (CheckedNumericComputationTable model) :=
  (elaborateNumericTargetComputationTable model group target
    [(condition, .literal { value := 1, authoredScale := 0 })] (targetScope := .row)).toOption

private def selected? (target : FieldId) (group : GroupPath)
    (condition : Option (CheckedComputationCondition model)) : Option (List FieldId) := do
  let table ← table? target group condition
  let plan ← table.formalInputPlan.toOption
  pure plan.selectedFields

example : model.validate.isOk = true ∧ (table? 3 boxPath none).isSome = true ∧
    (table? 3 boxPath (some (guard boxPath))).isSome = true := by native_decide

example : selected? 3 boxPath none = some [1, 2, 4, 5, 6] := by native_decide
example : selected? 3 boxPath (some (guard rowPath)) = some [1, 2, 4, 5, 6] ∧
    selected? 3 boxPath (some (guard boxPath)) = some [2, 4, 5] := by native_decide
example : selected? 5 innerPath none = some [4] := by native_decide

private def world : World := { now := { epochMillis := 0 } }
private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get (by native_decide)
private def input? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [{ group := 10, path := [1] }, { group := 20, path := [1, 1] }, { group := 30, path := [1, 1] }]
    cells := model.fields.map fun field => {
      address := { field := field.id, path := field.repeatableScope.map fun _ => 1 }
      stored := "bad", raw := .rejected .malformed } }).toOption

private def findings? (condition : Option (CheckedComputationCondition model)) : Option (List FieldId) := do
  let table ← table? 3 boxPath condition
  let plan ← table.formalInputPlan.toOption
  pure ((plan.findings (← input?)).map (·.address.field))

example : input?.isSome = true := by native_decide
example : findings? none = some [1, 2, 4, 5, 6] ∧
    findings? (some (guard boxPath)) = some [2, 4, 5] := by native_decide

private def cache? (condition : Option (CheckedComputationCondition model)) : Option (List RowAddr) := do
  let table ← table? 3 boxPath condition
  let plan ← (certifyMixedComputationPlan
    [MixedComputationStep.number (compilePattern := builtinStringPatternCompiler) table]).toOption
  (plan.documentFor {} (← input?)).filterRows

example : cache? none = some [{ group := 10, path := [1] }, { group := 20, path := [1, 1] }, { group := 30, path := [1, 1] }] := by
  native_decide

example : cache? (some (guard boxPath)) =
    some [{ group := 10, path := [1] }, { group := 20, path := [1, 1] }] := by native_decide

private def implicitScope (target : FieldId)
    (conditions : List (Option (CheckedComputationCondition model))) : List FieldId :=
  (model.fields.filter fun field => computationOperandField model target (fun _ => false)
    conditions field.id CheckedComputationPredicate.groupReference?).map (·.id)

example : implicitScope 0 [none] = [] ∧ implicitScope 99 [none] = [] ∧
    implicitScope 3 [none] = [1, 2, 3, 4, 5, 6] ∧
    implicitScope 5 [none] = [4, 5] := by native_decide

example : implicitScope 3 [some (guard boxPath)] = [] ∧
    implicitScope 3 [some (.and (guard boxPath) (.fieldFilled 2))] = [] ∧
    implicitScope 3 [some (.or (guard boxPath) (.fieldFilled 2))] = [1, 2, 3, 4, 5, 6] ∧
    implicitScope 3 [some (guard ["Form"])] = [1, 2, 3, 4, 5, 6] ∧
    implicitScope 3 [some (guard innerPath)] = [1, 2, 3, 4, 5, 6] ∧
    implicitScope 3 [some (guard boxPath .notFilled)] = [1, 2, 3, 4, 5, 6] := by native_decide

example : implicitScope 3 [some (guard boxPath), none] = [1, 2, 3, 4, 5, 6] ∧
    implicitScope 3 [none, some (guard boxPath)] = [1, 2, 3, 4, 5, 6] ∧
    implicitScope 3 [some (guard boxPath), some (guard boxPath)] = [] := by native_decide

private def mergedScope? (unguardedFirst : Bool) : Option (List FieldId) := do
  let unguarded ← table? 3 boxPath none
  let narrow ← table? 3 boxPath (some (guard boxPath))
  let steps := if unguardedFirst then [unguarded, narrow] else [narrow, unguarded]
  let plan ← (certifyAuthoredMixedComputationPlan (compilePattern := builtinStringPatternCompiler)
    (steps.map MixedComputationStep.number)).toOption
  pure ((model.fields.filter fun field => plan.authored.any (·.operandField field.id)).map (·.id))

example : mergedScope? true = some [1, 2, 3, 4, 5, 6] ∧
    mergedScope? false = some [1, 2, 3, 4, 5, 6] := by native_decide

private def noFalseDependency? : Option Bool := do
  let table ← table? 3 boxPath none
  pure (table.operandField 5 && !table.requiresProducer (fun _ _ => false) 5)

example : noFalseDependency? = some true := by native_decide

private def preservedCache? : Option (List RowAddr) := do
  let table ← table? 3 boxPath none
  let plan ← (certifyMixedComputationPlan
    [MixedComputationStep.number (compilePattern := builtinStringPatternCompiler) table]).toOption
  (plan.documentFor {} ((← input?).withComputationFilterRows (fun _ => false))).filterRows

example : preservedCache? = some [] := by native_decide

example : ((checkImplicitGuardFormalInputOperations model [(3, []), (5, [])]).toOption.map
    (·.selectedFields)) = some [1, 2, 4, 6] := by native_decide

private def computed? (condition : Option (CheckedComputationCondition model)) : Option (List (Option String)) := do
  let table ← table? 3 boxPath condition
  let plan ← (certifyMixedComputationPlan
    [MixedComputationStep.number (compilePattern := builtinStringPatternCompiler) table]).toOption
  let state ← (plan.execute world prepared.patterns (← input?)).toOption
  pure (state.map fun outcome => match outcome with
    | .number value => match value.outcome with
      | .accepted stored => some stored.render
      | _ => none
    | _ => none)

example : computed? none = some [some "1"] ∧
    computed? (some (guard boxPath)) = some [some "1"] := by native_decide

end A12Kernel.Conformance.ComputationOperandScope
