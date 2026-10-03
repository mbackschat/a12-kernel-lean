import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Parser
import A12Kernel.Reference.Dm.Document
import A12Kernel.Elaboration.GeneratedComputationValidation

/-! # Typed distinct counts in computation expressions

Execution locks for overload selection, phase poison, filtered extent and dependency overlays.
The retained clock computation and filter-carrier checkpoints own external correspondence;
composition and scheduling extensions here are internal checks.
-/

namespace A12Kernel.Dm.DistinctCountLocks

open A12Kernel A12Kernel.Dm Lean

private inductive Family where
  | number | token | enumeration | date | clock | instant | month
  deriving BEq

private def declaration (family : Family) (id : FieldId) (name : String) : FlatFieldDecl :=
  let format := match family with
    | .date => "yyyy-MM-dd" | .clock => "HH:mm:ss" | .instant => "yyyy-MM-dd'T'HH:mm:ss"
    | .month => "yyyy-MM" | _ => ""
  { id, name, groupPath := ["Form", "Inputs"]
    policy := { kind := match family with
      | .number => .number { scale := 0, signed := true }
      | .token => .string | .enumeration => .enumeration
      | _ => .temporal .date (TemporalComponents.ofFormat format) }
    temporalTargetPolicy := if format.isEmpty then none else some { format }
    enumeration := if family == .enumeration then some { storedTokens := ["A", "B"] } else none }

private def text (family : Family) (other : Bool) : String := match family, other with
  | .number, false => "1" | .number, true => "2"
  | .token, false | .enumeration, false => "A" | .token, true | .enumeration, true => "B"
  | .date, false => "2024-03-05" | .date, true => "2024-04-05"
  | .clock, false => "12:30:00" | .clock, true => "13:30:00"
  | .instant, false => "2024-03-05T12:30:00" | .instant, true => "2024-03-05T13:30:00"
  | .month, false => "2024-03" | .month, true => "2024-04"

private def execute (model : FlatModel) (data : Json) (definitions : List DmComputation) :
    Option (List String) := do
  let dm : DmModel := {
    flat := model, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }
  let input ← (readDocument dm data).toOption
  if !input.refusals.isEmpty then none
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" input.data).toOption
  let steps ← definitions.mapM fun definition =>
    (lowerComputation model .english definition).toOption.map (·.2)
  pure ((← (runComputations world prepared checked steps).toOption).map (·.outcome))

private def definition (name target operation : String) : DmComputation := {
  group := ["Form"], name, targetRelPath := target, commonPrecondition := none
  alternatives := [{ precondition := none, operation }], errorCodesToSuppress := [] }

private def run (family : Family) (values : List String) (operation : String :=
    "NumberOfDifferentValues(Inputs/A, Inputs/B)") (fresh : Bool := false) : Option (List String) := do
  let model : FlatModel := { timeZoneId := "UTC", fields := [
    declaration family 1 "A", declaration family 2 "B", declaration family 4 "C",
    { id := 3, name := "Out", groupPath := ["Form"],
      policy := { kind := .number { scale := 0, signed := true } } }] }
  execute model (Json.mkObj [("Form", Json.mkObj [
    ("Inputs", Json.mkObj ((["A", "B"].zip values).map fun (name, value) => (name, Json.str value))),
    ("Out", "9")])])
    ([definition "Count" "../Out" operation] ++
      if fresh then [definition "Producer" "../Inputs/A" "FirstFilledValue(Inputs/B, Inputs/C)"] else [])

example : [.number, .token, .enumeration, .date, .clock, .instant, .month].all (fun family =>
    run family [text family false, text family false] == some ["value 1"] &&
    run family [text family false, text family true] == some ["value 2"] &&
    run family [] == some ["value 0"] &&
    run family [text family false, ""] == some ["value 1"] &&
    run family [text family false, text family true] "1 + NumberOfDifferentValues(Inputs)" ==
      some ["value 3"]) := by native_decide

example : [.enumeration, .date, .clock, .instant, .month].all (fun family =>
    run family [text family false, "bad"] == some ["cleared"]) := by native_decide

example : run .token ["A", "B"] "NumberOfDifferentValues(Inputs/A, Inputs/B)" true =
    some ["value B", "value 1"] ∧
    run .date ["bad", "2024-04-05"] "1 + NumberOfDifferentValues(Inputs)" true =
      some ["value 2024-04-05", "value 2"] ∧
    run .date ["2024-04-05", "bad"] "NumberOfDifferentValues(Inputs)" true =
      some ["cleared", "cleared"] := by native_decide

private def repeated (family : Family) (guards : List String) (filtered : Bool)
    (sourcePoison : Bool := false) (fresh : Bool := false) : Option (List String) := do
  let model : FlatModel := {
    timeZoneId := "UTC"
    fields := [
      { (declaration family 1 "A") with repeatableScope := [10] },
      { id := 2, name := "Guard", groupPath := ["Form", "Inputs"], repeatableScope := [10],
        policy := { kind := .number { scale := 0, signed := true } } },
      { id := 3, name := "Out", groupPath := ["Form"],
        policy := { kind := .number { scale := 0, signed := true } } }],
    repeatableGroups := [{ level := 10, path := ["Form", "Inputs"], repeatability := some 3 }] }
  let rows := guards.zipIdx |>.map fun (guard, i) => Json.mkObj [
    ("A", Json.str (if i == 3 || (sourcePoison && i == 1) then "bad" else text family (i == 1))),
    ("Guard", Json.str guard)]
  let source := if filtered then "Inputs*/A Having FieldFilled(Inputs/Guard)" else "Inputs*/A"
  execute model (Json.mkObj [("Form", Json.mkObj [
      ("Inputs", Json.arr rows.toArray), ("Out", "9")])])
    ([definition "Count" "../Out" s!"1 + NumberOfDifferentValues({source})"] ++
      if fresh then [definition "Producer" "../Inputs/Guard" "1"] else [])

example : [.token, .enumeration, .date, .clock, .instant, .month].all (fun family =>
    repeated family ["1", "1", ""] true == some ["value 3"] &&
    repeated family ["1", "", ""] true == some ["value 2"] &&
    repeated family ["1", "bad", ""] true == some ["cleared"] &&
    repeated family ["1", "bad", ""] false == some ["value 3"] &&
    repeated family ["1", "1", "", "bad"] true == some ["value 3"] &&
    repeated family ["1", "1", "", "bad"] false == some ["value 3"]) := by native_decide

example : [.enumeration, .date, .clock, .instant, .month].all (fun family =>
    repeated family ["1", "1", ""] false true == some ["cleared"] &&
    repeated family ["1", "", ""] true true == some ["value 2"]) := by native_decide

example : repeated .date ["", "bad", ""] true false true =
    some ["value 1", "value 1", "value 1", "value 3"] := by native_decide

private def supplemented (year : Option Int) : Option (List String) := do
  let model : FlatModel := { timeZoneId := "UTC", baseYear := year, fields := [
    declaration .date 1 "A",
    { (declaration .date 2 "B") with
      policy := { kind := .temporal .date (TemporalComponents.ofFormat "MM-dd") }
      temporalTargetPolicy := some { format := "MM-dd" } },
    { id := 3, name := "Out", groupPath := ["Form"],
      policy := { kind := .number { scale := 0, signed := true } } }] }
  execute model (Json.mkObj [("Form", Json.mkObj [
    ("Inputs", Json.mkObj [("A", "2024-03-05"), ("B", "03-05")]), ("Out", "9")])])
    [definition "Count" "../Out" "NumberOfDifferentValues(Inputs/A, Inputs/B)"]

example : supplemented (some 2024) = some ["value 1"] ∧
    supplemented (some 2023) = some ["value 2"] ∧ supplemented none = none := by native_decide

private def targetScope (family : Family) (bound : Bool) : Bool :=
  let model : FlatModel := {
    timeZoneId := "UTC"
    fields := [
      { (declaration family 1 "A") with repeatableScope := [10] },
      { (declaration family 2 "B") with repeatableScope := [10] },
      { id := 3, name := "Out"
        groupPath := if bound then ["Form", "Inputs"] else ["Form"]
        repeatableScope := if bound then [10] else []
        policy := { kind := .number { scale := 0, signed := true } } }]
    repeatableGroups := [{ level := 10, path := ["Form", "Inputs"], repeatability := some 3 }] }
  (lowerComputation model .english (definition "Count" (if bound then "../Inputs/Out" else "../Out")
    "NumberOfDifferentValues(Inputs/A, Inputs/B)")).isOk

example : [.token, .enumeration, .date, .clock, .instant, .month].all (fun family =>
    targetScope family true && !targetScope family false) := by native_decide

private def retainedBridge (family : Family) : Option (Bool × Bool × NumericScaleSummary) := do
  let model : FlatModel := { timeZoneId := "UTC", fields := [
    declaration family 1 "A", declaration family 2 "B",
    { id := 3, name := "Out", groupPath := ["Form"],
      policy := { kind := .number { scale := 0, signed := true } } }] }
  let (_, .number table _) ← (lowerComputation model .english
    (definition "Count" "../Out" "NumberOfDifferentValues(Inputs/A, Inputs/B)")).toOption | none
  let .atom atom := table.first.operation.operation.core.expression | none
  let validation ← atom.toValidationAtom.toOption
  pure (validation.referencesField 1 && validation.referencesField 2 && !validation.referencesField 3,
    match atom, validation with
    | .tokenDistinctCount _, .tokenDistinctCount _ => true
    | .temporalDistinctCount _, .temporalDistinctCount _ => true
    | _, _ => false,
    atom.numericScaleSummary)

example : [.token, .enumeration, .date, .clock, .instant, .month].all (fun family =>
    retainedBridge family == some (true, true, NumericScaleSummary.field 0)) := by native_decide

private def scalarBoundary (family : Family) (shape : Nat) :
    Option (Bool × Sum NumericComputationFault NumericComputationResult) := do
  let model : FlatModel := {
    timeZoneId := "UTC"
    fields := [
      { (declaration family 1 "A") with repeatableScope := if shape == 1 then [10] else [] },
      { (declaration family 2 "B") with repeatableScope := if shape == 1 then [10] else [] },
      { id := 3, name := "Out", groupPath := ["Form"],
        policy := { kind := .number { scale := 0, signed := true } } }]
    repeatableGroups := if shape == 1 then
      [{ level := 10, path := ["Form", "Inputs"], repeatability := some 3 }] else [] }
  let operand := match shape with
    | 0 => "Inputs/A, Inputs/B" | 1 => "Inputs*/A" | _ => "Inputs"
  let (_, .number table _) ← (lowerComputation model .english
    (definition "Count" "../Out" s!"NumberOfDifferentValues({operand})")).toOption | none
  let .atom atom := table.first.operation.operation.core.expression | none
  let a := declaration family 1 "A"
  let b := declaration family 2 "B"
  let rawA ← (classifyStored model a { field := 1, path := [] } (text family false)).toOption
  let rawB ← (classifyStored model b { field := 2, path := [] } (text family true)).toOption
  let context : ScalarComputationContext := {
    read := fun field => if field == 1 then a.checkRaw rawA.raw else b.checkRaw rawB.raw }
  pure (atom.supportsScalarEvaluation, match context.readCheckedNumericComputationAtom atom with
    | .ok value => .inr value
    | .error fault => .inl fault)

example : [.token, .enumeration, .date, .clock, .instant, .month].all (fun family =>
    decide (scalarBoundary family 0 = some (true, .inr (.value 2)) ∧
      scalarBoundary family 1 = some (false, .inl .repeatableContextRequired) ∧
      scalarBoundary family 2 = some (false, .inl .repeatableContextRequired))) := by native_decide

end A12Kernel.Dm.DistinctCountLocks
