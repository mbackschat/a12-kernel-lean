import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document
import A12Kernel.Reference.Dm.Validate
import A12Kernel.Elaboration.BooleanComputationResult
import A12Kernel.Semantics.NumericComputationApplicationFold
import A12Kernel.Semantics.StringComputationApplicationFold

namespace A12Kernel.Dm.ApplicationKindLocks

open Lean

private inductive Kind where
  | number | boolean | confirm | enumeration
  deriving BEq

private def Kind.fieldKind : Kind → FieldKind
  | .number => .number { scale := 0, signed := true }
  | .boolean => .boolean
  | .confirm => .confirm
  | .enumeration => .enumeration

private def Kind.value (kind : Kind) (same : Bool) : Lean.Json :=
  match kind with
  | .number => toJson (if same then (7 : Nat) else 2)
  | .boolean => toJson same
  | .confirm => toJson true
  | .enumeration => .str (if same then "B" else "A")

private def Kind.operation : Kind → String
  | .number => "[Source]"
  | .boolean | .confirm => "True"
  | .enumeration => "\"B\""

private structure Summary where
  successful : Nat
  changed : Nat
  errored : Nat
  cleared : Nat
  attempted : List String := []
  applied : List String
  laterFilled : Nat
  downstream : List String
  referenceAgrees : Bool := true
  deriving Repr, BEq

private def run (kind : Kind) (repeated : Bool) (sourceSeed : Option Bool)
    (destinationSeed : Option Bool) (gate : String := "on") (number : Nat := 7)
    (secondGate : Option String := none) (unconverted : Bool := false) : Option Summary := do
  let group := if repeated then ["Form", "Rows"] else ["Form"]
  let scope := if repeated then [10] else []
  let model : FlatModel := {
    fields := [
      { id := 1, name := "Source", groupPath := group, repeatableScope := scope,
        policy.kind := .number { scale := 0, signed := true } },
      { id := 2, name := "Out", groupPath := group, repeatableScope := scope,
        policy.kind := kind.fieldKind,
        enumeration := if kind == .enumeration then some { storedTokens := ["A", "B"] } else none,
        numericTargetConstraints := if kind == .number then { maximum := some 9 } else {} },
      { id := 3, name := "Gate", groupPath := group, repeatableScope := scope, policy.kind := .string },
      { id := 4, name := "After", groupPath := group, repeatableScope := scope,
        policy.kind := .number { scale := 0, signed := true } }]
    repeatableGroups := if repeated then [{ level := 10, path := group, repeatability := some 2 }] else [] }
  let world : World := { now := { epochMillis := 0 } }
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let dm : DmModel := { flat := model, computations := [], rules := [], conditionLanguage := "en_US", refusals := [] }
  let data (targets : List (Option Lean.Json)) :=
    let rows := targets.zipIdx |>.map fun (target, index) => Lean.Json.mkObj (
      [("Source", toJson number), ("Gate", .str (if index == 1 then secondGate.getD gate else gate)), ("After", toJson (99 : Nat))] ++
        target.toList.map ("Out", ·))
    Lean.Json.mkObj [("Form", if repeated then .mkObj [("Rows", .arr rows.toArray)] else rows.head!)]
  let checked (targets : List (Option Lean.Json)) (unconverted : Bool := false) := do
    let input ← (readDocument dm (data targets)).toOption
    let data := if unconverted then { input.data with
      cells := input.data.cells.map fun cell =>
        if cell.address.field == 2 then { cell with sourceRepresentation := .unconvertedText } else cell }
      else input.data
    (checkDocument prepared "en_US" data).toOption
  let count := if repeated then 2 else 1
  let source ← checked (List.replicate count (sourceSeed.map kind.value)) unconverted
  let destination ← checked (List.replicate count (destinationSeed.map kind.value))
  let definitions : List DmComputation := [
    { name := "AfterComp", group, targetRelPath := "../After",
      commonPrecondition := some "FieldFilled(Out) Or FieldNotFilled(Out)",
      alternatives := [{ precondition := none, operation := "1" }], errorCodesToSuppress := [] },
    { name := "OutComp", group, targetRelPath := "../Out", commonPrecondition := some "FieldFilled(Gate)",
      alternatives := [{ precondition := none, operation := kind.operation }], errorCodesToSuppress := [] }]
  let lowered ← definitions.mapM fun definition => (lowerComputation model .english definition).toOption
  let steps := lowered.map (·.2.toMixedStep builtinStringPatternCompiler)
  let plan ← (certifyAuthoredMixedComputationPlan steps).toOption
  let outcomes ← (plan.execute world prepared.patterns source).toOption
  let addresses : List CellAddr := (List.range count).map fun index =>
    { field := 2, path := if repeated then [index + 1] else [] }
  let downstream := outcomes.filterMap fun
    | .number entry => if entry.targetField.field == 4 then
        some (match entry.outcome with | .accepted value => value.render | _ => "clear") else none
    | _ => none
  let (successful, changed, errored, cleared, attempted, targets, states) ← match kind with
    | .number => do
        let entries := outcomes.filterMap fun
          | .number entry => if entry.targetField.field == 2 then some entry else none
          | _ => none
        let result := NumericComputationRunView.fromPartitionedSourceOutcomes ([] : List Unit) entries
        let applied ← (result.applyTo destination.numericTargetPlacementStateAt).toOption
        let states : List (Option Json × String) := addresses.map fun address => match applied address with
          | .absent => (none, "absent") | .presentEmpty => (some .null, "empty")
          | .presentValue (.decimal value) => (some (.str value.render), value.render)
          | .presentValue .nonComputedForm => (none, "noncomputed")
        pure (result.withoutErrors.length, result.withChanges.length, result.withErrors.length,
          result.cleared.length, result.withErrors.map (·.attempted.render), states.map (·.1), states.map (·.2))
    | .boolean | .confirm => do
        let entries := outcomes.filterMap fun
          | .document address (.boolean outcome) =>
              if address.field == 2 then some (address, outcome, source.sourceBooleanTargetStateAt address) else none
          | _ => none
        let result := BooleanComputationRunView.fromSourcedOutcomes ([] : List Unit) entries
        let applied := result.applyTo destination.sourceBooleanTargetStateAt
        let states : List (Option Json × String) := addresses.map fun address => match applied address with
          | .absent => (none, "absent") | .presentEmpty => (some .null, "empty")
          | .presentValue value => (some (toJson value), if value then "true" else "false")
          | .presentInvalid text => (some (.str text), "invalid")
          | .presentUnconverted text => (some (.str text), "unconverted")
        pure (result.withoutErrors.length, result.withChanges.length, result.withErrors.length,
          result.cleared.length, [], states.map (·.1), states.map (·.2))
    | .enumeration => do
        let entries := outcomes.filterMap fun
          | .document address (.enumeration outcome) => if address.field == 2 then
              some { targetField := address, outcome, source := source.sourceStringTargetStateAt address } else none
          | _ => none
        let result := StringComputationRunView.fromSourcedOutcomes ([] : List Unit) entries
        let applied ← (result.applyTo destination.sourceStringTargetStateAt).toOption
        let states : List (Option Json × String) := addresses.map fun address => match applied address with
          | .absent => (none, "absent") | .presentEmpty => (some .null, "empty")
          | .presentValue value => (some (.str value.text), value.text)
          | .presentUnconverted value => (some (.str value.text), "unconverted")
        pure (result.withoutErrors.length, result.withChanges.length, result.withErrors.length,
          result.cleared.length, result.withErrors.map (·.attempted.text), states.map (·.1), states.map (·.2))
  let applied ← checked targets
  let definition : DmRule := {
    group, name := "Observed", errorEntityRelPath := "../Out"
    errorCode := "observed", condition := "FieldFilled(Out)", severity := "ERROR" }
  let rule ← (checkRule dm .english definition).toOption
  let messages ← (runRule world applied rule).toOption
  let reported ← (runComputations world prepared source (lowered.map (·.2))).toOption
  let pointers := addresses.map (fun address => renderPointer model (MessagePointer.ofCellAddr address))
  let referenceAgrees := (reported.filter fun result => pointers.contains result.pointer).length == changed + errored + cleared
  pure { successful, changed, errored, cleared, attempted, applied := states, laterFilled := messages.length, downstream, referenceAgrees }

private def kinds := [Kind.number, .boolean, .confirm, .enumeration]
private def resultText : Kind → String
  | .number => "7" | .boolean | .confirm => "true" | .enumeration => "B"

example : kinds.all (fun kind => [false, true].all fun repeated =>
    let n := if repeated then 2 else 1
    run kind repeated (some false) (some false) == some {
      successful := n, changed := if kind == .confirm then 0 else n, errored := 0, cleared := 0,
      applied := List.replicate n (resultText kind), laterFilled := n, downstream := List.replicate n "1" }) = true := by native_decide

example : kinds.all (fun kind => [false, true].all fun repeated =>
    let n := if repeated then 2 else 1
    run kind repeated none none == some {
      successful := n, changed := n, errored := 0, cleared := 0,
      applied := List.replicate n (resultText kind), laterFilled := n, downstream := List.replicate n "1" }) = true := by native_decide

example : kinds.all (fun kind => [false, true].all fun repeated =>
    let n := if repeated then 2 else 1
    run kind repeated (some true) none == some {
      successful := n, changed := 0, errored := 0, cleared := 0,
      applied := List.replicate n "absent", laterFilled := 0, downstream := List.replicate n "1" }) = true := by native_decide

example : kinds.all (fun kind => [false, true].all fun repeated =>
    let n := if repeated then 2 else 1
    run kind repeated (some false) none "" == some {
      successful := 0, changed := 0, errored := 0, cleared := n,
      applied := List.replicate n "empty", laterFilled := 0, downstream := List.replicate n "1" }) = true := by native_decide

example : kinds.all (fun kind => [false, true].all fun repeated =>
    let n := if repeated then 2 else 1
    run kind repeated none (some true) "" == some {
      successful := 0, changed := 0, errored := 0, cleared := 0,
      applied := List.replicate n (resultText kind), laterFilled := n, downstream := List.replicate n "1" }) = true := by native_decide

example : [false, true].all (fun repeated => [none, some false].all fun sourceSeed =>
    [none, some false].all fun destinationSeed =>
    let n := if repeated then 2 else 1
    (run .number repeated sourceSeed destinationSeed "on" 10).map
      (fun result => (result.successful, result.errored, result.attempted, result.applied, result.laterFilled, result.downstream)) ==
      some (0, n, List.replicate n "10", List.replicate n (if destinationSeed.isSome then "empty" else "absent"),
        0, List.replicate n "clear")) = true := by native_decide

example : kinds.all (fun kind =>
    run kind true (some true) none "on" 7 (some "") == some {
      successful := 1, changed := 0, errored := 0, cleared := 1,
      applied := ["absent", "empty"], laterFilled := 0, downstream := ["1", "1"] }) = true := by native_decide

example : [Kind.boolean, .confirm].all (fun kind => [false, true].all fun repeated =>
    let n := if repeated then 2 else 1
    (run kind repeated (some true) none "on" 7 none true).map
      (fun result => (result.successful, result.changed, result.applied, result.downstream, result.referenceAgrees)) ==
      some (n, n, List.replicate n "true", List.replicate n "1", true)) = true := by native_decide

end A12Kernel.Dm.ApplicationKindLocks
