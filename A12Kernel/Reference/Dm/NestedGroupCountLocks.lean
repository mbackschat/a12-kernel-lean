import A12Kernel.Reference.Dm.Compute
import A12Kernel.Reference.Dm.Document

namespace A12Kernel.Dm.NestedGroupCountLocks
open Lean A12Kernel

private def model : FlatModel :=
  let number (id : Nat) (group : GroupPath) (scope : List Nat) (name : String) : FlatFieldDecl :=
    { id, groupPath := group, repeatableScope := scope, name,
      policy := { kind := .number { scale := 0, signed := true } } }
  { fields := [
      { id := 1, groupPath := ["Form"], name := "Anchor", policy := { kind := .string } },
      number 2 ["Form", "Rows"] [10] "N", number 3 ["Form", "Rows"] [10] "M",
      number 4 ["Form", "Rows", "Items"] [10, 20] "N", number 5 ["Form", "Rows", "Items"] [10, 20] "M",
      number 6 ["Form", "Rows", "Items", "Detail"] [10, 20] "N",
      number 7 ["Form", "Rows", "Items", "Detail"] [10, 20] "M",
      number 8 ["Form", "Rows", "Items", "Desc"] [10, 20, 30] "N",
      number 9 ["Form", "Rows", "Items", "Desc"] [10, 20, 30] "M",
      number 10 ["Form"] [] "Target"]
    repeatableGroups := [
      { level := 10, path := ["Form", "Rows"], repeatability := some 2 },
      { level := 20, path := ["Form", "Rows", "Items"], repeatability := some 2 },
      { level := 30, path := ["Form", "Rows", "Items", "Desc"], repeatability := some 2 }] }

private def dm : DmModel := { flat := model, rules := [], computations := [], conditionLanguage := "en_US", refusals := [] }
private def world : World := { now := { epochMillis := 0 } }
private def item (bad : Bool := false) : Json := Json.mkObj [
  ("N", .str (if bad then "bad" else "1")), ("M", .str "2"),
  ("Detail", Json.mkObj [("N", .str "3"), ("M", .str "4")]),
  ("Desc", .arr #[Json.mkObj [("N", .str "5")], Json.mkObj [("N", .str "6")]])]
private def row (items : Array Json) : Json := Json.mkObj [("N", .str "1"), ("M", .str "2"), ("Items", .arr items)]
private def full : Array Json := #[row #[item, item], row #[item, item]]
private def emptyPrefix : Array Json := #[row #[], row #[item, item]]
private def suffix : Array Json := #[row #[item, item], row #[]]
private def missing : Array Json := #[row #[item, item]]
private def input (rows : Array Json) : Json := Json.mkObj [("Form", Json.mkObj [
  ("Anchor", .str "on"), ("Target", .str "99"), ("Rows", .arr rows)])]

private def validate (rows : Array Json) (partialMode : Bool) (operand : String) (n : Nat)
    (scope : ValidationRelevanceScope := .partialSet [{ path := ["Form"], indices := [.all] }]) :
    Option (List Polarity) := do
  let data ← (readDocument dm (input rows)).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" data.data).toOption
  let rule ← (checkRule dm .english {
    name := "Count", group := ["Form"], errorCode := "Count", errorEntityRelPath := "../Anchor", severity := "ERROR",
    condition := "FieldFilled(Anchor) And NumberOfFilledGroups(" ++ operand ++ ") == " ++ toString n }).toOption
  let messages ← if partialMode then
    match ← (rule.evalAddressedPartial document scope (some world)).toOption with
    | .skipped => pure []
    | .evaluated outcome => pure outcome.message?.toList
  else (runRule world document rule).toOption
  pure (messages.map (·.messageType))

private def computeIn (dm : DmModel) (rows : Array Json) : Option (Nat × Verdict) := do
  let data ← (readDocument dm (input rows)).toOption
  let prepared ← (prepareFlatStringContext world builtinStringPatternCompiler dm.flat).toOption
  let document ← (checkDocument prepared "en_US" data.data).toOption
  let lowered ← (lowerComputation dm.flat .english {
    group := ["Form"], name := "TargetComp", targetRelPath := "../Target", commonPrecondition := none,
    alternatives := [{ precondition := none, operation := "NumberOfFilledGroups(Rows*/Items*)" }], errorCodesToSuppress := [] }).toOption
  let .number table _ := lowered.2 | none
  let .atom atom@(.filledGroupCountMixed operands) := table.first.operation.operation.core.expression | none
  let read := fun env field => (document.checkedCellWithRead document.read env field).toOption.getD malformedCheckedCell
  let context : NumericComputationEvaluationContext := {
    scalar := { read := read [], world := some world }, document := document.source.toDocument,
    outer := [], filterRead := read, starRead := read }
  let .value computed ← (context.readCheckedNumericComputationAtom atom).toOption | none
  let channels ← (context.growthOfGroupCountOperands dm.flat operands).toOption
  let decided ← (context.groupCountOperandsDecided dm.flat operands).toOption
  let channels ← channels
  pure (computed.floor.toNat, computedNumberSelfValidationIfDecided decided 99 computed channels)

private def compute := computeIn dm

example : validate full false "Rows*/Items*" 4 = some [.value] := by native_decide
example : validate full true "Rows*/Items*" 4 = some [.value] := by native_decide
example : validate emptyPrefix false "Rows*/Items*" 2 = some [.omission] := by native_decide
example : validate emptyPrefix true "Rows*/Items*" 2 = some [.omission] := by native_decide
example : validate suffix false "Rows*/Items*" 2 = some [.omission] := by native_decide
example : validate suffix true "Rows*/Items*" 2 = some [.omission] := by native_decide
example : validate missing false "Rows*/Items*" 2 = some [.omission] := by native_decide
example : validate missing true "Rows*/Items*" 2 = some [.omission] := by native_decide
example : validate emptyPrefix true "Rows*/Items*/Detail" 2 = some [.omission] := by native_decide
example : validate full true "Rows*" 2 = some [.value] := by native_decide
example : validate #[row #[item true, item], row #[item, item]] false "Rows*/Items*" 4 = some [.value] := by native_decide
example : validate #[row #[item true, item], row #[item, item]] true "Rows*/Items*" 4 = some [] := by native_decide
example : validate #[row #[item, item], row #[item, item true]] true "Rows*/Items*" 4 = some [.value] := by native_decide
example : compute full = some (4, .fired .value) := by native_decide
example : compute emptyPrefix = some (2, .fired .omission) := by native_decide
example : compute suffix = some (2, .fired .omission) := by native_decide
example : compute missing = some (2, .fired .omission) := by native_decide

end A12Kernel.Dm.NestedGroupCountLocks
