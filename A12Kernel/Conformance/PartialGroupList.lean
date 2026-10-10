import A12Kernel.Elaboration.ValidationRule

namespace A12Kernel.Conformance.PartialGroupList

open A12Kernel

private def model (capacity : Nat) : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Form"], name := "Anchor", policy := { kind := .string } },
      { id := 2, groupPath := ["Form", "Fixed"], name := "N", policy := { kind := .number { scale := 0, signed := false } } },
      { id := 3, groupPath := ["Form", "Left", "Seal"], name := "N",
        policy := { kind := .number { scale := 0, signed := false } }, repeatableScope := [10] },
      { id := 4, groupPath := ["Form", "Left", "Seal"], name := "M",
        policy := { kind := .number { scale := 0, signed := false } }, repeatableScope := [10] }]
    repeatableGroups := [{ level := 10, path := ["Form", "Left"], repeatability := some capacity }] }

private def fixed : SurfaceGroupListOperand :=
  .group (.path { base := .absolute, groups := ["Form", "Fixed"] })

private def starred (terminal : Bool) : SurfaceGroupListOperand :=
  .starredGroup { base := .absolute, groups :=
    [{ name := "Form" }, { name := "Left", starred := true }] ++
      if terminal then [] else [{ name := "Seal" }] }

private def every (path : GroupPath) : RelevantEntityPattern :=
  { path, indices := path.map fun _ => .all }

private def row (coordinate : Nat) : RelevantEntityPattern :=
  { path := ["Form", "Left"], indices := [.all, .concrete coordinate] }

private def numberCell (field : FieldId) (path : List Nat) (bad : Bool) : ClassifiedCellInput :=
  { address := { field, path }, stored := if bad then "bad" else "1"
    raw := if bad then .rejected .malformed else .parsed (.num 1) }

private def document (rows : Nat) (cells : List ClassifiedCellInput) : DocumentData :=
  { instantiatedRows := (List.range rows).map fun i => { group := 10, path := [i + 1] }
    cells := { address := { field := 1, path := [] }, stored := "on", raw := .parsed (.str "on") } :: cells }

private def evaluateAtCapacity (capacity : Nat) (operator : GroupFillQuantifier) (operands : List SurfaceGroupListOperand)
    (data : DocumentData) (entities : List RelevantEntityPattern) : Option Verdict := do
  let model := model capacity
  let guard ← (elaborate model ["Form"] (.fieldFilled {
    base := .absolute, groups := ["Form"], field := "Anchor" })).toOption
  let guard ← (CheckedValidationCondition.fromFlat guard).toOption
  let predicate ← (CheckedValidationCondition.fromGroupList model ["Form"] operator operands).toOption
  let condition ← (guard.and predicate).toOption
  let rule ← (assembleResolvedValidationRule model condition 1 "probe" .error { parts := [] }).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" data).toOption
  let .evaluated outcome ← (rule.evalAddressedPartial checked
    (.partialSet (every ["Form", "Anchor"] :: entities))).toOption | none
  pure outcome.verdict

private def evaluate := evaluateAtCapacity 2

private def both (operands : List SurfaceGroupListOperand) (data : DocumentData)
    (entities : List RelevantEntityPattern) : List (Option Verdict) :=
  [.atLeastOneGroupFilled, .noGroupFilled].map fun operator => evaluate operator operands data entities

private def unknownPair : List (Option Verdict) := [some .unknown, some .unknown]
private def filledPair : List (Option Verdict) := [some (.fired .value), some .unknown]
private def emptyPair : List (Option Verdict) := [some .unknown, some (.fired .omission)]

example : both [starred false] (document 0 []) [] = unknownPair := by native_decide
example : both [starred false] (document 0 []) [every ["Form"]] = emptyPair := by native_decide
example : both [starred false] (document 1 []) [row 1] = unknownPair := by native_decide

example : [false, true].map (fun terminal =>
    both [starred terminal, starred terminal] (document 0 []) []) =
      [unknownPair, unknownPair] := by native_decide

example : [false, true].map (fun terminal =>
    both [starred terminal, starred terminal] (document 0 []) [every ["Form"]]) =
      [emptyPair, emptyPair] := by native_decide

example : both [starred true] (document 1 []) [every ["Form", "Left", "Seal", "N"]] =
    filledPair := by native_decide

example : [[fixed, starred false], [starred false, fixed]].map (fun operands =>
    both operands (document 1 [numberCell 2 [] false]) [every ["Form", "Fixed"]]) =
      [filledPair, filledPair] := by native_decide

example : [[fixed, starred false], [starred false, fixed]].map (fun operands =>
    both operands (document 1 [numberCell 2 [] true]) [every ["Form", "Fixed"]]) =
      [unknownPair, unknownPair] := by native_decide

example : both [starred false, starred false]
    (document 2 [numberCell 3 [1] true, numberCell 3 [2] false])
    [every ["Form"]] = filledPair := by native_decide

example : both [starred false, starred false]
    (document 2 [numberCell 3 [1] true]) [every ["Form"]] = unknownPair := by native_decide

example : both [starred false, starred false]
    (document 3 [numberCell 3 [3] false]) [every ["Form"]] = emptyPair := by native_decide

example : evaluateAtCapacity 1999999999 .atLeastOneGroupFilled [starred false]
    (document 1 [numberCell 3 [1] false]) [every ["Form", "Left", "Seal", "N"]] =
      some (.fired .value) := by native_decide

example : evaluateAtCapacity 1999999999 .noGroupFilled [starred false]
    (document 0 []) [] = some .unknown := by native_decide

example : [[fixed, starred false], [starred false, fixed]].map (fun operands =>
    evaluateAtCapacity 1999999999 .atLeastOneGroupFilled operands
      (document 0 [numberCell 2 [] false]) [every ["Form"]]) =
        [some (.fired .value), some (.fired .value)] := by native_decide

example : ValidationConditionLeaf.evalPartialGroupReaders .atLeastOneGroupFilled
    [fun () => .ok [.filled], fun () => .error (.checkedDocumentRequired [])] =
      .ok (.fired .value) := by rfl

example : ValidationConditionLeaf.evalPartialGroupReaders .noGroupFilled
    [fun () => .ok [.unavailable], fun () => .error (.checkedDocumentRequired [])] =
      .ok .unknown := by rfl

end A12Kernel.Conformance.PartialGroupList
