import A12Kernel.Elaboration.NumericAggregate.Entities
import A12Kernel.Elaboration.CheckedDocument

namespace A12Kernel.Conformance.PartialNumberGroupAggregate

open A12Kernel

private def parent (repeated : Bool) : GroupPath :=
  if repeated then ["Form", "Rows"] else ["Form"]

private def model (repeated : Bool) : FlatModel := {
  fields := [1, 2].map fun id => {
    id, groupPath := parent repeated ++ ["Pair"], name := if id == 1 then "A" else "B"
    policy := { kind := .number { scale := 0, signed := id == 1 } }
    repeatableScope := if repeated then [10] else [] }
  repeatableGroups := if repeated then
    [{ level := 10, path := parent true, repeatability := some 2 }] else [] }

private def result (repeated complete localView : Bool) (op : NumericAggregateOp) (contents : Nat := 0) (count : Bool := false) (unavailable : Bool := false) :
    Option PartialValidationNumberAggregateViewResult := do
  let model := model repeated
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := if repeated then [{ group := 10, path := [1] }] else []
    cells := [1, 2].map fun id =>
      let empty := contents == 3 || (contents == 1 && id == 2) || (contents == 2 && id == 1)
      let malformed := contents == 4 && id == 1
      let amount := if contents == 0 && id == 2 then 4 else 3
      { address := { field := id, path := if repeated then [1] else [] }
        stored := if empty then "" else if malformed then "bad" else toString amount
        raw := if empty then .presentEmpty else if malformed then .rejected .malformed else .parsed (.num amount) } }).toOption
  let source ← (elaborateNumberEntitySource model (parent repeated)
    { first := .group (.path { base := .relative 0, groups := ["Pair"] }), rest := [] }
    (bindingGroup? := some (parent repeated))).toOption
  let environment := if repeated then [(10, 1)] else []
  let scope := ValidationRelevanceScope.partialSet
    ((if complete then ["A", "B"] else ["A"]).map fun name =>
      RelevantEntityPattern.allInstances (parent repeated ++ ["Pair", name]))
  if count then
    (.result <$> source.evaluateCheckedDocumentPartialValueCount 3 document environment scope).toOption
  else if localView then
    (source.evaluatePartialViewAggregate op document environment scope
      fun row field => do
        if unavailable && field == 2 then pure none
        else pure (some (← document.addressedCell row field).cell)).toOption
  else
    (.result <$> source.evaluateCheckedDocumentPartialAggregate op document environment scope).toOption

example : [false, true].all (fun repeated => [false, true].all fun localView =>
    result repeated true localView .sum == some (.result (.evaluated (.value 7 .fixed))) &&
    result repeated true localView .maximum == some (.result (.evaluated (.value 4 .fixed))) &&
    result repeated false localView .sum == some (.result .nonRelevant)) = true := by
  native_decide

example : [false, true].all (fun repeated => [false, true].all fun localView =>
    result repeated true localView .sum 1 == some (.result (.evaluated (.value 3 .growOnly))) &&
    result repeated true localView .sum 2 == some (.result (.evaluated (.value 3 .both))) &&
    result repeated true localView .sum 3 == some (.result (.evaluated (.value 0 .both))) &&
    result repeated true localView .sum 4 == some (.result (.evaluated (.unknown .malformed)))) = true := by
  native_decide

example : [false, true].all (fun repeated =>
    result repeated true false .sum 0 true == some (.result (.evaluated (.value 1 .fixed))) &&
    result repeated false false .sum 0 true == some (.result .nonRelevant) &&
    result repeated true true .sum 0 false true == some .silentlyUnavailable) = true := by native_decide

private def tailResult (signedTail : Bool) : Option (List NumericOperand) := do
  let model : FlatModel := {
    fields := [
      { id := 1, groupPath := ["Form", "Pair"], name := "A"
        policy := { kind := .number { scale := 0, signed := !signedTail } } },
      { id := 2, groupPath := ["Form", "Pair", "Rows"], name := "B", repeatableScope := [10]
        policy := { kind := .number { scale := 0, signed := signedTail } } }]
    repeatableGroups := [{ level := 10, path := ["Form", "Pair", "Rows"], repeatability := some 2 }] }
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := [{ address := { field := 1, path := [] }, stored := "3", raw := .parsed (.num 3) }] }).toOption
  let source ← (elaborateNumberEntitySource model ["Form"]
    { first := .group (.path { base := .relative 0, groups := ["Pair"] }), rest := [] }).toOption
  let full ← (source.evaluateCheckedDocumentValidationAggregate .sum document []).toOption
  let computed ← (source.evaluateCheckedDocumentComputationAggregate .sum document []).toOption
  let .evaluated covered ← (source.evaluateCheckedDocumentPartialAggregate .sum document []
    (.partialSet [RelevantEntityPattern.allInstances ["Form"]])).toOption | none
  pure [full, computed, covered]

example : tailResult false = some (List.replicate 3 (.value 3 .growOnly)) ∧
    tailResult true = some (List.replicate 3 (.value 3 .both)) := by native_decide

end A12Kernel.Conformance.PartialNumberGroupAggregate
