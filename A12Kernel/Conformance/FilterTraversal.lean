import A12Kernel.Elaboration.StarPath
import A12Kernel.Semantics.Correlation

namespace A12Kernel.Conformance.FilterTraversal
open A12Kernel

local instance [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => decidable_of_iff (a = b) (by simp)
  | .error a, .error b => decidable_of_iff (a = b) (by simp)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

private def row (parent child : Nat) : Env := [(10, parent), (20, child)]
private def occupancy : FilterOccupancy := {
  levels := [none, some 10, none, some 20]
  occupied := [[1, 1, 1, 51], [1, 2, 1, 1]] }

example : occupancy.allowsAfter none (row 2 17) = true ∧
    occupancy.allowsAfter (some (row 1 51)) (row 2 17) = true ∧
    occupancy.allowsAfter (some (row 2 1)) (row 2 17) = false ∧
    { occupancy with occupied := occupancy.occupied ++ [[1, 2, 1, 17]] }.allowsAfter
      (some (row 2 1)) (row 2 17) = true := by decide

private def reference (field : FieldId) : HavingNumberRef :=
  { origin := .inner, field := { id := field, info := { scale := 0, signed := true } } }
private def positive : CorrelatedHaving := .compareNumbers .greaterThan (reference 0) (reference 1)
private def number (value : Int) : CheckedCell :=
  { rawPresent := true, parsed := some (.num value), findings := [] }
private def context (value : Env → Except CorrelationRuntimeFault Int) :
    ResolvingCorrelationContext CorrelationRuntimeFault :=
  { ({ read := fun _ _ => number 0 } : CorrelationContext).asResolving with
    read := fun env field => if field == 0 then number <$> value env else pure (number 0) }
private def trace (value : Env → Except CorrelationRuntimeFault Int) (candidates : List Env)
    (sparse : Option FilterOccupancy := some occupancy) :
    Except CorrelationRuntimeFault (ComputationHavingScanResult (List Env) Unit) :=
  positive.scanComputationResolving (context value) []
    (fun visited env => pure (.inl (visited ++ [env]))) candidates [] sparse

example : trace (fun env => if env == row 2 2 then .error .valueFailure else pure 1)
      [row 1 51, row 2 1, row 2 2] = .ok (.exhausted [row 1 51, row 2 1]) ∧
    trace (fun env => if env == row 2 2 then .error .valueFailure else pure 1)
      [row 1 51, row 2 1, row 2 2] none = .error .valueFailure := by native_decide

example : trace (fun env => if env == row 2 2 then .error .valueFailure
      else pure (if env == row 2 1 then 0 else 1))
      [row 1 51, row 2 1, row 2 2] = .error .valueFailure ∧
    trace (fun env => if env == row 2 2 then .error .valueFailure else pure 0)
      [row 2 1, row 2 2] = .error .valueFailure := by native_decide

private def stopAfterFirst (candidates : List Env) : Except CorrelationRuntimeFault
    (ComputationHavingScanResult Unit Env) :=
  positive.scanComputationResolving
    (context fun env => if env == row 2 1 then .error .valueFailure else pure 1) []
    (fun _ env => pure (.inr env)) candidates () (some occupancy)

example : stopAfterFirst [row 1 1, row 1 2, row 2 1] = .error .valueFailure ∧
    stopAfterFirst [row 1 1, row 1 51, row 2 1] = .ok (.terminated (row 1 1)) := by native_decide

example : positive.selectEnvironmentsResolving
      (context fun env => if env == row 2 2 then .error .valueFailure else pure 1) []
      [row 1 51, row 2 1, row 2 2] (some occupancy) = .ok [row 1 51, row 2 1] ∧
    positive.selectEnvironmentsResolving
      (context fun env => if env == row 2 2 then .error .valueFailure
        else pure (if env == row 2 1 then 0 else 1)) []
      [row 1 51, row 2 1, row 2 2] (some occupancy) = .error .valueFailure := by native_decide

private def model : FlatModel := {
  fields := []
  repeatableGroups := [
    { level := 10, path := ["Form", "Outer"], repeatability := some 2 },
    { level := 20, path := ["Form", "Outer", "Fixed", "Inner"], repeatability := some 51 },
    { level := 30, path := ["Form", "Other"], repeatability := some 2 },
    { level := 40, path := ["Form", "Other", "Fixed", "Items"], repeatability := some 51 },
    { level := 50, path := ["Form", "Other", "Items"], repeatability := some 51 }] }
private def path : StarPath := { axes := [
  { level := 10, repeatability := some 2 }, { level := 20, repeatability := some 51 }], firstStar := 0 }
private def domain (width : Nat) (extra : List RowAddr := []) : Option A12Kernel.FilterTraversal :=
  (model.filterTraversal path ([{ group := 10, path := [1] }, { group := 10, path := [2] },
    { group := 20, path := [1, width] },
    { group := 20, path := [2, 1] }] ++ extra) []).toOption

example : (domain 50).map (·.occupancy.isSome) = some false ∧
    (domain 51).map (·.occupancy.isSome) = some true ∧
    (domain 51).map (·.candidates.length) = some 102 := by native_decide

example : (model.filterTraversal { path with firstStar := 1 }
      [{ group := 10, path := [1] }, { group := 10, path := [2] },
        { group := 20, path := [1, 51] }] [(10, 2)]).toOption.map
      (fun traversal => (traversal.candidates.length, traversal.occupancy.isSome)) = some (51, false) ∧
    (model.filterTraversal path [{ group := 10, path := [2] },
      { group := 20, path := [1, 51] }] [] .requireSmall).toOption = none := by native_decide

private def permits (extra : List RowAddr) : Option Bool := do
  let domain ← domain 51 extra
  let occupancy ← domain.occupancy
  pure (occupancy.allowsAfter (some (row 2 1)) (row 2 17))

example : permits [] = some false ∧
    permits [{ group := 40, path := [2, 17] }] = some true ∧
    permits [{ group := 50, path := [2, 17] }] = some false := by native_decide

end A12Kernel.Conformance.FilterTraversal
