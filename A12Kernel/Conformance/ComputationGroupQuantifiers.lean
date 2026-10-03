import A12Kernel.Elaboration.ComputationCondition

namespace A12Kernel.Conformance.ComputationGroupQuantifiers

local instance [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => decidable_of_iff (a = b) (by simp)
  | .error a, .error b => decidable_of_iff (a = b) (by simp)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

private def context (left right : CheckedCell) : ScalarComputationContext :=
  { read := fun field => if field == 1 then left else right }

private def empty : CheckedCell :=
  { rawPresent := false, parsed := none, findings := [] }

private def filled : CheckedCell :=
  { rawPresent := true, parsed := some (.num 1), findings := [] }

private def group : ComputationGroupOperand := {
  reference := { path := ["Form", "Group"], origin := .path, boundRepeatableScope := [] }
  content := { scope := [], fields := [2], rowLevels := [] }
  members := [2] }

private def guard (operator : GroupFillQuantifier) : ComputationCondition :=
  ComputationCondition.ofGroupList operator
    (.fieldFilled 1, .fieldNotFilled 1)
    [(.leaf (.groupPresence .filled group), .leaf (.groupPresence .notFilled group))]

example :
    ([.allGroupsFilled, .noGroupFilled, .atLeastOneGroupFilled,
      .notAllGroupsFilled, .groupsNotCollectivelyFilled].map fun op =>
      (guard op).evalChecked (context empty malformedCheckedCell)) =
      [.ok .notTrue, .ok .notTrue, .ok .holds, .ok .holds, .ok .holds] := by native_decide

example :
    (guard .atLeastOneGroupFilled).evalChecked (context malformedCheckedCell filled) =
      .ok (.poison .malformed) ∧
    (guard .allGroupsFilled).evalChecked (context empty malformedCheckedCell) =
      .ok .notTrue := by native_decide

example :
    (guard .groupsNotCollectivelyFilled).evalChecked (context filled empty) = .ok .holds ∧
    (guard .groupsNotCollectivelyFilled).evalChecked (context filled filled) = .ok .notTrue := by
  native_decide

private def starredGroup : ComputationGroupOperand := {
  reference := { path := ["Form", "Rows"], origin := .path, boundRepeatableScope := [10] }
  content := { scope := [10], fields := [], rowLevels := [10] }
  members := []
  starPath := some { axes := [{ level := 10, repeatability := some 2 }], firstStar := 0 } }

private def starredContext (rows : List RowAddr) : ScalarComputationContext := {
  read := fun _ => empty
  addressed := some {
    document := { rawCells := fun _ => none, instantiatedRows := rows }
    read := fun _ _ => empty } }

example :
    ComputationCondition.evalChecked (.leaf (.groupPresence .filled starredGroup))
      (starredContext [{ group := 10, path := [1] }]) = .ok .holds ∧
    ComputationCondition.evalChecked (.leaf (.groupPresence .notFilled starredGroup))
      (starredContext []) = .ok .holds := by native_decide

end A12Kernel.Conformance.ComputationGroupQuantifiers
