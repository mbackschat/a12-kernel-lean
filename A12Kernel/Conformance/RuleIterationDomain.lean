import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.NumberEntityList

namespace A12Kernel.Conformance.RuleIterationDomain

open A12Kernel

-- The 2026-10-04 iteration grid separates the product threshold from per-axis capacity:
-- 2×2 visits absent coordinates; 2×3 uses occupied prefixes and still starts each axis at 1.
example : RuleIterationDomain.coordinates [1, 2, 2] [] [1] =
    [[1, 1, 1], [1, 1, 2], [1, 2, 1], [1, 2, 2]] := by native_decide

example : RuleIterationDomain.coordinates [1, 2, 3] [] [1] =
    [[1, 1, 1]] := by native_decide

example : RuleIterationDomain.coordinates [1, 5] [] [1] =
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5]] := by native_decide

example : RuleIterationDomain.coordinates [1, 6] [] [1] =
    [[1, 1]] := by native_decide

-- Occupancy belongs to the whole document's coordinates, including another group's rows.
example : RuleIterationDomain.coordinates [1, 2, 3]
    [[1, 2, 2], [1, 1, 2]] [1] =
    [[1, 1, 1], [1, 1, 2], [1, 2, 1], [1, 2, 2]] := by native_decide

example : RuleIterationDomain.coordinates [1, 2, 1, 3]
    [[1, 2, 1, 2]] [1] =
    [[1, 1, 1, 1], [1, 2, 1, 1], [1, 2, 1, 2]] := by native_decide

-- Root dispatch is independent of occupancy and never creates a missing root instance.
example : RuleIterationDomain.coordinates [2, 3] [[2, 3]] [1] =
    [[1, 1]] := by native_decide

example : RuleIterationDomain.coordinates [2] [[1], [2], [3]] [3, 2, 1] =
    [[1], [2]] := by native_decide

example : RuleIterationDomain.coordinates [1, 2] [[1, 2]] [] = [] := by native_decide

example : RuleIterationDomain.coordinates [1, 6]
    [[1, 2], [1, 8]] [1] = [[1, 1], [1, 2]] := by native_decide

private def model : FlatModel := {
  fields := [
    { id := 0, groupPath := ["Form"], name := "Flag", policy := { kind := .string } },
    { id := 1, groupPath := ["Form", "Outer", "Inner"], name := "S",
      repeatableScope := [10, 11], policy := { kind := .string } },
    { id := 2, groupPath := ["Other", "Outer", "Inner"], name := "S",
      repeatableScope := [20, 21], policy := { kind := .string } },
    { id := 3, groupPath := ["Form", "Outer", "Inner"], name := "N",
      repeatableScope := [10, 11], policy := { kind := .number { scale := 0, signed := true } } }]
  repeatableGroups := [
    { level := 10, path := ["Form", "Outer"], repeatability := some 2 },
    { level := 11, path := ["Form", "Outer", "Inner"], repeatability := some 3 },
    { level := 20, path := ["Other", "Outer"], repeatability := some 2 },
    { level := 21, path := ["Other", "Outer", "Inner"], repeatability := some 3 }] }

private def checked (rootFilled : Bool) : Option (CheckedDocument model) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" {
    instantiatedRows := [{ group := 20, path := [1] }, { group := 21, path := [1, 1] }, { group := 21, path := [1, 2] }]
    cells := if rootFilled then [{ address := { field := 0, path := [] }, stored := "g", raw := .parsed (.str "g") }] else [] }).toOption

example : (checked true).bind (fun document =>
    (document.fullValidationRowEnvironments [10, 11]).toOption) =
    some [[(10, 1), (11, 1)], [(10, 1), (11, 2)]] := by native_decide

example : (checked false).bind (fun document =>
    (document.fullValidationRowEnvironments [10, 11]).toOption) = some [] := by native_decide

-- The new read view admits only domain-owned implicit rows. Physical topology and the
-- independently owned partial domain remain unchanged, as the root-gate grid requires.
example : (checked true).map (fun document =>
    (document.fullValidationAddressedCell [(10, 1), (11, 2)] 1).isOk &&
    !(document.fullValidationAddressedCell [(10, 2), (11, 2)] 1).isOk &&
    !(document.addressedCell [(10, 1), (11, 2)] 1).isOk &&
    (document.validationRowEnvironments [10, 11]).toOption == some []) = some true := by native_decide

example : (do
    let document ← checked true
    let declaration ← (model.lookupUniqueId 3).toOption
    let field ← declaration.toNumberField?
    let empty := match document.numberValueListCellAt .validation [(10, 1), (11, 2)] field true with
      | .ok .empty => true
      | _ => false
    pure (empty &&
      !(document.numberValueListCellAt .validation [(10, 1), (11, 2)] field).isOk &&
      !(document.numberValueListCellAt .computation [(10, 1), (11, 2)] field true).isOk &&
      !(document.numberValueListCellAt .validation [(10, 2), (11, 2)] field true).isOk)) =
    some true := by native_decide

end A12Kernel.Conformance.RuleIterationDomain
