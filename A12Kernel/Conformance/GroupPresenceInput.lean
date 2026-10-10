import A12Kernel.Elaboration.GroupPresenceInput

namespace A12Kernel.Conformance.GroupPresenceInput

private def model : FlatModel := {
  fields := [{
    id := 1, groupPath := ["Form", "Rows", "Items"], name := "Value",
    repeatableScope := [10, 20], policy := { kind := .string } }]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 2 },
    { level := 20, path := ["Form", "Rows", "Items"], repeatability := some 2 }]
}

private def malformedAt (path : List Nat) : CheckedCellPlacement := {
  address := { field := 1, path }
  cell := { rawPresent := true, parsed := none, findings := [.malformed] }
}

private def project (path : List Nat) (outer : Nat := 1)
    (silent : Bool := false) (structural : Bool := false) :
    Option GroupPresenceState := do
  let input ← (model.groupPresenceInputFromSlice
    [{ group := 20, path }] (if silent then [] else [malformedAt path])
    ["Form", "Rows"] [(10, outer)] .fullyRelevant structural
    (if silent then [{ field := 1, path }] else [])).toOption
  pure input.derive

-- The bound/nested count capture separates cache errors from excess-row diagnostics;
-- these projection checks retain its in-capacity and parent-local controls (spec/10 §5).
example : project [1, 1] = some ⟨true, true, .fullyRelevant⟩ := by native_decide
example : project [1, 3] = some ⟨true, false, .fullyRelevant⟩ := by native_decide
example : project [3, 1] 3 = some ⟨true, false, .fullyRelevant⟩ := by native_decide
example : project [1, 1] 2 = some ⟨false, false, .fullyRelevant⟩ := by native_decide
example : project [1, 1] 1 true = some ⟨true, true, .fullyRelevant⟩ := by native_decide
example : project [1, 3] 1 true = some ⟨true, false, .fullyRelevant⟩ := by native_decide
example : project [1, 3] 1 false true = some ⟨true, true, .fullyRelevant⟩ := by native_decide

example : (match model.groupPresenceInputFromSlice [] [] ["Form", "Rows"] []
    .fullyRelevant false with
  | .error (.missingBinding 10) => true
  | _ => false) = true := by native_decide
example : (match model.groupPresenceInputFromSlice [] [] ["Missing"] []
    .fullyRelevant false with
  | .error (.unknownGroup ["Missing"]) => true
  | _ => false) = true := by native_decide

end A12Kernel.Conformance.GroupPresenceInput
