import A12Kernel.Elaboration.BooleanFirstFilledComputation

/-! # Direct one-star Boolean `FirstFilledValue` computation locks -/

namespace A12Kernel.Conformance.BooleanFirstFilledComputation

open A12Kernel

private def target : FlatFieldDecl := {
  id := 1
  groupPath := ["Review"]
  name := "FirstApproved"
  policy := { kind := .boolean }
}

private def source : FlatFieldDecl := {
  id := 2
  groupPath := ["Review", "Rows"]
  name := "Approved"
  policy := { kind := .boolean }
  repeatableScope := [10]
}

private def confirmSource : FlatFieldDecl := {
  source with id := 3, name := "Confirmed", policy := { kind := .confirm }
}

private def repeatedTarget : FlatFieldDecl := {
  source with id := 4, name := "RepeatedTarget"
}

private def nestedSource : FlatFieldDecl := {
  source with
    id := 5
    groupPath := ["Review", "Rows", "Details"]
    name := "NestedApproved"
    repeatableScope := [10, 20]
}

private def model : FlatModel := {
  fields := [target, source, confirmSource, repeatedTarget, nestedSource]
  repeatableGroups := [
    { level := 10, path := ["Review", "Rows"], repeatability := some 4 },
    { level := 20, path := ["Review", "Rows", "Details"], repeatability := some 3 }]
}

private def star (field : String) : SurfaceStarFieldPath := {
  base := .absolute
  groups := [{ name := "Review" }, { name := "Rows", starred := true }]
  field
}

private def nestedStar : SurfaceStarFieldPath := {
  base := .absolute
  groups := [
    { name := "Review" },
    { name := "Rows", starred := true },
    { name := "Details", starred := true }]
  field := "NestedApproved"
}

private def checked? (targetField : FieldId) (authored : SurfaceStarFieldPath) :=
  (checkBooleanFirstFilledComputation model ["Review"] targetField authored).toOption

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def input? (sourceStored : Option String) : Option (CheckedDocument model) :=
  let sourceCell := sourceStored.map fun stored => {
    address := { field := source.id, path := [1] }
    stored
    raw := classifyStoredBooleanText stored
  }
  (checkDocument prepared "en_US" {
    instantiatedRows := [{ group := 10, path := [1] }]
    cells := [{
      address := { field := target.id, path := [] }
      stored := "false"
      raw := .parsed (.bool false)
    }] ++ sourceCell.toList
  }).toOption

private def result? (sourceStored : Option String) :
    Option FirstFilledBooleanComputationResult := do
  let operation ← checked? target.id (star "Approved")
  let input ← input? sourceStored
  operation.execute input |>.toOption

/- The externally measured empty selection clears a seeded false target, while a filled true source preserves true. -/
example :
    result? none = some .noValue ∧
      result? (some "true") = some (.value true) := by
  native_decide

/- False is a filled Boolean in the internal total account; external correspondence for this row remains pending. -/
example : result? (some "false") = some (.value false) := by
  native_decide

/- A reached malformed Boolean poisons rather than clearing; this internal branch is not externally calibrated by the source case. -/
example : result? (some "TRUE") = some (.poison .booleanToken) := by
  native_decide

/- The checked boundary admits only a fixed Boolean target and one direct single-level starred Boolean source. -/
example :
    (checked? target.id (star "Approved")).isSome = true ∧
      (checked? target.id (star "Confirmed")).isNone = true ∧
      (checked? repeatedTarget.id (star "Approved")).isNone = true ∧
      (checked? target.id nestedStar).isNone = true := by
  native_decide

end A12Kernel.Conformance.BooleanFirstFilledComputation
