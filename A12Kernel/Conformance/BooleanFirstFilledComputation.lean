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

private def unrelated : FlatFieldDecl := {
  target with id := 6, name := "Unrelated"
}

/-- A fixed Boolean target in a group the declaring group does not contain. -/
private def otherGroupTarget : FlatFieldDecl := {
  target with id := 7, name := "OtherApproved", groupPath := ["Summary"]
}

private def model : FlatModel := {
  fields := [target, source, confirmSource, repeatedTarget, nestedSource,
    unrelated, otherGroupTarget]
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

private def document? (targetStored sourceStored : Option String)
    (unrelatedStored : String := "false") : Option (CheckedDocument model) :=
  let placed (field : FlatFieldDecl) (stored : String)
      (path : List Nat := []) : ClassifiedCellInput := {
    address := { field := field.id, path }
    stored
    raw := classifyStoredBooleanText stored
  }
  checkDocument prepared "en_US" {
    instantiatedRows := [{ group := 10, path := [1] }]
    cells := (targetStored.map (placed target)).toList ++
      (sourceStored.map (fun stored => placed source stored [1])).toList ++
      [placed unrelated unrelatedStored]
  } |>.toOption

private def resultView? (input : CheckedDocument model)
    (residualMessages : List FormalCause := []) := do
  let operation ← checked? target.id (star "Approved")
  operation.executeResult input residualMessages |>.toOption

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

/- Typed source equality determines the changed subset before application; an unchanged success remains inert against a different destination. -/
example : (do
    let input ← document? (some "true") (some "true")
    let destination ← document? (some "false") none
    let result ← resultView? input
    let applied := result.applyToChecked destination
    pure (result.withoutErrors, result.withChanges, result.withErrors,
      applied target.id, applied unrelated.id)) =
  some ([{ targetField := target.id, value := true }], [], [],
    .presentValue false, .presentValue false) := by
  native_decide

/- A changed Boolean value overwrites only the exact checked target. -/
example : (do
    let input ← document? (some "false") (some "true")
    let destination ← document? (some "false") none
    let result ← resultView? input
    let applied := result.applyToChecked destination
    pure (result.withChanges, applied target.id, applied unrelated.id)) =
  some ([{ targetField := target.id, value := true }],
    .presentValue true, .presentValue false) := by
  native_decide

/- Exhaustion clears a source-filled target and materializes an absent destination target; an absent source target mints no action. -/
example : (do
    let filledInput ← document? (some "false") none
    let absentInput ← document? none none
    let destination ← document? none none
    let filledResult ← resultView? filledInput
    let absentResult ← resultView? absentInput
    pure (filledResult.cleared,
      (filledResult.applyToChecked destination) target.id,
      absentResult.cleared,
      (absentResult.applyToChecked destination) target.id)) =
  some ([target.id], .presentEmpty, [], .absent) := by
  native_decide

/- Reached formal poison has no computed-error payload and applies through the source-filled clear action. -/
example : (do
    let input ← document? (some "false") (some "TRUE")
    let destination ← document? (some "true") none
    let result ← resultView? input
    let applied := result.applyToChecked destination
    pure (result.withoutErrors, result.withErrors, result.cleared,
      applied target.id, applied unrelated.id)) =
  some ([], [], [target.id], .presentEmpty, .presentValue false) := by
  native_decide

/- The independently supplied residual channel is retained and solely controls the Boolean result's error predicate. -/
example : (do
    let input ← document? (some "true") (some "true")
    let result ← resultView? input [.malformed]
    pure (result.formalErrorsInOperands, result.noErrorOccurred)) =
  some ([.malformed], false) := by
  native_decide

/- The checked boundary admits only a fixed Boolean target and one direct single-level starred Boolean source. Placement is not part of that boundary: a fixed target in `["Summary"]`, which the declaring group `["Review"]` does not contain, is admitted, because a star aggregate derives no iteration and the Kernel's containment gate cannot fire — measured at the [fixed-target star placement checkpoint](../../docs/SOURCES.md#src-fixed-target-star-placement). The repeatable target is still refused, on the fixed-target gate rather than on placement. -/
example :
    (checked? target.id (star "Approved")).isSome = true ∧
      (checked? otherGroupTarget.id (star "Approved")).isSome = true ∧
      (checked? target.id (star "Confirmed")).isNone = true ∧
      (checked? repeatedTarget.id (star "Approved")).isNone = true ∧
      (checked? target.id nestedStar).isNone = true := by
  native_decide

end A12Kernel.Conformance.BooleanFirstFilledComputation
