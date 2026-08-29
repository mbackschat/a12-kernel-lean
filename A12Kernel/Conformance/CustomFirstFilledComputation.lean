import A12Kernel.Elaboration.CustomFirstFilledComputation

/-! # Direct one-star Custom `FirstFilledValue` computation locks -/

namespace A12Kernel.Conformance.CustomFirstFilledComputation

open A12Kernel

private def customType : CustomFieldTypeDeclaration := { name := "ReviewCode" }
private def otherType : CustomFieldTypeDeclaration := { name := "OtherCode" }

private def customField (id : FieldId) (groups : GroupPath) (name : String)
    (scope : List RepeatableLevel := [])
    (declared : CustomFieldTypeDeclaration := customType) : FlatFieldDecl := {
  id
  groupPath := groups
  name
  policy := { kind := .string }
  customType := some declared
  repeatableScope := scope
}

private def target := customField 1 ["Review"] "FirstCode"
private def source := customField 2 ["Review", "Rows"] "Code" [10]
private def ordinary : FlatFieldDecl := {
  source with id := 3, name := "Ordinary", customType := none
}
private def other :=
  customField 4 ["Review", "Rows"] "OtherCode" [10] otherType
private def repeatedTarget :=
  customField 5 ["Review", "Rows"] "RepeatedTarget" [10]
private def nestedSource :=
  customField 6 ["Review", "Rows", "Details"] "NestedCode" [10, 20]
private def unrelated := customField 7 ["Review"] "Unrelated"

/-- A fixed Custom target in a group the declaring group does not contain. -/
private def otherGroupTarget := customField 8 ["Summary"] "OtherCode"

private def model : FlatModel := {
  fields := [target, source, ordinary, other, repeatedTarget, nestedSource,
    unrelated, otherGroupTarget]
  repeatableGroups := [
    { level := 10, path := ["Review", "Rows"], repeatability := some 4 },
    { level := 20, path := ["Review", "Rows", "Details"],
      repeatability := some 3 }]
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
  field := "NestedCode"
}

private def rejection : RegisteredCustomRejection := {
  projectCode := "REVIEW_CODE_INVALID"
}

private def validator : RegisteredCustomFieldValidator := fun value _ =>
  if value == "BAD" then some rejection else none

private def world : World := {
  now := { epochMillis := 0 }
  customFieldValidator? := fun name =>
    if name == customType.name || name == otherType.name then some validator else none
}

private def checked? (targetField : FieldId) (authored : SurfaceStarFieldPath) :=
  (checkCustomFirstFilledComputation model ["Review"] targetField authored).toOption

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def input? (sourceStored : Option String) : Option (CheckedDocument model) :=
  let sourceCell := sourceStored.map fun stored => {
    address := { field := source.id, path := [1] }
    stored
    raw := RawCell.parsed (.str stored)
  }
  (checkDocument prepared "en_US" {
    instantiatedRows := [{ group := 10, path := [1] }]
    cells := [{
      address := { field := target.id, path := [] }
      stored := "SEED"
      raw := .parsed (.str "SEED")
    }] ++ sourceCell.toList
  }).toOption

private def result? (sourceStored : Option String) :
    Option TokenComputationResult := do
  let operation ← checked? target.id (star "Code")
  let input ← input? sourceStored
  operation.execute input |>.toOption

private def document? (targetStored sourceStored : Option String)
    (unrelatedStored : String := "KEEP") : Option (CheckedDocument model) :=
  let placed (field : FlatFieldDecl) (stored : String)
      (path : List Nat := []) : ClassifiedCellInput := {
    address := { field := field.id, path }
    stored
    raw := RawCell.parsed (.str stored)
  }
  checkDocument prepared "en_US" {
    instantiatedRows := [{ group := 10, path := [1] }]
    cells := (targetStored.map (placed target)).toList ++
      (sourceStored.map (fun stored => placed source stored [1])).toList ++
      [placed unrelated unrelatedStored]
  } |>.toOption

private def resultView? (input : CheckedDocument model) := do
  let operation ← checked? target.id (star "Code")
  operation.executeResult input ([] : List FormalCause) |>.toOption

/- The externally measured empty selection clears a seeded target, while the filled source preserves its exact bytes. -/
example :
    result? none = some .noValue ∧
      result? (some "A7") = some (.value "A7") := by
  native_decide

/- A reached registered rejection poisons through the already prepared checked cell; this branch remains externally uncalibrated. -/
example :
    result? (some "BAD") =
      some (.poison (.registeredCustomValidation rejection)) := by
  native_decide

/- The checked boundary admits only the same Custom type on a fixed target and direct single-level starred source. Placement is not part of that boundary: a fixed target in `["Summary"]`, which the declaring group `["Review"]` does not contain, is admitted, because a star aggregate derives no iteration and the Kernel's containment gate cannot fire — measured at the [fixed-target star placement checkpoint](../../docs/SOURCES.md#src-fixed-target-star-placement). The repeatable target is still refused, on the fixed-target gate rather than on placement. -/
example :
    (checked? target.id (star "Code")).isSome = true ∧
      (checked? otherGroupTarget.id (star "Code")).isSome = true ∧
      (checked? target.id (star "Ordinary")).isNone = true ∧
      (checked? target.id (star "OtherCode")).isNone = true ∧
      (checked? repeatedTarget.id (star "Code")).isNone = true ∧
      (checked? target.id nestedStar).isNone = true := by
  native_decide

/- A source-relative unchanged token remains inert against a different destination value. -/
example : (do
    let input ← document? (some "A7") (some "A7")
    let destination ← document? (some "OLD") none
    let result ← resultView? input
    let applied ← result.applyToChecked destination |>.toOption
    pure (result.string.withChanges, applied target.id,
      applied unrelated.id)) =
  some ([], .presentValue ⟨"OLD", by decide⟩,
    .presentValue ⟨"KEEP", by decide⟩) := by
  native_decide

/- A changed accepted token overwrites only the checked Custom target. -/
example : (do
    let input ← document? (some "SEED") (some "A7")
    let destination ← document? (some "OLD") none
    let result ← resultView? input
    let applied ← result.applyToChecked destination |>.toOption
    pure (result.string.withErrors, applied target.id,
      applied unrelated.id)) =
  some ([], .presentValue ⟨"A7", by decide⟩,
    .presentValue ⟨"KEEP", by decide⟩) := by
  native_decide

/- Exhaustion clears a source-filled target and its retained action materializes an absent destination target. -/
example : (do
    let input ← document? (some "SEED") none
    let destination ← document? none none
    let result ← resultView? input
    let applied ← result.applyToChecked destination |>.toOption
    pure (result.string.cleared, applied target.id,
      applied unrelated.id)) =
  some ([target.id], .presentEmpty,
    .presentValue ⟨"KEEP", by decide⟩) := by
  native_decide

/- A reached registered rejection stays cause-blind poison in the result channels and clears only the target on application. -/
example : (do
    let input ← document? (some "SEED") (some "BAD")
    let destination ← document? (some "OLD") none
    let result ← resultView? input
    let applied ← result.applyToChecked destination |>.toOption
    pure (result.string.withoutErrors, result.string.withErrors,
      result.string.cleared, applied target.id, applied unrelated.id)) =
  some ([], [], [target.id], .presentEmpty,
    .presentValue ⟨"KEEP", by decide⟩) := by
  native_decide

end A12Kernel.Conformance.CustomFirstFilledComputation
