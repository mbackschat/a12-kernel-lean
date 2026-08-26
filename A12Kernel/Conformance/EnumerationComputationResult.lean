import A12Kernel.Elaboration.EnumerationComputationResult

/-! # Ordinary Enumeration computation result and application locks -/

namespace A12Kernel.Conformance.EnumerationComputationResult

open A12Kernel

private def enumeration : EnumerationDeclaration := {
  storedTokens := ["A", "B"]
}

private def enumerationField (id : FieldId) (name : String) : FlatFieldDecl := {
  id
  groupPath := ["Form"]
  name
  policy := { kind := .enumeration }
  enumeration := some enumeration
}

private def target := enumerationField 1 "Target"
private def source := enumerationField 2 "Source"
private def other := enumerationField 3 "Other"

private def model : FlatModel := {
  fields := [target, source, other]
}

private def prepared :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def bare (name : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field := name }

private def operation :=
  (elaborateEnumerationComputation model ["Form"] target.id
    (.field (.direct (bare "Source")))).toOption.get (by native_decide)

private def literalOperation :=
  (elaborateEnumerationComputation model ["Form"] target.id
    (.literal "B")).toOption.get (by native_decide)

private def placed (field : FlatFieldDecl) (stored : String) (raw : RawCell) :
    ClassifiedCellInput :=
  { address := { field := field.id, path := [] }, stored, raw }

private def document (targetCell sourceCell : Option (String × RawCell))
    (otherToken : String := "A") : Option (CheckedDocument model) :=
  let targetPlacement := targetCell.map fun cell => placed target cell.1 cell.2
  let sourcePlacement := sourceCell.map fun cell => placed source cell.1 cell.2
  checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := targetPlacement.toList ++ sourcePlacement.toList ++
      [placed other otherToken (.parsed (.enum otherToken))]
  } |>.toOption

private def value (token : String) : String × RawCell :=
  (token, .parsed (.enum token))

private def result? (input : CheckedDocument model) :
    Option (EnumerationComputationRunView model FormalCause) :=
  some (operation.executeResult input [])

/- Literal execution enters the same exact-token result boundary as a checked field source. -/
example : (do
    let input ← document (some (value "A")) none
    let result := literalOperation.executeResult input ([] : List FormalCause)
    pure result.string.withChanges) =
  some [{ targetField := target.id, value := ⟨"B", by decide⟩ }] := by
  native_decide

/- A changed exact token enters both successful channels relative to the immutable source target. -/
example : (do
    let input ← document (some (value "A")) (some (value "B"))
    let result ← result? input
    pure (result.string.withoutErrors, result.string.withChanges,
      result.string.withErrors, result.string.cleared)) =
  some ([{ targetField := target.id, value := ⟨"B", by decide⟩ }],
    [{ targetField := target.id, value := ⟨"B", by decide⟩ }], [], []) := by
  native_decide

/- Source-relative unchanged classification remains inert against a different destination value. -/
example : (do
    let input ← document (some (value "B")) (some (value "B"))
    let destination ← document (some (value "A")) none "B"
    let result ← result? input
    let applied ← result.applyToChecked destination |>.toOption
    pure (result.string.withChanges, applied target.id, applied other.id)) =
  some ([], .presentValue ⟨"A", by decide⟩,
    .presentValue ⟨"B", by decide⟩) := by
  native_decide

/- A retained changed token overwrites only its certified Enumeration target. -/
example : (do
    let input ← document (some (value "A")) (some (value "B"))
    let destination ← document (some (value "A")) none "A"
    let result ← result? input
    let applied ← result.applyToChecked destination |>.toOption
    pure (applied target.id, applied other.id)) =
  some (.presentValue ⟨"B", by decide⟩,
    .presentValue ⟨"A", by decide⟩) := by
  native_decide

/- Exhausted input clears a source-filled target and retained clearing materializes an absent destination target as present-empty. -/
example : (do
    let input ← document (some (value "A")) none
    let destination ← document none none "B"
    let result ← result? input
    let applied ← result.applyToChecked destination |>.toOption
    pure (result.string.cleared, applied target.id, applied other.id)) =
  some ([target.id], .presentEmpty,
    .presentValue ⟨"B", by decide⟩) := by
  native_decide

/- A reached invalid source token is cause-blind poison at the result boundary and clears only the computed target on application. -/
example : (do
    let input ← document (some (value "A"))
      (some ("C", .parsed (.enum "C")))
    let destination ← document (some (value "B")) none "A"
    let result ← result? input
    let applied ← result.applyToChecked destination |>.toOption
    pure (result.string.withoutErrors, result.string.withErrors,
      result.string.cleared, applied target.id, applied other.id)) =
  some ([], [], [target.id], .presentEmpty,
    .presentValue ⟨"A", by decide⟩) := by
  native_decide

end A12Kernel.Conformance.EnumerationComputationResult
