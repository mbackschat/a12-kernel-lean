import A12Kernel.Elaboration.AddressedStringLength

/-! # Addressed String `Length` locks — normalized UTF-16 length, zero, poison, target rejection, and exact addresses. -/

namespace A12Kernel.Conformance.AddressedStringLength

open A12Kernel

private def text : FlatFieldDecl := {
  id := 1
  groupPath := ["Order", "Rows"]
  name := "Text"
  policy := { kind := .string }
  stringPolicy := { lineBreaksPermitted := true, maxLength := some 6 }
  repeatableScope := [10]
}

private def length : FlatFieldDecl := {
  id := 2
  groupPath := ["Order", "Rows"]
  name := "Length"
  policy := { kind := .number { scale := 0, signed := false } }
  numericTargetConstraints := { maximum := some 4 }
  repeatableScope := [10]
}

private def outerText : FlatFieldDecl := {
  text with
    id := 3
    groupPath := ["Order"]
    name := "OuterText"
    repeatableScope := []
}

private def wrong : FlatFieldDecl := {
  length with
    id := 4
    name := "Wrong"
}

private def scaledLength : FlatFieldDecl := {
  length with
    id := 5
    name := "ScaledLength"
    policy := { kind := .number { scale := 2, signed := false } }
}

private def model : FlatModel := {
  fields := [text, length, outerText, wrong, scaledLength]
  repeatableGroups := [{
    level := 10
    path := ["Order", "Rows"]
    repeatability := some 5
  }]
}

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def parent (field : String) : SurfaceFieldPath :=
  { base := .relative 1, groups := [], field }

private def operation? : Option (CheckedAddressedStringLength model) :=
  (checkAddressedStringLength
    model ["Order", "Rows"] length.id (bare "Text")).toOption

private def rows : List RowAddr :=
  (List.range 5).map fun offset => { group := 10, path := [offset + 1] }

private def cell (field : FieldId) (row : Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := { field, path := [row] }, stored, raw }

private def checkedDocument (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := rows
    cells
  }).toOption

private def outcomes?
    (cells : List ClassifiedCellInput) :
    Option (List (SourcedNumericTargetOutcome CellAddr)) := do
  let operation ← operation?
  let input ← checkedDocument cells
  (operation.execute input).toOption

private def result?
    (cells : List ClassifiedCellInput) :
    Option (NumericComputationRunView
      (ComputationFormalMessage Unit) CellAddr) := do
  let operation ← operation?
  let input ← checkedDocument cells
  (operation.executeResult input (fun _ => ()) []).toOption

private def addressAt (field : FieldId) (row : Nat) : CellAddr :=
  { field, path := [row] }

private def stored (unscaled : Int) : StoredNumber := { unscaled, scale := 0 }

/- The checked route admits exactly an evaluated String source and scale-0 Number target in one nonempty repeatable scope. -/
example :
    operation?.isSome = true ∧
    (match checkAddressedStringLength
        model ["Order", "Rows"] length.id (bare "Wrong") with
      | .error (.sourceNotEvaluatedString path) => path == wrong.path
      | _ => false) = true ∧
    (match checkAddressedStringLength
        model ["Order", "Rows"] length.id (parent "OuterText") with
      | .error (.placement (.scopeMismatch targetPath sourcePath)) =>
          targetPath == length.path && sourcePath == outerText.path
      | _ => false) = true ∧
    (match checkAddressedStringLength
        model ["Order", "Rows"] scaledLength.id (bare "Text") with
      | .error (.scaleMismatch 2 0) => true
      | _ => false) = true := by
  native_decide

/- Empty placement is real zero. The supplementary character distinguishes UTF-16 length 4 from scalar length 3, while normalized CRLF distinguishes 5 from raw length 6 and reaches the target gate. -/
example :
    (outcomes? [
      cell text.id 2 "" .presentEmpty,
      cell text.id 3 "A😀B" (.parsed (.str "A😀B")),
      cell text.id 4 "AB\r\nCD" (.parsed (.str "AB\r\nCD")),
      cell text.id 5 "TOO-LONG" (.parsed (.str "TOO-LONG"))
    ]).map (·.map fun entry => (entry.targetField, entry.outcome)) =
      some [
        (addressAt length.id 1, .accepted (stored 0)),
        (addressAt length.id 2, .accepted (stored 0)),
        (addressAt length.id 3, .accepted (stored 4)),
        (addressAt length.id 4,
          .rejected (stored 5) .aboveMaximum),
        (addressAt length.id 5,
          .inheritedPoison .declaredConstraint)
      ] := by
  native_decide

/- Result classification preserves exact addresses across a changed UTF-16 value, normalized target rejection, and poison-cleared stale target. -/
example :
    (do
      let view ← result? [
        cell text.id 3 "A😀B" (.parsed (.str "A😀B")),
        cell length.id 3 "3" (.parsed (.num 3)),
        cell text.id 4 "AB\r\nCD" (.parsed (.str "AB\r\nCD")),
        cell text.id 5 "TOO-LONG" (.parsed (.str "TOO-LONG")),
        cell length.id 5 "2" (.parsed (.num 2))
      ]
      pure (view.cleared, view.withChanges.map
        fun entry => (entry.targetField, entry.value), view.withErrors)) =
      some (
        [addressAt length.id 5],
        [
          (addressAt length.id 1, stored 0),
          (addressAt length.id 2, stored 0),
          (addressAt length.id 3, stored 4)
        ],
        [{
          targetField := addressAt length.id 4
          attempted := stored 5
          cause := .aboveMaximum
        }]) := by
  native_decide

end A12Kernel.Conformance.AddressedStringLength
