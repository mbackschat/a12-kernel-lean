import A12Kernel.Elaboration.AddressedFieldValueAsNumber

/-! # Addressed `FieldValueAsNumber` locks

The matrix separates absent from present-empty String input, valid checked text, row-local formal poison, Number target rejection, and exact result addresses.
-/

namespace A12Kernel.Conformance.AddressedFieldValueAsNumber

open A12Kernel

private def code : FlatFieldDecl := {
  id := 1
  groupPath := ["Order", "Rows"]
  name := "Code"
  policy := { kind := .string }
  stringPolicy := { maxLength := some 15 }
  stringPatternSource := some asciiDigitsPatternSource
  repeatableScope := [10]
}

private def amount : FlatFieldDecl := {
  id := 2
  groupPath := ["Order", "Rows"]
  name := "Amount"
  policy := { kind := .number { scale := 0, signed := false } }
  numericTargetConstraints := { maximum := some 99 }
  repeatableScope := [10]
}

private def outerCode : FlatFieldDecl := {
  code with
    id := 3
    groupPath := ["Order"]
    name := "OuterCode"
    repeatableScope := []
}

private def wrong : FlatFieldDecl := {
  amount with
    id := 4
    name := "Wrong"
}

private def model : FlatModel := {
  fields := [code, amount, outerCode, wrong]
  repeatableGroups := [{
    level := 10
    path := ["Order", "Rows"]
    repeatability := some 2
  }]
}

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def parent (field : String) : SurfaceFieldPath :=
  { base := .relative 1, groups := [], field }

private def operation? : Option (CheckedAddressedFieldValueAsNumber model) :=
  (checkAddressedFieldValueAsNumber
    model ["Order", "Rows"] amount.id (bare "Code")).toOption

private def rows : List RowAddr :=
  [{ group := 10, path := [1] }, { group := 10, path := [2] }]

private def cell (field : FieldId) (path : List Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := { field, path }, stored, raw }

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

private def stored (unscaled : Int) : StoredNumber :=
  { unscaled, scale := 0 }

/- The checked authoring route is exactly same-scope, repeatable, String-to-Number; wrong-kind and noniterating String sources fail closed. -/
example :
    operation?.isSome = true ∧
    (match checkAddressedFieldValueAsNumber
        model ["Order", "Rows"] amount.id (bare "Wrong") with
      | .error (.sourceKindMismatch path .number) => path == wrong.path
      | _ => false) = true ∧
    (match checkAddressedFieldValueAsNumber
        model ["Order", "Rows"] amount.id (parent "OuterCode") with
      | .error (.scopeMismatch targetPath sourcePath) =>
          targetPath == amount.path && sourcePath == outerCode.path
      | _ => false) = true := by
  native_decide

/- Absent and present-empty checked String cells are distinct inputs but both convert to the real Number zero at their exact row addresses. -/
example :
    outcomes? [
      cell code.id [2] "" .presentEmpty
    ] = some [
      {
        targetField := addressAt amount.id 1
        outcome := .accepted (stored 0)
        source := .absent
      },
      {
        targetField := addressAt amount.id 2
        outcome := .accepted (stored 0)
        source := .absent
      }
    ] := by
  native_decide

/- A valid checked token converts exactly, while a neighboring value that exceeds the Number target policy is retained as a rejected attempt. -/
example :
    (outcomes? [
      cell code.id [1] "7" (.parsed (.str "7")),
      cell code.id [2] "123" (.parsed (.str "123"))
    ]).map (·.map fun entry => (entry.targetField, entry.outcome)) =
      some [
        (addressAt amount.id 1, .accepted (stored 7)),
        (addressAt amount.id 2, .rejected (stored 123) .aboveMaximum)
      ] := by
  native_decide

/- A token outside the statically required String pattern is formal poison before conversion; it remains local to its row. -/
example :
    (outcomes? [
      cell code.id [1] "12A" (.parsed (.str "12A")),
      cell code.id [2] "7" (.parsed (.str "7"))
    ]).map (·.map fun entry => (entry.targetField, entry.outcome)) =
      some [
        (addressAt amount.id 1, .inheritedPoison .declaredConstraint),
        (addressAt amount.id 2, .accepted (stored 7))
      ] := by
  native_decide

/- Source-relative result classification keeps both exact addresses: poison clears the filled first target, while the target-rejected second row remains an error. -/
example :
    (do
      let view ← result? [
        cell code.id [1] "12A" (.parsed (.str "12A")),
        cell amount.id [1] "9" (.parsed (.num 9)),
        cell code.id [2] "123" (.parsed (.str "123"))
      ]
      pure (view.cleared, view.withErrors)) =
      some (
        [addressAt amount.id 1],
        [{
          targetField := addressAt amount.id 2
          attempted := stored 123
          cause := .aboveMaximum
        }]) := by
  native_decide

end A12Kernel.Conformance.AddressedFieldValueAsNumber
