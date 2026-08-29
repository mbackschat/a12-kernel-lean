import A12Kernel.Elaboration.AddressedFieldValueAsString

/-! # Addressed `FieldValueAsString` locks

The matrix separates decimal- versus String-valued Number storage, absent versus present-empty input, local formal poison, target checking, exact row addresses, source-relative result classification, and retained-action application.
-/

namespace A12Kernel.Conformance.AddressedFieldValueAsString

open A12Kernel

private def firstTarget : CellAddr := { field := 2, path := [1] }

private def secondTarget : CellAddr := { field := 2, path := [2] }

private def value250 : StoredString := ⟨"250", by decide⟩

private def valueStale : StoredString := ⟨"stale", by decide⟩

private def addressedView :
    StringComputationRunView FormalCause CellAddr :=
  StringComputationRunView.fromSourcedOutcomes
    ([] : List FormalCause)
    [
      {
        targetField := firstTarget
        outcome := .accepted value250
        source := .absent
      },
      {
        targetField := secondTarget
        outcome := .noValue
        source := .presentValue valueStale
      }
    ]

/- Exact target keys survive source-relative classification and retained-action application. -/
example : (do
    let destination : StringComputationDestination CellAddr :=
      fun _ => .absent
    let applied ← (addressedView.applyTo destination).toOption
    pure (addressedView.withChanges.map (·.targetField),
      addressedView.cleared, applied firstTarget, applied secondTarget)) =
    some ([firstTarget], [secondTarget], .presentValue value250,
      .presentEmpty) := by
  native_decide

private def amount : FlatFieldDecl := {
  id := 1
  groupPath := ["Order", "Rows"]
  name := "Amount"
  policy := { kind := .number { scale := 2, signed := true } }
  repeatableScope := [10]
}

private def text : FlatFieldDecl := {
  id := 2
  groupPath := ["Order", "Rows"]
  name := "Text"
  policy := { kind := .string }
  stringPolicy := { maxLength := some 4 }
  repeatableScope := [10]
}

private def outerAmount : FlatFieldDecl := {
  id := 3
  groupPath := ["Order"]
  name := "OuterAmount"
  policy := { kind := .number { scale := 2, signed := true } }
}

/-- A real declared group strictly below the target's own group, so the placement separator below
refuses a genuine group rather than an invented path. -/
private def deeperAmount : FlatFieldDecl := {
  id := 4
  groupPath := ["Order", "Rows", "Deeper"]
  name := "DeeperAmount"
  policy := { kind := .number { scale := 2, signed := true } }
  repeatableScope := [10]
}

private def model : FlatModel := {
  fields := [amount, text, outerAmount, deeperAmount]
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

private def operation? : Option (CheckedAddressedFieldValueAsString model) :=
  (checkAddressedFieldValueAsString
    model ["Order", "Rows"] text.id (bare "Amount")).toOption

private def rows : List RowAddr :=
  [{ group := 10, path := [1] }, { group := 10, path := [2] }]

private def cell (field : FieldId) (path : List Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := { field, path }, stored, raw }

private def decimalCell (path : List Nat) (stored : String)
    (unscaled scale : Int) (raw : RawCell) : ClassifiedCellInput := {
  address := { field := amount.id, path }
  stored
  raw
  numericDecimal := some { unscaled, scale }
}

private def checkedDocument (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := rows
    cells
  }).toOption

private def outcomes?
    (cells : List ClassifiedCellInput) :
    Option (List (SourcedStringTargetOutcome CellAddr)) := do
  let operation ← operation?
  let input ← checkedDocument cells
  (operation.execute prepared.patterns input).toOption

private def result?
    (cells : List ClassifiedCellInput) :
    Option (StringComputationRunView FormalCause CellAddr) := do
  let operation ← operation?
  let input ← checkedDocument cells
  (operation.executeResult prepared.patterns input
    ([] : List FormalCause)).toOption

private def addressAt (field : FieldId) (row : Nat) : CellAddr :=
  { field, path := [row] }

private def stored250 : StoredString := ⟨"250", by decide⟩

private def stored350 : StoredString := ⟨"3.50", by decide⟩

private def stored2 : StoredString := ⟨"2", by decide⟩

private def stored12345 : StoredString := ⟨"12345", by decide⟩

/- The checked authoring route is exactly a repeatable Number-to-ordinary-String assignment whose operand scope the target's scope binds; a wrong-kind source and a nonrepeatable target fail closed, while an outer-scope Number source is admitted. -/
example :
    operation?.isSome = true ∧
    (match checkAddressedFieldValueAsString
        model ["Order", "Rows"] text.id (bare "Text") with
      | .error (.sourceKindMismatch path .string) => path == text.path
      | _ => false) = true ∧
    (checkAddressedFieldValueAsString
      model ["Order", "Rows"] text.id (parent "OuterAmount")).isOk = true := by
  native_decide

/- Placement is containment, not group equality: an ancestor declaring group admits the target, a declared group strictly below it does not, and an unrepresentable declaring group is refused before containment can vacuously admit everything. -/
example :
    (checkAddressedFieldValueAsString
      model ["Order"] text.id (bare "OuterAmount")).isOk = true ∧
    (match checkAddressedFieldValueAsString
        model ["Order", "Rows", "Deeper"] text.id (bare "DeeperAmount") with
      | .error (.targetOutsideDeclaringGroup path declaringGroup) =>
          path == text.path && declaringGroup == ["Order", "Rows", "Deeper"]
      | _ => false) = true ∧
    (match checkAddressedFieldValueAsString
        model [] text.id (bare "Amount") with
      | .error (.target (.invalidRuleGroup group)) => group == []
      | _ => false) = true ∧
    (match checkAddressedFieldValueAsString
        model ["Other"] text.id (bare "Amount") with
      | .error (.targetOutsideDeclaringGroup path _) => path == text.path
      | _ => false) = true := by
  native_decide

/- Placement and operand resolution are two gates, not one. Moving the declaration to the ancestor without re-spelling its operand still refuses, but on the source channel as an unresolvable entity rather than as a placement refusal. The [declaring-group gate checkpoint](../../docs/SOURCES.md#src-computation-declaring-group-gate) measures that pair as `MVK_INVALID_ENTITY` against `MVK_ERROR_FIELD_NOT_IN_RULEGROUP`, and records misattributing the first to the second as the origin of the superseded parenthood reading. -/
example :
    (match checkAddressedFieldValueAsString model ["Order"] text.id (bare "Amount") with
      | .error (.source (.invalidEntity reference)) => reference.field == "Amount"
      | _ => false) = true ∧
    (checkAddressedFieldValueAsString
      model ["Order"] text.id (bare "OuterAmount")).isOk = true := by
  native_decide

/- Decimal-valued input selects stripped formal-read text while String-valued Number input remains verbatim, and the two rows cannot alias. -/
example :
    outcomes? [
      decimalCell [1] "250.00" 25000 2 (.parsed (.num 250)),
      cell amount.id [2] "3.50" (.parsed (.num (7 / 2)))
    ] = some [
      {
        targetField := addressAt text.id 1
        outcome := .accepted stored250
        source := .absent
      },
      {
        targetField := addressAt text.id 2
        outcome := .accepted stored350
        source := .absent
      }
    ] := by
  native_decide

/- Absent and present-empty Number sources both yield standalone no-value; source-filled exact targets mint retained clears that apply even to an absent destination. -/
example : (do
    let view ← result? [
      cell amount.id [2] "" .presentEmpty,
      cell text.id [1] "old1" (.parsed (.str "old1")),
      cell text.id [2] "old2" (.parsed (.str "old2"))
    ]
    let destination : StringComputationDestination CellAddr := fun _ => .absent
    let applied ← (view.applyTo destination).toOption
    pure (view.cleared, applied (addressAt text.id 1),
      applied (addressAt text.id 2))) =
      some ([addressAt text.id 1, addressAt text.id 2],
        .presentEmpty, .presentEmpty) := by
  native_decide

/- Formal poison is local to its exact addressed source; the other row still reads and stores normally. -/
example :
    (outcomes? [
      cell amount.id [1] "250.000" (.rejected .declaredConstraint),
      cell amount.id [2] "2" (.parsed (.num 2))
    ]).map (·.map fun entry => (entry.targetField, entry.outcome)) =
      some [
        (addressAt text.id 1, .poison .declaredConstraint),
        (addressAt text.id 2, .accepted stored2)
      ] := by
  native_decide

/- The declaration-owned String target policy runs after the addressed Number read without affecting a neighboring row. -/
example :
    (outcomes? [
      cell amount.id [1] "12345" (.parsed (.num 12345)),
      cell amount.id [2] "2" (.parsed (.num 2))
    ]).map (·.map fun entry => (entry.targetField, entry.outcome)) =
      some [
        (addressAt text.id 1, .errored stored12345 .tooLong),
        (addressAt text.id 2, .accepted stored2)
      ] := by
  native_decide

end A12Kernel.Conformance.AddressedFieldValueAsString
