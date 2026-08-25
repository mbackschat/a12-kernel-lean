import A12Kernel.Elaboration.CurrentRepetitionNumberToStringRelation

/-! # CurrentRepetition Number-to-String cascade locks -/

namespace A12Kernel.Conformance.CurrentRepetitionNumberToString

open A12Kernel

private def base : FlatFieldDecl := {
  id := 1
  groupPath := ["Shipment", "Lines"]
  name := "Base"
  policy := { kind := .number { scale := 0, signed := true } }
  repeatableScope := [10]
}

private def first : FlatFieldDecl := { base with id := 2, name := "First" }

private def second : FlatFieldDecl := {
  id := 3
  groupPath := ["Shipment", "Lines"]
  name := "Second"
  policy := { kind := .string }
  repeatableScope := [10]
}

private def lines : RepeatableGroupDecl := {
  level := 10
  path := ["Shipment", "Lines"]
  repeatability := some 10
}

private def other : RepeatableGroupDecl := {
  level := 20
  path := ["Shipment", "Other"]
  repeatability := some 10
}

private def model : FlatModel := {
  fields := [base, first, second]
  repeatableGroups := [lines, other]
}

private def bare (field : String) : SurfaceFieldPath := {
  base := .relative 0
  groups := []
  field
}

private def group : SurfaceGroupPath := {
  base := .absolute
  groups := ["Shipment", "Lines"]
}

private def otherGroup : SurfaceGroupPath := {
  base := .absolute
  groups := ["Shipment", "Other"]
}

private def plan? :
    Option (CheckedCurrentRepetitionNumberToStringCascade model) :=
  (checkCurrentRepetitionNumberToStringCascade model lines.path group
    first.id (bare "Base") second.id (bare "First")).toOption

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def numericCell (field : FieldId) (row : Nat) (value : Int) :
    ClassifiedCellInput := {
  address := { field, path := [row] }
  stored := toString value
  raw := .parsed (.num value)
  numericDecimal := some { unscaled := value, scale := 0 }
}

private def stringCell (row : Nat) (value : String) :
    ClassifiedCellInput := {
  address := { field := second.id, path := [row] }
  stored := value
  raw := .parsed (.str value)
}

private def checkedInput? (rows : List Nat)
    (cells : List ClassifiedCellInput) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := rows.map fun row =>
      { group := lines.level, path := [row] }
    cells
  }).toOption

private def twoRowInput? (firstBase : ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  checkedInput? [1, 2] [
    firstBase,
    numericCell first.id 1 70,
    stringCell 1 "old1",
    numericCell base.id 2 11,
    numericCell first.id 2 110,
    stringCell 2 "old2"]

private def rowOutcomes? (firstBase : ClassifiedCellInput) :
    Option (List
      (Nat × CellAddr × NumericTargetOutcome × CellAddr × StringTargetOutcome)) := do
  let plan <- plan?
  let input <- twoRowInput? firstBase
  let outcomes <- plan.execute prepared.patterns input |>.toOption
  pure (outcomes.rows.map fun row =>
    (row.coordinate, row.number.targetField, row.number.outcome,
      row.string.targetField, row.string.outcome))

private def phasedOutcomes? (firstBase : ClassifiedCellInput) :
    Option (List Nat × List (CellAddr × NumericTargetOutcome) ×
      List (CellAddr × StringTargetOutcome)) := do
  let plan <- plan?
  let input <- twoRowInput? firstBase
  let number <- plan.executeNumberPhaseWithRead input input.read |>.toOption
  let string <- plan.executeStringPhase prepared.patterns input number |>.toOption
  pure (number.coordinates,
    number.outcomes.map fun outcome =>
      (outcome.targetField, outcome.outcome),
    string.map fun outcome => (outcome.targetField, outcome.outcome))

private def encounterOrderOutcomes? :
    Option (List
      (Nat × CellAddr × NumericTargetOutcome × CellAddr × StringTargetOutcome)) := do
  let plan <- plan?
  let input <- checkedInput? [3, 1, 2] [
    numericCell base.id 1 7,
    numericCell first.id 1 70,
    stringCell 1 "old1",
    numericCell base.id 2 11,
    numericCell first.id 2 110,
    stringCell 2 "old2",
    numericCell base.id 3 13,
    numericCell first.id 3 130,
    stringCell 3 "old3"]
  let outcomes <- plan.execute prepared.patterns input |>.toOption
  pure (outcomes.rows.map fun row =>
    (row.coordinate, row.number.targetField, row.number.outcome,
      row.string.targetField, row.string.outcome))

private def stored (text : String) (nonempty : text ≠ "") : StoredString :=
  { text, nonempty }

/- Analyze keeps the structural coordinate separate from the two real cross-family field edges. -/
example :
    plan?.map CheckedCurrentRepetitionNumberToStringCascade.analyze = some {
      structuralGroup := lines.path
      scope := [lines.level]
      fieldDependencies := [
        (first.id, [base.id]),
        (second.id, [first.id])]
    } := by
  native_decide

/- Distinct seeded rows expose each newly computed Number only to the String conversion at its own address. -/
example :
    rowOutcomes? (numericCell base.id 1 7) = some [
      (1, { field := first.id, path := [1] },
        .accepted { unscaled := 7, scale := 0 },
        { field := second.id, path := [1] },
        .accepted (stored "7" (by decide))),
      (2, { field := first.id, path := [2] },
        .accepted { unscaled := 11, scale := 0 },
        { field := second.id, path := [2] },
        .accepted (stored "11" (by decide)))] := by
  native_decide

/- The explicit phase boundary retains every Number completion before the dependent String phase reads it, rather than re-reading stale seeded targets. -/
example :
    phasedOutcomes? (numericCell base.id 1 7) = some (
      [1, 2],
      [({ field := first.id, path := [1] },
          .accepted { unscaled := 7, scale := 0 }),
        ({ field := first.id, path := [2] },
          .accepted { unscaled := 11, scale := 0 })],
      [({ field := second.id, path := [1] },
          .accepted (stored "7" (by decide))),
        ({ field := second.id, path := [2] },
          .accepted (stored "11" (by decide)))]) := by
  native_decide

/- A wider finite input preserves physical encounter order rather than sorting by coordinate. -/
example :
    encounterOrderOutcomes? = some [
      (3, { field := first.id, path := [3] },
        .accepted { unscaled := 13, scale := 0 },
        { field := second.id, path := [3] },
        .accepted (stored "13" (by decide))),
      (1, { field := first.id, path := [1] },
        .accepted { unscaled := 7, scale := 0 },
        { field := second.id, path := [1] },
        .accepted (stored "7" (by decide))),
      (2, { field := first.id, path := [2] },
        .accepted { unscaled := 11, scale := 0 },
        { field := second.id, path := [2] },
        .accepted (stored "11" (by decide)))] := by
  native_decide

/- Numeric empty substitution precedes the reached String conversion and stays local to its row. -/
example :
    rowOutcomes? {
      address := { field := base.id, path := [1] }
      stored := ""
      raw := .presentEmpty
    } = some [
      (1, { field := first.id, path := [1] },
        .accepted { unscaled := 0, scale := 0 },
        { field := second.id, path := [1] },
        .accepted (stored "0" (by decide))),
      (2, { field := first.id, path := [2] },
        .accepted { unscaled := 11, scale := 0 },
        { field := second.id, path := [2] },
        .accepted (stored "11" (by decide)))] := by
  native_decide

/- Reached Number poison becomes cause-blind String dependency poison without aborting another row. -/
example :
    rowOutcomes? {
      address := { field := base.id, path := [1] }
      stored := "bad"
      raw := .rejected .malformed
    } = some [
      (1, { field := first.id, path := [1] },
        .inheritedPoison .malformed,
        { field := second.id, path := [1] },
        .poison .computedDependency),
      (2, { field := first.id, path := [2] },
        .accepted { unscaled := 11, scale := 0 },
        { field := second.id, path := [2] },
        .accepted (stored "11" (by decide)))] := by
  native_decide

/- A wrong structural group and a String consumer that bypasses the Number producer fail before execution. -/
example :
    (match checkCurrentRepetitionNumberToStringCascade model lines.path otherGroup
        first.id (bare "Base") second.id (bare "First") with
      | .error (.groupMismatch source declaring) =>
          source == other.path && declaring == lines.path
      | _ => false) = true ∧
    (match checkCurrentRepetitionNumberToStringCascade model lines.path group
        first.id (bare "Base") second.id (bare "Base") with
      | .error (.dependency expected actual) =>
          expected == first.id && actual == base.id
      | _ => false) = true := by
  native_decide

/- No physical target row remains explicit insufficient information. -/
example :
    (do
      let plan <- plan?
      let input <- checkedInput? [] []
      pure (match plan.execute prepared.patterns input with
        | .error (.rowCardinality 0) => true
        | _ => false)) = some true := by
  native_decide

private def nestedPath : GroupPath := ["Shipment", "Lines", "Entries"]

private def nestedBase : FlatFieldDecl := {
  base with
  groupPath := nestedPath
  repeatableScope := [10, 20]
}

private def nestedFirst : FlatFieldDecl := {
  first with
  groupPath := nestedPath
  repeatableScope := [10, 20]
}

private def nestedSecond : FlatFieldDecl := {
  second with
  groupPath := nestedPath
  repeatableScope := [10, 20]
}

private def nestedModel : FlatModel := {
  fields := [nestedBase, nestedFirst, nestedSecond]
  repeatableGroups := [lines, {
    level := 20
    path := nestedPath
    repeatability := some 10
  }]
}

private def nestedGroup : SurfaceGroupPath := {
  base := .absolute
  groups := nestedPath
}

/- A valid two-level model retains its complete scope and both typed field edges. -/
example :
    (checkCurrentRepetitionNumberToStringCascade nestedModel nestedPath
      nestedGroup nestedFirst.id (bare "Base") nestedSecond.id
      (bare "First")).toOption.map
        CheckedCurrentRepetitionNumberToStringCascade.analyze = some {
          structuralGroup := nestedPath
          scope := [10, 20]
          fieldDependencies := [
            (nestedFirst.id, [nestedBase.id]),
            (nestedSecond.id, [nestedFirst.id])]
        } := by
  native_decide

end A12Kernel.Conformance.CurrentRepetitionNumberToString
