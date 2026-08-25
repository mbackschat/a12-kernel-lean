import A12Kernel.Elaboration.CurrentRepetitionStringToNumber

/-! # CurrentRepetition String-to-Number cascade locks -/

namespace A12Kernel.Conformance.CurrentRepetitionStringToNumber

open A12Kernel

private def base : FlatFieldDecl := {
  id := 1
  groupPath := ["Shipment", "Lines"]
  name := "BaseNumber"
  policy := { kind := .number { scale := 0, signed := true } }
  repeatableScope := [10]
}

private def first : FlatFieldDecl := {
  id := 2
  groupPath := ["Shipment", "Lines"]
  name := "FirstString"
  policy := { kind := .string }
  stringPolicy := { maxLength := some 15 }
  stringPatternSource := some asciiDigitsPatternSource
  repeatableScope := [10]
}

private def second : FlatFieldDecl := {
  id := 3
  groupPath := ["Shipment", "Lines"]
  name := "SecondNumber"
  policy := { kind := .number { scale := 0, signed := false } }
  repeatableScope := [10]
}

private def otherString : FlatFieldDecl := {
  first with id := 4, name := "OtherString"
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
  fields := [base, first, second, otherString]
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
    Option (CheckedCurrentRepetitionStringToNumberCascade model) :=
  (checkCurrentRepetitionStringToNumberCascade model lines.path group
    first.id (bare "BaseNumber") second.id (.direct (bare "FirstString"))).toOption

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
  address := { field := first.id, path := [row] }
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
    stringCell 1 "70",
    numericCell second.id 1 700,
    numericCell base.id 2 11,
    stringCell 2 "110",
    numericCell second.id 2 1100]

private def rowOutcomes? (firstBase : ClassifiedCellInput) :
    Option (List
      (Nat × CellAddr × StringTargetOutcome × CellAddr × NumericTargetOutcome)) := do
  let plan <- plan?
  let input <- twoRowInput? firstBase
  let outcomes <- plan.execute prepared.patterns input |>.toOption
  pure (outcomes.rows.map fun row =>
    (row.coordinate, row.string.targetField, row.string.outcome,
      row.number.targetField, row.number.outcome))

private def encounterOrderOutcomes? :
    Option (List
      (Nat × CellAddr × StringTargetOutcome × CellAddr × NumericTargetOutcome)) := do
  let plan <- plan?
  let input <- checkedInput? [3, 1, 2] [
    numericCell base.id 1 7,
    stringCell 1 "70",
    numericCell second.id 1 700,
    numericCell base.id 2 11,
    stringCell 2 "110",
    numericCell second.id 2 1100,
    numericCell base.id 3 13,
    stringCell 3 "130",
    numericCell second.id 3 1300]
  let outcomes <- plan.execute prepared.patterns input |>.toOption
  pure (outcomes.rows.map fun row =>
    (row.coordinate, row.string.targetField, row.string.outcome,
      row.number.targetField, row.number.outcome))

private def storedString (text : String) (nonempty : text ≠ "") : StoredString :=
  { text, nonempty }

/- Analyze keeps the structural coordinate separate from the two cross-family field edges. -/
example :
    plan?.map CheckedCurrentRepetitionStringToNumberCascade.analyze = some {
      structuralGroup := lines.path
      scope := [lines.level]
      fieldDependencies := [
        (first.id, [base.id]),
        (second.id, [first.id])]
    } := by
  native_decide

/- Distinct seeded rows consume each newly computed String only at its own Number address. -/
example :
    rowOutcomes? (numericCell base.id 1 7) = some [
      (1, { field := first.id, path := [1] },
        .accepted (storedString "7" (by decide)),
        { field := second.id, path := [1] },
        .accepted { unscaled := 7, scale := 0 }),
      (2, { field := first.id, path := [2] },
        .accepted (storedString "11" (by decide)),
        { field := second.id, path := [2] },
        .accepted { unscaled := 11, scale := 0 })] := by
  native_decide

/- A wider finite input preserves physical encounter order rather than sorting by coordinate. -/
example :
    encounterOrderOutcomes? = some [
      (3, { field := first.id, path := [3] },
        .accepted (storedString "13" (by decide)),
        { field := second.id, path := [3] },
        .accepted { unscaled := 13, scale := 0 }),
      (1, { field := first.id, path := [1] },
        .accepted (storedString "7" (by decide)),
        { field := second.id, path := [1] },
        .accepted { unscaled := 7, scale := 0 }),
      (2, { field := first.id, path := [2] },
        .accepted (storedString "11" (by decide)),
        { field := second.id, path := [2] },
        .accepted { unscaled := 11, scale := 0 })] := by
  native_decide

/- Number empty produces String no-value, then the reached conversion supplies Number zero only in that row. -/
example :
    rowOutcomes? {
      address := { field := base.id, path := [1] }
      stored := ""
      raw := .presentEmpty
    } = some [
      (1, { field := first.id, path := [1] }, .noValue,
        { field := second.id, path := [1] },
        .accepted { unscaled := 0, scale := 0 }),
      (2, { field := first.id, path := [2] },
        .accepted (storedString "11" (by decide)),
        { field := second.id, path := [2] },
        .accepted { unscaled := 11, scale := 0 })] := by
  native_decide

/- Reached String poison becomes cause-blind Number dependency poison without aborting another row. -/
example :
    rowOutcomes? {
      address := { field := base.id, path := [1] }
      stored := "bad"
      raw := .rejected .malformed
    } = some [
      (1, { field := first.id, path := [1] }, .poison .malformed,
        { field := second.id, path := [1] },
        .inheritedPoison .computedDependency),
      (2, { field := first.id, path := [2] },
        .accepted (storedString "11" (by decide)),
        { field := second.id, path := [2] },
        .accepted { unscaled := 11, scale := 0 })] := by
  native_decide

/- A producer target error retains its attempted String but becomes the same cause-blind Number dependency poison. -/
example :
    rowOutcomes? (numericCell base.id 1 (-5)) = some [
      (1, { field := first.id, path := [1] },
        .errored (storedString "-5" (by decide)) .pattern,
        { field := second.id, path := [1] },
        .inheritedPoison .computedDependency),
      (2, { field := first.id, path := [2] },
        .accepted (storedString "11" (by decide)),
        { field := second.id, path := [2] },
        .accepted { unscaled := 11, scale := 0 })] := by
  native_decide

/- Wrong structural group, bypassed dependency, and reverse dependency fail before execution. -/
example :
    (match checkCurrentRepetitionStringToNumberCascade model lines.path otherGroup
        first.id (bare "BaseNumber") second.id (.direct (bare "FirstString")) with
      | .error (.groupMismatch source declaring) =>
          source == other.path && declaring == lines.path
      | _ => false) = true ∧
    (match checkCurrentRepetitionStringToNumberCascade model lines.path group
        first.id (bare "BaseNumber") second.id (.direct (bare "OtherString")) with
      | .error (.dependency expected actual) =>
          expected == first.id && actual == otherString.id
      | _ => false) = true ∧
    (match checkCurrentRepetitionStringToNumberCascade model lines.path group
        first.id (bare "SecondNumber") second.id (.direct (bare "FirstString")) with
      | .error (.reverseDependency field) => field == second.id
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
  base with groupPath := nestedPath, repeatableScope := [10, 20]
}

private def nestedFirst : FlatFieldDecl := {
  first with groupPath := nestedPath, repeatableScope := [10, 20]
}

private def nestedSecond : FlatFieldDecl := {
  second with groupPath := nestedPath, repeatableScope := [10, 20]
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

private def nestedPlan? :
    Option (CheckedCurrentRepetitionStringToNumberCascade nestedModel) :=
  (checkCurrentRepetitionStringToNumberCascade nestedModel nestedPath
    nestedGroup nestedFirst.id (bare "BaseNumber") nestedSecond.id
    (.direct (bare "FirstString"))).toOption

private def nestedPrepared :
    PreparedFlatStringContext nestedModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler nestedModel).toOption.get (by native_decide)

private def nestedNumberCell (field : FieldId) (path : List Nat)
    (value : Int) : ClassifiedCellInput := {
  address := { field, path }
  stored := toString value
  raw := .parsed (.num value)
  numericDecimal := some { unscaled := value, scale := 0 }
}

private def nestedStringCell (path : List Nat) : ClassifiedCellInput := {
  address := { field := nestedFirst.id, path }
  stored := "old"
  raw := .parsed (.str "old")
}

private def nestedOutcomes? : Option (List
    (Nat × CellAddr × StringTargetOutcome × CellAddr × NumericTargetOutcome)) := do
  let plan ← nestedPlan?
  let input ← (checkDocument nestedPrepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] }, { group := 10, path := [2] },
      { group := 20, path := [1, 1] }, { group := 20, path := [2, 1] },
      { group := 20, path := [1, 2] }]
    cells := [
      nestedNumberCell nestedBase.id [1, 1] 7,
      nestedNumberCell nestedBase.id [2, 1] 11,
      nestedNumberCell nestedBase.id [1, 2] 13,
      nestedStringCell [1, 1], nestedStringCell [2, 1],
      nestedStringCell [1, 2],
      nestedNumberCell nestedSecond.id [1, 1] 700,
      nestedNumberCell nestedSecond.id [2, 1] 1100,
      nestedNumberCell nestedSecond.id [1, 2] 1300]
  }).toOption
  let outcomes ← plan.execute nestedPrepared.patterns input |>.toOption
  pure (outcomes.rows.map fun row =>
    (row.coordinate, row.string.targetField, row.string.outcome,
      row.number.targetField, row.number.outcome))

/- A valid two-level model retains its complete scope and both typed field edges. -/
example :
    nestedPlan?.map CheckedCurrentRepetitionStringToNumberCascade.analyze = some {
          structuralGroup := nestedPath
          scope := [10, 20]
          fieldDependencies := [
            (nestedFirst.id, [nestedBase.id]),
            (nestedSecond.id, [nestedFirst.id])]
        } := by
  native_decide

/- Equal terminal coordinates under different parent rows retain distinct typed state at full addresses. -/
example : nestedOutcomes? = some [
    (1, { field := nestedFirst.id, path := [1, 1] },
      .accepted (storedString "7" (by decide)),
      { field := nestedSecond.id, path := [1, 1] },
      .accepted { unscaled := 7, scale := 0 }),
    (1, { field := nestedFirst.id, path := [2, 1] },
      .accepted (storedString "11" (by decide)),
      { field := nestedSecond.id, path := [2, 1] },
      .accepted { unscaled := 11, scale := 0 }),
    (2, { field := nestedFirst.id, path := [1, 2] },
      .accepted (storedString "13" (by decide)),
      { field := nestedSecond.id, path := [1, 2] },
      .accepted { unscaled := 13, scale := 0 })] := by
  native_decide

end A12Kernel.Conformance.CurrentRepetitionStringToNumber
