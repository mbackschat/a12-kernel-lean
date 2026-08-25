import A12Kernel.Elaboration.CurrentRepetitionComputation

/-! # CurrentRepetition computation cascade locks -/

namespace A12Kernel.Conformance.CurrentRepetitionComputation

open A12Kernel

private def base : FlatFieldDecl := {
  id := 1
  groupPath := ["Shipment", "Lines"]
  name := "Base"
  policy := { kind := .number { scale := 0, signed := true } }
  repeatableScope := [10]
}

private def first : FlatFieldDecl := { base with id := 2, name := "First" }
private def second : FlatFieldDecl := { base with id := 3, name := "Second" }

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

private def plan? : Option (CheckedCurrentRepetitionNumberCascade model) :=
  (checkCurrentRepetitionNumberCascade model lines.path group
    first.id (bare "Base") second.id (bare "First")).toOption

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def input? (rows : Nat) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := (List.range rows).map fun offset =>
      { group := lines.level, path := [offset + 1] }
    cells := if rows = 0 then [] else [{
      address := { field := base.id, path := [1] }
      stored := "7"
      raw := .parsed (.num 7)
    }]
  }).toOption

private def inputWithSecond? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [{ group := lines.level, path := [1] }]
    cells := [{
      address := { field := base.id, path := [1] }
      stored := "7"
      raw := .parsed (.num 7)
    }, {
      address := { field := second.id, path := [1] }
      stored := "9"
      raw := .parsed (.num 9)
      numericDecimal := some { unscaled := 9, scale := 0 }
    }]
  }).toOption

private def numericCell (field : FieldId) (row : Nat) (value : Int) :
    ClassifiedCellInput := {
  address := { field, path := [row] }
  stored := toString value
  raw := .parsed (.num value)
  numericDecimal := some { unscaled := value, scale := 0 }
}

private def twoRowInput? (firstBase : ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := lines.level, path := [1] },
      { group := lines.level, path := [2] }]
    cells := [
      firstBase,
      numericCell first.id 1 70,
      numericCell second.id 1 700,
      numericCell base.id 2 11,
      numericCell first.id 2 110,
      numericCell second.id 2 1100]
  }).toOption

private def twoRowOutcomes? (firstBase : ClassifiedCellInput) :
    Option CurrentRepetitionNumberCascadeOutcomes := do
  let plan <- plan?
  let input <- twoRowInput? firstBase
  plan.execute input |>.toOption

private def rowOutcomes? (firstBase : ClassifiedCellInput) :
    Option (List
      (Nat × CellAddr × NumericTargetOutcome × CellAddr × NumericTargetOutcome)) :=
  twoRowOutcomes? firstBase |>.map fun outcomes =>
    outcomes.rows.map fun row =>
      (row.coordinate, row.first.targetField, row.first.outcome,
        row.second.targetField, row.second.outcome)

private def encounterOrderOutcomes? :
    Option (List
      (Nat × CellAddr × NumericTargetOutcome × CellAddr × NumericTargetOutcome)) := do
  let plan <- plan?
  let input <- (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := lines.level, path := [3] },
      { group := lines.level, path := [1] },
      { group := lines.level, path := [2] }]
    cells := [
      numericCell base.id 1 7,
      numericCell first.id 1 70,
      numericCell second.id 1 700,
      numericCell base.id 2 11,
      numericCell first.id 2 110,
      numericCell second.id 2 1100,
      numericCell base.id 3 13,
      numericCell first.id 3 130,
      numericCell second.id 3 1300]
  }).toOption
  let outcomes <- plan.execute input |>.toOption
  pure (outcomes.rows.map fun row =>
    (row.coordinate, row.first.targetField, row.first.outcome,
      row.second.targetField, row.second.outcome))

private def outcome? :
    Option CurrentRepetitionNumberCascadeOutcomes := do
  let plan <- plan?
  let input <- input? 1
  plan.execute input |>.toOption

private def outcomeWithSecond? :
    Option CurrentRepetitionNumberCascadeOutcomes := do
  let plan <- plan?
  let input <- inputWithSecond?
  plan.execute input |>.toOption

private def outcomeRow? : Option CurrentRepetitionNumberCascadeRowOutcomes :=
  outcome?.bind (·.rows.head?)

private def outcomeWithSecondRow? :
    Option CurrentRepetitionNumberCascadeRowOutcomes :=
  outcomeWithSecond?.bind (·.rows.head?)

/- Analyze retains the structural coordinate separately from the two real field edges. -/
example :
    plan?.map CheckedCurrentRepetitionNumberCascade.analyze = some {
      structuralGroup := lines.path
      scope := [lines.level]
      fieldDependencies := [
        (first.id, [base.id]),
        (second.id, [first.id])]
    } := by
  native_decide

/- The second outcome retains its own immutable pre-computation source state rather than the first overlay. -/
example :
    (outcomeWithSecondRow?.map fun outcomes => outcomes.second.source) =
      some (.presentValue (.decimal { unscaled := 9, scale := 0 })) := by
  native_decide

/- The fixed guard itself retains and evaluates the one-based coordinate through the shared numeric comparison. -/
example :
    (do
      let plan ← plan?
      plan.evaluatePositiveGuardAt [(lines.level, 1)] |>.toOption) =
      some (1, true) := by
  native_decide

/- The checked one-row cascade overlays the first exact result before the second read. -/
example :
    (outcomeRow?.map fun outcomes =>
      (outcomes.first.targetField, outcomes.first.outcome,
        outcomes.second.targetField, outcomes.second.outcome)) =
      some (
        { field := first.id, path := [1] },
        .accepted { unscaled := 7, scale := 0 },
        { field := second.id, path := [1] },
        .accepted { unscaled := 7, scale := 0 }) := by
  native_decide

/- Cross-group structural sources and reverse field edges fail before execution. -/
example :
    (match checkCurrentRepetitionNumberCascade model lines.path otherGroup
        first.id (bare "Base") second.id (bare "First") with
      | .error (.groupMismatch source declaring) =>
          source == other.path && declaring == lines.path
      | _ => false) = true ∧
    (match checkCurrentRepetitionNumberCascade model lines.path group
        first.id (bare "Second") second.id (bare "First") with
      | .error (.reverseDependency field) => field == second.id
      | _ => false) = true := by
  native_decide

/- A second copy that does not read the first target is not this bounded cascade. -/
example :
    (match checkCurrentRepetitionNumberCascade model lines.path group
        first.id (bare "Base") second.id (bare "Base") with
      | .error (.dependency expected actual) =>
          expected == first.id && actual == base.id
      | _ => false) = true := by
  native_decide

/- Distinct seeded rows expose only their own newly computed first value to the dependent read. -/
example :
    rowOutcomes? (numericCell base.id 1 7) = some [
      (1, { field := first.id, path := [1] },
        .accepted { unscaled := 7, scale := 0 },
        { field := second.id, path := [1] },
        .accepted { unscaled := 7, scale := 0 }),
      (2, { field := first.id, path := [2] },
        .accepted { unscaled := 11, scale := 0 },
        { field := second.id, path := [2] },
        .accepted { unscaled := 11, scale := 0 })] := by
  native_decide

/- A wider finite input preserves physical encounter order rather than sorting by coordinate. -/
example :
    encounterOrderOutcomes? = some [
      (3, { field := first.id, path := [3] },
        .accepted { unscaled := 13, scale := 0 },
        { field := second.id, path := [3] },
        .accepted { unscaled := 13, scale := 0 }),
      (1, { field := first.id, path := [1] },
        .accepted { unscaled := 7, scale := 0 },
        { field := second.id, path := [1] },
        .accepted { unscaled := 7, scale := 0 }),
      (2, { field := first.id, path := [2] },
        .accepted { unscaled := 11, scale := 0 },
        { field := second.id, path := [2] },
        .accepted { unscaled := 11, scale := 0 })] := by
  native_decide

/- Empty Number substitution stays local to its own row. -/
example :
    rowOutcomes? {
      address := { field := base.id, path := [1] }
      stored := ""
      raw := .presentEmpty
    } = some [
      (1, { field := first.id, path := [1] },
        .accepted { unscaled := 0, scale := 0 },
        { field := second.id, path := [1] },
        .accepted { unscaled := 0, scale := 0 }),
      (2, { field := first.id, path := [2] },
        .accepted { unscaled := 11, scale := 0 },
        { field := second.id, path := [2] },
        .accepted { unscaled := 11, scale := 0 })] := by
  native_decide

/- Reached formal poison clears only its own row and the dependent read at that address. -/
example :
    rowOutcomes? {
      address := { field := base.id, path := [1] }
      stored := "bad"
      raw := .rejected .malformed
    } = some [
      (1, { field := first.id, path := [1] },
        .inheritedPoison .malformed,
        { field := second.id, path := [1] },
        .inheritedPoison .computedDependency),
      (2, { field := first.id, path := [2] },
        .accepted { unscaled := 11, scale := 0 },
        { field := second.id, path := [2] },
        .accepted { unscaled := 11, scale := 0 })] := by
  native_decide

/- Zero instantiated rows are the other explicit cardinality refusal. -/
example :
    (do
      let plan <- plan?
      let input <- input? 0
      pure (match plan.execute input with
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

private def nestedPlan? :
    Option (CheckedCurrentRepetitionNumberCascade nestedModel) :=
  (checkCurrentRepetitionNumberCascade nestedModel nestedPath nestedGroup
    nestedFirst.id (bare "Base") nestedSecond.id (bare "First")).toOption

private def nestedPrepared :
    PreparedFlatStringContext nestedModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler nestedModel).toOption.get (by native_decide)

private def nestedCell (field : FieldId) (path : List Nat) (value : Int) :
    ClassifiedCellInput := {
  address := { field, path }
  stored := toString value
  raw := .parsed (.num value)
  numericDecimal := some { unscaled := value, scale := 0 }
}

private def nestedOutcomes? : Option (List
    (Nat × CellAddr × NumericTargetOutcome × CellAddr × NumericTargetOutcome)) := do
  let plan ← nestedPlan?
  let input ← (checkDocument nestedPrepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] }, { group := 10, path := [2] },
      { group := 20, path := [1, 1] }, { group := 20, path := [2, 1] },
      { group := 20, path := [1, 2] }]
    cells := [
      nestedCell nestedBase.id [1, 1] 7,
      nestedCell nestedBase.id [2, 1] 11,
      nestedCell nestedBase.id [1, 2] 13,
      nestedCell nestedFirst.id [1, 1] 70,
      nestedCell nestedFirst.id [2, 1] 110,
      nestedCell nestedFirst.id [1, 2] 130,
      nestedCell nestedSecond.id [1, 1] 700,
      nestedCell nestedSecond.id [2, 1] 1100,
      nestedCell nestedSecond.id [1, 2] 1300]
  }).toOption
  let outcomes ← plan.execute input |>.toOption
  pure (outcomes.rows.map fun row =>
    (row.coordinate, row.first.targetField, row.first.outcome,
      row.second.targetField, row.second.outcome))

/- A valid two-level model retains its complete scope separately from the selected terminal coordinate. -/
example :
    nestedPlan?.map CheckedCurrentRepetitionNumberCascade.analyze = some {
          structuralGroup := nestedPath
          scope := [10, 20]
          fieldDependencies := [
            (nestedFirst.id, [nestedBase.id]),
            (nestedSecond.id, [nestedFirst.id])]
        } := by
  native_decide

/- Equal terminal coordinates under different parent rows retain distinct full addresses and fresh Number state. -/
example : nestedOutcomes? = some [
    (1, { field := nestedFirst.id, path := [1, 1] },
      .accepted { unscaled := 7, scale := 0 },
      { field := nestedSecond.id, path := [1, 1] },
      .accepted { unscaled := 7, scale := 0 }),
    (1, { field := nestedFirst.id, path := [2, 1] },
      .accepted { unscaled := 11, scale := 0 },
      { field := nestedSecond.id, path := [2, 1] },
      .accepted { unscaled := 11, scale := 0 }),
    (2, { field := nestedFirst.id, path := [1, 2] },
      .accepted { unscaled := 13, scale := 0 },
      { field := nestedSecond.id, path := [1, 2] },
      .accepted { unscaled := 13, scale := 0 })] := by
  native_decide

end A12Kernel.Conformance.CurrentRepetitionComputation
