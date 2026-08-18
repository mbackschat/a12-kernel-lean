import A12Kernel.Elaboration.CurrentRepetitionComputation

/-! # Exact one-row CurrentRepetition computation cascade locks -/

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
    (outcomeWithSecond?.map fun outcomes => outcomes.second.source) =
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
    (outcome?.map fun outcomes =>
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

/- Multiple instantiated rows remain explicit insufficient information. -/
example :
    (do
      let plan <- plan?
      let input <- input? 2
      pure (match plan.execute input with
        | .error (.rowCardinality 2) => true
        | _ => false)) = some true := by
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

/- A valid two-level model reaches and is rejected by the capsule's one-level source-scope gate. -/
example :
    (match checkCurrentRepetitionNumberCascade nestedModel nestedPath nestedGroup
        nestedFirst.id (bare "Base") nestedSecond.id (bare "First") with
      | .error (.sourceScope [10, 20]) => true
      | _ => false) = true := by
  native_decide

end A12Kernel.Conformance.CurrentRepetitionComputation
