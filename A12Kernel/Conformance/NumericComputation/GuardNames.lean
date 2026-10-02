import A12Kernel.Elaboration.NumericComputation.Table

/-! # Number computation precondition name locks

Every replayable row of the
[precondition-name grid](../../../docs/sources/computation-scheduling-probes.md#src-computation-precondition-names),
measured on the Kernel's static check: a whole Number computation whose alternatives carry presence
guards authored by name, the class the Kernel reports, or none for an admitted computation. The model's
root `G` holds Numbers `A`, `N` and the target `T`, a String `S`, a nonrepeatable group `Sub` holding
`X`, and a repeatable `Rows` holding `R`. A starred guard path, a starred group and a two-field
`FieldFilled` are surfaces a presence guard here does not carry, and are not replayed.

The rows separate a guard's name class from its operation's (a typing failure beside an unknown guard
draws the guard's class), a guard's class from an unguarded sibling's (a guard naming a group draws its
class beside an admitted unguarded alternative), the group class from the unbound-level one (a fixed
group against a repeatable one), and a left leaf's class from a right one's (`k01` to `k04`).
-/

namespace A12Kernel.Conformance.NumericComputation.GuardNames

open A12Kernel

private def declaration (id : FieldId) (group : GroupPath) (name : String) (kind : FieldKind)
    (scope : List RepeatableLevel := []) : FlatFieldDecl :=
  { id, groupPath := group, name, policy := { kind }, repeatableScope := scope }

private def number : FieldKind := .number { scale := 0, signed := true }

private def targetId : FieldId := 2

private def model : FlatModel :=
  { fields := [
      declaration 0 ["G"] "A" number, declaration 1 ["G"] "N" number,
      declaration targetId ["G"] "T" number, declaration 3 ["G"] "S" .string,
      declaration 4 ["G", "Sub"] "X" number, declaration 5 ["G", "Rows"] "R" number [10]]
    repeatableGroups := [{ level := 10, path := ["G", "Rows"], repeatability := some 3 }] }

private def path (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups, field }

private def filled (groups : List String) (field : String) : SurfaceComputationCondition :=
  .fieldFilled (path groups field)

private def read (field : String) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.field (path [] field))

/-- The Kernel code the whole computation reports, `none` for an admitted one. -/
private def codeOf
    (alternatives : List (Option SurfaceComputationCondition × AuthoredNumericExpr SurfaceNumericAtom)) :
    Option String :=
  match elaborateNumericTargetComputationTableFromSurface model ["G"] targetId alternatives with
  | .ok _ => none
  | .error error => some ((error.diagnostic?.map (·.kernelCode)).getD "unprojected")

private def rows :
    List (String × List (Option SurfaceComputationCondition × AuthoredNumericExpr SurfaceNumericAtom) ×
      Option String) := [
  ("g01", [(some (filled [] "Nope"), read "A")], some "MVK_INVALID_ENTITY"),
  ("g02", [(some (filled [] "Sub"), read "A")], some "MVK_NO_GROUPS_ALLOWED"),
  ("g03", [(some (filled ["Rows"] "R"), read "A")], some "MVK_NO_WILDCARD"),
  ("g05", [(some (filled [] "Rows"), read "A")], some "MVK_NO_WILDCARD"),
  ("g06", [(some (filled [] "S"), read "A")], none),
  ("g07", [(some (.and (filled [] "A") (filled [] "Nope")), read "A")], some "MVK_INVALID_ENTITY"),
  ("g08", [(some (filled [] "Nope"), .binary .add (read "S") (.literal { value := 1, authoredScale := 0 }))],
    some "MVK_INVALID_ENTITY"),
  ("g09", [(some (filled [] "T"), read "A")], some "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD"),
  ("g10", [(some (.fieldNotFilled (path [] "Nope")), read "A")], some "MVK_INVALID_ENTITY"),
  ("g11", [(some (filled ["Sub"] "X"), read "A")], none),
  ("g12", [(some (filled [] "A"), read "A")], none),
  ("g13", [(some (.fieldFilled { base := .absolute, groups := ["G"], field := "A" }), read "A")], none),
  ("g14", [(some (.or (filled [] "Nope") (filled [] "A")), read "A")], some "MVK_INVALID_ENTITY"),
  ("g17", [(none, read "A"), (some (filled [] "Sub"), read "N")], some "MVK_NO_GROUPS_ALLOWED"),
  ("g18", [(some (filled [] "Nope"), read "Nope2")], some "MVK_INVALID_ENTITY"),
  ("g19", [(some (filled ["Sub"] "Nope"), read "A")], some "MVK_INVALID_ENTITY"),
  ("g20", [(some (.fieldNotFilled (path ["Rows"] "R")), read "A")], some "MVK_NO_WILDCARD"),
  -- Two differently classed leaves: the left one answers under either connective (rows `k01` to `k04`
  -- of the division-walk grids' guard table).
  ("k01", [(some (.and (filled [] "Sub") (filled [] "Nope")), read "A")], some "MVK_NO_GROUPS_ALLOWED"),
  ("k02", [(some (.and (filled [] "Nope") (filled [] "Sub")), read "A")], some "MVK_INVALID_ENTITY"),
  ("k03", [(some (.or (filled [] "Sub") (filled [] "Nope")), read "A")], some "MVK_NO_GROUPS_ALLOWED"),
  ("k04", [(some (.or (filled [] "Nope") (filled [] "Sub")), read "A")], some "MVK_INVALID_ENTITY")]

/- Every row reports the Kernel's code; the failing ids are listed, so a mismatch names its row. -/
example : (rows.filter fun (_, alternatives, expected) => codeOf alternatives != expected).map (·.1) =
    [] := by
  native_decide

end A12Kernel.Conformance.NumericComputation.GuardNames
