import A12Kernel.Elaboration.RepeatableNumberPlan

/-! # Authored repeatable Number plan locks: a row table of guarded alternatives

A repeatable `Rows` (at most three rows) with Numbers `G1`, `G2`, `RA`, `RB`, `RC`, the row table
`RT = [RA]` under `FieldFilled(G1)` or else `[RB]` under `FieldFilled(G2)`, and its reader
`RD = [RT] + [RC]`, authored ahead of it. Every row holds `RA` `7`, `RB` `3`, `RC` `1`, and stale `99`
targets. The two documents are the Kernel's rows at the
[row-alternatives checkpoint](../../docs/sources/computation-scheduling-probes.md#src-repeatable-row-alternatives),
measured on both codegen strategies, together with its two static refusals.

The rows separate first-match from last-match selection (both guards filled), a selection that continues
past a poisoned guard from one that aborts (a malformed `G1` beside a filled `G2`), and a clean no-match,
which its reader reads as empty, from poison.
-/

namespace A12Kernel.Conformance.RepeatableNumberPlanRowAlternatives

open A12Kernel

private def g1Id : FieldId := 0
private def g2Id : FieldId := 1
private def raId : FieldId := 2
private def rbId : FieldId := 3
private def rcId : FieldId := 4
private def rtId : FieldId := 5
private def rdId : FieldId := 6
private def sId : FieldId := 7

private def rowsPath : GroupPath := ["Alt", "Rows"]

private def number (id : FieldId) (name : String) : FlatFieldDecl where
  id
  groupPath := rowsPath
  name
  repeatableScope := [10]
  policy := { kind := .number { scale := 0, signed := true } }

/-- A Number in a sibling repeatable group, which no row of `Rows` binds. -/
private def sibling : FlatFieldDecl :=
  { number sId "S" with groupPath := ["Alt", "Sib"], repeatableScope := [20] }

private def model : FlatModel where
  fields := [number g1Id "G1", number g2Id "G2", number raId "RA", number rbId "RB",
    number rcId "RC", number rtId "RT", number rdId "RD", sibling]
  repeatableGroups := [{ level := 10, path := rowsPath, repeatability := some 3 },
    { level := 20, path := ["Alt", "Sib"], repeatability := some 3 }]

private def world : World := { now := { epochMillis := 0 } }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext world builtinStringPatternCompiler model).toOption.get
    (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def read (field : String) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.field (bare field))

private def table (alternatives : List (Option (CheckedComputationCondition model) × String)) :
    Except NumericComputationTableElabError (CheckedNumericComputationTable model) :=
  elaborateNumericTargetComputationTable model rowsPath rtId
    (alternatives.map fun (precondition, source) => (precondition, read source)) (targetScope := .row)

private def reader : Option (CheckedNumericComputationTable model) :=
  (elaborateNumericTargetComputationTable model rowsPath rdId
    [(none, .binary .add (read "RT") (read "RC"))] (targetScope := .row)).toOption

private def plan? : Option (CheckedRepeatableNumberPlan model) := do
  let rt ← (table [(some (.fieldFilled g1Id), "RA"), (some (.fieldFilled g2Id), "RB")]).toOption
  (certifyRepeatableNumberPlan [← reader, rt]).toOption

private inductive Gate where
  | value (number : Int)
  | malformed
  | absent

private def numberCell (field : FieldId) (row : Nat) (number : Int) : ClassifiedCellInput :=
  { address := { field, path := [row] }, stored := toString number, raw := .parsed (.num number) }

private def gateCells (field : FieldId) (row : Nat) : Gate → List ClassifiedCellInput
  | .value number => [numberCell field row number]
  | .malformed => [{ address := { field, path := [row] }, stored := "x", raw := .rejected .malformed }]
  | .absent => []

private def document? (rows : List (Gate × Gate)) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := rows.zipIdx.map fun (_, index) => { group := 10, path := [index + 1] }
    cells := rows.zipIdx.flatMap fun ((g1, g2), index) =>
      gateCells g1Id (index + 1) g1 ++ gateCells g2Id (index + 1) g2 ++
        [numberCell raId (index + 1) 7, numberCell rbId (index + 1) 3, numberCell rcId (index + 1) 1,
          numberCell rtId (index + 1) 99, numberCell rdId (index + 1) 99]
  }).toOption

private def reported? : NumericTargetOutcome → Option (Option Int)
  | .accepted stored => if stored.scale = 0 then some (some stored.unscaled) else none
  | .noValue | .inheritedPoison _ => some none
  | .rejected _ _ | .invalidNoValue _ => none

/-- `RT` then `RD` at each row in order; `none` is a clear. -/
private def reports? (rows : List (Gate × Gate)) : Option (List (Option Int)) := do
  let plan ← plan?
  let input ← document? rows
  let outcomes ← (plan.execute world input).toOption
  let found ← outcomes.mapM fun outcome => (reported? outcome.outcome).map (outcome.targetField, ·)
  (rows.zipIdx.flatMap fun (_, index) => [rtId, rdId].map fun field =>
    (found.find? (·.1 == { field, path := [index + 1] })).map (·.2)).mapM id

/- Row `a01`: both guards filled selects the first alternative, the first alone selects it too, and the
second alone selects the second. -/
example : reports? [(.value 1, .value 1), (.value 1, .absent), (.absent, .value 1)] =
    some [some 7, some 8, some 7, some 8, some 3, some 4] := by
  native_decide

/- Row `a02`: no guard holding clears `RT`, which `RD` reads as empty; a malformed `G1` poisons the row
although `G2` holds, so selection aborts rather than passing on; and a malformed `G2` reached after a
clean miss poisons it too. -/
example : reports? [(.absent, .absent), (.malformed, .value 1), (.absent, .malformed)] =
    some [none, some 1, none, none, none, none] := by
  native_decide

/- Lazy selection: a malformed second guard is never read once the first holds, so rows `1`/`x` and
`0`/`x` select `RA` while `x`/`x` clears its row's target, as the Kernel computes them. An eager scan
of every guard would clear all three rows. -/
example : reports? [(.value 1, .malformed), (.malformed, .malformed), (.value 0, .malformed)] =
    some [some 7, some 8, none, none, some 7, some 8] := by
  native_decide

/- Every guard's admission is asked before any alternative's own class: beside an unguarded first
alternative, a second guard reading the sibling group's `S` is refused as unbound, where the Kernel
reports `MVK_NO_WILDCARD` alone and not `MVK_ERROR_EMPTY_PRECONDITION`, and so is a guard naming no
field, where it reports `MVK_INVALID_ENTITY` alone. Neither class is projected here. -/
example :
    (match table [(none, "RA"), (some (.fieldFilled sId), "RB")] with
      | .error error => some error | _ => none) = some (.table (.guardNotAdmitted 2)) ∧
    (match table [(none, "RA"), (some (.fieldFilled 99), "RB")] with
      | .error error => some error | _ => none) = some (.table (.guardNotAdmitted 2)) := by
  native_decide

/- The two static refusals, each in the first or the later position: an unguarded alternative among
several, and a guard reading the table's own target. -/
example :
    ((table [(none, "RA"), (some (.fieldFilled g2Id), "RB")]).toBool,
      match table [(none, "RA"), (some (.fieldFilled g2Id), "RB")] with
      | .error error => error.diagnostic? | _ => none) = (false, some .errorEmptyPrecondition) ∧
    (match table [(some (.fieldFilled g1Id), "RA"), (none, "RB")] with
      | .error error => error.diagnostic? | _ => none) = some .errorEmptyPrecondition ∧
    (match table [(some (.fieldFilled rtId), "RA"), (some (.fieldFilled g2Id), "RB")] with
      | .error error => error.diagnostic? | _ => none) =
        some .errorReferenceToCalculatedField := by
  native_decide

end A12Kernel.Conformance.RepeatableNumberPlanRowAlternatives
