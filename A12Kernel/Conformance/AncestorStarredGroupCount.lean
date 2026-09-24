import A12Kernel.Elaboration.NumericValidation.Resolution
import A12Kernel.Elaboration.NumericValidation.Evaluation
import A12Kernel.Elaboration.CheckedDocument

/-! # A fixed group below a starred level as a `NumberOfFilledGroups` operand

The Kernel admits `NumberOfFilledGroups(Batches*/Seal)`, alone or beside a fixed group, although
`Seal` does not repeat, and counts the batch environments whose `Seal` is filled rather than the
batch rows ([inbound](../../docs/SOURCES.md#inbound-2026-09-24-ancestor-starred-group-count)). The six
documents below are that record's, each read alone and beside `Grading`. The one that separates the
two readings instantiates two batches and fills neither `Seal`: a row count answers two, and the
Kernel zero. The extent rows are the two peer rows the same record adopts.
-/

namespace A12Kernel.Conformance.AncestorStarredGroupCount

open A12Kernel

private def title : FlatFieldDecl :=
  { id := 1, groupPath := ["Item"], name := "Title", policy := { kind := .string } }

private def grade : FlatFieldDecl :=
  { id := 2, groupPath := ["Item", "Grading"], name := "Grade"
    policy := { kind := .number { scale := 0, signed := false } } }

private def lot : FlatFieldDecl :=
  { id := 3, groupPath := ["Item", "Batches"], name := "Lot", policy := { kind := .string }
    repeatableScope := [10] }

private def code : FlatFieldDecl :=
  { id := 4, groupPath := ["Item", "Batches", "Seal"], name := "Code"
    policy := { kind := .string }, repeatableScope := [10] }

private def model : FlatModel :=
  { fields := [title, grade, lot, code]
    repeatableGroups := [{ level := 10, path := ["Item", "Batches"], repeatability := some 4 }] }

private def boxCode : FlatFieldDecl :=
  { id := 5, groupPath := ["Item", "Batches", "Boxes", "Seal"], name := "Code"
    policy := { kind := .string }, repeatableScope := [10, 20] }

/-- `Batches` (2) holding `Boxes` (2), each box a fixed `Seal`: the carrier on which the product of
    the two capacities and the inner capacity alone part. -/
private def nestedModel : FlatModel :=
  { fields := [title, boxCode]
    repeatableGroups := [{ level := 10, path := ["Item", "Batches"], repeatability := some 2 },
      { level := 20, path := ["Item", "Batches", "Boxes"], repeatability := some 2 }] }

private def seals : SurfaceGroupCountOperand :=
  .starred { base := .absolute
             groups := [{ name := "Item" }, { name := "Batches", starred := true }, { name := "Seal" }] }

private def boxSeals : SurfaceGroupCountOperand :=
  .starred { base := .absolute
             groups := [{ name := "Item" }, { name := "Batches", starred := true },
               { name := "Boxes", starred := true }, { name := "Seal" }] }

private def grading : SurfaceGroupCountOperand :=
  .fixed (.path { base := .absolute, groups := ["Item", "Grading"] })

private def cellAt (field : FlatFieldDecl) (path : List Nat) : ClassifiedCellInput :=
  { address := { field := field.id, path }
    stored := if field.id == grade.id then "1" else "c"
    raw := if field.id == grade.id then .parsed (.num 1) else .parsed (.str "c") }

/-- The count and whether it can still grow, over one checked document of `model` whose listed
    rows are instantiated and whose listed cells are set. Each fixed operand's state is the
    document's own derivation. -/
private def readingOf (model : FlatModel) (operands : List SurfaceGroupCountOperand)
    (rows : List RowAddr) (cells : List (FlatFieldDecl × List Nat)) : Option (Rat × Bool) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let comparison ←
    (elaborateMixedFilledGroupCountComparison model ["Item"] operands .greater 0).toOption
  let atom ← match comparison.core.left with
    | .atom source => some source
    | _ => none
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := rows
    cells := cells.map fun (field, path) => cellAt field path }).toOption
  let context : AddressedValidationEvaluationContext model := {
    scalar := {
      fields := document.flatContext
      groups := fun path =>
        (document.groupPresenceInput path [] .fullyRelevant false).toOption.map (·.derive) }
    outer := []
    input := .checked document }
  match atom.resolveAddressed context with
  | .ok (.ok (.value amount fillability)) => some (amount, fillability.canGrow)
  | _ => none

private def batches (rows : List Nat) : List RowAddr :=
  rows.map fun row => { group := 10, path := [row] }

/-- Each document as (instantiated batch rows, set cells), in the record's order. -/
private def documents : List (List Nat × List (FlatFieldDecl × List Nat)) :=
  [([], []),
   ([1, 2], [(code, [1]), (code, [2])]),
   ([1, 2], [(code, [1]), (lot, [2])]),
   ([1, 2], []),
   ([1, 2, 3], [(code, [1]), (code, [3])]),
   ([1], [(code, [1]), (grade, [])])]

/- A `Seal` counts only when it holds a value: not because its batch row exists, and not because the
   row holds another field. Beside `Grading` the fixed group adds its own filled state, which only the
   last document sets. -/
example :
    documents.map (fun (rows, cells) =>
      (readingOf model [seals] (batches rows) cells).map (·.1)) =
      [some 0, some 2, some 1, some 0, some 2, some 1] ∧
    documents.map (fun (rows, cells) =>
      (readingOf model [seals, grading] (batches rows) cells).map (·.1)) =
      [some 0, some 2, some 1, some 0, some 2, some 2] := by
  native_decide

/- The extent is one `Seal` per batch the star reaches, so four sealed batches cannot grow, while
   beside an empty `Grading` the same four still can; an extent of one per operand would close both
   ([`kf463`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf463)). With two starred levels it is the
   product, so one batch with both boxes sealed can still grow, where the inner capacity alone
   would read two as full. -/
example :
    readingOf model [seals] (batches [1, 2, 3, 4]) ([1, 2, 3, 4].map ((code, [·]))) =
      some (4, false) ∧
    readingOf model [seals, grading] (batches [1, 2, 3, 4]) ([1, 2, 3, 4].map ((code, [·]))) =
      some (4, true) ∧
    readingOf nestedModel [boxSeals]
        [{ group := 10, path := [1] }, { group := 20, path := [1, 1] },
          { group := 20, path := [1, 2] }]
        [(boxCode, [1, 1]), (boxCode, [1, 2])] =
      some (2, true) := by
  native_decide

end A12Kernel.Conformance.AncestorStarredGroupCount
