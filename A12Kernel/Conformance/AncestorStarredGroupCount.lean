import A12Kernel.Elaboration.NumericValidation.Resolution
import A12Kernel.Elaboration.NumericValidation.Evaluation
import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Elaboration.ValidationRule

/-! # A fixed group below a starred level as a `NumberOfFilledGroups` operand

The Kernel admits `NumberOfFilledGroups(Batches*/Seal)`, alone or beside a fixed group, although
`Seal` does not repeat, and counts the batch environments whose `Seal` is filled rather than the
batch rows ([inbound](../../docs/SOURCES.md#inbound-2026-09-24-ancestor-starred-group-count)). The
thirteen documents below are the peer's `kf463` validation table, read by the three operand lists
of that table this carrier owns; its fixed-only pair and a lone starred row count have carriers of
their own ([inbound](../../docs/SOURCES.md#inbound-2026-09-24b-kf463-validation)). The one that separates a
content count from a row count instantiates two batches and fills neither `Seal`: a row count
answers two, and the Kernel zero. A malformed-only instance separates this arm from the computation
arm, which counts it.
-/

namespace A12Kernel.Conformance.AncestorStarredGroupCount

open A12Kernel

private def unsigned : NumField := { scale := 0, signed := false }

private def title : FlatFieldDecl :=
  { id := 1, groupPath := ["Item"], name := "Title", policy := { kind := .string } }

private def grade : FlatFieldDecl :=
  { id := 2, groupPath := ["Item", "Grading"], name := "Grade"
    policy := { kind := .number unsigned } }

private def lot : FlatFieldDecl :=
  { id := 3, groupPath := ["Item", "Batches"], name := "Lot", policy := { kind := .string }
    repeatableScope := [10] }

private def code : FlatFieldDecl :=
  { id := 4, groupPath := ["Item", "Batches", "Seal"], name := "Code"
    policy := { kind := .string }, repeatableScope := [10] }

private def weight : FlatFieldDecl :=
  { id := 6, groupPath := ["Item", "Batches", "Seal"], name := "Weight"
    policy := { kind := .number unsigned }, repeatableScope := [10] }

private def note : FlatFieldDecl :=
  { id := 7, groupPath := ["Item", "Grading"], name := "Note", policy := { kind := .string } }

private def label : FlatFieldDecl :=
  { id := 8, groupPath := ["Item", "Specs"], name := "Label", policy := { kind := .string } }

private def tare : FlatFieldDecl :=
  { id := 9, groupPath := ["Item", "Crates"], name := "Tare"
    policy := { kind := .number unsigned }, repeatableScope := [30] }

private def model : FlatModel :=
  { fields := [title, grade, lot, code, weight, note, label, tare]
    repeatableGroups := [{ level := 10, path := ["Item", "Batches"], repeatability := some 4 },
      { level := 30, path := ["Item", "Crates"], repeatability := some 2 }] }

private def boxCode : FlatFieldDecl :=
  { id := 5, groupPath := ["Item", "Batches", "Boxes", "Seal"], name := "Code"
    policy := { kind := .string }, repeatableScope := [10, 20] }

/-- `Batches` (2) holding `Boxes` (2), each box a fixed `Seal`: the carrier on which the product of
    the two capacities and the inner capacity alone part. -/
private def nestedModel : FlatModel :=
  { fields := [title, boxCode]
    repeatableGroups := [{ level := 10, path := ["Item", "Batches"], repeatability := some 2 },
      { level := 20, path := ["Item", "Batches", "Boxes"], repeatability := some 2 }] }

private def starred (groups : List SurfaceStarGroupSegment) : SurfaceGroupCountOperand :=
  .starred { base := .absolute, groups := { name := "Item" } :: groups }

private def fixed (name : String) : SurfaceGroupCountOperand :=
  .fixed (.path { base := .absolute, groups := ["Item", name] })

private def seals : SurfaceGroupCountOperand :=
  starred [{ name := "Batches", starred := true }, { name := "Seal" }]

private def batchRows : SurfaceGroupCountOperand := starred [{ name := "Batches", starred := true }]

private def crateRows : SurfaceGroupCountOperand := starred [{ name := "Crates", starred := true }]

private def boxSeals : SurfaceGroupCountOperand :=
  starred [{ name := "Batches", starred := true }, { name := "Boxes", starred := true },
    { name := "Seal" }]

private def grading : SurfaceGroupCountOperand := fixed "Grading"

/-- A set cell, or with `malformed` an unparseable one: `abc` in a Number, which no text field
    carries in these documents. -/
private def cellAt (malformed : Bool) (field : FlatFieldDecl) (path : List Nat) :
    ClassifiedCellInput :=
  if malformed then
    { address := { field := field.id, path }, stored := "abc", raw := .rejected .malformed }
  else match field.policy.kind with
    | .number _ => { address := { field := field.id, path }, stored := "1", raw := .parsed (.num 1) }
    | _ => { address := { field := field.id, path }, stored := "c", raw := .parsed (.str "c") }

/-- A count and whether it can still grow, or a count the rule cannot evaluate. -/
private inductive Reading where
  | count (amount : Rat) (grows : Bool)
  | unavailable
  deriving Repr, DecidableEq

/-- The `n:V`/`n:O` spelling of the peer's table: `V` when the count has reached its extent. -/
private def v (amount : Rat) : Option Reading := some (.count amount false)
private def o (amount : Rat) : Option Reading := some (.count amount true)
private def unevaluable : Option Reading := some .unavailable

/-- One checked document of `model`: its instantiated rows, set cells and malformed cells. -/
private structure Doc where
  rows : List RowAddr := []
  cells : List (FlatFieldDecl × List Nat) := []
  malformed : List (FlatFieldDecl × List Nat) := []

/-- The reading of `operands` over `doc`. Each fixed operand's state is the document's own
    derivation. -/
private def readingOf (model : FlatModel) (operands : List SurfaceGroupCountOperand) (doc : Doc) :
    Option Reading := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let comparison ←
    (elaborateMixedFilledGroupCountComparison model ["Item"] operands .greater 0).toOption
  let atom ← match comparison.core.left with
    | .atom source => some source
    | _ => none
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := doc.rows
    cells := doc.cells.map (fun (field, path) => cellAt false field path) ++
      doc.malformed.map fun (field, path) => cellAt true field path }).toOption
  let context : AddressedValidationEvaluationContext model := {
    scalar := {
      fields := document.flatContext
      groups := fun path =>
        (document.groupPresenceInput path [] .fullyRelevant false).toOption.map (·.derive) }
    outer := []
    input := .checked document }
  match atom.resolveAddressed context with
  | .ok (.ok (.value amount fillability)) => some (.count amount fillability.canGrow)
  | .ok (.error _) => some .unavailable
  | _ => none

private def batches (rows : List Nat) : List RowAddr :=
  rows.map fun row => { group := 10, path := [row] }

private def sealed (rows : List Nat) : List (FlatFieldDecl × List Nat) := rows.map ((code, [·]))

/-- The peer's thirteen documents, in its order. -/
private def documents : List Doc :=
  [{},
   { rows := batches [1, 2], cells := sealed [1, 2] },
   { rows := batches [1, 2], cells := sealed [1] ++ [(lot, [2])] },
   { rows := batches [1, 2] },
   { rows := batches [1, 2, 3], cells := sealed [1, 3] },
   { rows := batches [1, 2, 3, 4], cells := sealed [1, 2, 3, 4] },
   { rows := batches [1], cells := sealed [1] ++ [(grade, [])] },
   { rows := batches [1], malformed := [(weight, [1])] },
   { rows := batches [1, 2], cells := sealed [1], malformed := [(weight, [2])] },
   { rows := batches [1], cells := sealed [1], malformed := [(weight, [1])] },
   { rows := batches [1], cells := sealed [1] ++ [(note, [])], malformed := [(grade, [])] },
   { rows := batches [1], cells := sealed [1], malformed := [(grade, [])] },
   { cells := [(note, []), (label, [])], malformed := [(grade, [])] }]

private def table (operands : List SurfaceGroupCountOperand) : List (Option Reading) :=
  documents.map (readingOf model operands)

/- A `Seal` counts by its content: an instantiated empty one adds nothing, a malformed-only one leaves
   the count unevaluable, and one holding admitted content counts beside a malformed value. Four
   sealed batches reach the extent of one `Seal` per batch; beside `Grading` the same four can still
   grow, which an extent of one per operand would close. -/
example :
    table [seals] = [o 0, o 2, o 1, o 0, o 2, v 4, o 1, unevaluable, unevaluable, o 1, o 1, o 1, o 0] ∧
    table [seals, grading] =
      [o 0, o 2, o 1, o 0, o 2, o 4, o 2, unevaluable, unevaluable, o 1, o 2, unevaluable, o 1] := by
  native_decide

/- A starred repeatable level counts every instantiated row, whatever it holds, malformed content
   included, while a malformed-only fixed group beside it still leaves the count unevaluable and
   `Grading` holding a note beside a malformed grade counts. -/
example :
    table [batchRows, grading] =
      [o 0, o 2, o 2, o 2, o 3, o 4, o 2, o 1, o 2, o 1, o 2, unevaluable, o 1] := by
  native_decide

/- The same below-star operand twice is admitted on this arm as on the computation arm, since the
   duplicate scan skips a starred operand (the peer's rule-arm row). -/
example :
    (elaborateMixedFilledGroupCountComparison model ["Item"] [seals, seals] .greater 0).toOption.isSome =
      true := by
  native_decide

/- Two starred scopes count against the sum of their extents, and a crate holding only a malformed
   value directly in its row still counts once instantiated. -/
example :
    let crates (rows : List Nat) : List RowAddr := rows.map fun row => { group := 30, path := [row] }
    [readingOf model [batchRows, crateRows]
        { rows := batches [1] ++ crates [1], cells := sealed [1] ++ [(tare, [1])] },
      readingOf model [batchRows, crateRows]
        { rows := batches [1] ++ crates [1], cells := sealed [1], malformed := [(tare, [1])] },
      readingOf model [batchRows, crateRows] { rows := crates [1], malformed := [(tare, [1])] },
      readingOf model [batchRows, crateRows]
        { rows := batches [1, 2, 3, 4] ++ crates [1, 2], cells := sealed [1, 2, 3, 4] }] =
    [o 2, o 2, o 1, v 6] := by
  native_decide

/- With two starred levels the extent is the product, so one batch with both boxes sealed can still
   grow where the inner capacity alone would read two as full. -/
example :
    let box (batch slot : Nat) : RowAddr := { group := 20, path := [batch, slot] }
    let docs : List Doc :=
      [{ rows := batches [1] ++ [box 1 1, box 1 2], cells := [(boxCode, [1, 1]), (boxCode, [1, 2])] },
       { rows := batches [1, 2] ++ [box 1 1, box 2 1],
         cells := [(boxCode, [1, 1]), (boxCode, [2, 1])] },
       { rows := batches [1, 2] ++ [box 1 1, box 1 2, box 2 1, box 2 2],
         cells := [(boxCode, [1, 1]), (boxCode, [1, 2]), (boxCode, [2, 1]), (boxCode, [2, 2])] }]
    docs.map (readingOf nestedModel [boxSeals]) = [o 2, o 2, v 4] := by
  native_decide

/-- `nestedModel` plus a field of `Batches` itself, the error field a rule bound to a batch row names. -/
private def boundModel : FlatModel :=
  { nestedModel with fields := nestedModel.fields ++ [lot] }

private def outerUnstarredSeals : SurfaceGroupCountOperand :=
  .starred { base := .absolute
             groups := [{ name := "Item" }, { name := "Batches" },
               { name := "Boxes", starred := true }, { name := "Seal" }] }

private def iterationScopeOf (operand : SurfaceGroupCountOperand) :
    Option (Option (List RepeatableLevel)) := do
  let comparison ← (elaborateMixedFilledGroupCountComparison boundModel ["Item", "Batches"]
    [operand] .greater 0).toOption
  let condition ← (CheckedValidationCondition.fromOrderedNumeric comparison).toOption
  condition.core.ordinaryIterationScope.toOption

/-- Whether a rule whose error field is `field` may carry the group count over `operand`, reading the
    rule's iteration off the checked condition rather than supplying it. -/
private def admitsErrorField (field : FlatFieldDecl) (operand : SurfaceGroupCountOperand) :
    Option Bool := do
  let scope ← iterationScopeOf operand
  pure (ruleErrorScopeCompatible true field scope)

/- `Batches/Boxes*/Seal` reads its batch per row, so the rule iterates `Batches` exactly as every
   other star with an unstarred level above it makes it, while starring the batch too leaves the rule
   without an iteration. Rule assembly then admits an error field inside `Batches` and refuses one
   outside it. The Kernel admits the first rule and draws `MVK_NO_WILDCARD` for the second, on the
   checkpoint's `Batches/Boxes*/BSeal`, the same two-level shape under a `Probe` root
   ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-computation-star-binding-gate));
   this project's refusal there carries no class yet. -/
example :
    iterationScopeOf outerUnstarredSeals = some (some [10]) ∧
    iterationScopeOf boxSeals = some none ∧
    admitsErrorField lot outerUnstarredSeals = some true ∧
    admitsErrorField title outerUnstarredSeals = some false := by
  native_decide

/- An unstarred level below the first star is refused while the operand resolves, with the
   missing-star class, before any iteration is derived; the checkpoint measures it on this carrier
   at both error-field loci. -/
example :
    (match elaborateMixedFilledGroupCountComparison nestedModel ["Item"]
        [starred [{ name := "Batches", starred := true }, { name := "Boxes" }, { name := "Seal" }]]
        .greater 0 with
      | .ok _ => none
      | .error error => error.groupCountDiagnostic?) = some .noWildcard := by
  native_decide

end A12Kernel.Conformance.AncestorStarredGroupCount
