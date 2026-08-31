import A12Kernel.Elaboration.NumberValuesNotUnique
import A12Kernel.Elaboration.TokenValuesNotUnique
import A12Kernel.Elaboration.TokenDistinctCount
import A12Kernel.Elaboration.TokenFirstFilledValue
import A12Kernel.Elaboration.CheckedDocument

/-! # The declared-capacity extent reaches the last four operand-stream consumers

Kernel 30.8.1 excludes a row beyond its group's declared repeatability from the **extent** every
operand denotes, and this module locks the four consumers that had no measurement of their own:
uniqueness on the Number and token carriers, the token distinct count, and `FirstFilledValue`. Each
is measured on the operand forms it admits — a starred field, a starred group, and a fixed group —
against an in-capacity control differing only in the offending index
([checkpoint](../../docs/SOURCES.md#src-capacity-consumer-sweep)).

**Only two of the four are separable, and the module says which.** The distinct count and
`FirstFilledValue` answer differently under the two accounts, because an excluded row contributes
nothing while an admitted-and-unavailable one makes the whole result unavailable; the Kernel answers
definitely, so those two consumers now read the in-capacity projection. Uniqueness reaches the same
verdict either way — it skips an unavailable cell as it skips an empty — so no document distinguishes
the accounts for it and its call sites are left alone.
-/

namespace A12Kernel.Conformance.CapacityConsumerSweep

open A12Kernel

private def tag : FlatFieldDecl :=
  { id := 1, groupPath := ["Cap", "TShell", "TRows"], name := "Tag",
    policy := { kind := .string },
    stringPolicy := { lineBreaksPermitted := true }, repeatableScope := [10] }

private def amount : FlatFieldDecl :=
  { id := 2, groupPath := ["Cap", "NShell", "NRows"], name := "Amount",
    policy := { kind := .number { scale := 0, signed := false } },
    repeatableScope := [20] }

/-- Two same-kind shells, because a shell holding both kinds refuses the distinct count's fixed-group
operand outright ([checkpoint](../../docs/SOURCES.md#src-distinct-count-first-operand-class)). -/
private def model : FlatModel :=
  { fields := [tag, amount]
    repeatableGroups := [
      { level := 10, path := ["Cap", "TShell", "TRows"], repeatability := some 2 },
      { level := 20, path := ["Cap", "NShell", "NRows"], repeatability := some 2 }] }

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def tagStar : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [{ name := "Cap" }, { name := "TShell" }, { name := "TRows", starred := true }]
    field := "Tag" }

private def amountStar : SurfaceStarFieldPath :=
  { base := .absolute
    groups := [{ name := "Cap" }, { name := "NShell" }, { name := "NRows", starred := true }]
    field := "Amount" }

private def tagShell : SurfaceGroupPath :=
  { base := .absolute, groups := ["Cap", "TShell"] }

private def tagRowStar : SurfaceStarGroupPath :=
  { base := .absolute
    groups := [{ name := "Cap" }, { name := "TShell" }, { name := "TRows", starred := true }] }

/-- An **absent** entry is how this fixture spells an empty cell: `checkDocument` refuses a cell
input whose stored text is empty, so the emptied rows below simply carry no entry. -/
private def tagCell (row : Nat) (text : String) : ClassifiedCellInput :=
  { address := { field := tag.id, path := [row] }, stored := text,
    raw := .parsed (.str text) }

private def amountCell (row : Nat) (value : Nat) : ClassifiedCellInput :=
  { address := { field := amount.id, path := [row] }, stored := toString value,
    raw := .parsed (.num value) }

private def malformedAmount (row : Nat) : ClassifiedCellInput :=
  { address := { field := amount.id, path := [row] }, stored := "abc",
    raw := .rejected .malformed }

private def document? (rowCount : Nat) (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows :=
      (List.range rowCount).flatMap fun index =>
        [{ group := 10, path := [index + 1] }, { group := 20, path := [index + 1] }]
    cells }).toOption

/-- `FieldValuesNotUnique` over the starred token field, as the retained artifact authors it. -/
private def tokenUnique? (rowCount : Nat) (cells : List ClassifiedCellInput) :
    Option Verdict := do
  let source ←
    (elaborateTokenValuesNotUniqueSource model ["Cap"]
      { first := .star tagStar, rest := [] }).toOption
  let document ← document? rowCount cells
  (source.evaluateCheckedDocumentValuesNotUnique document []).toOption

private def numberUnique? (rowCount : Nat) (cells : List ClassifiedCellInput) :
    Option Verdict := do
  let source ←
    (elaborateNumberValuesNotUniqueSource model ["Cap"]
      { first := .star amountStar, rest := [] }).toOption
  let document ← document? rowCount cells
  (CheckedNumberValuesNotUniqueSource.evaluateCheckedDocumentValuesNotUnique
    source document []).toOption

/-- Only the count is locked, because the artifact reports a fired comparison rather than this
project's own fillability projection. -/
private def distinctCount? (operand : SurfaceTokenDistinctCountOperand)
    (rowCount : Nat) (cells : List ClassifiedCellInput) : Option Rat := do
  let source ←
    (elaborateTokenDistinctCountSource model ["Cap"]
      { first := operand, rest := [] }).toOption
  let document ← document? rowCount cells
  match ← (source.evaluateCheckedDocumentDistinctValidation document []).toOption with
  | .value count _ => some count
  | .unknown _ => none

private def firstFilled? (operand : SurfaceFirstFilledTokenOperand)
    (rowCount : Nat) (cells : List ClassifiedCellInput) :
    Option (Option FirstFilledTokenResult) := do
  let source ←
    (elaborateFirstFilledTokenSource model ["Cap"]
      { first := operand, rest := [] }).toOption
  let document ← document? rowCount cells
  (source.evaluateCheckedGroupFirstFilledValidation? document []).toOption

/- **Uniqueness answers the Kernel's row, and the two accounts coincide there.** `A, B, A` and
   `5, 7, 5` hold their only duplicate pair across rows 1 and 3, and both carriers stay silent — but
   so would a carrier reading the complete view, because an over-limit cell is formally unavailable
   and this operator **skips** an unavailable cell exactly as it skips an empty. No document
   separates the two accounts here, so these rows lock the answer and not the mechanism, and the
   uniqueness call sites are deliberately left on the complete view. The in-capacity control fires,
   which is what keeps the silence from being a dead fixture. -/
example :
    (tokenUnique? 3 [tagCell 1 "A", tagCell 2 "B", tagCell 3 "A"],
     numberUnique? 3 [amountCell 1 5, amountCell 2 7, amountCell 3 5],
     tokenUnique? 2 [tagCell 1 "A", tagCell 2 "A"],
     numberUnique? 2 [amountCell 1 5, amountCell 2 5]) =
    (some .notFired, some .notFired, some (.fired .value), some (.fired .value)) := by
  native_decide

/- **The distinct set that would gain a value from the over-limit row.** `A, A, B` answers `1` on the
   extent and `2` on the complete view, on the starred field and on the fixed group alike, so this
   pair separates the accounts where the duplicate document above cannot. -/
example :
    (distinctCount? (.star tagStar) 3 [tagCell 1 "A", tagCell 2 "A", tagCell 3 "B"],
     distinctCount? (.group (.path tagShell)) 3
       [tagCell 1 "A", tagCell 2 "A", tagCell 3 "B"],
     distinctCount? (.star tagStar) 3 [tagCell 1 "A", tagCell 2 "B", tagCell 3 "A"]) =
    (some 1, some 1, some 2) := by
  native_decide

/- **The value that exists only beyond capacity.** With both in-capacity rows empty and `Z` at the
   over-limit row, the extent account produces no value at all while the complete view would answer
   `Z`. Both group forms agree, and the distinct count answers a definite `0` over the same two empty
   cells rather than going unavailable. -/
example :
    (firstFilled? (.starredGroup tagRowStar) 3
       [tagCell 3 "Z"],
     firstFilled? (.group (.path tagShell)) 3
       [tagCell 3 "Z"],
     distinctCount? (.star tagStar) 3 [tagCell 3 "Z"]) =
    (some (some .noValue), some (some .noValue), some 0) := by
  native_decide

/- **Where the two exclusions meet.** A malformed cell in capacity and a duplicate needing the
   over-limit row: uniqueness skips the malformed operand exactly as it skips an empty, so the
   remaining in-capacity value has no partner and the rule stays silent, while the distinct count
   answers definitely over the reached cells. An implementation that terminalized on the malformed
   cell, or that reached the third row, disagrees here. -/
example :
    (numberUnique? 3 [malformedAmount 1, amountCell 2 5, amountCell 3 5],
     tokenUnique? 3 [tagCell 1 "X", tagCell 2 "Y", tagCell 3 "X"],
     distinctCount? (.star tagStar) 3 [tagCell 1 "X", tagCell 2 "Y", tagCell 3 "X"]) =
    (some .notFired, some .notFired, some 2) := by
  native_decide

/- A group holding no row at all answers `0` and produces no first-filled value, which is the
   ladder's zero member reached positively rather than by the absence of a firing. -/
example :
    (distinctCount? (.star tagStar) 0 [],
     firstFilled? (.starredGroup tagRowStar) 0 []) =
    (some 0, some (some .noValue)) := by
  native_decide

end A12Kernel.Conformance.CapacityConsumerSweep
