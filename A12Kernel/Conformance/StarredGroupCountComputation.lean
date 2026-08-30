import A12Kernel.Semantics.GroupPresence

/-! # The computation arm's starred group-count operand

`NumberOfFilledGroups` folds its operand list additively into one result domain, with a
**form-dependent contribution**: a fixed operand contributes an indicator of its descendant
content, a starred repeatable operand contributes that group's instantiated row count. What the
operator is not is a uniform *presence* tally with a wildcard spelling — a presence question
cannot express the second contribution — but the fold itself stays uniform, so one traversal
carrying a form-dependent contribution is enough and no per-form result type is needed.

Measured at the [starred group-count
checkpoint](../../docs/SOURCES.md#src-starred-group-count-computation) over seven documents on
both Kernel codegen strategies. These cases replay that table at the clause that owns the
fold, under a stated mapping from each measured document to an operand reading: a
filled `FlatValue` to a present fixed cell, and `n` instantiated `Rows` to `starredRows n`.
The numbers are measured; that mapping is this project's representation choice and is exactly
what elaboration would have to establish. It does not: the checked scalar computation still
refuses both admitted shapes, fail-closed, and `ResolvedGroupReference.computationDescendants?`
owns that boundary. So these cases carry the clause's meaning, not elaboration coverage.

Two Kernel rows collapse to one reading here — one instantiated row filled and one instantiated
row empty — and the collapse *is* the claim, since a starred operand never reads a cell.
-/

namespace A12Kernel.Conformance.StarredGroupCountComputation

open A12Kernel

/-- `Flat` holding a filled `FlatValue`: one present descendant cell. -/
private def flatFilled : GroupCountOperandReading := .fixed [.value (.num 1)]

/-- `Flat` with nothing in it. The operator tests presence and never reads, so present-empty and
    absent are the same operand reading. -/
private def flatEmpty : GroupCountOperandReading := .fixed [.empty]

/-- `Tally := NumberOfFilledGroups(Rows*)` over a repeatable group holding `n` instantiated rows. -/
private def tally (n : Nat) : Nat :=
  numberOfFilledGroupsForComputationOperands [.starredRows n]

/-- `TallyMixed := NumberOfFilledGroups(Flat, Rows*)`, the measured mixed list. -/
private def tallyMixed (flat : GroupCountOperandReading) (n : Nat) : Nat :=
  numberOfFilledGroupsForComputationOperands [flat, .starredRows n]

/- **The discriminator.** Three instantiated rows carrying no content at all still answer three.
   A presence account answers one here and a filled-row account zero, so the row count is neither
   of them; the one-row and no-row rows keep the answer from being an unconditional constant. -/
example : tally 3 = 3 ∧ tally 1 = 1 ∧ tally 0 = 0 := by
  decide

/- **The mixed separator.** Emptying `Flat` leaves both targets equal, which is what shows the
   fixed operand contributing nothing while the starred one still contributes every row; filling
   it moves the mixed total by exactly one over the same row count. -/
example :
    tallyMixed flatEmpty 2 = tally 2 ∧ tallyMixed flatFilled 2 = tally 2 + 1 := by
  decide

/- The two operand forms are unlike rather than two spellings of one thing: at a fixed row count
   the fixed operand's cells still move the total, where no cell moves the starred operand's. -/
example : tallyMixed flatFilled 0 ≠ tallyMixed flatEmpty 0 := by
  decide

/- The all-absent control. Neither operand form counts unconditionally. -/
example : tallyMixed flatEmpty 0 = 0 := by
  decide

/-- The seven measured documents as `(fixed operand, instantiated rows)`, in capture order. -/
private def kernelRows : List (GroupCountOperandReading × Nat) :=
  [(flatFilled, 0), (flatFilled, 1), (flatFilled, 1), (flatFilled, 2),
    (flatFilled, 3), (flatEmpty, 2), (flatEmpty, 0)]

/- The whole retained table, both targets, row for row. -/
example :
    kernelRows.map (fun row => (tally row.2, tallyMixed row.1 row.2)) =
      [(0, 1), (1, 2), (1, 2), (2, 3), (3, 4), (2, 2), (0, 0)] := by
  decide

end A12Kernel.Conformance.StarredGroupCountComputation
