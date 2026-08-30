import A12Kernel.Semantics.ComputationSelfValidation

/-! # The implicit self-validation message's type, over a starred operand

Replays the ten retained documents of the [message-polarity
checkpoint](../../docs/SOURCES.md#src-starred-operand-message-polarity) at the clause that derives
the type, on both Kernel codegen strategies' agreeing observation.

The computed values are **inputs** here, read off the same capture; the clauses that produce them
are locked elsewhere. What these cases lock is the mapping from a document's growth state to the
message type, under a stated mapping from each measured document to an operand list — a filled
`FlatValue` to a present fixed group, `n` instantiated `Rows` of a `max 5` group to that operand's
row state, and whether every instantiated row carries its `RowValue`.

The ten documents all have their computed value **below** the stored seed, so none of them
separates the directional reading from a coarser "can it move at all" one. The separating document
was measured afterwards and is locked below; the account here is the rule arm's, and it survives.
-/

namespace A12Kernel.Conformance.ComputationSelfValidation

open A12Kernel

/-- Declared `repeatability` of `/Probe/Rows` in every model these documents use. -/
private def capacity : Nat := 5

/-- `NumberOfFilledGroups(Flat, Other)` — the wildcard-free control target. -/
private def fixedPair (flat other : Bool) : List ComputationOperandGrowth :=
  [.fixedGroup flat, .fixedGroup other]

/-- `NumberOfFilledGroups(Rows*)`. -/
private def starCount (rows : Nat) : List ComputationOperandGrowth :=
  [.starredGroupCount rows capacity]

/-- `NumberOfFilledGroups(Flat, Rows*)`. -/
private def mixedCount (flat : Bool) (rows : Nat) : List ComputationOperandGrowth :=
  [.fixedGroup flat, .starredGroupCount rows capacity]

/-- `Sum(Rows*/RowValue)`. -/
private def starSum (rows : Nat) (everyRowCellFilled : Bool) : List ComputationOperandGrowth :=
  [.starredRowValues rows capacity everyRowCellFilled]

private def typeOf (stored computed : Rat) (operands : List ComputationOperandGrowth) : Verdict :=
  computedNumberSelfValidation stored computed operands

/- **The capacity boundary.** One document apart in row count alone, at a seed no row can reach.
   With five of five rows filled every target is fixed and types VALUE; with four of five the three
   starred targets can still grow and type OMISSION, while the wildcard-free pair stays VALUE in
   both. One row of remaining capacity is the entire difference. -/
example :
    [typeOf 99 2 (fixedPair true true), typeOf 99 5 (starCount 5),
      typeOf 99 6 (mixedCount true 5), typeOf 99 5 (starSum 5 true)] =
      [.fired .value, .fired .value, .fired .value, .fired .value] := by
  native_decide

example :
    [typeOf 99 2 (fixedPair true true), typeOf 99 4 (starCount 4),
      typeOf 99 5 (mixedCount true 4), typeOf 99 4 (starSum 4 true)] =
      [.fired .value, .fired .omission, .fired .omission, .fired .omission] := by
  native_decide

/- **The separator.** Five of five rows, every row empty: the two counts cannot move, because a
   count grows only by rows and capacity is exhausted, while the sum over the same rows still can,
   because a row's empty cell can be filled. Operand form is held constant and the two starred
   targets still differ, which is what rules out an account keyed on starredness itself. -/
example :
    [typeOf 99 2 (fixedPair true true), typeOf 99 5 (starCount 5),
      typeOf 99 6 (mixedCount true 5), typeOf 99 0 (starSum 5 false)] =
      [.fired .value, .fired .value, .fired .value, .fired .omission] := by
  native_decide

/- The witness run, two of five rows with every cell filled. The wildcard-free target reads its own
   cells and types VALUE; the three with headroom type OMISSION even though every referenced cell
   is filled. Below capacity, so it corroborates the boundary rather than establishing it. -/
example :
    [typeOf 9 2 (fixedPair true true), typeOf 9 2 (starCount 2),
      typeOf 9 3 (mixedCount true 2), typeOf 99 15 (starSum 2 true)] =
      [.fired .value, .fired .omission, .fired .omission, .fired .omission] := by
  native_decide

/- No rows at all. The starred targets keep their whole capacity as headroom. -/
example :
    [typeOf 9 2 (fixedPair true true), typeOf 9 0 (starCount 0),
      typeOf 9 1 (mixedCount true 0), typeOf 99 0 (starSum 0 true)] =
      [.fired .value, .fired .omission, .fired .omission, .fired .omission] := by
  native_decide

/- Both fixed operands emptied. The wildcard-free target flips to OMISSION, which is what shows
   its VALUE above reading its own cells rather than being an inert default for a starless list. -/
example :
    [typeOf 9 0 (fixedPair false false), typeOf 9 1 (starCount 1),
      typeOf 9 1 (mixedCount false 1), typeOf 99 7 (starSum 1 true)] =
      [.fired .omission, .fired .omission, .fired .omission, .fired .omission] := by
  native_decide

/- The three all-referenced-filled documents of the third capture, on the two-target model. Every
   referenced cell is filled in the first two and the fixed group is empty in the third, and all
   six type OMISSION — headroom, not cell content, is what decides. -/
example :
    [typeOf 9 1 (starCount 1), typeOf 9 2 (mixedCount true 1),
      typeOf 9 2 (starCount 2), typeOf 9 3 (mixedCount true 2),
      typeOf 9 2 (starCount 2), typeOf 9 2 (mixedCount false 2)] =
      List.replicate 6 (.fired .omission) := by
  native_decide

/- **The control.** A seed already equal to its computed value produces no message at all, which is
   the established changed-subset projection and is what makes every row above a stored-versus-
   computed mismatch rather than an independent finding. -/
example : typeOf 2 2 (starCount 2) = .notFired ∧ typeOf 3 3 (mixedCount true 2) = .notFired := by
  native_decide

/-! ## Direction

Measured after the ten documents above, on the separating document none of them supplies.
-/

/- **The direction discriminator.** One document, one variable: the stored seed. A grow-only count
   three of five rows deep with every cell filled types VALUE when its computed `3` already
   *exceeds* a seed of `1`, because growing moves it further away, and OMISSION at a seed of `9`.
   A coarse "can the quantity move at all" account predicts OMISSION on both and is refuted here;
   headroom is necessary but not sufficient. -/
example :
    typeOf 1 3 (starCount 3) = .fired .value ∧
      typeOf 9 3 (starCount 3) = .fired .omission := by
  native_decide

/-! ## `fillToFix` -/

private def referenced : List MessagePointer :=
  [{ field := 0, coordinates := [] }, { field := 1, coordinates := [] }]

/- The projection is the whole referenced set or nothing. **The trap:** in the witness document
   every referenced cell is filled, and the mixed target's OMISSION still lists them all — so a
   listed pointer is not a claim that this cell is empty. The two counts differ in that same
   document only through the target's own headroom. -/
example :
    selfValidationFillToFix referenced (typeOf 9 3 (mixedCount true 2)) = referenced ∧
      selfValidationFillToFix referenced (typeOf 9 2 (fixedPair true true)) = [] := by
  native_decide

/- No message carries a proper subset, and the no-message case carries none either. -/
example :
    selfValidationFillToFix referenced (typeOf 2 2 (starCount 2)) = [] ∧
      selfValidationFillToFix referenced (typeOf 99 0 (starSum 5 false)) = referenced := by
  native_decide

end A12Kernel.Conformance.ComputationSelfValidation
