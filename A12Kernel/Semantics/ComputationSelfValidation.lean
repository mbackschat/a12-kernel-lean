import A12Kernel.Semantics.ComputationMessage
import A12Kernel.Semantics.NumericComparison

/-! # A computed Number target's implicit self-validation message

A computed target that disagrees with its stored cell carries a formal message of its own, with no
authored condition behind it. This module derives that message's **type** and its `fillToFix`
projection; it constructs no text, no pointer, and no referenced set.

The type is not a new rule. The fired condition is the computed value differing from the stored
one, and `NumericComparisonOp.notEqual` already types exactly that firing from directional
fillability, so this carrier reuses it outright rather than restating it. What the carrier
supplies is the computed side's fillability, which is where the measured content sits: **each
operator reads headroom against its own quantity**, so two computations over the same starred
group can type differently in one document.

Measured at the [message-polarity checkpoint](../../docs/SOURCES.md#src-starred-operand-message-polarity)
over ten documents on both Kernel codegen strategies. Two limits ride along. Every retained row has
the computed value **below** its stored seed, so the rows are equally consistent with a coarser
account that ignores direction; the directional reading is inherited from the rule arm rather than
separated here. And growth was exercised only through row count and cell fill.
-/

namespace A12Kernel

/-- What one operand of a computed Number target can still contribute, as a growth channel.

    The three constructors are the measured split, not a taxonomy: a count over a fixed group
    grows by content, a count over a starred group grows by rows, and a value read inside starred
    rows grows by either. The separating document holds a starred group at declared capacity with
    every row empty — there the count cannot move and a sum over the same rows still can. -/
inductive ComputationOperandGrowth where
  /-- A fixed group operand, contributing an indicator of its subtree content.

      A present operand is **closed**, because the indicator is capped at one and no fill can move
      it further — including a group already present through one instantiated row of a repeatable
      descendant, which can gain rows without gaining contribution. That case is a consequence of
      the cap rather than a measurement: every measured document types its polarity from operands
      with no repeatable descendant. -/
  | fixedGroup (present : Bool)
  /-- A starred group operand counted by rows, at `instantiated` of `capacity` declared rows. -/
  | starredGroupCount (instantiated capacity : Nat)
  /-- An operand reading cells inside starred rows, which a new row or a new value can move. -/
  | starredRowValues (instantiated capacity : Nat) (everyRowCellFilled : Bool)
  deriving Repr, DecidableEq

namespace ComputationOperandGrowth

/-- Whether a legal move can still change this operand's contribution.

    Emptying a cell is not a fill, so no channel here shrinks; every quantity these operands feed
    is grow-only. -/
def canGrow : ComputationOperandGrowth → Bool
  | .fixedGroup present => !present
  | .starredGroupCount instantiated capacity => instantiated < capacity
  | .starredRowValues instantiated capacity everyRowCellFilled =>
      instantiated < capacity || !everyRowCellFilled

end ComputationOperandGrowth

/-- The computed side's directional fillability, from the operand list the computation reads. -/
def computedNumberFillability (operands : List ComputationOperandGrowth) : NumericFillability :=
  { canGrow := operands.any ComputationOperandGrowth.canGrow, canShrink := false }

/-- The implicit self-validation verdict of a computed Number target.

    `notFired` is the equal-seed case, which produces no message and no computed outcome at all.
    The stored side is `fixed` because the target is written by the computation rather than by a
    filler; the at-capacity documents discharge that, since a stored side able to shrink would
    have typed them OMISSION. -/
def computedNumberSelfValidation (stored computed : Rat)
    (operands : List ComputationOperandGrowth) : Verdict :=
  NumericComparisonOp.notEqual.eval
    (.value computed (computedNumberFillability operands))
    (.value stored NumericFillability.fixed)

/-- The message's `fillToFix` projection.

    **It is one decision spelled as a list, not a per-cell analysis.** An OMISSION message carries
    its whole referenced set — including cells that are already filled, whenever some *other*
    channel is open — and a VALUE message carries none. Across every retained observation the set
    is exactly `referenced` or exactly empty, never a proper subset, so a consumer must not read a
    listed pointer as a claim that this cell is empty. -/
def selfValidationFillToFix (referenced : List MessagePointer) :
    Verdict → List MessagePointer
  | .fired .omission => referenced
  | .fired .value => []
  | .notFired => []
  | .unknown => []

end A12Kernel
