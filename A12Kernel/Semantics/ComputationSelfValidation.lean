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

Measured at the [message-polarity checkpoint](../../docs/sources/group-and-iteration-probes.md#src-starred-operand-message-polarity)
over ten documents on both Kernel codegen strategies, and the direction separately afterwards on the
document none of those ten supplies: headroom is necessary but not sufficient, since a quantity whose
computed value already exceeds its seed types VALUE despite having room to grow. Growth itself was
exercised only through row count and cell fill.
-/

namespace A12Kernel

/-- What one operand of a computed Number target can still contribute, as a growth channel.

    The constructors are the measured split, not a taxonomy: a count over a fixed group grows by
    content, a count over a starred group grows by rows, and a value read inside starred rows grows
    by either. The separating document holds a starred group at declared capacity with every row
    empty — there the count cannot move and a sum over the same rows still can. A count over a fixed
    group below a star grows by content in any instance, which the same document separates from the
    row count ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-ancestor-starred-group-count-computation)). -/
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
  /-- A fixed group below a starred level, with `present` of its `extent` instances holding
      content, one instance per environment the star can reopen. An instantiated but empty instance
      leaves it open even at full row capacity. -/
  | fixedGroupInstances (present extent : Nat)
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
  | .fixedGroupInstances present extent => present < extent

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

/-- The implicit self-validation verdict once it is known whether validation's own reading of the
    operation answers.

    The message is a generated validation rule
    ([§6](../../spec/09-computations.md#6-the-implicit-validation-rule-precisely)). Where that
    reading leaves the operation unavailable the rule has no answer, `.unknown`, which fires nothing
    and carries no message, even though the computation writes its value. -/
def computedNumberSelfValidationIfDecided (decided : Bool) (stored computed : Rat)
    (operands : List ComputationOperandGrowth) : Verdict :=
  if decided then computedNumberSelfValidation stored computed operands else .unknown

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
