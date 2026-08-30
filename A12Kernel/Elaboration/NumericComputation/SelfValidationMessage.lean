import A12Kernel.Elaboration.NumericComputation.Core

/-! # The referenced-field inventory of a computed target's self-validation message

A computed Number target whose value disagrees with its stored cell carries a formal message naming
the cells behind it. This module owns **which fields** that message names for a
`NumberOfFilledGroups` target. It constructs no pointer coordinates, no text, and no message.

The extent is each operand's **own reach**. Every operand of this operator is a group, so each names
the fields anywhere in its subtree at any depth and however many there are, which is exactly what
the count reads, and both
operand forms use that one extent — the message does not distinguish a fixed operand from a starred
one, the distinction living in the coordinates rather than the field set. Do not carry the subtree
rule to a **field** operand of another carrier: a `Sum` over one flattened field is measured to name
that field alone and not its sibling.

Two properties matter to a consumer and neither is visible from the type. It is an **authored-shape
inventory, not a reached-cell trace**, and the sharp form of that is invariance: the set is
byte-identical between a document with no instantiated row and one whose every row cell is filled,
which a partially-read account cannot produce. And the channel is a **set** — the retained observations arrive ordered by
their rendered spelling, which is the capture's normalization rather than a Kernel guarantee, so no
order is claimed here.

Only the field half is modelled, and that is this project's boundary rather than the observation's.
Each named cell also carries repetition coordinates in two spellings — bare for a repetition-free
address, and carrying its axes for one crossing a repeatable group, where the starred axis is
**unbound** rather than a row index. That value is measured off the Kernel pointer's own repetition
indexes and is invariant in the row count, so the domain question is answered; representing it here
belongs to [`SEMANTICS-GAPS.md`](../../../docs/SEMANTICS-GAPS.md)'s SG10.
-/

namespace A12Kernel

namespace CheckedGroupCountOperand

/-- The group whose content this operand weighs, whichever form it takes. -/
def groupPath : CheckedGroupCountOperand model → GroupPath
  | .fixed reference => reference.path
  | .starred source => source.group.path

/-- The fields this operand names in the target's self-validation message.

    The whole subtree at any depth, measured on a group whose only field lies two levels below it
    and again on one whose only content is a repeatable descendant. A group's own depth therefore
    does not bound what the message reports. -/
def referencedFields (operand : CheckedGroupCountOperand model) (model' : FlatModel) :
    List FieldId :=
  (model'.groupSubtreeFields operand.groupPath).map (·.id)

end CheckedGroupCountOperand

/-- Every field a `NumberOfFilledGroups` target's self-validation message names.

    The operands' subtree fields together with the computed target itself. A repeated operand
    contributes its fields once per authored position, matching the fold; deduplication is a
    consumer's choice and is deliberately not made here, since the channel's own multiplicity is
    unmeasured. -/
def referencedFieldsForFilledGroupCount (model : FlatModel)
    (operands : List (CheckedGroupCountOperand model)) (target : FieldId) : List FieldId :=
  operands.flatMap (·.referencedFields model) ++ [target]

end A12Kernel
