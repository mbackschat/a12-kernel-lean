import A12Kernel.Elaboration.NumericComputation.Core
import A12Kernel.Elaboration.CheckedStarShape
import A12Kernel.Elaboration.ValidationCondition.Reference
import A12Kernel.Semantics.ComputationSelfValidation

/-! # Checked inputs to a computed target's self-validation message

A computed Number target whose value disagrees with its stored cell carries a formal message. This
module owns the fields named by a `NumberOfFilledGroups` target and the reference and growth
projections of the measured plain-star `Sum` carrier. It constructs no text or message.

## Referenced fields

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

The measured plain-star `Sum` additionally projects through the shared checked reference owner, so
its source field carries an unbound coordinate while its nonrepeatable computed target stays exact.
Its field inventory is the field projection of those pointers rather than a second owner.
-/

namespace A12Kernel

namespace CheckedGroupCountOperand

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

/-! ## Plain-star `Sum` projections -/

namespace CheckedNumberEntitySource

/-- Narrow a checked Number source to the measured plain-star `Sum` carrier.

    The shared direct-single-star predicate owns the one-axis declaration shape. This narrowing
    adds the operator-local requirements: one authored operand and a finite declared capacity. -/
def plainStarSumCarrier? (checked : CheckedNumberEntitySource model) :
    Option (CheckedStarNumberSource model × Nat) :=
  match checked.first, checked.rest with
  | .star source, [] =>
      if source.source.isDirectSingleStar then
        source.source.path.axes.head?.bind fun axis =>
          axis.repeatability.map fun capacity => (source, capacity)
      else
        none
  | _, _ => none

/-- Derive the implicit-message growth channel for the measured checked `Sum` carrier.

    The closed carrier is exactly one plain Number star declared directly in one reopened axis
    with finite capacity. The immutable checked document supplies the same in-capacity cells that
    aggregate evaluation reads. Filtered, nested, mixed, direct, unbounded, and formally
    unavailable sources return `none`; structural checked-document failures remain explicit. -/
def plainStarSumGrowth? (checked : CheckedNumberEntitySource model)
    (document : CheckedDocument model) (outer : Env) :
    Except CheckedAddressingError (Option ComputationOperandGrowth) :=
  match checked.plainStarSumCarrier? with
  | none => pure none
  | some (_, capacity) => do
      let resolved ← checked.first.resolveCheckedValidationOperand document outer
      let side := resolved.inCapacityValueListSideAt .computation
      match side.available with
      | .error _ => pure none
      | .ok _ =>
          pure (some (.starredRowValues side.cells.length capacity
            (!side.hasEmpty)))

end CheckedNumberEntitySource

namespace CheckedNumericComputationOperation

/-- Derive the formal-message pointers for the measured plain-star `Sum` carrier.

    The source delegates to [`CheckedNumberEntitySource.referencePointers`] so the reopened axis
    remains wildcarded, matching the computation-message coordinate observation in
    [`spec/10`](../../../spec/10-validation-and-polarity.md#41-the-same-rule-fires-either-type).
    The checked computation target is admitted only as a nonrepeatable Number field by
    [`FlatModel.admitsNumericComputationTarget`], so its pointer is the exact empty path. The list
    order is deterministic only; the observed message channel is a set. Filtered, nested, mixed,
    direct, unbounded, and non-`Sum` shapes remain outside this projection. -/
def plainStarSumReferencedPointers?
    (checked : CheckedNumericComputationOperation model) :
    Except ReferenceProjectionError (Option (List MessagePointer)) :=
  match checked.core.expression with
  | .atom (.numeric (.aggregate .sum source)) =>
      match source.plainStarSumCarrier? with
      | none => pure none
      | some _ => do
          let sourcePointers ← source.referencePointers []
          pure (some (sourcePointers ++ [
            MessagePointer.ofCellAddr { field := checked.core.target.id, path := [] }]))
  | _ => pure none

end CheckedNumericComputationOperation

end A12Kernel
