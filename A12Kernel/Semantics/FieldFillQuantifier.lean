import A12Kernel.Cell
import A12Kernel.Semantics.NumericFillability

/-! # Field-fill quantifier vocabulary and the filled-field count

The validation and computation phases share these seven language-level operators. Their evaluators remain separate because validation observes an extensional tally and a collapsed result, while computation performs ordered, poison-preserving scans.

`NumberOfFilledFields` is the same family's **numeric** member and lives here for the same reason `NumberOfFilledGroups` lives beside the group predicates.
-/

namespace A12Kernel

/-- The seven field-fill operators admitted by the resolved validation and computation capsules. -/
inductive FieldFillQuantifier where
  | allFieldsFilled
  | noFieldFilled
  | atLeastOneFieldFilled
  | moreThanOneFieldFilled
  | notAllFieldsFilled
  | notExactlyOneFieldFilled
  | fieldsNotCollectivelyFilled
  deriving Repr, DecidableEq

/-- The result of `NumberOfFilledFields` in the **validation** arm. It can be unavailable, which is
measured rather than mirrored from the group count: on a two-operand count with one filled operand
beside one **formally invalid** one, kernel 30.8.1 reported the operand's own formal error and fired
**none** of three rules comparing the count to 0, 1, and 2, on both codegen strategies. So an invalid
operand is neither skipped nor counted as filled — the whole count is unavailable. -/
inductive FilledFieldCount where
  | value (count : Nat)
  | unknown
  deriving Repr, DecidableEq

namespace FilledFieldCount

/-- Pair an available validation count with its movement against the declared entity extent. A
    missing entity can only increase the count; exhausting the extent makes it fixed. Cause-free
    count unavailability remains absent rather than acquiring a fabricated formal cause.

    `declaredExtent` is the number of **slots the document can hold**, not the number of fields
    declared. The two differ as soon as the operand's subtree owns a repeatable descendant, and
    passing the declaration count there freezes the movement early
    ([checkpoint](../../docs/SOURCES.md#src-filled-field-count-nested-capacity)). -/
def availableWithFillability? (result : FilledFieldCount)
    (declaredExtent : Nat) : Option (Nat × NumericFillability) :=
  match result with
  | .unknown => none
  | .value count =>
      some (count,
        if count < declaredExtent then .growOnly else .fixed)

end FilledFieldCount

/-- Count the filled operands of `NumberOfFilledFields` in the validation arm.

**An empty cell is never counted, and an invalid one makes the count unavailable.** Both halves are
measured: an all-empty operand list counts `0` and compares normally rather than answering unknown, a
filled-beside-empty pair counts `1`, and a filled-beside-invalid pair answers unknown. The empty rule is
what keeps the count *growable*, so a comparison it satisfies still types OMISSION rather than VALUE.

A `poison` observation is the computation face of the same invalidity and cannot reach this arm; it is
folded into `unknown` so a misrouted observation fails closed rather than counting as filled.

**There is no computation arm, and that is measured rather than deferred.** The group count needs two
arms because an invalid *descendant* leaves its group operand present, so the group count must decide
what to do with it. A field count's invalid operand is the operand itself, so the general
operand-poison rule fires first: measured, the target is CLEARED and its dependents poisoned before any
count is evaluated, which is [`spec/09` §3.2](../../spec/09-computations.md)'s existing rule and not this
operator's to restate. -/
def numberOfFilledFields (cells : List CellObservation) : FilledFieldCount :=
  if cells.any fun cell =>
      match cell with
      | .unknown _ | .poison _ => true
      | .empty | .value _ => false then
    .unknown
  else
    .value (cells.countP fun cell =>
      match cell with
      | .value _ => true
      | .empty | .unknown _ | .poison _ => false)

end A12Kernel
