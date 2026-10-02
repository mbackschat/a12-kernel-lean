import A12Kernel.Semantics.Condition

/-! # Negating a condition tree

The A12 condition language has no `Not` (spec §A.2): every negative check is its own predicate. Rule
negation is therefore a rewrite, not an operator. It pushes the negation through `And` and `Or` by De
Morgan and replaces each leaf with the tree its family supplies as the leaf's complement, which may be
a single predicate (`FieldNotFilled` for `FieldFilled`) or a compound one (`AllFieldsFilled Or
NoFieldFilled` for `FieldsNotCollectivelyFilled`).

The relation the rewrite preserves is stated on firing, because a leaf's false-versus-unknown split
is invisible on a rule's outcome ([kf233](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf233)): see
`Proofs/ConditionNegation`. Polarity is not part of it.
-/

namespace A12Kernel

namespace Verdict

/-- Whether a verdict emits a message, in either polarity. -/
def fires : Verdict → Bool
  | .fired _ => true
  | .notFired | .unknown => false

end Verdict

namespace ConditionTree

/-- De Morgan negation with a caller-supplied complement per leaf. -/
def negate (complement : Leaf → ConditionTree Leaf) : ConditionTree Leaf → ConditionTree Leaf
  | .leaf value => complement value
  | .and left right => .or (left.negate complement) (right.negate complement)
  | .or left right => .and (left.negate complement) (right.negate complement)

end ConditionTree

end A12Kernel
