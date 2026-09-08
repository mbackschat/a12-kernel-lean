import A12Kernel.Elaboration.RepeatabilityRestriction

/-! # Locks on the repeatability-restriction reading

Source-derived. The measured negative that bounds it is that a rule deriving the refusing bound is
admitted by both available gates and leaves the model valid, so the shape is legal and the pass
simply is not reached ([checkpoint](../../docs/SOURCES.md#src-repeatability-restriction)). The matrix
separates the four spellings onto two bounds, the three-way outcome in both spellings, the per-rule
refusal against aggregation, the minimum, and the group side's six-part shape gate.
-/

namespace A12Kernel.Conformance.RepeatabilityRestriction

open A12Kernel

private def outcome (comparison : RestrictionComparison) (constant : Int) : RestrictionOutcome :=
  restrictionOutcome .groupContext comparison constant

private def key? (comparison : RestrictionComparison) (constant : Int) : Option String :=
  match restrictionOutcome .groupContext comparison constant with
  | .refused diagnostic => some diagnostic.kernelCode
  | _ => none

/- **Four spellings, two bounds.** Mirroring the operator is meaning-preserving, and the strict and
   non-strict forms of one numeral differ by one — so the same `2` restricts to two or refuses,
   depending only on the operator. -/
example :
    declaredMaximum .countGreaterThan 2 = 2 ∧
      declaredMaximum .constantLessThan 2 = 2 ∧
      declaredMaximum .countAtLeast 2 = 1 ∧
      declaredMaximum .constantAtMost 2 = 1 := by
  native_decide

/- **The three-way outcome, non-monotone in the bound.** Two restricts, one refuses, zero and below
   are silent — so the refusal is a point and not a threshold, and the fourth row is the one a
   "must be at least two" guard gets wrong. -/
example :
    outcome .countGreaterThan 3 = .restricts 3 ∧
      outcome .countGreaterThan 2 = .restricts 2 ∧
      outcome .countGreaterThan 1 = .refused .maxGroupRestrictionToOne ∧
      outcome .countGreaterThan 0 = .ignored ∧
      outcome .countGreaterThan (-4) = .ignored := by
  native_decide

/- The same three points shifted by one in the non-strict spelling, which is what makes the bound
   derivation observable rather than an internal step. -/
example :
    outcome .countAtLeast 3 = .restricts 2 ∧
      outcome .countAtLeast 2 = .refused .maxGroupRestrictionToOne ∧
      outcome .countAtLeast 1 = .ignored := by
  native_decide

/- **The two carriers report different classes for the identical bound**, and nothing else about them
   differs. -/
example :
    key? .countGreaterThan 1 = some "MVK_MAX_GROUP_RESTRICTION_TO_ONE" ∧
      (match restrictionOutcome .formSerial .countGreaterThan 1 with
       | .refused diagnostic => some diagnostic.kernelCode
       | _ => none) = some "MVK_MAX_LFDNR_RESTRICTION_TO_ONE" ∧
      restrictionOutcome .formSerial .countGreaterThan 4 =
        restrictionOutcome .groupContext .countGreaterThan 4 := by
  native_decide

/- **Refusal is per rule and precedes aggregation.** A carrier holding a refusing rule beside a
   restricting one still aggregates to the restricting rule's bound and still reports the class, so a
   consumer reading only the aggregate misses the refusal and one reading only the refusal misses the
   bound. -/
example :
    restrictionRefusals .groupContext [(.countGreaterThan, 1), (.countGreaterThan, 5)] =
        [.maxGroupRestrictionToOne] ∧
      effectiveMaximum [outcome .countGreaterThan 1, outcome .countGreaterThan 5] = some 5 ∧
      effectiveMaximum [outcome .countGreaterThan 7, outcome .countGreaterThan 5] = some 5 ∧
      effectiveMaximum [outcome .countGreaterThan 0, outcome .countGreaterThan 5] = some 5 := by
  native_decide

/- No restricting rule at all leaves the declared repeatability standing, which is a different answer
   from a restriction that happens to be large. -/
example :
    effectiveMaximum [] = none ∧
      effectiveMaximum [outcome .countGreaterThan 0, outcome .countGreaterThan 1] = none ∧
      effectiveMaximum [outcome .countGreaterThan 9] = some 9 := by
  native_decide

/- **The group side's shape gate, each condition alone.** Six operands, each differing from the
   admitted one in a single flag, and every one of them makes the rule ordinary rather than refused —
   the bound that would otherwise refuse is unchanged throughout. -/
example :
    groupRestrictionOutcome {} .countGreaterThan 1 = .refused .maxGroupRestrictionToOne ∧
      groupRestrictionOutcome { isFilledGroupCount := false } .countGreaterThan 1 = .ignored ∧
      groupRestrictionOutcome { singleEntity := false } .countGreaterThan 1 = .ignored ∧
      groupRestrictionOutcome { noSemanticIndex := false } .countGreaterThan 1 = .ignored ∧
      groupRestrictionOutcome { noFilterCondition := false } .countGreaterThan 1 = .ignored ∧
      groupRestrictionOutcome { wildcardAtLowestLevel := false } .countGreaterThan 1 = .ignored ∧
      groupRestrictionOutcome { noWildcardAbove := false } .countGreaterThan 1 = .ignored := by
  native_decide

end A12Kernel.Conformance.RepeatabilityRestriction
