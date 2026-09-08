import A12Kernel.Elaboration.RepeatabilityRestriction

/-! # Laws of the repeatability-restriction reading

Four results carry the family. Mirroring the comparison preserves the bound, so four spellings
collapse onto two and the strict form of a constant equals the non-strict form of its successor. The
outcome is non-monotone in that bound: two restricts, one refuses, zero is silently ignored, so the
refusal is a point rather than a threshold. Refusal is decided per rule and before aggregation, so it
survives a neighbouring rule that would restrict the same carrier further. And aggregation takes the
minimum over the restricting rules only.
-/

namespace A12Kernel

/-- **Mirroring preserves the bound.** Writing the constant first changes nothing, which is what makes
strictness the only content of the spelling. -/
theorem declaredMaximum_mirror (constant : Int) :
    declaredMaximum .countGreaterThan constant = declaredMaximum .constantLessThan constant ∧
      declaredMaximum .countAtLeast constant = declaredMaximum .constantAtMost constant :=
  ⟨rfl, rfl⟩

/-- **The two bounds are one apart**, so the same numeral declares different maxima in the two forms
and a non-strict rule is the strict rule of its predecessor. -/
theorem declaredMaximum_strict_succ (constant : Int) :
    declaredMaximum .countAtLeast constant = declaredMaximum .countGreaterThan (constant - 1) := by
  simp [declaredMaximum, RestrictionComparison.isStrict]

/-- **The outcome is non-monotone in the derived bound**: it restricts at two, refuses at one, and is
silent at zero. A consumer guarding "at least two" reports on the third, which the Kernel does not. -/
theorem restrictionOutcome_three_way (carrier : RepetitionCarrier) :
    restrictionOutcome carrier .countGreaterThan 2 = .restricts 2 ∧
      restrictionOutcome carrier .countGreaterThan 1 = .refused carrier.restrictionToOne ∧
      restrictionOutcome carrier .countGreaterThan 0 = .ignored := by
  cases carrier <;> simp [restrictionOutcome, declaredMaximum, RestrictionComparison.isStrict,
    RepetitionCarrier.restrictionToOne]

/-- The same three points in the non-strict spelling sit one higher, which is the observable
consequence of the bound law above. -/
theorem restrictionOutcome_nonStrict_shifted (carrier : RepetitionCarrier) :
    restrictionOutcome carrier .countAtLeast 3 = .restricts 2 ∧
      restrictionOutcome carrier .countAtLeast 2 = .refused carrier.restrictionToOne ∧
      restrictionOutcome carrier .countAtLeast 1 = .ignored := by
  cases carrier <;> simp [restrictionOutcome, declaredMaximum, RestrictionComparison.isStrict,
    RepetitionCarrier.restrictionToOne]

/-- **The two carriers differ only in the class they report.** Their bounds and their three-way split
are one mechanism. -/
theorem restrictionOutcome_carriers_agree_except_class (comparison : RestrictionComparison)
    (constant : Int) (h : declaredMaximum comparison constant ≠ 1) :
    restrictionOutcome .formSerial comparison constant =
      restrictionOutcome .groupContext comparison constant := by
  simp only [restrictionOutcome]
  have : (declaredMaximum comparison constant == 1) = false := by
    simpa using h
  simp [this]

/-- **A refused rule contributes nothing to the aggregate**, and neither does an ignored one — so a
carrier restricted to one by a bad rule and to five by a good one still aggregates to five while the
class is reported. Refusal is per rule and prior to aggregation. -/
theorem effectiveMaximum_ignores_nonRestricting (carrier : RepetitionCarrier) :
    effectiveMaximum
        [restrictionOutcome carrier .countGreaterThan 1,
         restrictionOutcome carrier .countGreaterThan 5,
         restrictionOutcome carrier .countGreaterThan 0] = some 5 ∧
      restrictionRefusals carrier [(.countGreaterThan, 1), (.countGreaterThan, 5)] =
        [carrier.restrictionToOne] := by
  cases carrier <;> exact ⟨rfl, rfl⟩

/-- **Aggregation takes the minimum**, in either rule order. -/
theorem effectiveMaximum_min (first second : Int) :
    effectiveMaximum [.restricts first, .restricts second] = some (min first second) ∧
      effectiveMaximum [.restricts second, .restricts first] = some (min second first) := by
  constructor <;> simp [effectiveMaximum, RestrictionOutcome.contributedMaximum]

/-- No restricting rule leaves the carrier's declared repeatability standing. -/
theorem effectiveMaximum_none :
    effectiveMaximum [] = none ∧ effectiveMaximum [.ignored, .refused .maxGroupRestrictionToOne] =
      none := by
  constructor <;> rfl

/-- **The group side's shape gate makes a non-matching operand ordinary, never refused.** Each of the
six conditions alone suppresses the reading. -/
theorem groupRestrictionOutcome_shape_gate (comparison : RestrictionComparison) (constant : Int)
    (operand : GroupCountOperand) (h : operand.isRestrictionShape = false) :
    groupRestrictionOutcome operand comparison constant = .ignored := by
  simp [groupRestrictionOutcome, h]

end A12Kernel
