import A12Kernel.Elaboration.EnumerationComparability

/-! # Ordinary Enumeration direct-field comparability laws -/

namespace A12Kernel

/-- Authored labels that all equal their stored tokens are operationally textless for this gate. -/
theorem enumerationDisplay_identityFacts_notEffective
    (profile : ResolvedEnumerationDisplay)
    (identity :
      ∀ fact ∈ profile.facts, fact.display = fact.stored) :
    profile.hasEffectiveDisplay = false := by
  rw [ResolvedEnumerationDisplay.hasEffectiveDisplay,
    List.any_eq_false]
  intro fact member
  simp [EnumerationDisplayFact.isEffectiveDisplay,
    identity fact member]

/-- Pairwise map conflict is independent of operand order. -/
theorem enumerationDisplayFact_conflictsWith_comm
    (left right : EnumerationDisplayFact) :
    left.conflictsWith right = right.conflictsWith left := by
  simp [EnumerationDisplayFact.conflictsWith, bne,
    Bool.beq_comm, Bool.or_comm]

/-- Cross-profile conflict existence is symmetric even when declaration order differs. -/
theorem enumerationDisplay_conflictsWith_comm
    (left right : ResolvedEnumerationDisplay) :
    left.conflictsWith right = right.conflictsWith left := by
  apply Bool.eq_iff_iff.2
  simp only [ResolvedEnumerationDisplay.conflictsWith,
    List.any_eq_true]
  constructor
  · rintro ⟨leftFact, leftMember, rightFact, rightMember, conflict⟩
    exact ⟨rightFact, rightMember, leftFact, leftMember,
      enumerationDisplayFact_conflictsWith_comm leftFact rightFact ▸ conflict⟩
  · rintro ⟨rightFact, rightMember, leftFact, leftMember, conflict⟩
    exact ⟨leftFact, leftMember, rightFact, rightMember,
      enumerationDisplayFact_conflictsWith_comm rightFact leftFact ▸ conflict⟩

/-- A direct String field is comparable with an ordinary Enumeration exactly when that Enumeration has no effective display remapping. -/
theorem stringEnumeration_allowed_iff_textless
    (profile : ResolvedEnumerationDisplay) :
    directFieldComparisonAllowed .plainString (.enumeration profile) =
      !profile.hasEffectiveDisplay := by
  cases effective : profile.hasEffectiveDisplay <;>
    simp [directFieldComparisonAllowed,
      classifyDirectFieldComparison,
      EnumerationComparisonAdmission.isAccepted, effective]

/-- Exactly one display-bearing Enumeration causes the display-class rejection. -/
theorem enumeration_mixedDisplayClass_rejected
    (left right : ResolvedEnumerationDisplay)
    (different :
      (left.hasEffectiveDisplay != right.hasEffectiveDisplay) = true) :
    classifyDirectFieldComparison (.enumeration left) (.enumeration right) =
      .rejected .displayClassMismatch := by
  simp [classifyDirectFieldComparison, different]

/-- Two display-bearing profiles with a shared-locale mapping conflict receive the map-conflict rejection. -/
theorem enumeration_sharedDisplayMapConflict_rejected
    (left right : ResolvedEnumerationDisplay)
    (leftEffective : left.hasEffectiveDisplay = true)
    (rightEffective : right.hasEffectiveDisplay = true)
    (conflict : left.conflictsWith right = true) :
    classifyDirectFieldComparison (.enumeration left) (.enumeration right) =
      .rejected .displayMapConflict := by
  simp [classifyDirectFieldComparison, leftEffective,
    rightEffective, conflict]

/-- Direct-field admission is symmetric. Error payload order never affects whether a comparison is legal. -/
theorem directFieldComparisonAllowed_comm
    (left right : DirectComparableField) :
    directFieldComparisonAllowed left right =
      directFieldComparisonAllowed right left := by
  cases left with
  | plainString =>
      cases right <;>
        simp [directFieldComparisonAllowed,
          classifyDirectFieldComparison]
  | enumeration leftProfile =>
      cases right with
      | plainString =>
          simp [directFieldComparisonAllowed,
            classifyDirectFieldComparison]
      | enumeration rightProfile =>
          rw [directFieldComparisonAllowed,
            directFieldComparisonAllowed,
            classifyDirectFieldComparison,
            classifyDirectFieldComparison]
          rw [enumerationDisplay_conflictsWith_comm
            rightProfile leftProfile]
          cases leftProfile.hasEffectiveDisplay <;>
            cases rightProfile.hasEffectiveDisplay <;>
              simp

end A12Kernel
