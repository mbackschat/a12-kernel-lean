import A12Kernel.Elaboration.EnumerationCategoryConstant

/-! # Laws of the enumeration-category constant gate

Three results carry the family. An enumeration value is not a category value, so one literal is
admitted against the plain reading and refused against the category reading of the same field. The
class then depends on the **carrier**: the value list keeps the category and whole-enumeration arms
apart while equality collapses them, so neither carrier's mapping transfers to the other. And an
unknown category is decided before any value is examined, which keeps the value classes meaning what
they say.
-/

namespace A12Kernel

/-- **An enumeration value is not a category value.** One literal, one field, two readings, two
answers — the trap the Kernel's own operator catalog flags as a surprise. -/
theorem enumConstant_enumeration_value_fails_category (carrier : EnumConstantCarrier) :
    enumConstantRefusal carrier .wholeEnumeration { inEnumeration := true } = none ∧
      enumConstantRefusal carrier (.category true) { inEnumeration := true } ≠ none := by
  constructor
  · cases carrier <;> rfl
  · cases carrier <;> simp [enumConstantRefusal, LiteralMembership.satisfies]

/-- **The value list keeps the two arms apart.** The same failing literal reports a different class
depending on whether a category was read. -/
theorem enumConstant_valueList_splits :
    enumConstantRefusal .valueList (.category true) {} =
        some .invalidStringConstantForEnumerationCategory ∧
      enumConstantRefusal .valueList .wholeEnumeration {} =
        some .invalidStringConstantForEnumeration :=
  ⟨rfl, rfl⟩

/-- **Equality collapses them.** The same two readings that split above report one class here, so the
distinction is a property of the carrier and not of the rule. -/
theorem enumConstant_equality_collapses (reading : EnumReading) (membership : LiteralMembership)
    (hdeclared : reading ≠ .category false) (hfails : membership.satisfies reading = false) :
    enumConstantRefusal .equality reading membership =
      some .invalidStringConstantForEnumComparison := by
  cases reading with
  | wholeEnumeration => simp [enumConstantRefusal, hfails]
  | category declared =>
    cases declared
    · exact absurd rfl hdeclared
    · simp [enumConstantRefusal, hfails]

/-- The two carriers therefore disagree on a literal outside a declared category, which is the
nearest false generalisation of either law above. -/
theorem enumConstant_carriers_disagree :
    enumConstantRefusal .valueList (.category true) {} ≠
      enumConstantRefusal .equality (.category true) {} := by
  decide

/-- **An unknown category is decided before any value.** Whatever the literal's memberships, the
category class is what is reported. -/
theorem enumConstant_unknown_category_first (carrier : EnumConstantCarrier)
    (membership : LiteralMembership) :
    enumConstantRefusal carrier (.category false) membership = some .categoryUnknown := by
  cases carrier <;> rfl

/-- And it precedes the list check too, so an all-valid list under an undeclared category still
reports the category class. -/
theorem enumConstantList_unknown_category_first (literals : List LiteralMembership) :
    enumConstantListRefusal (.category false) literals = some .categoryUnknown := rfl

/-- **A list is admitted exactly when every literal satisfies the reading.** -/
theorem enumConstantList_none_iff (reading : EnumReading) (literals : List LiteralMembership)
    (hdeclared : reading ≠ .category false) :
    enumConstantListRefusal reading literals = none ↔
      ∀ membership ∈ literals, membership.satisfies reading = true := by
  have hunfold : enumConstantListRefusal reading literals =
      match literals.find? fun membership => !membership.satisfies reading with
      | none => none
      | some membership => enumConstantRefusal .valueList reading membership := by
    unfold enumConstantListRefusal
    cases reading with
    | wholeEnumeration => rfl
    | category declared =>
      cases declared
      · exact absurd rfl hdeclared
      · rfl
  rw [hunfold]
  cases hfind : literals.find? fun membership => !membership.satisfies reading with
  | none =>
    simp only [true_iff]
    intro membership hmem
    simpa using List.find?_eq_none.1 hfind membership hmem
  | some bad =>
    have hfail : bad.satisfies reading = false := by simpa using List.find?_some hfind
    have hmem := List.mem_of_find?_eq_some hfind
    have hne : enumConstantRefusal .valueList reading bad ≠ none := by
      cases reading with
      | wholeEnumeration => simp [enumConstantRefusal, hfail]
      | category declared =>
        cases declared
        · exact absurd rfl hdeclared
        · simp [enumConstantRefusal, hfail]
    simp only []
    exact ⟨fun h => absurd h hne, fun h => absurd (h bad hmem) (by simp [hfail])⟩

end A12Kernel
