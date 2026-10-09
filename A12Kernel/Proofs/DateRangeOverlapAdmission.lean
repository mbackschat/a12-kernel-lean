import A12Kernel.Semantics.DateRangeOverlapOperators

namespace A12Kernel

/-- Base Year disables the complete agreement test; field legality is a separate earlier gate. -/
theorem dateRangeFormatAgreement_of_baseYear (expansions : List (List String)) :
    dateRangeFormatAgreement true expansions = true := by
  rfl

/-- A single expansion compares spellings even when both formats carry the same year class. -/
theorem dateRangeFormatAgreement_one_reference (left right : String) :
    dateRangeFormatAgreement false [[left, right]] = (left == right) := by
  by_cases h : left = right
  · subst right; simp [dateRangeFormatAgreement]
  · simp [dateRangeFormatAgreement, beq_eq_false_iff_ne.mpr h,
      beq_eq_false_iff_ne.mpr (Ne.symm h)]

/-- Naming fields separately compares year classes rather than their format spellings. -/
theorem dateRangeFormatAgreement_two_references (left right : String) :
    dateRangeFormatAgreement false [[left], [right]] = (left.contains 'y' == right.contains 'y') := by
  simp only [dateRangeFormatAgreement, Bool.false_eq_true, ↓reduceIte, List.all_cons,
    List.all_nil, List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    Bool.and_true, Bool.true_and]
  exact Bool.beq_comm

end A12Kernel
