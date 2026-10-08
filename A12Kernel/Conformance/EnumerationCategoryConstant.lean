import A12Kernel.Elaboration.EnumerationCategoryConstant

/-! # Locks on the enumeration-category constant gate

Every row replays a measured one: twelve conditions on a model with three enumeration values and one
two-valued category, across both carriers
([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-enumeration-category-constant)).
-/

namespace A12Kernel.Conformance.EnumerationCategoryConstant

open A12Kernel

/-- A literal that is one of the enumeration's own values and not one of the category's — the trap. -/
private def enumValueOnly : LiteralMembership := { inEnumeration := true }

/-- A literal valid for the read category. -/
private def categoryValue : LiteralMembership := { inCategory := true }

/-- A literal valid for neither. -/
private def strayValue : LiteralMembership := {}

private def key? (carrier : EnumConstantCarrier) (reading : EnumReading)
    (membership : LiteralMembership) : Option String :=
  (enumConstantRefusal carrier reading membership).map KernelStaticDiagnostic.kernelCode

private def listKey? (reading : EnumReading) (literals : List LiteralMembership) : Option String :=
  (enumConstantListRefusal reading literals).map KernelStaticDiagnostic.kernelCode

/- **The equality carrier, all four measured rows.** A category value is admitted; an enumeration
   value against the category reading is refused; a stray literal is refused; and the same
   enumeration value against the plain reading is admitted — which is what makes the second row the
   category's doing and not the literal's. -/
example :
    key? .equality (.category true) categoryValue = none ∧
      key? .equality (.category true) enumValueOnly =
        some "MVK_INVALID_STRING_CONSTANT_FOR_ENUM_COMPARISON" ∧
      key? .equality (.category true) strayValue =
        some "MVK_INVALID_STRING_CONSTANT_FOR_ENUM_COMPARISON" ∧
      key? .equality .wholeEnumeration enumValueOnly = none ∧
      key? .equality .wholeEnumeration strayValue =
        some "MVK_INVALID_STRING_CONSTANT_FOR_ENUM_COMPARISON" := by
  native_decide

/- **The value-list carrier splits where equality collapsed.** The same two readings and the same two
   literals, four rows, and two distinct classes — so the carrier and not the rule decides the
   vocabulary. -/
example :
    key? .valueList (.category true) categoryValue = none ∧
      key? .valueList (.category true) enumValueOnly =
        some "MVK_INVALID_STRING_CONSTANT_FOR_ENUMERATION_CATEGORY" ∧
      key? .valueList .wholeEnumeration enumValueOnly = none ∧
      key? .valueList .wholeEnumeration strayValue =
        some "MVK_INVALID_STRING_CONSTANT_FOR_ENUMERATION" := by
  native_decide

/- **The two carriers disagree on one input**, stated as the row a consumer reusing one mapping on
   the other gets wrong. -/
example :
    key? .valueList (.category true) enumValueOnly ≠
      key? .equality (.category true) enumValueOnly := by
  native_decide

/- **An undeclared category is refused before any literal is examined**, on both carriers and even
   for a literal that would satisfy everything. -/
example :
    key? .equality (.category false) categoryValue = some "MVK_CATEGORY_UNKOWN" ∧
      key? .valueList (.category false) categoryValue = some "MVK_CATEGORY_UNKOWN" ∧
      listKey? (.category false) [categoryValue, categoryValue] = some "MVK_CATEGORY_UNKOWN" := by
  native_decide

/- **A list is admitted only when every literal satisfies the reading.** The all-valid pair is
   admitted and the mixed pair is refused with the category class, which is the measured pair. -/
example :
    listKey? (.category true) [categoryValue, categoryValue] = none ∧
      listKey? (.category true) [categoryValue, strayValue] =
        some "MVK_INVALID_STRING_CONSTANT_FOR_ENUMERATION_CATEGORY" ∧
      listKey? (.category true) [strayValue, categoryValue] =
        some "MVK_INVALID_STRING_CONSTANT_FOR_ENUMERATION_CATEGORY" ∧
      listKey? .wholeEnumeration [enumValueOnly, strayValue] =
        some "MVK_INVALID_STRING_CONSTANT_FOR_ENUMERATION" ∧
      listKey? .wholeEnumeration [] = none := by
  native_decide

end A12Kernel.Conformance.EnumerationCategoryConstant
