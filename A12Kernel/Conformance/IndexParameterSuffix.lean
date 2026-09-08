import A12Kernel.Elaboration.IndexParameterSuffix

/-! # Locks on the `index(...)` parameter's two suffix readings

`FIELD_NO_ENUM`, `INVALID_CATEGORY`, the suffix-missing class, and the value-set and category-mapping
classes are measured ([checkpoint](../../docs/SOURCES.md#src-index-terminal-refusal-classes),
[cross-field pairs](../../docs/SOURCES.md#src-message-parameter-surface-and-iteration-gates)); the
display-mapping and inconsistent-types classes are source-derived and honestly unwitnessed.

The matrix separates the suffix-missing refusal from both readings, the two suffixes' opposite verdicts
on one non-Enumeration set, each suffix's own cascade order, and — the rows the proofs deliberately do
not generalize — that each suffix ignores exactly the declaration part the other reads.
-/

namespace A12Kernel.Conformance.IndexParameterSuffix

open A12Kernel

private def key? (suffix : ParameterSuffix) (referenced : List ReferencedDeclaration) :
    Option String :=
  (suffixRefusal suffix referenced).map KernelStaticDiagnostic.kernelCode

/-- A well-formed Enumeration declaration both suffixes accept. -/
private def base : ReferencedDeclaration :=
  { values := ["A", "B"], categoryValues := ["hot", "cold"], displayMapping := ["en:A1", "en:B1"] }

/- **A missing suffix refuses whatever was referenced**, including the empty set both readings admit —
   so the class belongs to the parameter's spelling and not to the declarations. -/
example :
    key? .absent [] = some "INVALID_INDEX_FIELD_PARAMETER" ∧
      key? .absent [base] = some "INVALID_INDEX_FIELD_PARAMETER" ∧
      key? .category [] = none ∧ key? .value [] = none := by
  native_decide

/- **The family's sharpest separator: one set, opposite verdicts.** Two uniformly non-Enumeration
   declarations are admitted by `.value`, which asks only for agreement, and refused by `->Category`,
   which demands the kind. A rewrite between the suffixes therefore does not preserve legality. -/
example :
    key? .value [{ isEnumeration := false }, { isEnumeration := false }] = none ∧
      key? .category [{ isEnumeration := false }, { isEnumeration := false }] =
        some "FIELD_NO_ENUM" := by
  native_decide

/- **Disagreement about the kind is what `.value` refuses**, so the class needs a mixed set and one
   uniform set of either kind is admitted. -/
example :
    key? .value [base, { isEnumeration := false }] =
        some "INVALID_INDEX_FIELD_INCONSISTENT_TYPES" ∧
      key? .value [{ isEnumeration := false }, base] =
        some "INVALID_INDEX_FIELD_INCONSISTENT_TYPES" ∧
      key? .value [base, base] = none := by
  native_decide

/- **The category suffix's own cascade order.** A non-Enumeration outranks a missing category on the
   very same declaration, and a missing category outranks a value-set difference. -/
example :
    key? .category [{ isEnumeration := false, declaresCategory := false }] =
        some "FIELD_NO_ENUM" ∧
      key? .category [{ base with declaresCategory := false }] = some "INVALID_CATEGORY" ∧
      key? .category [base, { base with declaresCategory := false, values := ["A"] }] =
        some "INVALID_CATEGORY" := by
  native_decide

/- **Both suffixes read the declared value set, and order is part of it.** A reordered set is a
   difference, which is the nearest false generalization to comparing membership. -/
example :
    key? .category [base, { base with values := ["B", "A"] }] =
        some "INVALID_INDEX_FIELD_ENUM_XML_VALUES" ∧
      key? .value [base, { base with values := ["B", "A"] }] =
        some "INVALID_INDEX_FIELD_ENUM_XML_VALUES" := by
  native_decide

/- **The category suffix reads the category mapping and the value suffix does not.** One pair differing
   in that field alone, read both ways. -/
example :
    key? .category [base, { base with categoryValues := ["cold", "hot"] }] =
        some "INVALID_INDEX_FIELD_ENUM_XML_TO_CAT" ∧
      key? .value [base, { base with categoryValues := ["cold", "hot"] }] = none := by
  native_decide

/- **The value suffix reads the display mapping and the category suffix does not.** The mirror pair,
   differing in that field alone — together with the row above this is the disjointness the proofs
   deliberately state as separators rather than in quantified form. -/
example :
    key? .value [base, { base with displayMapping := ["en:A2", "en:B2"] }] =
        some "INVALID_INDEX_FIELD_ENUM_XML_TO_DISPLAY" ∧
      key? .category [base, { base with displayMapping := ["en:A2", "en:B2"] }] = none := by
  native_decide

/- **A single declaration is compared against nothing**, so every cross-declaration class needs a
   second member; the singleton rows admit under both suffixes. -/
example :
    key? .category [base] = none ∧ key? .value [base] = none ∧
      key? .value [{ base with displayMapping := [] }] = none := by
  native_decide

/- **A later member disagreeing with the first still refuses.** Three declarations where the second and
   third agree with each other but not with the first. The row pins the class and **not** the walk: a
   predecessor-walk reports the same class here, and no row can separate the two walks, because they
   differ only in the entity name the message would carry and this vocabulary models classes alone. -/
example :
    key? .value [base, { base with values := ["A"] }, { base with values := ["A"] }] =
      some "INVALID_INDEX_FIELD_ENUM_XML_VALUES" := by
  native_decide

end A12Kernel.Conformance.IndexParameterSuffix
