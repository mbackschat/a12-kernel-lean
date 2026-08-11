/-! # Kernel static-legality diagnostic classes

The Kernel reports an illegal model as a named diagnostic, and **which** name it reports is observable behavior, not an implementation detail. Two illegal models that both fail authoring are still distinguishable if they report different classes, and three consumer profiles depend on that distinction: an importer must decide whether a rejected model is repairable, a rule-refactoring tool must preserve the class its transformation would trigger, and an Explain consumer must name the actual failure.

This vocabulary is therefore part of the semantic account rather than an error-message convenience. It grows one family at a time, and it deliberately admits **no** class this project has not established, so a family's uncovered refusals stay visibly uncovered instead of being mapped to a plausible-looking name. A local refusal with no established class projects to `none`, which is the honest state and a countable coverage measure.

Distinguish this from `A12Kernel.Reference.Support.DiagnosticCode`, which is the public reference process's own transport-level rejection surface (bad JSON, unsupported version, resource limit). That vocabulary describes *this project's* protocol boundary; this one describes the *Kernel's* model check.

Scope: the codes below cover the established field-list operand-admission, fixed filled-group computation-admission, computed Number, ordinary String, and ordinary Enumeration target admission, including the bounded Enumeration category-target distinction, computed-Date partial-target, String pattern-comparison, raw-String length-admission, group-list quantifier admission, `RepetitionNotUnique` key admission, the `Having` filter's iterated-level gate, and the whole-rule error-field reference gate. Coverage, per-mapping evidence status, and remaining families belong to [`IMPLEMENTATION-MAP.md`](../../docs/IMPLEMENTATION-MAP.md); [`SEMANTICS-GAPS.md`](../../docs/SEMANTICS-GAPS.md) owns the open axis.
-/

namespace A12Kernel

/-- One Kernel model-check diagnostic class this project has established. The constructor names are local; `kernelCode` carries the exact `MVK_` identity a consumer compares against. -/
inductive KernelStaticDiagnostic where
  /-- An operand kind the operator refuses outright, or a temporal operand list whose declared formats disagree. Both report this one code. -/
  | onlyStringEnumNumberDateAllowed
  /-- Operands drawn from two different comparability categories, each individually admissible. -/
  | varyingTypesNotAllowed
  /-- An operand list below the operator's required arity. -/
  | paramSizeInvalidN
  /-- A fixed filled-group count carries a single **unstarred** operand. Measured on both a repeatable and a nonrepeatable single operand and in both path forms; a single starred operand is admitted, so this is not simply an operand-count gate. -/
  | paramSizeInvalidGN
  /-- A group-list quantifier that requires at least two operands received one. Shared by `AllGroupsFilled`, `NotAllGroupsFilled`, and `GroupsNotCollectivelyFilled`; the two singleton-admitting quantifiers never reach it. -/
  | paramSizeInvalid2
  /-- The exact same group operand occurs more than once. -/
  | duplicateParam1
  /-- Two group operands overlap by ancestor and descendant. -/
  | duplicateParam2
  /-- A repeatable group was supplied as a quantifier operand without its required star address. -/
  | noWildcard
  /-- A starred group operand appeared under a quantifier that forbids one. Distinct from the scalar-presence wildcard class below, which the same star draws through a different carrier. -/
  | noWildcardsGAllowed
  /-- Scalar `GroupFilled` received a starred group, where the group must stay whole. -/
  | noWildcardsAllowed
  /-- A group path names no group in the model, or a key path names no field. Retained because it separates an unknown operand from every overlap class. -/
  | invalidEntity
  /-- A `RepetitionNotUnique` key does not sit in the repeatable group the operator iterates: either it is in a different group than the first key, or the sole key's group is not repeatable at all. Both draw this one class. -/
  | repeatableGroupMissing
  /-- A `Having` filter references no operand at the iterated level, so the wildcard has nothing to iterate. -/
  | noIterationForWildcard
  /-- The rule's error field is named nowhere in its condition. A whole-rule gate rather than an operand gate, so it is projected at rule assembly. -/
  | errorFieldNotReferenced
  /-- A pattern source fails Java compilation or the Kernel's additional source gate. -/
  | invalidPattern
  /-- A pattern-comparison operand has the wrong scalar kind for its slot. -/
  | invalidTypeForPatternComparison
  /-- A recognized strict raw-String length declaration has a decimal spelling or lies outside the signed-32-bit bound domain. -/
  | internalError
  /-- A raw-String length use is not one of the two strict whole-rule shapes. -/
  | invalidLengthOfRawType
  /-- A computed Number operation's derived scale fails the shared target comparison gate. -/
  | invalidCompareDecimalPlaces
  /-- A computation directly references its own calculated field. -/
  | errorReferenceToCalculatedField
  /-- An established Enumeration computation shape reads the calculated field through a compatible category projection. -/
  | errorSemanticIndexOrCategoryForErrorField
  /-- A Date computation targets a declaration with partial rather than FULL precision. -/
  | invalidDateType
  deriving Repr, DecidableEq

namespace KernelStaticDiagnostic

/-- The exact Kernel diagnostic identifier. This string is the observable, so it is never derived from the constructor name. -/
def kernelCode : KernelStaticDiagnostic → String
  | .onlyStringEnumNumberDateAllowed => "MVK_ONLY_STRING_ENUM_NUMBER_DATE_ALLOWED"
  | .varyingTypesNotAllowed => "MVK_VARYING_TYPES_NOT_ALLOWED"
  | .paramSizeInvalidN => "MVK_PARAMSIZE_INVALIDN"
  | .paramSizeInvalidGN => "MVK_PARAMSIZE_INVALIDGN"
  | .duplicateParam1 => "MVK_DUPLICATE_PARAM1"
  | .duplicateParam2 => "MVK_DUPLICATE_PARAM2"
  | .paramSizeInvalid2 => "MVK_PARAMSIZE_INVALID2"
  | .noWildcard => "MVK_NO_WILDCARD"
  | .noWildcardsGAllowed => "MVK_NO_WILDCARDS_G_ALLOWED"
  | .noWildcardsAllowed => "MVK_NO_WILDCARDS_ALLOWED"
  | .invalidEntity => "MVK_INVALID_ENTITY"
  | .repeatableGroupMissing => "MVK_REPEATABLE_GROUP_MISSING"
  | .noIterationForWildcard => "MVK_NO_ITERATION_FOR_WILDCARD"
  | .errorFieldNotReferenced => "MVK_ERROR_FIELD_NOT_REFERENCED"
  | .invalidPattern => "MVK_INVALID_PATTERN"
  | .invalidTypeForPatternComparison =>
      "MVK_INVALID_TYPE_FOR_PATTERN_COMPARISON"
  | .internalError => "MVK_INTERNAL_ERROR"
  | .invalidLengthOfRawType => "MVK_INVALID_LENGTH_OF_RAW_TYPE"
  | .invalidCompareDecimalPlaces => "MVK_INVALID_COMPARE_DEC_PLACES"
  | .errorReferenceToCalculatedField =>
      "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD"
  | .errorSemanticIndexOrCategoryForErrorField =>
      "MVK_ERROR_SEMANTIC_INDEX_OR_CATEGORY_FOR_ERRORFIELD"
  | .invalidDateType => "MVK_INVALID_DATE_TYPE"

/-- Every established class, so a consumer can enumerate the covered surface and a law can quantify over it. -/
def all : List KernelStaticDiagnostic :=
  [.onlyStringEnumNumberDateAllowed, .varyingTypesNotAllowed, .paramSizeInvalidN,
    .paramSizeInvalidGN, .paramSizeInvalid2, .duplicateParam1, .duplicateParam2,
    .noWildcard, .noWildcardsGAllowed, .noWildcardsAllowed, .invalidEntity,
    .repeatableGroupMissing, .noIterationForWildcard, .errorFieldNotReferenced,
    .invalidPattern, .invalidTypeForPatternComparison, .internalError,
    .invalidLengthOfRawType, .invalidCompareDecimalPlaces,
    .errorReferenceToCalculatedField,
    .errorSemanticIndexOrCategoryForErrorField, .invalidDateType]

end KernelStaticDiagnostic

end A12Kernel
