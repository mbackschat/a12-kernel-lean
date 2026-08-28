/-! # Kernel static-legality diagnostic classes

The Kernel reports an illegal model as a named diagnostic, and **which** name it reports is observable behavior, not an implementation detail. Two illegal models that both fail authoring are still distinguishable if they report different classes, and three consumer profiles depend on that distinction: an importer must decide whether a rejected model is repairable, a rule-refactoring tool must preserve the class its transformation would trigger, and an Explain consumer must name the actual failure.

This vocabulary is therefore part of the semantic account rather than an error-message convenience. It grows one family at a time, and it deliberately admits **no** class this project has not established, so a family's uncovered refusals stay visibly uncovered instead of being mapped to a plausible-looking name. A local refusal with no established class projects to `none`, which is the honest state and a countable coverage measure.

Distinguish this from `A12Kernel.Reference.Support.DiagnosticCode`, which is the public reference process's own transport-level rejection surface (bad JSON, unsupported version, resource limit). That vocabulary describes *this project's* protocol boundary; this one describes the *Kernel's* model check.

Scope: the codes below cover the established field-list operand-admission including the shared entity list's group-scope slot, DateRange full-year/yearless mismatch, the plural String-literal value list's Date-group refusal, the bounded `FirstFilledValue` Confirm refusal, Boolean/Confirm constant computation target admission, and the Number aggregates' op-keyed expansion-kind classes, fixed filled-group computation-admission, computed Number, ordinary String, and ordinary Enumeration target admission, including the bounded Enumeration category-target distinction, computed-Date partial-target, String pattern-comparison, raw-String length-admission, group-list quantifier admission, one syntax-sensitive iteration-condition class, `RepetitionNotUnique` key admission, and the whole-rule error-field reference gate. Coverage, per-mapping evidence status, and remaining families belong to [`IMPLEMENTATION-MAP.md`](../../docs/IMPLEMENTATION-MAP.md); [`SEMANTICS-GAPS.md`](../../docs/SEMANTICS-GAPS.md) owns the open axis.
-/

namespace A12Kernel

/-- One Kernel model-check diagnostic class this project has established. The constructor names are local; `kernelCode` carries the exact `MVK_` identity a consumer compares against. -/
inductive KernelStaticDiagnostic where
  /-- An operand kind the operator refuses outright, or a temporal operand list whose declared formats disagree. Both report this one code. -/
  | onlyStringEnumNumberDateAllowed
  /-- A plural value-list field side expands to a homogeneous Date group while its literal side is String-valued. -/
  | onlyStringEnumNumberAllowed
  /-- Operands drawn from two different comparability categories, each individually admissible. -/
  | varyingTypesNotAllowed
  /-- `FirstFilledValue` received the measured homogeneous two-Confirm operand expansion. -/
  | noBoolyAllowed
  /-- A Confirm computation target received the constant False. True is accepted, and Boolean targets accept either constant. -/
  | invalidCompareToYes
  /-- An operand list below the operator's required arity. -/
  | paramSizeInvalidN
  /-- A filled-group count carries one fixed unstarred operand, including a repeatable operand whose level is bound by the error-field row. The same repeatable operand outside that row draws `noWildcard`; a single starred operand is admitted, so this is not simply an operand-count gate. -/
  | paramSizeInvalidGN
  /-- A group-list quantifier that requires at least two operands received one. Shared by `AllGroupsFilled`, `NotAllGroupsFilled`, and `GroupsNotCollectivelyFilled`; the two singleton-admitting quantifiers never reach it. -/
  | paramSizeInvalid2
  /-- The **direct**-duplicate arm: the exact same non-wildcarded operand occurs more than once, whether that is a repeated group under the quantifiers or a repeated field in an entity list. A wildcarded reference is skipped, so a repeated star is two independent occurrences. -/
  | duplicateParam1
  /-- The **indirect** arm: two operands overlap by ancestor and descendant. It fires between two wildcarded references where the direct arm does not, and between a group and a field below it. -/
  | duplicateParam2
  /-- A repeatable group was reached without its required star address, either as an unstarred group operand or below an earlier star. Measured on the group-list quantifiers and, on conditions character-identical apart from the missing `*`, on the shared entity list. -/
  | noWildcard
  /-- A star was written on a **nonrepeatable** group operand, which has no level to reopen. The opposite arm of the class above, and a separate class rather than a shared wildcard refusal. -/
  | invalidWildcard
  /-- A starred group operand appeared under a quantifier that forbids one. Distinct from the scalar-presence wildcard class below, which the same star draws through a different carrier. -/
  | noWildcardsGAllowed
  /-- Scalar `GroupFilled` received a starred group, where the group must stay whole. -/
  | noWildcardsAllowed
  /-- An operator-specific field-list gate refused a group-scope operand. -/
  | noGroupsAllowed
  /-- A group path names no group in the model, or a key path names no field. Retained because it separates an unknown operand from every overlap class. -/
  | invalidEntity
  /-- A root group appears under a group-list operator that forbids every root operand. -/
  | rootGroupReferenced
  /-- A root group appears beside another operand under a carrier that admits it only as a singleton. -/
  | rootGroupWithOtherParameters
  /-- `RepetitionNotUnique` cannot select the repeated group: a second key lies in a nonrepeatable group, the sole key has no repeated group, or the rule is already placed at that repeated group. These shapes draw one class. -/
  | repeatableGroupMissing
  /-- A measured condition shape is refused at the error field's iterated level by the Kernel's syntax-sensitive iteration gate. This class does not assert a semantic notion of negativity. -/
  | negativeConditionInIteration
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
  /-- `Sum` received an operand, or a group whose expansion contains one, that is not Number-valued. -/
  | noNumber
  /-- The extrema received an operand whose kind has no ordering. Measured on a group's expansion and on the equivalent explicit field list, which places this gate on the operand's kind rather than on its groupness. -/
  | notSortable
  /-- `NumberOfDifferentValues` received an operand list mixing its String/stored-Enumeration family with a non-member. -/
  | stringEnumAndNonStringEnum
  /-- A computed Number operation's derived scale fails the shared target comparison gate. -/
  | invalidCompareDecimalPlaces
  /-- A computation directly references its own calculated field. -/
  | errorReferenceToCalculatedField
  /-- An established Enumeration computation shape reads the calculated field through a compatible category projection. -/
  | errorSemanticIndexOrCategoryForErrorField
  /-- A Date computation targets a declaration with partial rather than FULL precision. -/
  | invalidDateType
  /-- The measured direct Number/Number source pair under plural DateRange overlap contains no DateRange. -/
  | noDateRange
  /-- `AtLeastOneDateRangeOverlaps` received a starred field in its scalar position rather than its list position. -/
  | invalidParameterForDateRangeComparison
  /-- A full-year DateRange overlap operand was paired with an `MM` or `MM-dd` range that has no Base Year. -/
  | dateWithAndWithoutYear
  /-- Two temporal operands of a direct comparison disagree on year presence, or on whether they carry a date at all, with no Base Year to supply the missing year. -/
  | invalidCompareToDate
  /-- A date-component extractor was applied to a source whose declared format does not expose that component. Quarter counts as the month, so the four extractors gate on three components. -/
  | wrongDateFormatForOp
  /-- Two stored DateRange operands of an equality expose different date-component sets. Lexical spelling does not enter it, so both spellings of one component set cross freely and the refusal is symmetric in the authored order and identical for `==` and `!=`. -/
  | invalidCompareToDateRange
  /-- An overlap operand's DateRange declaration carries an `interpretationOfYear`. Both operators key their format allowlist on the whole declaration including that reading, so the composite format is refused on either side, under every profile, and with or without a Base Year. -/
  | invalidDateRangeFormat
  /-- A semantic index's field-valued key is read from a field **inside the indexed group itself**, so a rule iterating that group cannot key the lookup by its current row's own field. The same lookup keyed by a field outside the group, or by a literal, is admitted from that same locus. -/
  | semanticIndexContainedInIndex
  /-- A rule's error text uses a **semantic index** its condition does not use the same way. The gate's subject is the index rather than the field: measured, a keyed parameter naming a field absent from the condition is admitted whenever the condition keys that group by that key, so the field's own membership is required only of an *unkeyed* parameter, which is refused `INVALID_FIELD` instead. The pairing is exact in both directions — a keyed condition operand does not license an unkeyed parameter, and a differently keyed one does not license this key. No clause produces it yet: the modeled message fragment is nonrepeatable, so it declares no index to pair. -/
  | indexForErrorTextInvalid
  deriving Repr, DecidableEq

namespace KernelStaticDiagnostic

/-- The exact Kernel diagnostic identifier. This string is the observable, so it is never derived from the constructor name. -/
def kernelCode : KernelStaticDiagnostic → String
  | .onlyStringEnumNumberDateAllowed => "MVK_ONLY_STRING_ENUM_NUMBER_DATE_ALLOWED"
  | .onlyStringEnumNumberAllowed => "MVK_ONLY_STRING_ENUM_NUMBER_ALLOWED"
  | .varyingTypesNotAllowed => "MVK_VARYING_TYPES_NOT_ALLOWED"
  | .noBoolyAllowed => "MVK_NO_BOOLY_ALLOWED"
  | .invalidCompareToYes => "MVK_INVALID_COMPARE_TO_YES"
  | .paramSizeInvalidN => "MVK_PARAMSIZE_INVALIDN"
  | .paramSizeInvalidGN => "MVK_PARAMSIZE_INVALIDGN"
  | .duplicateParam1 => "MVK_DUPLICATE_PARAM1"
  | .duplicateParam2 => "MVK_DUPLICATE_PARAM2"
  | .paramSizeInvalid2 => "MVK_PARAMSIZE_INVALID2"
  | .noWildcard => "MVK_NO_WILDCARD"
  | .invalidWildcard => "MVK_INVALID_WILDCARD"
  | .noWildcardsGAllowed => "MVK_NO_WILDCARDS_G_ALLOWED"
  | .noWildcardsAllowed => "MVK_NO_WILDCARDS_ALLOWED"
  | .noGroupsAllowed => "MVK_NO_GROUPS_ALLOWED"
  | .invalidEntity => "MVK_INVALID_ENTITY"
  | .rootGroupReferenced => "MVK_ROOT_GROUP_REFERENCED"
  | .rootGroupWithOtherParameters =>
      "MVK_ROOT_GROUP_WITH_OTHER_PARAMETERS"
  | .repeatableGroupMissing => "MVK_REPEATABLE_GROUP_MISSING"
  | .negativeConditionInIteration => "MVK_NEG_CONDITION_IN_ITERATION"
  | .errorFieldNotReferenced => "MVK_ERROR_FIELD_NOT_REFERENCED"
  | .invalidPattern => "MVK_INVALID_PATTERN"
  | .invalidTypeForPatternComparison =>
      "MVK_INVALID_TYPE_FOR_PATTERN_COMPARISON"
  | .internalError => "MVK_INTERNAL_ERROR"
  | .invalidLengthOfRawType => "MVK_INVALID_LENGTH_OF_RAW_TYPE"
  | .noNumber => "MVK_NO_NUMBER"
  | .notSortable => "MVK_NOT_SORTABLE"
  | .stringEnumAndNonStringEnum => "MVK_STRING_ENUM_AND_NON_STRING_ENUM"
  | .invalidCompareDecimalPlaces => "MVK_INVALID_COMPARE_DEC_PLACES"
  | .errorReferenceToCalculatedField =>
      "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD"
  | .errorSemanticIndexOrCategoryForErrorField =>
      "MVK_ERROR_SEMANTIC_INDEX_OR_CATEGORY_FOR_ERRORFIELD"
  | .invalidDateType => "MVK_INVALID_DATE_TYPE"
  | .noDateRange => "MVK_NO_DATE_RANGE"
  | .invalidParameterForDateRangeComparison =>
      "MVK_INVALID_PARAMETER_FOR_DATE_RANGE_COMPARISON"
  | .dateWithAndWithoutYear => "MVK_DATE_WITH_AND_WITHOUT_YEAR"
  | .invalidCompareToDate => "MVK_INVALID_COMPARE_TO_DATE"
  | .wrongDateFormatForOp => "MVK_WRONG_DATE_FORMAT_FOR_OP"
  | .invalidCompareToDateRange => "MVK_INVALID_COMPARE_TO_DATE_RANGE"
  | .invalidDateRangeFormat => "MVK_INVALID_DATE_RANGE_FORMAT"
  | .semanticIndexContainedInIndex => "MVK_SEMANTIC_INDEX_CONTAINED_IN_INDEX"
  | .indexForErrorTextInvalid => "MVK_INDEX_FOR_ERROR_TEXT_INVALID"

/-- Every established class, so a consumer can enumerate the covered surface and a law can quantify over it. -/
def all : List KernelStaticDiagnostic :=
  [.onlyStringEnumNumberDateAllowed, .onlyStringEnumNumberAllowed,
    .varyingTypesNotAllowed, .noBoolyAllowed, .invalidCompareToYes,
    .paramSizeInvalidN,
    .paramSizeInvalidGN, .paramSizeInvalid2, .duplicateParam1, .duplicateParam2,
    .noWildcard, .invalidWildcard, .noWildcardsGAllowed, .noWildcardsAllowed,
    .noGroupsAllowed,
    .invalidEntity, .rootGroupReferenced, .rootGroupWithOtherParameters,
    .repeatableGroupMissing, .negativeConditionInIteration,
    .errorFieldNotReferenced,
    .invalidPattern, .invalidTypeForPatternComparison, .internalError,
    .invalidLengthOfRawType, .noNumber, .notSortable,
    .stringEnumAndNonStringEnum, .invalidCompareDecimalPlaces,
    .errorReferenceToCalculatedField,
    .errorSemanticIndexOrCategoryForErrorField, .invalidDateType, .noDateRange,
    .invalidParameterForDateRangeComparison, .dateWithAndWithoutYear,
    .invalidDateRangeFormat, .invalidCompareToDateRange, .wrongDateFormatForOp,
    .invalidCompareToDate, .semanticIndexContainedInIndex,
    .indexForErrorTextInvalid]

end KernelStaticDiagnostic

end A12Kernel
