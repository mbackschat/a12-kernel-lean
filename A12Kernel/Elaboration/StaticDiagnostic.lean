/-! # Kernel static-legality diagnostic classes

The Kernel reports an illegal model as a named diagnostic, and **which** name it reports is observable behavior, not an implementation detail. Two illegal models that both fail authoring are still distinguishable if they report different classes, and three consumer profiles depend on that distinction: an importer must decide whether a rejected model is repairable, a rule-refactoring tool must preserve the class its transformation would trigger, and an Explain consumer must name the actual failure.

This vocabulary is therefore part of the semantic account rather than an error-message convenience. It grows one family at a time, and it deliberately admits **no** class this project has not established, so a family's uncovered refusals stay visibly uncovered instead of being mapped to a plausible-looking name. A local refusal with no established class projects to `none`, which is the honest state and a countable coverage measure.

Distinguish this from `A12Kernel.Reference.Support.DiagnosticCode`, which is the public reference process's own transport-level rejection surface (bad JSON, unsupported version, resource limit). That vocabulary describes *this project's* protocol boundary; this one describes the *Kernel's* model check.

Scope: the codes below cover the established field-list operand-admission including the shared entity list's group-scope slot, DateRange full-year/yearless mismatch, the plural String-literal value list's Date-group refusal, the bounded `FirstFilledValue` Confirm refusal, Boolean/Confirm constant computation target admission, and the Number aggregates' op-keyed expansion-kind classes and bounded `SumOfProducts` pair matrix, fixed filled-group computation-admission, computed Number, ordinary String, and ordinary Enumeration target admission, including the bounded Enumeration category-target distinction, computed-Date partial-target, String pattern-comparison, raw-String length-admission, date-extraction source admission, group-list quantifier admission, one syntax-sensitive iteration-condition class, `RepetitionNotUnique` key admission, the index-group resolution walk ([`IndexGroupResolution`](IndexGroupResolution.lean)), the rule-change service's two move refusals ([`RuleChangePropagation`](RuleChangePropagation.lean)), the two repeatability-restriction refusals ([`RepeatabilityRestriction`](RepeatabilityRestriction.lean)), the error-text row-index parameter's cascade ([`ErrorTextRowParameter`](ErrorTextRowParameter.lean)), the `index(...)` parameter's resolution and repeatability stages ([`IndexParameterResolution`](IndexParameterResolution.lean)), the enumeration-category constant gate ([`EnumerationCategoryConstant`](EnumerationCategoryConstant.lean)), and the whole rule's error-target declarations — the error field's own declaration gate, the reference gate, the iteration cascade that gate opens, and the two custom error-entity slots ([`ErrorTargetDeclaration`](ErrorTargetDeclaration.lean)). Coverage, per-mapping evidence status, and remaining families belong to [`IMPLEMENTATION-MAP.md`](../../docs/IMPLEMENTATION-MAP.md); [`SEMANTICS-GAPS.md`](../../docs/SEMANTICS-GAPS.md) owns the open axis.
-/

namespace A12Kernel

/-- One Kernel model-check diagnostic class this project has established. The constructor names are local; `kernelCode` carries the exact `MVK_` identity a consumer compares against. -/
inductive KernelStaticDiagnostic where
  /-- An operand kind the operator refuses outright, or a temporal operand list whose declared formats disagree. Both report this one code. -/
  | onlyStringEnumNumberDateAllowed
  /-- A plural value-list field side expands to a homogeneous Date group while its literal side is String-valued. -/
  | onlyStringEnumNumberAllowed
  /-- A field whose kind the operator admits, paired with a value list its kind cannot be compared against. Distinct from the admitted-set class above, and the distinction is the operator's own message vocabulary: a Number field passes a `STRING_ENUM_NUMBER` gate and then fails the **literal** comparison, where a Date never reaches that stage. -/
  | invalidTypesForComparison
  /-- A **numeric** comparison whose field side is neither a Number nor a temporal field. The Kernel spells this one singular, and it is a different constant from the plural neighbour above: measured inside a `Having` filter, String, Boolean, Confirm, Enumeration and DATE_RANGE all draw it, while a temporal field draws `invalidCompareToDate` instead ([checkpoint](../../docs/SOURCES.md#src-having-filter-comparison-and-scope-classes)). -/
  | invalidTypeForComparison
  /-- A filter leaf reads a field that no iteration in scope binds — measured with an absolute root-level field inside a starred operand's filter. The message names a wildcard because the filter's own binding comes from the star it qualifies. -/
  | noIterationForWildcard
  /-- A filter leaf reads a **different** repeatable group's field without a star. Distinct from the class above: the field is repeatable rather than root-level, so an iteration exists and is the wrong one. -/
  | invalidIterationInFilterCondition
  /-- Operands drawn from two different comparability categories, each individually admissible. -/
  | varyingTypesNotAllowed
  /-- `FirstFilledValue` received the measured homogeneous two-Confirm operand expansion. -/
  | noBoolyAllowed
  /-- A Confirm computation target received the constant False. True is accepted, and Boolean targets accept either constant. -/
  | invalidCompareToYes
  /-- A Boolean computation target received a constant of any other family. It is the **top** of the shared literal-comparison ladder: measured across an eight-constant by ten-target grid, a Boolean target reports this class even against a temporal constant, which outranks every other target ([checkpoint](../../docs/SOURCES.md#src-constant-assignment-diagnostic-ladder)). Its Confirm neighbour reports `invalidCompareToYes` in the same position, so the two kinds do not share a class even though they share the ladder rung. -/
  | invalidCompareToYesNo
  /-- A computation's target does not lie at or below its declaring group while the computation
  iterates. Iteration is derived from the target's own repeatable scope or from a per-row operand of
  a repeatable declaring group, so a bare constant into a repeatable target reaches this class with
  no operand at all. -/
  | fieldNotInRuleGroup
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
  /-- The measured `SumOfProducts` pair resolves two Number operand paths whose immediate owning groups differ. This includes a plain field outside the starred owner; sharing a starred ancestor is also insufficient, while two fixed descendants of one owner are admitted. -/
  | differentGroups
  /-- A repeatable group was reached without its required star address, either as an unstarred group operand or below an earlier star. Measured on the group-list quantifiers and, on conditions character-identical apart from the missing `*`, on the shared entity list. -/
  | noWildcard
  /-- The measured `SumOfProducts` operand writes stars at more than one repeatable level. A sole star at the lowest level remains the admitted spelling. -/
  | wildcardOnlyAtLowestLevelAllowed
  /-- The measured `SumOfProducts` pair adds `Having` to either otherwise-admissible starred operand. This is the carrier's exact refusal; ordinary aggregate lists retain their separate filtered-star route. -/
  | wildcardAtLowestLevelRequired
  /-- The measured `SumOfProducts` pair consists of two Number fields below no repeatable level at all. -/
  | repeatableLevelRequired
  /-- A star was written on a **nonrepeatable** group operand, which has no level to reopen. The opposite arm of the class above, and a separate class rather than a shared wildcard refusal. -/
  | invalidWildcard
  /-- A starred group operand appeared under a quantifier that forbids one. Distinct from the scalar-presence wildcard class below, which the same star draws through a different carrier. -/
  | noWildcardsGAllowed
  /-- A star was written at an operand position that forbids one. Scalar `GroupFilled` reaches it with a starred **group**, where the group must stay whole, and field-operand carriers reach it with a starred **field**, so this is not a group-only refusal. Its fix is the opposite of `noWildcard`'s: remove the star, rather than supply the binding a repeatable operand is missing. The two names differ by one word and the wrong reading sends a consumer the wrong way. -/
  | noWildcardsAllowed
  /-- An operator-specific field-list gate refused a group-scope operand. -/
  | noGroupsAllowed
  /-- A value-validation predicate's operand declaration is outside the String/Enumeration/extensible-Enumeration set its text names. The measured members are Number, Boolean, Confirm, and a **Custom**-typed declaration — the last being the operand a reader most expects to be admitted, since the predicate names a custom type. -/
  | noStringOrEnumOrExtEnum
  /-- Two temporal operands of one extremum expose different date/time **component sets**, the message naming both declared formats. The gate reads the component set and not the format spelling, so two identical sets under different spellings cross it freely; a declared Base Year supplies a missing year to one side before the comparison. -/
  | dateFormatsNotCompatible
  /-- An operand list whose **first** member is temporal carries a later member that is not. The Kernel's own text states the rule positionally — "if the first parameter is a date than all parameters have to be dates" — so this is the mirror of `notSortable` rather than a second spelling of it: the same two operands in the other order draw that code instead. Measured on the extrema and on the distinct count, which share the mechanism. -/
  | dateAndNonDate
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
  /-- A literal in a **value list** is not a value of the enumeration the compared field declares. The whole-enumeration arm of the split below. -/
  | invalidStringConstantForEnumeration
  /-- The same list carrier with a category qualifier written: the literal is not a value of **that category**, which is a different set from the enumeration's own values. -/
  | invalidStringConstantForEnumerationCategory
  /-- The named category is not declared on the field's enumeration. The Kernel's own constant carries the misspelling. -/
  | categoryUnknown
  /-- An `index(...)` parameter whose short name matches no index field on the error field's own path. **Not** the same class as `nameUnresolved .indexField`: that one is the model's own `MVK_INVALID_INDEX_FIELD` declaration refusal, while this is the error-text checker's prefix-free `INVALID_INDEX_FIELD`. Two codes, one identifier apart. -/
  | indexFieldUnresolved
  /-- Several index fields on the error field's path share the parameter's short name, so the name selects none of them. The identical parameter is admitted from an error field on a level carrying only one. -/
  | indexFieldAmbiguous
  /-- The resolved index field's own group declares more than one index-field name. -/
  | indexFieldComposedIndex
  /-- The error path's index field and one the condition references **disagree** about repeatability. The class is raised from both branches in opposite directions, so it names the disagreement and not either side's state. -/
  | indexFieldRepeatabilityMismatch
  /-- Both sides repeat, but a referenced index field's own read is neither an iteration nor a parallel iteration. Reachable only from the repeatable branch. -/
  | indexFieldNotIterating
  /-- Both sides are non-repeatable, and a referenced index field is not an Enumeration declaring exactly one value with its s-value set. Reachable only from the non-repeatable branch, so no model reports this beside `indexFieldNotIterating`. -/
  | indexFieldNonRepeatableEnum
  /-- An error-text `$#group$` parameter whose path names no group, **or** names one the condition does not reference in a way the parameter may read. The Kernel spells two distinct causes with this one code. -/
  | invalidGroupInParameter
  /-- The named group is referenced in the condition only **with** a star, so no single row is determined. An unstarred reference anywhere alongside the starred one admits the parameter. -/
  | iterParamWithStarReference
  /-- The parameter wrote a semantic index the condition's iteration cannot support. -/
  | invalidUseOfSemanticIndex
  /-- The same final stage without a semantic index written: the parameter's iteration is unsupportable on its own. -/
  | invalidUseOfIterationParam
  /-- An error text carrying a `$` could not be checked because the condition it needs did not parse. Reported **alongside** the other error-text findings rather than instead of them. -/
  | errorTextInvalidCondition
  /-- A field parameter wrote a path where the model kind requires a short name. -/
  | invalidPathSpecInParameter
  /-- A rule read backwards as a repeatability restriction derives a maximum of exactly one for a repeatable **group**. Restricting a group to a single repetition this way is refused; a maximum of two or more is accepted and a maximum below one is silently ignored. -/
  | maxGroupRestrictionToOne
  /-- The same refusal for the **form serial**, derived from a rule counting root-group repetitions. Its message carries no path where the group class names one. -/
  | maxLfdNrRestrictionToOne
  /-- The rule-change service was asked to propagate an entity **move** into a condition, in an A12 model. It declines and returns nothing; a rename in the same model is propagated normally. -/
  | entityMoveInA12ModelCondition
  /-- The same refusal from the service's error-text entry point, which reports a different class for the identical situation so a caller can tell which surface declined. -/
  | entityMoveInA12ModelErrortext
  /-- A second index-declaring group lies above the first on the walked path. Reported without examining that second group's own multiplicity, so it outranks the class below. -/
  | multipleIndexFields
  /-- The innermost index-declaring group on the path declares more than one index field name. -/
  | multipleIndexFields2
  /-- The resolved index group's declared index-field name names nothing in that group, or names a group rather than a field. -/
  | indexFieldInvalid
  /-- The rule declares no error field at all. Reported **before the condition is parsed**, so it hides every syntax class the condition would otherwise draw. -/
  | missingErrorField
  /-- The rule declares an error field the model does not know. Same pre-grammar stage as the class above, but unlike it this one is suppressed by a lenient parse. -/
  | errorFieldNotValid
  /-- Row iteration paired with an error field the condition reaches only through its root group. An old-world branch: it is guarded on a non-A12 model, and its only catalog entry is an unauthored placeholder rather than a message, so it is named here for the total function's sake and not because a consumer can render it. -/
  | errorFieldAndZIterationInvalid
  /-- Plain iteration below the root-group level, paired with an error field the condition reaches only through its root group. -/
  | errorFieldGroupIteration4Invalid
  /-- Parallel iteration paired with such an error field, when the rule's index field does not sit at the root-group level. -/
  | errorFieldGroupIteration5Invalid
  /-- A path in the rule's *error-causing entities if filled* slot that its condition does not reference. -/
  | refErrorEntityIfFilledNotReferenced
  /-- The same for the *if not filled* slot. Both slots report in one run, which is why they are two classes rather than one. -/
  | refErrorEntityIfNotFilledNotReferenced
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
  /-- `NumberOfDifferentValues` received a **Number-first** operand list with a non-Number member.
      The Kernel reports homogeneity from the family of the *first* operand, so this and
      `stringEnumAndNonStringEnum` are the same illegal pair under two codes, selected by operand
      order alone. -/
  | numberAndNonNumber
  /-- `NumberOfDifferentValues` received an operand outside its kind domain — a Boolean or Confirm.
      Distinct from the confusably similar `onlyStringEnumNumberDateAllowed`, which is a **different
      operator's** code: `FieldValuesNotUnique` draws that one for the same shape, and the two differ
      only by a `CMP_` segment. -/
  | onlyStringEnumNumberCmpDateAllowed
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
  /-- A partially known Date supplied where the operator admits only fully known ones. -/
  | partialDateNotAllowed
  /-- `AtLeastOneDateRangeOverlaps` received a non-scalar operand in its **scalar** position. Every non-scalar form draws it — plain star, filtered star, fixed group, starred group, and a star above a nonrepeatable terminal — while the identical operand is admitted in the `In` list, so the class belongs to the slot rather than to the form. -/
  | invalidParameterForDateRangeComparison
  /-- A value was assigned or compared against a String or Enumeration declaration that cannot hold it. Measured as the Boolean constant computation's refusal on both of those target kinds, which share this one class. -/
  | invalidCompareToEnumOrString
  /-- A value was assigned or compared against a Number declaration that cannot hold it. Distinct from the String/Enumeration class above, which is why the Boolean constant's target gate maps per kind rather than to one refusal. -/
  | inconsistentTypesCompared
  /-- A full-year DateRange overlap operand was paired with an `MM` or `MM-dd` range that has no Base Year. -/
  | dateWithAndWithoutYear
  /-- Two temporal operands of a direct comparison disagree on year presence, or on whether they carry a date at all, with no Base Year to supply the missing year. -/
  | invalidCompareToDate
  /-- A measured date extractor received an authorable non-temporal field declaration. The established denominator is exact per carrier and excludes `UNKNOWN`, which has no authorable counterpart. -/
  | noDate
  /-- A date-component extractor was applied to a source whose declared format does not expose that component. Quarter counts as the month, so the four extractors gate on three components. -/
  | wrongDateFormatForOp
  /-- Two stored DateRange operands of an equality expose different date-component sets. Lexical spelling does not enter it, so both spellings of one component set cross freely and the refusal is symmetric in the authored order and identical for `==` and `!=`. -/
  | invalidCompareToDateRange
  /-- An overlap operand's DateRange declaration carries an `interpretationOfYear`. Both operators key their format allowlist on the whole declaration including that reading, so the composite format is refused on either side, under every profile, and with or without a Base Year. -/
  | invalidDateRangeFormat
  /-- A semantic index's field-valued key is read from a field **inside the indexed group itself**, so a rule iterating that group cannot key the lookup by its current row's own field. The same lookup keyed by a field outside the group, or by a literal, is admitted from that same locus. -/
  | semanticIndexContainedInIndex
  /-- `RuleGroup For "key"` selected a containing group that declares no semantic-index field. This carrier-specific projection is calibrated independently of other semantic-index surfaces ([checkpoint](../../docs/SOURCES.md#src-pr2-rulegroup-semantic-index)). -/
  | noIndexField
  /-- A valid semantic-index suffix appears in an operator slot that forbids semantic indexing. The
  class is carrier-specific rather than an invalid-index result
  ([checkpoint](../../docs/SOURCES.md#src-pr2-semantic-index-carrier-matrix)). -/
  | semanticIndexNotAllowed
  /-- The checked one-level Number carrier writes an otherwise-valid exact-text semantic-index
  suffix on the same selected group it stars
  ([checkpoint](../../docs/SOURCES.md#src-pr2-semantic-index-carrier-matrix)). -/
  | semanticIndexAndWildcard
  /-- A rule's error text uses a **semantic index** its condition does not use the same way. The gate's subject is the index rather than the field: measured, a keyed parameter naming a field absent from the condition is admitted whenever the condition keys that group by that key, so the field's own membership is required only of an *unkeyed* parameter, which is refused `INVALID_FIELD` instead. The pairing is exact in both directions — a keyed condition operand does not license an unkeyed parameter, and a differently keyed one does not license this key. No clause produces it yet: the modeled message fragment is nonrepeatable, so it declares no index to pair. -/
  | indexForErrorTextInvalid
  /-- A computation assigns an Enumeration target a literal naming no value in its selected domain. This is the one constant family whose target constrains the literal's **value** statically: every other measured kind either renders the constant into the declared format or checks nothing until runtime, while an undeclared token here never reaches runtime at all. The code names a *comparison* because the check is the generated equality's, not the assignment's. -/
  | invalidStringConstantForEnumComparison
  /-- A `Date(...)` construction supplied a day and a month but no year. The Kernel treats the year as mandatory in the three-argument form rather than defaulting it from the model's Base Year. -/
  | missingYear
  /-- A validity wrapper applied to a date construction whose every argument is a literal. Refused because an all-constant date's validity is already settled at construction, so the wrapper could only ever be constant-true or constant-false. -/
  | onlyConstantsUsed
  /-- The four-argument `Date(...)` form, whose fourth argument is the split-century year, admits no extraction operator at its third or fourth position. Distinct from the wrong-family class: here the operator's family is irrelevant and only the arity is decisive. -/
  | extractOpNotAllowedForFourParamDateConstruct
  /-- A date-shifting operator's amount argument does not evaluate to a number. -/
  | nonNumeric
  /-- A constant the operator's grammar reads as a **date** literal, in a slot admitting only number, string, or the two boolean tokens. The content decides the kind, so a quoted value can reach this class purely by looking like a date. -/
  | noDateConstant
  /-- A `True`/`False` constant paired with a field list containing a field that is neither Boolean nor Confirm. -/
  | noTypeYesOrYesNo
  /-- A range-as-string source that is not string-like. -/
  | invalidType
  /-- Multiplication, division, or subtraction applied to an operand that is not a Number. -/
  | noNumberForCalc
  /-- A count-of-value operand's sought constant is of a kind the operator's grammar rejects. The grammar admits a boolean, a number, or a string literal, so a temporal constant draws this class before any field in the list is examined — measured with the current-date constant against two String fields. -/
  | invalidConst
  /-- A count-of-value field list mixes kinds where the operator requires string-like operands. Reached after the constant clears the class above, which is what orders the two: a temporal constant against the same list never gets here. -/
  | noStringOrEnum
  /-- Two Enumerations compared where exactly one declares display labels, or an Enumeration with labels compared against a plain string. The label/no-label matrix, not the value domains, is what decides this. -/
  | invalidCompareEnumToString
  /-- An operator requiring exactly two field-list parameters received a different count. -/
  | paramSizeInvalidTwo
  /-- A dotted line specifier on a path element. The grammar accepts the shape so the Kernel can name it, and A12 models then refuse it semantically — so this class exists precisely because parsing succeeded. -/
  | pointInA12Model
  /-- A field-list operand outside the rule's own group or root group, in the form that takes no explicit source group. -/
  | notInRuleGroup
  /-- Two groups related by parallel iteration whose declared index fields differ in base type. Distinct from the missing-index class: both groups **have** an index here, and only their types disagree. -/
  | indexTypeInconsistent
  /-- A message parameter naming a form-pointer target that resolves to a group rather than to a field. The parameter grammar admits the shape, so the refusal is the resolution's and not the parser's. -/
  | invalidFieldInParameter
  /-- A computation with more than one alternative whose tier carries no precondition. The single-tier form admits the bare comparison, so this class is about tier *arity* rather than about preconditions being mandatory. -/
  | errorEmptyPrecondition
  /-- A computation whose computed field is a repeatable group's declared index field. -/
  | errorIndexAsCalculatedField
  /-- An Enumeration value carrying a character outside the model's declared supported set. This class belongs to the Kernel's **code-generation** check family, and it is reachable from ordinary authoring because the consistency check runs the validation code generator: one registered consistency rule generates the validator and turns every notification it collects into a consistency problem. The Kernel reports one diagnostic per offending **character**, not one per value. -/
  | enumValueWithInvalidCharacter
  deriving Repr, DecidableEq

namespace KernelStaticDiagnostic

/-- The exact Kernel diagnostic identifier. This string is the observable, so it is never derived from the constructor name. -/
def kernelCode : KernelStaticDiagnostic → String
  | .invalidStringConstantForEnumComparison =>
      "MVK_INVALID_STRING_CONSTANT_FOR_ENUM_COMPARISON"
  | .onlyStringEnumNumberDateAllowed => "MVK_ONLY_STRING_ENUM_NUMBER_DATE_ALLOWED"
  | .onlyStringEnumNumberAllowed => "MVK_ONLY_STRING_ENUM_NUMBER_ALLOWED"
  | .invalidTypesForComparison => "MVK_INVALID_TYPES_FOR_COMPARISON"
  | .invalidTypeForComparison => "MVK_INVALID_TYPE_FOR_COMPARISON"
  | .noIterationForWildcard => "MVK_NO_ITERATION_FOR_WILDCARD"
  | .invalidIterationInFilterCondition =>
      "MVK_INVALID_ITERATION_IN_FILTER_CONDITION"
  | .varyingTypesNotAllowed => "MVK_VARYING_TYPES_NOT_ALLOWED"
  | .noBoolyAllowed => "MVK_NO_BOOLY_ALLOWED"
  | .invalidCompareToYes => "MVK_INVALID_COMPARE_TO_YES"
  | .invalidCompareToYesNo => "MVK_INVALID_COMPARE_TO_YESNO"
  | .fieldNotInRuleGroup => "MVK_ERROR_FIELD_NOT_IN_RULEGROUP"
  | .paramSizeInvalidN => "MVK_PARAMSIZE_INVALIDN"
  | .paramSizeInvalidGN => "MVK_PARAMSIZE_INVALIDGN"
  | .duplicateParam1 => "MVK_DUPLICATE_PARAM1"
  | .duplicateParam2 => "MVK_DUPLICATE_PARAM2"
  | .differentGroups => "MVK_DIFFERENT_GROUPS"
  | .paramSizeInvalid2 => "MVK_PARAMSIZE_INVALID2"
  | .noWildcard => "MVK_NO_WILDCARD"
  | .wildcardOnlyAtLowestLevelAllowed =>
      "MVK_WILDCARD_ONLY_AT_LOWEST_LEVEL_ALLOWED"
  | .wildcardAtLowestLevelRequired =>
      "MVK_WILDCARD_AT_LOWEST_LEVEL_REQUIRED"
  | .repeatableLevelRequired => "MVK_REPEATABLE_LEVEL_REQUIRED"
  | .invalidWildcard => "MVK_INVALID_WILDCARD"
  | .noWildcardsGAllowed => "MVK_NO_WILDCARDS_G_ALLOWED"
  | .noWildcardsAllowed => "MVK_NO_WILDCARDS_ALLOWED"
  | .noGroupsAllowed => "MVK_NO_GROUPS_ALLOWED"
  | .noStringOrEnumOrExtEnum => "MVK_NO_STRING_OR_ENUM_OR_EXT_ENUM"
  | .dateFormatsNotCompatible => "MVK_DATEFORMATS_NOT_COMPATIBLE"
  | .dateAndNonDate => "MVK_DATE_AND_NONDATE"
  | .invalidEntity => "MVK_INVALID_ENTITY"
  | .rootGroupReferenced => "MVK_ROOT_GROUP_REFERENCED"
  | .rootGroupWithOtherParameters =>
      "MVK_ROOT_GROUP_WITH_OTHER_PARAMETERS"
  | .repeatableGroupMissing => "MVK_REPEATABLE_GROUP_MISSING"
  | .negativeConditionInIteration => "MVK_NEG_CONDITION_IN_ITERATION"
  | .errorFieldNotReferenced => "MVK_ERROR_FIELD_NOT_REFERENCED"
  | .invalidStringConstantForEnumeration =>
      "MVK_INVALID_STRING_CONSTANT_FOR_ENUMERATION"
  | .invalidStringConstantForEnumerationCategory =>
      "MVK_INVALID_STRING_CONSTANT_FOR_ENUMERATION_CATEGORY"
  | .categoryUnknown => "MVK_CATEGORY_UNKOWN"
  | .indexFieldUnresolved => "INVALID_INDEX_FIELD"
  | .indexFieldAmbiguous => "INVALID_INDEX_FIELD_AMBIGUOUS"
  | .indexFieldComposedIndex => "INVALID_INDEX_FIELD_COMPOSED_INDEX"
  | .indexFieldRepeatabilityMismatch => "INVALID_INDEX_FIELD_REP"
  | .indexFieldNotIterating => "INVALID_INDEX_FIELD_REP_ITER"
  | .indexFieldNonRepeatableEnum => "INVALID_INDEX_FIELD_NONREP_ENUM"
  | .invalidGroupInParameter => "INVALID_GROUP"
  | .iterParamWithStarReference => "ITER_PARAM_WITH_STARREFERENCE"
  | .invalidUseOfSemanticIndex => "INVALID_USE_OF_SEMANTIC_INDEX"
  | .invalidUseOfIterationParam => "INVALID_USE_OF_ITERATION_PARAM"
  | .errorTextInvalidCondition => "INVALID_CONDITION"
  | .invalidPathSpecInParameter => "INVALID_PATH_SPEC_IN_PARAMETER"
  | .maxGroupRestrictionToOne => "MVK_MAX_GROUP_RESTRICTION_TO_ONE"
  | .maxLfdNrRestrictionToOne => "MVK_MAX_LFDNR_RESTRICTION_TO_ONE"
  | .entityMoveInA12ModelCondition =>
      "MVK_ENTITY_MOVE_IN_A12_MODEL_CONDITION"
  | .entityMoveInA12ModelErrortext =>
      "MVK_ENTITY_MOVE_IN_A12_MODEL_ERRORTEXT"
  | .multipleIndexFields => "MVK_MULTIPLE_INDEX_FIELDS"
  | .multipleIndexFields2 => "MVK_MULTIPLE_INDEX_FIELDS2"
  | .indexFieldInvalid => "MVK_INDEX_FIELD_INVALID"
  | .missingErrorField => "MVK_MISSING_ERROR_FIELD"
  | .errorFieldNotValid => "MVK_ERROR_FIELD_NOT_VALID"
  | .errorFieldAndZIterationInvalid =>
      "MVK_ERROR_FIELD_AND_ZITERATION_INVALID"
  | .errorFieldGroupIteration4Invalid =>
      "MVK_ERROR_FIELDGROUP_ITERATION4_INVALID"
  | .errorFieldGroupIteration5Invalid =>
      "MVK_ERROR_FIELDGROUP_ITERATION5_INVALID"
  | .refErrorEntityIfFilledNotReferenced =>
      "MVK_REF_ERROR_ENTITY_IF_FILLED_NOT_REFERENCED"
  | .refErrorEntityIfNotFilledNotReferenced =>
      "MVK_REF_ERROR_ENTITY_IF_NOT_FILLED_NOT_REFERENCED"
  | .invalidPattern => "MVK_INVALID_PATTERN"
  | .invalidTypeForPatternComparison =>
      "MVK_INVALID_TYPE_FOR_PATTERN_COMPARISON"
  | .internalError => "MVK_INTERNAL_ERROR"
  | .invalidLengthOfRawType => "MVK_INVALID_LENGTH_OF_RAW_TYPE"
  | .noNumber => "MVK_NO_NUMBER"
  | .notSortable => "MVK_NOT_SORTABLE"
  | .stringEnumAndNonStringEnum => "MVK_STRING_ENUM_AND_NON_STRING_ENUM"
  | .numberAndNonNumber => "MVK_NUMBER_AND_NON_NUMBER"
  | .onlyStringEnumNumberCmpDateAllowed =>
      "MVK_ONLY_STRING_ENUM_NUMBER_CMP_DATE_ALLOWED"
  | .invalidCompareDecimalPlaces => "MVK_INVALID_COMPARE_DEC_PLACES"
  | .errorReferenceToCalculatedField =>
      "MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD"
  | .errorSemanticIndexOrCategoryForErrorField =>
      "MVK_ERROR_SEMANTIC_INDEX_OR_CATEGORY_FOR_ERRORFIELD"
  | .invalidDateType => "MVK_INVALID_DATE_TYPE"
  | .noDateRange => "MVK_NO_DATE_RANGE"
  | .partialDateNotAllowed => "MVK_PARTIAL_DATE_NOT_ALLOWED"
  | .invalidParameterForDateRangeComparison =>
      "MVK_INVALID_PARAMETER_FOR_DATE_RANGE_COMPARISON"
  | .invalidCompareToEnumOrString => "MVK_INVALID_COMPARE_TO_ENUM_OR_STRING"
  | .inconsistentTypesCompared => "MVK_INCONSISTENT_TYPES_COMPARED"
  | .dateWithAndWithoutYear => "MVK_DATE_WITH_AND_WITHOUT_YEAR"
  | .invalidCompareToDate => "MVK_INVALID_COMPARE_TO_DATE"
  | .noDate => "MVK_NO_DATE"
  | .wrongDateFormatForOp => "MVK_WRONG_DATE_FORMAT_FOR_OP"
  | .invalidCompareToDateRange => "MVK_INVALID_COMPARE_TO_DATE_RANGE"
  | .invalidDateRangeFormat => "MVK_INVALID_DATE_RANGE_FORMAT"
  | .semanticIndexContainedInIndex => "MVK_SEMANTIC_INDEX_CONTAINED_IN_INDEX"
  | .noIndexField => "MVK_NO_INDEX_FIELD"
  | .semanticIndexNotAllowed => "MVK_SEMANTIC_INDEX_NOT_ALLOWED"
  | .semanticIndexAndWildcard => "MVK_SEMANTIC_INDEX_AND_WILDCARD"
  | .indexForErrorTextInvalid => "MVK_INDEX_FOR_ERROR_TEXT_INVALID"
  | .missingYear => "MVK_MISSING_YEAR"
  | .onlyConstantsUsed => "MVK_ONLY_CONSTANTS_USED"
  | .extractOpNotAllowedForFourParamDateConstruct =>
      "MVK_EXTRACT_OP_NOT_ALLOWED_4_DATE_CONSTRUCT_WITH_4_PARAMS"
  | .nonNumeric => "MVK_NON_NUMERIC"
  | .noDateConstant => "MVK_NO_DATE_CONSTANT"
  | .noTypeYesOrYesNo => "MVK_NO_TYPE_YES_OR_YESNO"
  | .invalidType => "MVK_INVALID_TYPE"
  | .noNumberForCalc => "MVK_NO_NUMBER_FOR_CALC"
  | .invalidConst => "MVK_INVALID_CONST"
  | .noStringOrEnum => "MVK_NO_STRING_OR_ENUM"
  | .invalidCompareEnumToString => "MVK_INVALID_COMPARE_ENUM_TO_STRING"
  | .paramSizeInvalidTwo => "MVK_PARAMSIZE_INVALID_2"
  | .pointInA12Model => "MVK_POINT_IN_A12_MODEL"
  | .notInRuleGroup => "MVK_NOT_IN_RULEGROUP"
  | .indexTypeInconsistent => "MVK_INDEX_TYPE_INCONSISTENT"
  | .invalidFieldInParameter => "INVALID_FIELD_IN_PARAMETER"
  | .errorEmptyPrecondition => "MVK_ERROR_EMPTY_PRECONDITION"
  | .errorIndexAsCalculatedField => "MVK_ERROR_INDEX_AS_CALCULATED_FIELD"
  | .enumValueWithInvalidCharacter => "MVK_ENUM_VALUE_WITH_INVALID_CHARACTER"

/-- Every established class, so a consumer can enumerate the covered surface and a law can quantify over it. -/
def all : List KernelStaticDiagnostic :=
  [.invalidStringConstantForEnumComparison,
    .onlyStringEnumNumberDateAllowed, .onlyStringEnumNumberAllowed,
    .invalidTypesForComparison, .invalidTypeForComparison,
    .noIterationForWildcard, .invalidIterationInFilterCondition,
    .numberAndNonNumber, .onlyStringEnumNumberCmpDateAllowed,
    .varyingTypesNotAllowed, .noBoolyAllowed, .invalidCompareToYes,
    .invalidCompareToYesNo,
    .fieldNotInRuleGroup,
    .paramSizeInvalidN,
    .paramSizeInvalidGN, .paramSizeInvalid2, .duplicateParam1, .duplicateParam2,
    .differentGroups, .noWildcard, .wildcardOnlyAtLowestLevelAllowed,
    .wildcardAtLowestLevelRequired, .repeatableLevelRequired,
    .invalidWildcard, .noWildcardsGAllowed, .noWildcardsAllowed,
    .noGroupsAllowed, .noStringOrEnumOrExtEnum, .dateFormatsNotCompatible,
    .dateAndNonDate,
    .invalidEntity, .rootGroupReferenced, .rootGroupWithOtherParameters,
    .repeatableGroupMissing, .negativeConditionInIteration,
    .errorFieldNotReferenced, .invalidStringConstantForEnumeration,
    .invalidStringConstantForEnumerationCategory, .categoryUnknown,
    .indexFieldUnresolved, .indexFieldAmbiguous, .indexFieldComposedIndex,
    .indexFieldRepeatabilityMismatch, .indexFieldNotIterating, .indexFieldNonRepeatableEnum,
    .invalidGroupInParameter, .iterParamWithStarReference,
    .invalidUseOfSemanticIndex, .invalidUseOfIterationParam, .errorTextInvalidCondition,
    .invalidPathSpecInParameter,
    .maxGroupRestrictionToOne, .maxLfdNrRestrictionToOne,
    .entityMoveInA12ModelCondition,
    .entityMoveInA12ModelErrortext, .multipleIndexFields, .multipleIndexFields2,
    .indexFieldInvalid, .missingErrorField, .errorFieldNotValid,
    .errorFieldAndZIterationInvalid, .errorFieldGroupIteration4Invalid,
    .errorFieldGroupIteration5Invalid, .refErrorEntityIfFilledNotReferenced,
    .refErrorEntityIfNotFilledNotReferenced,
    .invalidPattern, .invalidTypeForPatternComparison, .internalError,
    .invalidLengthOfRawType, .noNumber, .notSortable,
    .stringEnumAndNonStringEnum, .invalidCompareDecimalPlaces,
    .errorReferenceToCalculatedField,
    .errorSemanticIndexOrCategoryForErrorField, .invalidDateType, .noDateRange,
    .partialDateNotAllowed,
    .invalidParameterForDateRangeComparison, .dateWithAndWithoutYear,
    .invalidCompareToEnumOrString, .inconsistentTypesCompared,
    .invalidDateRangeFormat, .invalidCompareToDateRange, .wrongDateFormatForOp,
    .invalidCompareToDate, .noDate, .semanticIndexContainedInIndex,
    .noIndexField, .semanticIndexNotAllowed, .semanticIndexAndWildcard,
    .indexForErrorTextInvalid,
    .missingYear, .onlyConstantsUsed, .extractOpNotAllowedForFourParamDateConstruct,
    .nonNumeric, .noDateConstant, .noTypeYesOrYesNo, .invalidType, .noNumberForCalc,
    .invalidCompareEnumToString, .paramSizeInvalidTwo, .pointInA12Model,
    .notInRuleGroup, .indexTypeInconsistent, .invalidFieldInParameter,
    .errorEmptyPrecondition, .errorIndexAsCalculatedField, .enumValueWithInvalidCharacter,
    .invalidConst, .noStringOrEnum]

end KernelStaticDiagnostic

end A12Kernel
