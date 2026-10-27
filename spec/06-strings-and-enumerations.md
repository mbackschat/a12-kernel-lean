# 06 — Strings, patterns, and enumerations (§7 + §8)

Part A covers how a stored String is checked and normalized, `Length`, pattern admission and execution, String concatenation, raw-type Strings, the legal character set and custom field-type validation. Part B covers Enumeration comparison and categories, the value-list quantifiers, scalar membership, membership in computations and the table-backed Enumeration boundary.

Empty behaviour (`== ""` never holds; `Length(empty) = 0`; a nonempty authored pattern is not evaluated on empty input) is [§2's](03-empty-and-required.md#a2-where-an-operator-overrides-its-kinds-default). Which class each operator takes per column is [the operator reference's](14-operator-reference.md); this chapter defines the mechanisms and the classes of its column W.

---

## Part A — §7 Strings and patterns

### Stored-value checking and normalization

**Under the full formal check every stored value, whatever its kind, passes one first-failure sequence before its declaration's own clauses; the first failing step is the finding.**

| Step | Applies | Finding code on failure |
|---|---|---|
| 1. raw-type gate | a String declared with `noValueValidation` ([A.1](#a1-raw-type-strings-novaluevalidation)) | none: the value bypasses every later step and is never interned |
| 2. technical length | the authored text is longer than 99,999 UTF-16 code units, whatever the declaration says | `wertZuLang` |
| 3. legal character set | a character outside the model's `supportedCharacters` ([A.2](#a2-legal-charset-definitions-and-atomic-matching)) | `ZeichenNichtImZeichensatz` |
| 4. leading blank | the text begins with an ASCII space | `fuehrendesBlank` |
| 5. trailing blank | the text ends with an ASCII space | `nachfolgendesBlank` |
| 6. declared format | the declaration's own clauses: for a String or an Enumeration the table below, for a Custom declaration its registered validator ([A.3](#a3-custom-field-type-validation)), for a Number [§5 §4.8](04-numbers-and-decimals.md#48-the-formal-check-of-a-stored-value), for a temporal kind [§6](05-dates-and-time.md) | per clause |

- **Steps 2–5 are input gates of the full check only.** The technical length counts the text as authored, before line-break normalization, so a supplementary character and a CRLF pair each count two; it is distinct from a declared maximum length, which a String field still meets later. A failure stops the sequence: an unsupported character preempts a pattern or custom-validator finding, including a reserved custom report, and a custom validator receives the original text only after these gates succeed.
- **A computed result meets the reduced check.** Checking a computed target omits steps 2–5; a String target still meets its type's own maximum ([§11 §4](09-computations.md#4-the-stored-form--a-computed-value-lands-as-a-string-in-the-targets-shape)).
- **Measured scope.** `wertZuLang`, the trailing-blank code and the order of steps 3–5 rest on source reading, with no local capture; the charset and leading-blank codes are measured.

**A nonempty String or Enumeration value then meets its declared-format clauses, first failure first:**

| Clause | Reads | Finding code | Message |
|---|---|---|---|
| 1. line break: CR or LF where line breaks are not permitted | the raw text | `stringMitNewline` (measured on a String; on an Enumeration inferred, unmeasured) | key `STRING_ENTHAELT_NEWLINE` |
| 2. normalization ([below](#stored-value-checking-and-normalization)) | — | — | — |
| 3. the effective declared pattern against the complete value (String), or membership in the declared values (Enumeration) | the normalized text | `stringFalschesMuster` | String: the declaration's own error text, which a pattern requires; Enumeration: the declaration's own error text when it carries one, otherwise key `ENUMERATION_DEFAULT_ERROR` |
| 4. positive minimum length | the normalized text | `stringZuKurz` | key `STRING_ZU_KURZ`, with the declared bound |
| 5. positive maximum length | the normalized text | `stringZuLang` | key `STRING_ZU_LANG`, with the declared bound |

- The line-break clause covers Enumeration fields too, so a break-carrying value outside the Enumeration's values reports the line-break finding before any domain or pattern finding. A pattern failure wins over a simultaneous length failure.
- An absent or explicitly empty declared pattern constructs no matcher at this declaration locus; this differs from an empty source authored as a `PatternMatched`/`PatternViolated` condition ([Pattern admission and execution](#pattern-admission-and-execution)).
- Empty input bypasses the pattern and length clauses through the ordinary empty-value boundary. Every declared-format failure makes later value consumers observe formal unavailability ([§3 B.3](02-logic-and-formal-errors.md#b3-what-puts-a-cell-in-the-third-state)).
- The other kinds' token keys: a refused Boolean token selects `FELD_JA_NEIN` and a refused Confirm token `FELD_JA`. A message key is chosen on a finer axis than the code ([§5 §4.8](04-numbers-and-decimals.md#48-the-formal-check-of-a-stored-value)).

**Normalization is an ingestion boundary for evaluation, not a rewrite of storage.** A checked-and-valid String enters the evaluation cache with each CRLF pair replaced by LF; the stored document text is never rewritten. The format measure, rule reads including `Length`, and computation reads consume the normalized value: a permitted `"AB\r\nCD"` measures 5 UTF-16 code units and a whitespace-class pattern sees one `\n`.

**Message display is a separate path.** Rule-message field-value interpolation consumes the caller's display value; the public DocumentV2 route takes it from the immutable input document rather than the evaluation cache, and the renderer performs no CRLF normalization. A CRLF-bearing String is therefore normalized for rule evaluation while its message display keeps the original CRLF bytes.

Sources: [formal pre-check](../docs/sources/static-admission-and-class-probes.md#src-universal-value-formal-precheck), [technical length](../docs/sources/domain-ingestion-probes.md#src-technical-length-k13), [checked String ingestion](../docs/sources/domain-ingestion-probes.md#src-checked-string-ingestion-k13), [String expression family](../docs/sources/evaluation-and-application-routes.md#src-string-expression-family) (charset code), [message keys](../docs/sources/domain-ingestion-probes.md#src-date-message-keys-k22), [inbound 2026-10-13](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-13), a12-dmkits [`CrlfLengthNormalizationDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/CrlfLengthNormalizationDiffTest.kt).

### `Length`

**`Length` and the declared minimum and maximum lengths count UTF-16 code units of the normalized text exactly.** No length-bearing path folds code points or clusters graphemes: a decomposed `e` + `U+0301` counts 2, and a supplementary-plane character counts 2, although realistic legal-character policies reject it first. Grapheme clustering appears only in legal-charset acceptance ([A.2](#a2-legal-charset-definitions-and-atomic-matching)), never in a count.

- An addressed `Length` reads that exact checked String cell and uses its ordinary evaluated UTF-16 length.
- Over a raw-type String, `Length` follows [A.1](#a1-raw-type-strings-novaluevalidation).
- **Measured scope.** The combining-sequence count is differentially locked; the supplementary-plane count rests on source reading and is unmeasured.

Sources: a12-dmkits [`AbsLengthDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/AbsLengthDiffTest.kt), [`CrlfLengthNormalizationDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/CrlfLengthNormalizationDiffTest.kt), [iteration-guard checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-iteration-guard-k04).

### Pattern admission and execution

**`PatternMatched` and `PatternViolated` evaluate the whole value — implicitly anchored, so the pattern must match the entire string — with Java `Pattern` semantics; the Groovy-dynamic strategy is the observation anchor.** They read the evaluation-normalized text. A fired pattern comparison is always a **VALUE** error, since no fillable branch exists, and an empty value violates no nonempty authored pattern ([§2](03-empty-and-required.md#a2-where-an-operator-overrides-its-kinds-default)).

**Static admission of the condition.** The [constant-pair gate](04-numbers-and-decimals.md#14-the-constant-pair-gate) runs first, so a pair of String literals draws its refusal. The pattern checks then require, before the pattern source is validated:

| Requirement | Class otherwise |
|---|---|
| an ungrouped field-value operation on the left; a grouped String field and a String concatenation fail it | `MVK_INVALID_PARAMETER_FOR_PATTERN_COMPARISON` |
| a String result type in both slots | `MVK_INVALID_TYPE_FOR_PATTERN_COMPARISON` |
| a constant on the right; a grouped String literal is one | `MVK_MISSING_CONST_IN_PATTERN_COMP` |

A constant is typed before these checks, so a valid date or `HH:mm:ss` literal, `True` and `Today` on the right each draw the type class, while `"12:30"` is a String there and admitted. A Number field against a String field reports the type refusal before the missing-constant refusal. The left field is a field-value read, so its own classes answer ahead of the type class ([§10 §3](08-paths-and-references.md#3-the-asterisk-and-)).

**Pattern admission: a condition-literal pattern and a declared field pattern pass the same two gates.** The source must compile as a Java `Pattern`, and its source text must then pass a finite blacklist. **The two loci draw different codes, the same two words swapped:** a refused condition literal draws `MVK_INVALID_PATTERN` and a refused declared field pattern `MVK_PATTERN_INVALID`. Passing establishes Java legality only, not portability to another regex host.

**The blacklist reads the source text character by character, not the pattern the source spells.** The source is refused when it contains any of these:

| Form | Character-level definition |
|---|---|
| possessive quantifier | `?`, `+`, `}` or `*` immediately followed by `+` |
| group prefix | `(?<` or `(?>`; this covers lookbehind, named capture and atomic groups |
| escape | `\` immediately followed by one of `A`, `G`, `Z`, `z`, `a`, `e`, `p`, `Q`, `E` |
| nested class opener | a `[` not immediately preceded by `\`, after an earlier such `[` with no `]` between them; any `]` ends the scan, escaped or not |

- Measured members: `\P{L}+` is refused for its `}+` adjacency, while bare `\P{L}` is admitted and bare `\p{L}` refused; `a\*+` is refused for the `*+` it carries; `a\+\+` and `\[a\[b` are admitted; `[a\][b]]` is admitted although Java reads its second `[` as a nested class, because the escaped `]` ends the scan.
- The double-backslash readings that follow from the predicate — `\\p` refused, and the `[` in `\\[` treated as escaped — are unmeasured.
- Ordinary lookahead, `(?=...)` and `(?!...)`, is not blacklisted.

**Admission does not imply JavaScript portability.** Known legal separators include inline flag forms, `\R` and `\h`, Unicode `\s`, dot and code-point differences, unmatched backreferences, non-nested class intersections, `\x{…}`, `\N{…}`, `\X` and `\b{g}`. Generated static Java agrees with the Java runtime on the exercised cases. The Kernel's TypeScript target anchors the raw source inside a JavaScript regular expression as a non-capturing group between `^` and `$`; any resulting difference is a characterized strategy split and never replaces the Groovy-dynamic result.

**An empty authored condition pattern is admitted statically but fails when its call is reached**, before the supplied String's availability is inspected. This is a runtime failure, not either operator's ordinary match result: a preceding false guard hides it, while a subsequent false condition cannot suppress it.

- Validation catches it at the enclosing rule and emits that rule's VALUE error. Partial validation still applies error-field dispatch relevance, but operand non-relevance alone does not hide a reached call.
- Computation clears the affected target and blocks alternative fallback; formal-input prechecking can prevent the call first, while independent computations continue.
- `Having` filters carry the same failure to their enclosing rule or computation, a reached declared-but-uninstantiated candidate included.
- Measured for both operators against nonempty twins.

> **Non-normative implementation note.** Keep pattern admission (Java compilation, then the source-text blacklist) separate from whole-value execution, record target splits explicitly, and fail closed outside a declared fragment rather than inventing a portable grammar. An admitted pattern can still backtrack catastrophically, for example `(a+)+`.

Sources: [inbound 2026-09-21 corrections](../docs/sources/inbound-handbacks.md#inbound-2026-09-21-corrections), [inbound 2026-09-30a regex operands](../docs/sources/inbound-handbacks.md#inbound-2026-09-30a-regex-operands), [inbound 2026-09-26d constant typing](../docs/sources/inbound-handbacks.md#inbound-2026-09-26d-constant-typing), [comparison entry gates](../docs/sources/static-admission-and-class-probes.md#src-comparison-entry-gates), [empty pattern execution](../docs/sources/computation-scheduling-probes.md#src-empty-pattern-execution).

### String concatenation

**`+` between two string-like operands concatenates them; between two Numbers it adds.** The operand-kind gate of `+` and its `MVK_NO_STRING_OR_NUMBER_FOR_ADD` class, the gates of the other arithmetic operators, and the order in which these meet the division and power checks are [§5 §4.1–§4.2](04-numbers-and-decimals.md#41-arithmetic-operand-kinds), which also says which result type an outer operator judges.

**A direct Enumeration field operand of `+` is refused under that addition class when it carries effective display remapping** ([B.1](#b1-comparison-is-by-stored-value-and-direct-field-comparability-depends-on-effective-display-remapping)). Absent labels and identity-only labels pass, as does a category access.

- **The restriction inspects an immediate field-value operand only**, not every Enumeration result. `{[E]} + "x"` passes even when `[E] + "x"` fails, while `{[E] + "x"}` still fails at the inner addition. Grouping keeps the Enumeration result type; only the completed concatenation has String type. The same holds for key-selected Enumeration fields.
- An admitted Enumeration operand contributes its stored value, not its display label; a category contributes its projected category value. Two grouped Enumerations concatenate by the same rule, and `FirstFilledValue` over Enumeration operands contributes its selected stored value.
- An empty operand contributes no text, and a wholly empty concatenation clears a computed String target.
- A String literal shaped like a date is a date constant ([§6 §1](05-dates-and-time.md#1-constant-format-and-the-stringdate-literal-ambiguity-)), so it cannot be concatenated.

Sources: [String expression family](../docs/sources/evaluation-and-application-routes.md#src-string-expression-family), [reviewed handback 2026-10-09](../docs/sources/inbound-handbacks.md#inbound-2026-10-09-extensions).

### A.1 Raw-type Strings (`noValueValidation`)

**A String declared with `noValueValidation` is a raw type: its value stays in the document but is never interned for evaluation, so model validation refuses every construct that would read the value, while its presence stays readable.** It never enters the third state ([§3 B.3](02-logic-and-formal-errors.md#string-ingestion-boundary)); its formal check is step 1 of [the stored-value check](#stored-value-checking-and-normalization).

How a construct treats a raw String operand is its class in [column W of the operator reference](14-operator-reference.md#raw-string-operand):

| Class | Treatment |
|---|---|
| `raw class` | refused `MVK_INVALID_RAW_TYPE`. A bracketed field-value read refuses a raw String wherever it stands ([§10 §3](08-paths-and-references.md#3-the-asterisk-and-)), so every value slot does; an operator naming the field as an entity parameter takes this class only where its own gate is this one. A computation whose target is a raw String is refused the same way. |
| `own class` | refused by the operator's own class for its operand: `MVK_NO_CONVERT_IN_NUMBER` for `FieldValueAsNumber`, `MVK_NO_NUMBER` for `FieldValueAsString` and `MVK_NO_ENUMERATION` for a category read ([§10 §3](08-paths-and-references.md#3-the-asterisk-and-)); `MVK_NO_FIELDS_ALLOWED` for a field operand of `GroupFilled`, `GroupNotFilled`, `NumberOfFilledGroups` ([§1 A.4.9](02-logic-and-formal-errors.md#a49-static-admission-of-group-and-field-slot-operands)) and `CurrentRepetition`; `MVK_TABLE_ENUM_EXPECTED` for a `ValueNotConsistent` subject ([B.6](#b6-table-backed-enumerations-and-valuenotconsistent)) |
| `presence only` | admitted: presence predicates and the field-fill counts observe whether content exists without reading it, and a filled raw cell counts as filled. Raw content inside a group operand counts as content for a group predicate in the same way, whatever the predicate's class for a raw field operand. |
| `placeholder X` | admitted as a `FirstFilledValue` member, in a rule or a computation and in any position: a filled raw member reads as the token `X` whatever its text, a single space included, and an empty one is skipped, on both Kernel strategies |
| `length shape` | `Length`: admitted only in the shape below |

Message interpolation of the value, `$Field.value$`, is refused `INVALID_NO_VALUE_VALIDATION` ([§13 A.6](11-messages-and-custom.md#a6-name-position-field-references)).

**`Length` over a raw String is authorable only as the whole rule condition, and that shape is metadata, not a runtime rule.**

| Shape | Outcome |
|---|---|
| the whole rule condition `Length(f) > c`, or the mirrored `c < Length(f)`, with strict `>`/`<` and a constant written without a decimal point whose exact integer value lies in `-2147483648..2147483647` | admitted |
| the same strict whole-rule shape with a decimal-point spelling, a fractional value, or an integer outside that interval | `MVK_INTERNAL_ERROR` |
| every other `Length` shape, computation preconditions included | `MVK_INVALID_LENGTH_OF_RAW_TYPE` |

Shape admission precedes bound admission: an overlapping form such as `Length(f) >= 5.0` reports `MVK_INVALID_LENGTH_OF_RAW_TYPE`, not `MVK_INTERNAL_ERROR`. Code generation eliminates the admitted shape in both strategies and lifts `(field, c)` into the generated meta-model's maximum-length metadata, so it never fires, for a filled value or an empty one. Presence semantics over the same cell remain ordinary.

**Measured scope.** Measured rows: `==`; `+` (Number), `*` and `Abs` in a computation; a computation's operation and target; the scalar `FieldValueIncludedInValueList` members and subject; the three value-list quantifiers' field and value lists; `NumberOfDifferentValues`; `FieldValuesNotUnique`; `RepetitionNotUnique`; `RangeAsNumber`; `FieldValueAsNumber`; `FieldValueAsString`; the category read; a raw key field of `[F For key]`; `Valid` and `Invalid` over a named type; `Length`; `FirstFilledValue` in rules and computations; `NumberOfFilledFields` and `AtLeastOneFieldFilled` (presence). A pattern comparison's field and a DateRange comparison's right side are measured with the operator unnamed. Every other assignment follows the general rule and is unmeasured, the `own class` cells of the group predicates, `CurrentRepetition` and `ValueNotConsistent` included.

> **Non-normative implementation note.** Reject every raw-type value window during static checking, and desugar the admitted `Length` shape into metadata with no runtime rule. No runtime value state is needed for a raw String, because legal evaluation cannot read its value.

Sources: [K22 static batch 4](../docs/sources/group-count-topology.md#src-k22-static-s4), [checked String ingestion](../docs/sources/domain-ingestion-probes.md#src-checked-string-ingestion-k13) (named-type validity), [field-value read predictions](../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions), a12-dmkits [`NvvRawTypeDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/NvvRawTypeDiffTest.kt).

### A.2 Legal charset definitions and atomic matching

**The model's `supportedCharacters` is a cross-kind baseline for stored and input values**, step 3 of [the stored-value check](#stored-value-checking-and-normalization).

**Definition.** An absent definition or an empty list selects the default policy: the non-surrogate Basic Multilingual Plane. A list containing an empty string differs: `[]` is the default, while `[""]` is malformed. A nonempty entry is legal only in one of these forms:

- one non-surrogate BMP UTF-16 unit, defining a singleton;
- exactly three UTF-16 units `X-Y`, where `X` and `Y` are non-surrogate BMP endpoints and `X ≤ Y`, defining an inclusive range; or
- a surrogate-free combined atomic entry of two or three UTF-16 units whose Unicode grapheme-cluster decomposition is shorter than its UTF-16 representation, so the entry contains a combining sequence. The entry may contain more than one cluster, but matching consumes the whole configured entry atomically.

An empty entry, a surrogate-bearing entry, a reversed range, a combined entry longer than three UTF-16 units, or a plain multi-character sequence such as `ab` with no combined grapheme is malformed. Shared prefixes are otherwise legal: configured `e`+combining-acute and `e`+combining-grave may coexist, and a complete atomic entry may be a terminal prefix of a longer one.

**The ambiguous-overlap rejection is narrower than "no overlap".** For a combined entry whose grapheme-cluster decomposition is `p₁ … pₙ · s` with at least one prefix cluster, reject it only when every prefix cluster is independently representable by a configured singleton, range or atomic entry, and the final cluster `s` is a proper, different-length UTF-16 prefix of another configured atomic entry. So the `q`+combining-acute+`r` entry is rejected when `q`+combining-acute and `r`+combining-grave are also configured, while the legal shared-prefix cases stay legal.

**Matching proceeds left to right.** At each input position, walk the configured atomic-entry trie and consume the longest complete terminal entry that bounded walk selects. If no complete atomic entry matches, test exactly the leading code point against singleton and range membership and consume it only when admitted; otherwise the value fails the charset check. Every successful step advances, because empty entries are forbidden and every accepted atomic entry is bounded. A configured combined entry admits only its complete sequence: its base, combining mark, reversed sequence, suffix or repeated component is not independently legal unless another singleton, range or atomic entry admits it.

Charset matching does not alter length semantics ([`Length`](#length)).

Sources: [checked String ingestion](../docs/sources/domain-ingestion-probes.md#src-checked-string-ingestion-k13), a12-dmkits [`SupportedCharactersDefinitionDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/SupportedCharactersDefinitionDiffTest.kt), [`SupportedCharactersGraphemeDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/SupportedCharactersGraphemeDiffTest.kt) (both Kernel strategies), [`LegalCharsetDefinitionTest`](../../a12-rulekit/interpreter/src/commonTest/kotlin/io/github/mbackschat/a12/dm/interpreter/LegalCharsetDefinitionTest.kt), [`LegalCharsetGraphemeTest`](../../a12-rulekit/interpreter/src/commonTest/kotlin/io/github/mbackschat/a12/dm/interpreter/LegalCharsetGraphemeTest.kt).

### A.3 Custom field-type validation

**A declared `CustomFieldType(name, minLength?, maxLength?)` delegates its value-specific acceptance completely to the named registered validator, a host-supplied oracle.** Its declared bounds are callback context, not generic String minimum and maximum checks: no ordinary String length check runs before the validator.

**The callback's inputs are exactly these:** the cell's text; an effective minimum, the authored value or `1`; an effective maximum, the authored value or `999`; the effective locale; and the stored/display-value mode. The raw declaration preserves whether each bound was authored. The validator receives no document, sibling cell or repetition context, so acceptance is local to the cell by construction; a host-constructed validator may still carry state, so its purity is a contract expectation, not a guarantee. The ordinary stored-document check supplies the stored-value mode (`isDisplayValue = false`); the display-value mode arises only on the conversion-enabled path below, and its behaviour is unmeasured.

**Input and evaluated text.** The validator receives the original stored text. After acceptance, or after a reserved report that admits the value, evaluation caches exactly one non-overlapping CRLF-to-LF pass; a lone CR is preserved. Value reads, `Length` and computations consume that evaluated payload without repeating ingestion. Raw storage stays unchanged until a computation explicitly writes its target.

**One observation per relevant concrete-valued cell, reused by every consumer:** automatic formal-message emission, authored-rule and candidate suppression, computation poison, and `RepetitionNotUnique` key filtering. An empty or non-relevant cell is excluded before the oracle is sampled.

- **The sampling unit is the cell, never the distinct value.** Two cells holding the same value are two observations, reported at their own pointers; this cardinality is differentially locked. Because the oracle is taken as pure and total, that cardinality changes no verdict, and an implementation may memoize on the complete declaration, context and value key; keying on the bare value across declarations or contexts is wrong even for a pure oracle, and an oracle that is not pure, such as a counting or logging validator, observes the per-cell count directly.
- **An observation is acceptance or a project rejection** carrying a required project error code and an optional message template. The project code is preserved verbatim in the formal report and, for an unavailable value, in its suppression cause; it does not collapse to a generic constant.
- **In a rejection template,** every literal token naming the field as `$<fieldName>$` is replaced with that field's localized label under the [label-resolution rule](11-messages-and-custom.md#a11-rendering-a-rule-owned-message); all other text is unchanged.

**The reserved callback code `testIDNummer` reports while admitting the value.** It reports a `VALUE_ERROR` with severity `ERROR` while the normalized value stays readable. Case changes, suffixes and whitespace variants are ordinary rejections.

- The report does not add the cell to the custom-condition invalid-pointer set and does not itself exclude a message-cache key; a later duplicate-index finding can still make the cell unavailable.
- Full examination continues through either kind of custom finding. The core abort-on-formal-errors mode stops after either kind, the readable reserved report included: readability alone does not decide continuation.
- This account is the modern expanded-A12 profile. The legacy unique-entity profile is outside this specification: no witness is known of the supported A12 generation route selecting it, and its reserved-result behaviour is unmeasured.

**Registration and lookup.**

- **The supplied factory and the static registry are alternatives, not a fallback chain.** The registry is consulted only when no factory was supplied at all, so a static registration does not rescue a factory that answers empty.
- **The model check does not reject a missing registration**, and lookup happens only under a full check: a format check run with the full-check flag off accepts the value without consulting the factory. The computed-target check runs custom format validation with that flag on, so the reduced check of a computed target still invokes the registered validator.
- **Under a full check, a relevant concrete cell reaching an unregistered validator fails loudly.** It is neither accepted nor converted into a generic formal rejection; a validator-missing exception naming the declared type is in the cause chain. **The failure escapes the full-check call, so the document receives no validation result at all:** the offending cell contributes no formal message beside the other fields', and every message the same document produces when the cell is empty is lost with the call. At the runtime API boundary the caller observes a generic invocation failure, with the declared type name one level below it in the cause. An absent cell raises nothing and never calls the validator. Measured with a value-absent and a field-absent control.
- The separate declarative predefined-type fallback uses the fixed `customFieldTypeInvalid` code; it cannot replace or reinterpret the registered validator's result.
- The explicit `Valid(field, "Name")` and `Invalid(field, "Name")` predicates invoke the registered validator as an authored condition; their admission and runtime, the unregistered-name failure included, are [§6 §3.7's](05-dates-and-time.md#37-valid-and-invalid-over-a-named-type). Custom field validation is also distinct from [`CustomCondition`](11-messages-and-custom.md#part-b--14-customcondition--the-escape-hatch).

**A registered custom field type is a triple, not a predicate: an acceptance decision and a bidirectional codec.** The codec maps display-to-internal and internal-to-display, each taking one string to a converted string plus an optional error message. An evaluator therefore accepts a registry of these triples as host input, as it accepts a clock, because acceptance is not derivable from the model.

**The codec runs only on a conversion-enabled presentation path, which the caller opts into.** In the Java runtime the codec has one engine-side caller, gated on the caller's presentation information requesting custom-field-type conversion; the direction follows the ingress, XML selecting internal-to-display and every other ingress display-to-internal. Neither arm runs on the ordinary `validateFull` path, on either strategy, where acceptance is called once in the stored-value mode; an implementation offering acceptance alone is complete for that path. On the conversion-enabled path:

1. the full-input charset and blank gates run;
2. registered acceptance runs with the declared bounds, its stored/display mode supplied by the presentation flag;
3. the once-normalized text is converted after acceptance, and the converted string is selected from the codec result, whose optional error message that caller does not consume.

Empty values bypass this path. The conversion-enabled path rests on source reading of the Java runtime, not on a runtime calibration of host codec algorithms; the TypeScript runtime carries its own mirror site, which is unmeasured.

> **Non-normative implementation note.** An analysis or SMT consumer can model acceptance as an uninterpreted predicate over the cell's text, parameterized by the two declared bounds, the effective locale and the stored/display mode; an impure validator breaks that model as it breaks memoization. The codec resists the same treatment, since an uninterpreted string-to-string function blocks most reasoning about its result, but only a consumer that opts conversion in reaches it. The pinned host interface is `ICustomFieldValidator`; its predecessor, which carries a per-declaration configuration map, is deprecated for removal.

Sources: [custom ingestion](../docs/sources/custom-field-probes.md#src-custom-ingestion), [reserved test range](../docs/sources/custom-field-probes.md#src-custom-test-range), [legacy profile](../docs/sources/custom-field-probes.md#src-custom-legacy-profile), [custom field-type SPI](../docs/sources/evaluation-and-application-routes.md#src-custom-field-type-spi), [presence, Confirm and custom carriers](../docs/sources/having-filter-probes.md#src-presence-confirm-custom-carriers), [checked String ingestion](../docs/sources/domain-ingestion-probes.md#src-checked-string-ingestion-k13), [Kernel lock index](../docs/sources/kernel-locks.md#src-kernel-lock-index), [validator cardinality](../docs/sources/inbound-group-operand-batches.md#validator-cardinality-and-cleared-value-checkpoints), a12-dmkits [`CustomFieldTypeContextCacheTest`](../../a12-rulekit/interpreter/src/commonTest/kotlin/io/github/mbackschat/a12/dm/interpreter/CustomFieldTypeContextCacheTest.kt).

---

## Part B — §8 Enumerations

### B.1 Comparison is by stored value, and direct-field comparability depends on effective display remapping

- Rule conditions compare the **stored enumeration value**, not the displayed text: write `[Country] == "F"`, not `[Country] == "France"`.
- An ordinary enumeration is **effectively display-bearing** only when at least one localized display differs from its stored value. No authored labels and labels that all repeat their stored values are both effectively textless for this rule.
- A direct plain-String field can be compared with an effectively textless enumeration field, but not with an effectively display-bearing one. Likewise, two enumeration fields are rejected when exactly one is effectively display-bearing.
- Two effectively display-bearing enumeration fields need not have identical declarations. For every locale common to both, a shared stored value must have the same display and a shared display must denote the same stored value. Disjoint mappings and non-overlapping locale sets are accepted.
- This direct-field gate is shared by `==` and `!=`. A String literal that is a valid stored or selected-category token and an already-checked category access follow their separate domain and projection rules rather than this field-to-field display gate.
- If either Enumeration operand is an already-checked category access, the display-remapping gate is bypassed. Its projected category token can be compared by `==`/`!=` with a direct String value, another category token, or a plain Enumeration's stored token.
- Operand shape matters on the String side: `{[S]}` and String-producing operations do not undergo the immediate String-field display gate. Grouping an Enumeration retains its domain and display policy, and grouping a String literal retains its constant-domain check. `FirstFilledValue` over text operands, two Enumerations included, produces a String result, so its result does not carry an Enumeration literal domain.
- **Measured scope.** The operand-shape distinctions are measured in both operand orders, with grouped valid and invalid literals and effective-display controls.

> **Non-normative implementation note.** Keep static comparability separate from runtime projection. For a legal ordinary enum declaration, retain locale-tagged `(stored, display)` facts, derive effective display-bearing status from `stored ≠ display`, and check the common-locale relation in both directions. Runtime evaluation compares stored tokens; `->` is a positional lookup over parallel stored/category vectors, so many-to-one mapping falls out directly.

Sources: [reviewed comparison matrix](../docs/sources/inbound-handbacks.md#inbound-2026-10-09-reconciliation).

### B.2 Categories via `->`

**An Enumeration value can carry named category attributes, read with the `->` operator, and the mapping is positional and many-to-one.** `values[i]` categorizes enum value *i*, so a comparison over a category fires for *every* value sharing that category value:

```
[Country -> AdministrationArea] != "EU"
```

An empty enum rides the not-evaluated track, category hop or not. How a category projection classifies an empty, unavailable or invalid cell is [B.3](#b3-the-value-list-quantifiers--per-cell-three-way-classification-)'s.

#### Category declaration

**A category's token list must have exactly as many entries as the enum has values; equal cardinality is the whole rule.**

- A shorter list draws `MVK_MISSING_CATEGORY_VALUE`, once per unclassified value, so an empty list draws it once per value rather than once for the declaration. A longer list draws `MVK_MISSING_INTERNAL_VALUE` once per surplus token, so two surplus tokens draw it twice.
- Same-length tokens **disjoint** from the enum's own values are admitted, which separates positional pairing from any set-membership reading, and a same-length reordering is admitted too. Repeated category tokens are admitted. Every enum value therefore has exactly one category token, so no stored value lacks a category token.
- A second category is judged independently of the first, and a body carrying no `categories` member is admitted.
- An Enumeration with no value fails the build ([data model §1.3](01-data-model.md#13-declaration-generation-classes)), with categories and without them alike, so no category arity class is raised for it.

#### Declaration notifications

**The declaration check collects its notifications rather than stopping at the first, so order and multiplicity are observable.** Every notification is an ERROR, and they arrive in six blocks, in this order:

| Block | Notifications |
|---|---|
| 1 | Only under a restricted `supportedCharacters` list: one `MVK_ENUM_VALUE_WITH_INVALID_CHARACTER` per rejected UTF-16 code unit of each stored value, one per rejected index. |
| 2 | One codeless supplementary-plane notification for the whole field when any stored value or display label holds a supplementary-plane scalar, under every charset; BMP non-ASCII text does not raise it. |
| 3 | The category arity classes, every category's `MVK_MISSING_CATEGORY_VALUE` notifications ahead of every category's `MVK_MISSING_INTERNAL_VALUE` notifications, whatever the category order. |
| 4 | One `MVK_CATEGORY_VALUE_DUPLICATE` per repeated stored value and category. |
| 5 | One `MVK_INTERNAL_VALUES_DUPLICATE` per repeated stored value. |
| 6 | One codeless repeated-value notification per repeated stored value. |

- **A stored value holding a supplementary-plane scalar.** In block 1 its high surrogate is rejected even under a range numerically covering it, and its low surrogate is judged alone, rejected unless a declared range numerically covers it: under `A-Z` the scalar counts as two, under `U+0020–U+FFFD` as one, and two scalars sharing a high surrogate in one value under that range count once, while two values sharing it count once each. The one model measured declaring a supplementary range does not build. In block 3 such a value draws no shortfall notification, although its position still counts toward the arity; blocks 4 and 5 skip it, and block 6 does not. The repertoire substitution of [data model §1.3](01-data-model.md#13-declaration-generation-classes) therefore does not apply to blocks 1 and 6.
- **Identical notifications collapse:** the same rejected unit twice in one value, or the same surplus token twice in one category, counts once, while equal notifications from different categories stay separate.
- The order of categories or values inside blocks 3 and 4 is not observable through class codes and is not stated.

Sources: [inbound 2026-09-21 corrections](../docs/sources/inbound-handbacks.md#inbound-2026-09-21-corrections), [declaration notifications](../docs/sources/model-structure-and-declaration-probes.md#src-enumeration-declaration-notifications), [supplementary charset supplement](../docs/sources/model-structure-and-declaration-probes.md#src-sort-list-capacity), [inbound 2026-10-13](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-13).

### B.3 The value-list quantifiers — per-cell three-way classification ⚠

**`AtLeastOne` / `No` / `NotAll` `…FieldValue(s)IncludedInValueList(f1, f2 In v1, v2, …)` expand both sides per cell and classify each cell three ways — filled, empty, or not check-relevant (UNKNOWN, [§3](02-logic-and-formal-errors.md#b2-the-three-cell-states--the-third-one-is-not-empty)) — and each quantifier then runs its own ordered passes over those cells.** A starred entry contributes one cell per instantiated row. The three are not Boolean duals of one another.

#### Static admission

**The field list asks its own repeat first, as it is built, then its root, base-type and kind gates, then its value validation; the values side follows.** The scope gate outranks the kind gate.

1. **Repeat.** An exact repeated reference in the field list draws `MVK_DUPLICATE_PARAM1` as the list is built, ahead of its base-type and kind gates: `(Ref, Ref, Amount In "x")` draws it over a String `Ref` and a Number `Amount`.
2. **Scope.** On an **unstarred repeatable** level the kind gate is never reached and `MVK_NO_WILDCARD` answers, whatever the slot's kind and shape: a group, its fields listed out and a single field draw it alike. A non-repeatable carrier, or a repeatable one written with its star, binds the level, and the gates below apply unchanged.
3. **One base type.** The field list must share one base type, or it draws `MVK_VARYING_TYPES_NOT_ALLOWED` whatever its kinds. The four temporal kinds share one base type and a Custom declaration shares String's; every other kind is a base type of its own. A group operand's expansion joins this gate, and a category read counts as an Enumeration there.
4. **Kind.** On a list of one base type the admitted kinds are String, Enumeration, Number and Custom; every other declared kind — DATE, TIME, DATETIME, DATEFRAGMENT, DATERANGE, BOOLEAN and CONFIRM, a closed list — draws `MVK_ONLY_STRING_ENUM_NUMBER_ALLOWED`. **The code's name lists three kinds over a set of four**, because the string-likeness test admits a Custom declaration: derive the admitted set by complementing the refused one, not from the name. **The gate does not read the operand's shape:** a homogeneous group, a two-field list and a sole field of the same kind draw the identical class. **Number is admitted, which makes this a kind gate and not a literal-agreement one:** against a String literal list a Number slot clears this class and draws `MVK_INVALID_TYPES_FOR_COMPARISON` one step later, in every slot shape.
5. **Value validation.** A raw String draws `MVK_INVALID_RAW_TYPE` ([A.1](#a1-raw-type-strings-novaluevalidation)).
6. **The values side**, below.

Measured base-type and kind cases:

| Field list | Class |
|---|---|
| a Date beside a date fragment; a Time beside a DateTime | pass the base-type gate and meet the kind gate |
| a String beside a Custom field | admitted |
| String beside Number, Date or Enumeration; Boolean beside Confirm or Date; Number beside Date; a date range beside String, each in either order where both were measured | `MVK_VARYING_TYPES_NOT_ALLOWED` |
| a group holding a String and a Date, as the field list or opposite a String; a group holding a Number, beside or opposite a String; a category read opposite a String | `MVK_VARYING_TYPES_NOT_ALLOWED` |

**A literal values side** is available for String fields, a Custom field included (unmeasured), and for Enumeration fields. Plain String literals are unrestricted decoded String tokens.

- When the fields side holds ordinary Enumerations or category accesses, static admission uses the **union** of the selected domains: every literal must be a stored token of at least one direct Enumeration operand or a category token of at least one category operand, but need not belong to every listed declaration.
- The fields side is nonempty, preserves authored order and refuses an exact repeated reference; direct stored access and named category access on the same physical field are distinct references.
- **A multi-field Number form has no literal-list shape** and requires a nonempty field-valued values side: after `In`, a bare `1` is read as a path and draws `MVK_INVALID_ENTITY`, while `1.00` does not survive the parser (`MVK_UNEXPECTED_TOKEN`). The scalar twin does not share this limit: `FieldValueIncludedInValueList(Assessed, 1, 2)` is admitted in the same model ([B.4](#b4-scalar-membership-is-a-singleton-specialization-not-boolean-negation-)), so the two carriers' literal surfaces are not interchangeable.

**An empty stored token is a legal declared value and literal, never a cell value.** An Enumeration may declare `""`: the model loads, and the literal `""` passes the union gate exactly where it is a token of a selected domain, drawing `MVK_INVALID_STRING_CONSTANT_FOR_ENUMERATION` elsewhere. A stored `""` cell is [present-empty](01-data-model.md#2-document--an-instance-of-the-tree) whatever the declaration, so the token never matches a cell: that cell reads as an absent one, with no formal finding, while `FieldValueNotIncludedInValueList(E, "")` fires on a cell holding another token. As on a String, `[E] == ""` and `[E] != ""` are admitted and never evaluated, so neither fires on any cell.

**A field-valued values side** matches the first field's base type, and its arity rule is not the entity-list family's ([§9](07-repetition-and-iteration.md)): a sole field on each side is admitted, so `AtLeastOne…(A In B)` over two plain String fields is admitted, while repeating the reference draws `MVK_DUPLICATE_PARAM1` and crossing the base kind `MVK_VARYING_TYPES_NOT_ALLOWED`. Both sides are nonempty and preserve authored order, and no reference may occur twice across the combined lists, nor a group beside its own member. A value list's base-type refusals: a Time value beside a String one opposite a String field, a Number or an Enumeration value opposite a String field, a String value opposite an Enumeration field and a String value opposite a Number field each draw `MVK_VARYING_TYPES_NOT_ALLOWED`, as does the scalar `FieldValueIncludedInValueList(Carrier, [PickupTime])` over a String and a Time. Enumeration declarations need not share or contain each other's stored or category domains; runtime compares the selected projected tokens actually present on the two sides.

**With a field-valued values side the construct asks its gates in five positions:**

1. the field list refuses its own repeat as it is built;
2. it then asks its root, base-type and kind gates and its value validation, so a raw String draws `MVK_INVALID_RAW_TYPE`;
3. the value list asks its root gate and the first field's base type, a field value list refusing its own repeat first;
4. a repeat across the two lists comes next, an exact one drawing `MVK_DUPLICATE_PARAM1` and a group beside its own member, `Recipient In Recipient/RecipientName`, `MVK_DUPLICATE_PARAM2`;
5. a field value list's value validation comes last.

Every operand of both lists is resolved as the text is parsed, so a name resolving to nothing on either side draws `MVK_INVALID_ENTITY` ahead of a raw String's refusal on the other side. Witnesses, over a String `Ref`, a Number `Amount` and a Date `Due`: `AtLeastOne…(Ref, Amount In Ref)` and `(Ref In Ref, Amount)` draw `MVK_VARYING_TYPES_NOT_ALLOWED` and `(Due In Due)` draws `MVK_ONLY_STRING_ENUM_NUMBER_ALLOWED`, while `(Ref, Ref, Amount In "x")` against a literal draws `MVK_DUPLICATE_PARAM1`; a checker that asks every repeat first reports the duplicate class for all four. Over a String `Reference` and a raw String `InternalMemo`, `(InternalMemo In InternalMemo)` draws `MVK_INVALID_RAW_TYPE` and `(Reference In Reference, InternalMemo)` draws `MVK_DUPLICATE_PARAM1`: the field list's value validation stands ahead of the repeat across the lists, the value list's behind it.

**Measured scope.** The static admission rules are measured on `AtLeastOne`; `No` and `NotAll` state the same slot rules and are not separately measured.

#### Per-cell classification

**A category projection inherits the underlying Enumeration cell's three-way classification before projecting its token.** Empty stays empty, a formally unavailable or invalid stored value stays UNKNOWN, and only a filled valid stored value contributes its possibly many-to-one category token. So an empty Enumeration reached through a category hop makes a fired `No` OMISSION and leaves `NotAll` non-firing; the hop never turns the empty cell into a present literal-like value. An index cell the document makes unavailable, a duplicated key or a row above capacity, stays UNKNOWN through the hop as it does for the value read.

#### The three quantifiers

**Omission potential** on a side is an empty member cell, an open declared tail ([§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing)) or a reached `Having` filter on that side's operand.

- **`AtLeastOne`** consumes the complete values side first, skipping empty and UNKNOWN member cells; an empty collected set does not fire and leaves the fields unread. It then scans fields in authored encounter order until a present match, skipping empty and UNKNOWN field cells. A fire is **OMISSION** when the matching fields operand was filtered or any filtered values operand contributed a present member, otherwise **VALUE**; a filtered values operand that contributes only empty or UNKNOWN cells does not change polarity.
- **`No`** consumes the complete values side first: an UNKNOWN member suppresses the result, while values-side omission potential is sticky. It then scans fields in authored cell order: a match ends the scan as non-firing before every later field cell or operand, while a reached UNKNOWN before any match suppresses the result. If the scan exhausts without a match, it fires **OMISSION** when a reached empty field cell, a fields-side open declared tail or filter, or values-side omission potential occurred, otherwise **VALUE**. It is the only member that can fire when nothing is filled. That a fields-side match hides a later UNKNOWN rests on source reading; validation emits no message for either a non-firing or an UNKNOWN result, so it is not message-observable without a negation consumer.
- **`NotAll`** runs three passes:
  1. **Presence search:** it scans the fields for a present cell. With none it does not fire and leaves the values side unread, even when a member is formally unavailable.
  2. **Member collection:** it consumes the complete values side with `No`'s classification: an UNKNOWN member suppresses the result, and omission potential is sticky.
  3. **Restarted subject scan:** it scans the fields again and fires at the first present value outside the member set, skipping empty and UNKNOWN field cells. The fire is **OMISSION** when the outside-witness operand was filtered or the values side has omission potential, otherwise **VALUE**.

**The presence search is observable.** Because it leaves the values side unread, a `Having` filter failure on that unread side is suppressed, while a reached filter failure stays observable. Each filtered scan keeps the kept-successor lookahead of [§9 §3.9](07-repetition-and-iteration.md#39-filter-traversal) before consuming its pending payload, so an early match or outside witness can hide later failures beyond that successor.

**A size-selected emission route omits the presence search without changing a result.** It is selected when a fields operand has at least ten iterations and the values side has no filter, no iteration and at least twenty operands; it hoists those member values and skips the presence search. The equivalence holds for this filter-free member classification only: it does not justify eagerly executing filtered values on the ordinary route.

**Traversal.** Each pass uses the filter scan the [operator reference](14-operator-reference.md#traversal) assigns its quantifier: `AtLeastOne`'s member collection and subject search alike, and every pass of `No` and `NotAll`, `NotAll`'s presence search included. A formally unavailable member ends the collection of `No` and `NotAll` before later filters or authored operands, while `AtLeastOne` skips that member and continues. These traversal distinctions are stated for full validation and computation, computation keeping its poison behaviour for reached unavailable cells ([B.5](#b5-computation-preconditions-preserve-reached-errors-and-traversal-order)).

**A `Having` filter is accepted on either side** and drops rows before per-cell classification, but its polarity effect is encounter- and witness-sensitive as stated above, not one side-wide flag ([§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing)).

#### Partial validation

**A starred entry has two independent relevance facts.** Its instantiated cells are classified individually and filtered by concrete relevance: a non-relevant cell contributes no available concrete value to the scan ([§12 §5.3](10-validation-and-polarity.md#53-reading-a-cell-under-a-relevant-set)); `AtLeastOne` consults only this fact. Its extent is the **declared-slots** predicate, and an extent-unknown entry is consumed side-specifically, both as [§12 §5.4](10-validation-and-polarity.md#54-the-extent-of-a-multi-cell-operand) states. A filtered rule is skipped in a partial call ([§12 §5.2](10-validation-and-polarity.md#52-which-rules-run-and-where)).

> **Non-normative implementation note.** Preserve authored operand boundaries and encounter order rather than flattening each side into one aggregate classification, and preserve observable filter execution as well as the materialized outcome. Return a three-valued verdict and retain UNKNOWN explicitly. An encoding that poisons the values side at collection time needs `NotAll`'s presence search to produce the non-firing result when no field cell is present; without it, it would yield UNKNOWN.

Sources: [inbound 2026-09-25e value-list base type](../docs/sources/inbound-handbacks.md#inbound-2026-09-25e-value-list-base-type), [base-type cross pairs](../docs/sources/static-admission-and-class-probes.md#src-value-list-base-type-cross-pairs), [kind-gate partitions](../docs/sources/static-admission-and-class-probes.md#src-value-list-quantifier-kind-gate-partitions-three-ways), [slot kind set](../docs/sources/static-admission-and-class-probes.md#src-value-list-slot-kind-set), [field-value read predictions](../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions), [sole-operand arity](../docs/sources/static-admission-and-class-probes.md#src-entity-list-sole-operand-arity), [empty Enumeration token](../docs/sources/model-structure-and-declaration-probes.md#src-empty-enumeration-token), [cross-list repeat order](../docs/sources/static-admission-and-class-probes.md#src-value-list-cross-list-repeat-order), [inbound 2026-09-25g value-list order](../docs/sources/inbound-handbacks.md#inbound-2026-09-25g-value-list-order), [inbound 2026-09-25h category index relevance](../docs/sources/inbound-handbacks.md#inbound-2026-09-25h-category-index-relevance), [sparse filter traversal](../docs/sources/group-and-iteration-probes.md#src-sparse-filter-traversal).

### B.4 Scalar membership is a singleton specialization, not Boolean negation ⚠

**`FieldValueIncludedInValueList(subject, members…)` is one-subject `AtLeastOne`, and `FieldValueNotIncludedInValueList(subject, members…)` is one-subject `NotAll`, never the empty-firing `No`.**

- An empty or formally unavailable subject makes **both** scalar forms non-firing.
- With a present subject, `Included` fires **VALUE** iff at least one present member equals it, and `NotIncluded` fires iff no present member equals it.
- An empty field-valued member contributes no atom; if `NotIncluded` otherwise fires, that missing member makes the fire **OMISSION**. A fire against an all-literal member list is **VALUE**.
- A formally unavailable member is skipped by `Included` but makes `NotIncluded` UNKNOWN.

**Runtime equality follows the family's ordinary value boundary:** normalized evaluated text for String, the selected stored or category token for Enumeration, and numeric equality after the ordinary scale-19 normalization for Number. An empty Number member field contributes no zero atom.

#### Static admission

**The subject and the members admit only the String, Enumeration and Number families, and the member list is nonempty.** A Custom declaration carries the String kind, so it takes the String family's rules here; unlike the quantifiers' Custom slot, this is unmeasured on the scalar forms, as is a Custom field against a literal member list.

- **Literal members** must match the subject family: String literals are unrestricted decoded strings, Enumeration literals must belong to the selected stored or category projection's domain, and Number literals are grammar-level integers with an optional leading minus.
- **A field-valued member list** has the same base type as the subject and refuses an exact reference repeated anywhere across the subject plus the members.
- **A member is a string literal, a number literal or a bracketed read:** a bare name or a keyword such as `True` there draws `MVK_UNEXPECTED_TOKEN`.
- **The subject is an entity, not a bracket.** A semantic-index subject is admitted and lowers the same way: `FieldValueIncludedInValueList(Items/ILabel For "a", "x", "y")` fires when the row keyed `a` holds `x` or `y`, its `NotIncluded` twin when that row holds another value, and neither fires when no row carries the key or its field is empty; a key the index field refuses draws `MVK_INDEX_VALUE_INVALID` and an unknown field `MVK_INVALID_ENTITY`.
- Stored and category access on one physical field are distinct references, as in [B.3](#b3-the-value-list-quantifiers--per-cell-three-way-classification-); category identity is retained, and no cross-declaration domain-containment or display-remapping gate is added.

**Gate order.** The subject is read first. Each field-valued member is a field-value read ([§10 §3](08-paths-and-references.md#3-the-asterisk-and-)), so its own gates run during the parse, ahead of the subject's group and kind gates and of the member list's duplicate and base-type gates; how those list gates order against the subject's group and kind gates is not stated.

| Stage | Witnesses |
|---|---|
| 1. the subject's read | an unstarred repeatable group draws `MVK_NO_WILDCARD`, a name resolving to nothing `MVK_INVALID_ENTITY`, a category subject over a String `MVK_NO_ENUMERATION` and a category subject over a group, `(Ledger -> Band, [Note])`, `MVK_NO_GROUPS_ALLOWED`, each ahead of the members |
| 2. each member's read gates, in parse order | a raw member draws `MVK_INVALID_RAW_TYPE` beside a Number member, after a repeated member and against a Boolean subject; a group member draws `MVK_NO_GROUPS_ALLOWED` against a String or a Boolean subject; a starred member `MVK_NO_WILDCARDS_ALLOWED`; a partially known Date member against a String subject `MVK_INVALID_DATE_TYPE` |
| 3. the subject's group gate | against field-valued members, a plain subject naming a fixed group, or the root, is refused `MVK_NO_GROUPS_ALLOWED` only after the members' reads: beside a raw member, `FieldValueIncludedInValueList(Ledger, [Note])` draws `MVK_INVALID_RAW_TYPE`. Against literal members nothing is read first, so the group gate answers at once: a fixed group and the root draw `MVK_NO_GROUPS_ALLOWED` and an unstarred repeatable group `MVK_NO_WILDCARD`, on the String and the Number literal form, and so does a bare name naming a fixed group on the String form |
| 4. the subject's kind gate, then its value validation | a partially known Date draws `MVK_ONLY_STRING_ENUM_NUMBER_ALLOWED` as a full Date does, against literals and against a field member; a raw String draws `MVK_INVALID_RAW_TYPE` |

> **Non-normative implementation note.** For validation, reuse the resolved value-list quantifiers: `Included → AtLeastOne`, `NotIncluded → NotAll`. Do not introduce Boolean negation or a second membership evaluator; those shortcuts lose the empty-subject and UNKNOWN-member asymmetries.

Sources: [inbound 2026-09-25f field-value read](../docs/sources/inbound-handbacks.md#inbound-2026-09-25f-field-value-read), [field-value read grid](../docs/sources/static-admission-and-class-probes.md#src-field-value-read-grid), [remaining read sites](../docs/sources/static-admission-and-class-probes.md#src-field-value-read-remaining-sites), [field-value read predictions](../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions), [K22 join, count and membership](../docs/sources/group-count-topology.md#src-k22-join-count-membership), [K22 static classes](../docs/sources/group-count-topology.md#src-k22-static-classes).

### B.5 Computation preconditions preserve reached errors and traversal order

**Static field-list reading resolves and checks computation binding for each authored operand before advancing to the next.** An unbound repeatable operand therefore preempts a later unresolved name, and reversing those operands reverses the reported class. Whole-list checks, such as repeated direct operands and mixed kinds, follow successful operand reading. The first failing operand read is reported whichever reading the list then takes, Number or String/Enumeration token: a later token-reading failure does not replace it.

**Computation preconditions use computation-phase reads:** a reached formally invalid operand poisons the computation rather than becoming validation's skipped or UNKNOWN operand.

- **`AtLeastOneFieldValueIncludedInValueList` and `NoFieldValueIncludedInValueList`** collect the field-valued members before scanning the subjects, and the subject scan stops on its deciding match. `AtLeastOne` with no present members returns not-true without reading the subjects; `No` still scans them.
- **`NotAllFieldValuesIncludedInValueList`** first searches for a present subject, then collects the members, then restarts the subject scan and stops at the first present value outside the member set. If the presence search finds none, it returns not-true without reading the members.
- **Scalar `FieldValueIncludedInValueList` and `FieldValueNotIncludedInValueList`** collect their members before reading the subject. Both return not-true for an empty subject, but neither inherits a plural presence search: an invalid member poisons even when the subject is empty, and an invalid subject poisons even when every member is empty. A present subject selects `Included` on a match and `NotIncluded` on no match. An empty Number member is absent, not zero.

**Filtered computation streams keep the iterator's one-kept-successor lookahead:** before consuming a selected subject, they search for its next selected successor. A failure in that search poisons before the pending subject can decide; after a deciding subject, filters beyond that prefetched successor stay unread. Member collection still exhausts its selected stream and reaches later invalid members. Excluded candidates contribute no target reads.

**Measured scope.** Measured across stored Number, String and Enumeration fields, scalar literals and field-valued members, and Number and String filtered stars, with a 13-case admission matrix separating missing names, unbound fields and groups, duplicate operands and mixed kinds beside admitted Number and String controls. Category-projected runtime behaviour, indexed and correlated compositions and generated-validation messages are unmeasured.

Sources: [membership read order](../docs/sources/domain-ingestion-probes.md#src-membership-read-order-k13), [computation membership grids](../docs/sources/computation-scheduling-probes.md#src-compositional-computation-guards).

### B.6 Table-backed Enumerations and `ValueNotConsistent`

**Table-backed (dynamic) Enumerations are outside this specification on every target:** no witness is known of a model supplying a table, or a dependent-column list, so their would-be semantics — a domain filtered by sibling field values, with omission polarity for a not-given subject — is not specified.

**One static gate belongs to the observable language.** `ValueNotConsistent(<subject> To <values>)` asks its subject gate first, and that gate demands a table-backed Enumeration, so it refuses every subject known:

| Subject | Class |
|---|---|
| an ordinary Enumeration, a String or a Number | `MVK_TABLE_ENUM_EXPECTED` |
| a group | `MVK_NO_GROUPS_ALLOWED` |
| a starred selector | `MVK_NO_WILDCARDS_ALLOWED` |
| an undeclared path | `MVK_INVALID_ENTITY` |

The subject demand answers before the family's arity and member-kind gates, so neither a wrong member count nor a non-Enumeration member is visible, and the subject's own kind never matters: every subject that is not a table-backed Enumeration, a group, a starred selector or an undeclared path draws `MVK_TABLE_ENUM_EXPECTED`, a Date, a Boolean and a raw String included. Measured against another operator on the same subject as the admitted control. A consumer that skips the whole family reports nothing where A12 refuses.

Sources: [inbound 2026-09-21 corrections](../docs/sources/inbound-handbacks.md#inbound-2026-09-21-corrections).

---

## Checklist for §7 + §8

- [ ] The formal check runs the raw-type gate, then under the full check only the technical length, charset, leading-blank and trailing-blank gates, then the declared format; a String or Enumeration's declared format runs line break on the raw text, CRLF→LF normalization, pattern or Enumeration domain, minimum, maximum, each with its own finding code and message key.
- [ ] String `Length` and min/max limits count UTF-16 code units after CRLF→LF evaluation ingestion; no length-bearing path counts code points or graphemes.
- [ ] Condition and declared-field patterns share Java compilation plus the character-level source-text blacklist; a condition-pattern failure draws `MVK_INVALID_PATTERN` and a declared-field one `MVK_PATTERN_INVALID`; condition operands keep their exact wrong-shape, wrong-type and missing-constant classes; evaluation is anchored, whole-value Java-Pattern semantics under the Groovy-dynamic anchor; target-language divergences stay explicit; a fired pattern check is always **VALUE**; an empty authored pattern fails when reached.
- [ ] `+` dispatches by operand kind ([§5 §4.1](04-numbers-and-decimals.md#41-arithmetic-operand-kinds)); a direct display-remapped Enumeration operand is refused, by immediate operand shape only; date-shaped literals are dates, not concatenable strings.
- [ ] Raw-type String values stay available to presence predicates and read as `X` in `FirstFilledValue`; every other value window is refused by its column W class; the sole strict whole-condition `Length` form is eliminated into metadata and never runs.
- [ ] `supportedCharacters`: absent/empty list selects the BMP default, an empty entry is malformed, accepted entries are bounded and surrogate-free, configured combined entries match atomically with the exact overlap restriction, and every successful match advances.
- [ ] A declared custom field type passes raw optional bounds, effective `1`/`999`, locale and stored-value mode to one registered-validator observation per relevant concrete cell, reused by every consumer, and preserves a rejection's project code and optional field-aware message; an unregistered validator under a full check aborts the whole call; the codec runs only on an opted-in conversion path.
- [ ] Enums compare **stored values**; direct-field comparability uses effective display remapping, treats identity labels as textless, and requires a consistent common-locale partial bijection between two display-bearing enums.
- [ ] `->` category read is **positional, many-to-one**; a category list's length equals the value count, and declaration notifications arrive in the six blocks.
- [ ] Multi-field value lists ask scope, base type, then kind (String, Enumeration, Number, Custom); only String fields (a Custom field included, unmeasured) and Enumeration fields take a literal list; Number has no multi-field literal form; Enumeration literals use the selected-domain union; exact references are unique across field-valued sides.
- [ ] Value-list quantifiers classify each cell three-way. `AtLeastOne` and `No` consume values before fields; `NotAll` searches for a present subject, then collects values, then restarts the subject scan, and that presence search is observable through an unread values-side filter; the size-selected route that omits it is equivalent only for filter-free member classification. A fields-side `No` match hides later UNKNOWN cells, and filter polarity follows the reached and witness-specific rules rather than one global marker.
- [ ] Under partial validation a starred entry's extent is the declared-slots predicate of [§12 §5.4](10-validation-and-polarity.md#54-the-extent-of-a-multi-cell-operand), consumed side-specifically.
- [ ] Scalar `Included` is singleton `AtLeastOne`, scalar `NotIncluded` is singleton `NotAll`, and neither fires on an empty or unavailable subject; an unavailable member makes `NotIncluded` UNKNOWN in validation and poisons in computation.
- [ ] `ValueNotConsistent` refuses every known subject at its table-Enumeration subject gate.
