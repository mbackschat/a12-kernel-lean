# 06 — Strings, patterns, and enumerations (§7 + §8)

Two mostly-manageable areas with a few sharp edges: Unicode length counting, legal-character definitions, custom field validation, Java-Pattern admission and execution, enum comparability rules, and the three-way value-list quantifiers (whose `No`-vs-`NotAll` poison asymmetry is the one genuinely tricky part).

Empty behaviour (`== ""` never holds; `Length(empty) = 0`; patterns are not evaluated on empty) is in [§2](03-empty-and-required.md). Scalar `Included`/`NotIncluded` semantics are stated in [§B.4](#b4-scalar-membership-is-a-singleton-specialization-not-boolean-negation-), and the distinct multi-cell empty and UNKNOWN rules are stated in [§B.3](#b3-the-value-list-quantifiers--per-cell-three-way-classification-).

---

## Part A — §7 Strings and patterns

- **`Length` and min/max-length checks count UTF-16 code units exactly.** There is no code-point folding or grapheme clustering in any length-bearing path. A decomposed combining sequence `e` + `U+0301` counts 2, and a supplementary-plane character would also count 2 code units, although realistic legal-character policies reject it first. Grapheme clustering appears only in legal-charset acceptance, never in a count.
- **`PatternMatched` / `PatternViolated`** evaluate the **whole** value (implicitly **anchored** — the pattern must match the entire string) with Java `Pattern` semantics under the Groovy-dynamic observation anchor. A fired pattern comparison is always a **VALUE** error (there is no fillable branch); an empty string violates no pattern ([§2](03-empty-and-required.md)). Length and pattern consumers see the evaluation-normalized text: a permitted `"AB\r\nCD"` measures 5 UTF-16 code units and a whitespace-class pattern sees one `\n`, while the stored text remains unchanged ([§3](02-logic-and-formal-errors.md#b3-what-puts-a-cell-in-the-third-state)). Patterns can still be a performance/security risk if written to backtrack, for example `(a+)+`.
- **`+` is overloaded** — numeric **addition** between Number operands, string **concatenation** between strings. There is no general operand-dispatch rule beyond one pitfall: a string literal shaped like a date parses as a *date constant* and cannot be concatenated ([§6](05-dates-and-time.md)).

### Pattern admission and execution

Condition-literal patterns (`PatternMatched` / `PatternViolated`) and declared STRING or predefined-type patterns have the same observed model-legality contract: the source must compile as a Java `Pattern` and then pass kernel admission. The source-visible `PatternUtils.isPatternValid` check contains the finite blacklist below, but that expression is not an exhaustive account of total admission. A direct typed/full-kernel model additionally rejects uppercase `\P{L}` with `MVK_INVALID_PATTERN` even though uppercase `P` is absent from the displayed expression. A condition-literal failure is rejected with `MVK_INVALID_PATTERN`; this clause does not infer the same outward diagnostic surface for every declared-pattern API or an undiscovered general grammar behind the additional exclusion.

```text
[?+}*]\+                 possessive quantifiers
(?<...                   every such prefix, including lookbehind and named capture
(?>...)                   atomic/independent groups
\A \G \Z \z \a \e \p \Q \E
an unescaped [ nested after an earlier unescaped [ before its closing ]
```

Ordinary positive and negative lookahead (`(?=...)` / `(?!...)`) are not categorically blacklisted. Nor does passing kernel admission imply JavaScript portability: known legal separators include inline flag forms, `\R` / `\h`, Unicode `\s`, dot/code-point differences, unmatched backreferences, non-nested class intersections, `\x{…}`, `\N{…}`, `\X`, and `\b{g}`. Generated static-Java agrees with the normative Java runtime on the exercised cases. The kernel TypeScript target instead wraps the raw source as `new RegExp("^(?:" + p + ")$")`; any resulting difference is a characterized strategy split and is never adopted over the Groovy-dynamic result.

### A.1 Raw-type Strings (`noValueValidation`)

The String-only `noValueValidation` option declares a **raw type**. Its value remains in the document but is never interned for evaluation. Model validation closes every value window:

- comparisons, value lists, computation operands, coercions, and any other value operation are rejected with `MVK_INVALID_RAW_TYPE`;
- message interpolation of the value is rejected;
- `Length` is authorable only as the whole rule condition `Length(f) > c`, or the mirrored `c < Length(f)`, using strict GT/LT;
- every other `Length` shape, including computation preconditions, is rejected with `MVK_INVALID_LENGTH_OF_RAW_TYPE`.

The one legal `Length` shape is **not a runtime rule**. Code generation eliminates it in both strategies and lifts `(field, c)` into the generated meta-model's maximum-length metadata, so it never fires for either filled or empty values. Presence semantics over the same cell remain ordinary: `FieldFilled`, quantifiers, and counts can observe whether content exists without reading its value.

The JVM/JavaScript rule is UTF-16 code-unit length. a12-dmkits' [`AbsLengthDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/AbsLengthDiffTest.kt) differentially locks the BMP combining-sequence discriminator—decomposed `e` plus U+0301 counts as two rather than one grapheme—while supplementary-plane characters counting as two UTF-16 units is source-characterized and internally locked by Lean's [`StringLength` conformance cases](../A12Kernel/Conformance/StringLength.lean), not by retained kernel differential evidence. CRLF ingestion and raw-type closure are differentially locked by [`CrlfLengthNormalizationDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/CrlfLengthNormalizationDiffTest.kt) and [`NvvRawTypeDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/NvvRawTypeDiffTest.kt).

> **Lean modelling note.** Represent String length as UTF-16 code-unit count after the ingestion normalization described in [§3](02-logic-and-formal-errors.md#b3-what-puts-a-cell-in-the-third-state); do **not** use Unicode scalar count or grapheme clusters. Do not turn the bounded admission evidence into an invented portable grammar: a faithful pattern capsule must separate Java compilation plus kernel admission—the source-visible `PatternUtils` blacklist and the directly observed uppercase-`\P` exclusion—from whole-value Java-Pattern execution and record target splits explicitly, or fail closed outside its declared fragment. The checked elaborator rejects every raw-type value window, while the one admitted strict `Length` declaration desugars to metadata and produces no core runtime rule. No additional runtime value state is needed because legal evaluation cannot read the raw value.

### A.2 Legal charset definitions and atomic matching

The model's `supportedCharacters` is a cross-kind baseline for stored/input values under the full formal check. Computed-result target checking uses the reduced basic check and deliberately omits this charset and the leading/trailing-blank baseline ([§11](09-computations.md#4-the-stored-form--a-computed-value-lands-as-a-string-in-the-targets-shape)).

An absent definition or an empty list selects the default non-surrogate Basic Multilingual Plane policy. This is different from a list containing an empty string: `[]` is the default, while `[""]` is a malformed definition. A nonempty entry is legal only in one of these forms:

- one non-surrogate BMP UTF-16 unit, defining a singleton;
- exactly three UTF-16 units `X-Y`, where `X` and `Y` are non-surrogate BMP endpoints and `X ≤ Y`, defining an inclusive range; or
- a surrogate-free combined atomic entry of two or three UTF-16 units whose Unicode grapheme-cluster decomposition is shorter than its UTF-16 representation, so the entry contains a combining sequence. The entry may contain more than one cluster, but matching consumes the whole configured entry atomically.

An empty entry, a surrogate-bearing entry, a reversed range, a combined entry longer than three UTF-16 units, or a plain multi-character sequence such as `ab` with no combined grapheme is malformed. Shared prefixes are otherwise legal: configured `e`+combining-acute and `e`+combining-grave may coexist, and a complete atomic entry may be a terminal prefix of a longer one. The pinned ambiguous-overlap rejection is narrower than “no overlap”: for a combined entry whose grapheme-cluster decomposition is `p₁ … pₙ · s` with at least one prefix cluster, reject it only when every prefix cluster is independently representable by a configured singleton, range, or atomic entry and the final cluster `s` is a proper, different-length UTF-16 prefix of another configured atomic entry. This is why the focused `q`+combining-acute+`r` entry is rejected when `q`+combining-acute and `r`+combining-grave are also configured, without making the legal shared-prefix cases illegal.

Runtime matching proceeds left-to-right. At each input position, walk the configured atomic-entry trie and consume the longest complete terminal entry selected by that bounded walk. If no complete atomic entry matches, test exactly the leading code point against singleton/range membership and consume it only when admitted; otherwise the value fails the charset formal check. Every successful step advances because empty entries are forbidden and every accepted atomic entry is bounded. A configured combined entry admits only its complete sequence: its base, combining mark, reversed sequence, suffix, or repeated component is not independently legal unless another singleton, range, or atomic entry admits it.

Charset matching does not alter length semantics. `Length` and min/max checks continue to count UTF-16 code units, never grapheme clusters.

a12-dmkits' [`SupportedCharactersDefinitionDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/SupportedCharactersDefinitionDiffTest.kt) and [`SupportedCharactersGraphemeDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/SupportedCharactersGraphemeDiffTest.kt) lock the definition discriminators and atomic matching against both kernel strategies; [`LegalCharsetDefinitionTest`](../../a12-rulekit/interpreter/src/commonTest/kotlin/io/github/mbackschat/a12/dm/interpreter/LegalCharsetDefinitionTest.kt) and [`LegalCharsetGraphemeTest`](../../a12-rulekit/interpreter/src/commonTest/kotlin/io/github/mbackschat/a12/dm/interpreter/LegalCharsetGraphemeTest.kt) provide the peer portable controls.

### A.3 Custom field-type validation

A declared `CustomFieldType(name, minLength?, maxLength?)` delegates its value-specific acceptance decision completely to the named registered validator. The raw declaration preserves whether each length bound was authored; the bounds are callback context, not generic predefined-String minimum/maximum checks. The callback receives an effective minimum of the authored value or `1`, an effective maximum of the authored value or `999`, the effective locale, and the stored/display-value mode. The ordinary stored-document formal-check path supplies `isDisplayValue = false`; no behavior is claimed here for the unevidenced display-value mode.

For each relevant concrete-valued cell, the semantics obtains one custom-validation observation from a named pure, total oracle and reuses it for every consumer: automatic formal-message emission, authored-rule and candidate suppression, computation poison, and `RepetitionNotUnique` key filtering. An empty or nonrelevant cell is excluded before the oracle is sampled. The observation is either accepted or a project rejection carrying a required project error code and an optional message template. The project code is preserved verbatim as both the formal error code and the suppression cause; it does not collapse to a generic constant.

In a supplied rejection template, every literal token naming the field as `$<fieldName>$` is replaced with that field's localized label under the established [label-resolution rule](11-messages-and-custom.md#part-a--13-error-message-interpolation); all other text remains unchanged. This implicit declaration-driven formal check is distinct from the explicit `Valid(field, "Name")` rule predicate, which invokes the registered validator as an authored condition, and custom field validation is distinct from [`CustomCondition`](11-messages-and-custom.md#part-b--14-customcondition--the-escape-hatch).

The checked Lean account requires every referenced validator name to exist in `World`; absence is a well-formedness/elaboration failure. Kernel 30.8.1 does not reject the missing registration while parsing the model: if a relevant concrete cell reaches an unregistered validator, the validation call fails loudly. It is neither accepted nor converted into a generic formal rejection. The separate declarative predefined-type fallback continues to use the fixed `customFieldTypeInvalid` code; that fallback cannot replace or reinterpret the registered-oracle result.

a12-dmkits' [`CustomFieldTypeContextDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/CustomFieldTypeContextDiffTest.kt), [`CustomFieldTypeRejectionCodeDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/CustomFieldTypeRejectionCodeDiffTest.kt), and [`CustomFieldTypeMessageDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/CustomFieldTypeMessageDiffTest.kt) lock the registered path against both kernel strategies; [`CustomFieldTypeContextCacheTest`](../../a12-rulekit/interpreter/src/commonTest/kotlin/io/github/mbackschat/a12/dm/interpreter/CustomFieldTypeContextCacheTest.kt) checks the peer's one-observation consumer boundary.

---

## Part B — §8 Enumerations

### B.1 Comparison is by stored value, and direct-field comparability depends on effective display remapping

- Rule conditions compare the **stored enumeration value**, not the displayed text: write `[Country] == "F"`, not `[Country] == "France"`.
- An ordinary enumeration is **effectively display-bearing** only when at least one localized display differs from its stored value. No authored labels and labels that all repeat their stored values are both effectively textless for this rule.
- A direct plain-String field can be compared with an effectively textless enumeration field, but not with an effectively display-bearing one. Likewise, two enumeration fields are rejected when exactly one is effectively display-bearing.
- Two effectively display-bearing enumeration fields need not have identical declarations. For every locale common to both, a shared stored value must have the same display and a shared display must denote the same stored value. Disjoint mappings and non-overlapping locale sets are accepted.
- This direct-field gate is shared by `==` and `!=`. A String literal that is a valid stored or selected-category token and an already-checked category access follow their separate domain and projection rules rather than this field-to-field display gate.
- If either Enumeration operand is an already-checked category access, the display-remapping gate is bypassed. Its projected category token can be compared by `==`/`!=` with a direct String value, another category token, or a plain Enumeration's stored token.

### B.2 Categories via `->`

Enumeration values can carry named **category** attributes, read with the `->` operator:

```
[Country -> AdministrationArea] != "EU"
```

The category mapping is **positional** (`values[i]` categorizes enum value *i*) and **many-to-one** — the comparison fires for *every* value sharing that category value. An empty enum rides the not-evaluated track, category hop or not.

> **Lean modelling note.** Keep static comparability separate from runtime projection. For a legal ordinary enum declaration, retain locale-tagged `(stored, display)` facts, derive effective display-bearing status from `stored ≠ display`, and check the common-locale relation in both directions. Runtime evaluation compares stored tokens; `->` is a positional lookup over parallel stored/category vectors, so many-to-one mapping falls out directly.

### B.3 The value-list quantifiers — per-cell three-way classification ⚠

`AtLeastOne` / `No` / `NotAll` `…FieldValue(s)IncludedInValueList(f1, f2 In v1, v2, …)` expand **both** sides per cell (a starred entry contributes one cell per instantiated row) and classify each cell by the three-way state (filled / empty / not-check-relevant = UNKNOWN, [§3](02-logic-and-formal-errors.md)):

- The multi-field family admits only String, Enumeration, or Number fields. A literal right side is available for String and Enumeration fields: plain String literals are unrestricted decoded String tokens, while Enumeration literals follow the selected stored/category union rule below. A multi-field Number form has no literal-list shape and requires a nonempty field-valued right side. Field-valued forms require the same base type on both sides.
- When the values side is a literal String list and the fields side contains ordinary Enumerations or category accesses, static admission uses the **union** of the selected domains: every literal must be a stored token of at least one direct Enumeration operand or a category token of at least one category operand, but need not belong to every listed declaration. The fields side is nonempty, preserves authored order, and rejects an exact repeated reference; direct stored access and named category access on the same physical field are distinct references.
- When the values side is another field list, both sides are nonempty and preserve authored order, and no exact reference may occur twice across the combined lists. Enumeration declarations need not share or contain each other's stored/category domains; runtime compares the selected projected tokens actually present in the two sides.
- A category projection inherits the underlying Enumeration cell's three-way classification before projecting its token: empty stays empty, a formally unavailable or invalid stored value stays UNKNOWN, and only a filled valid stored value contributes its possibly many-to-one category token. Consequently, an empty Enumeration reached through a category hop makes a fired `No` OMISSION and leaves `NotAll` non-firing; the hop never turns the empty cell into a present literal-like value.
- **`AtLeastOne`** fires iff **some filled cell's value is in the set**. Empty and UNKNOWN cells and members are skipped outright; an empty value *set* → no fire. Fired polarity **VALUE**.
- **`No`** fires iff **no filled cell's value is in the set** — *including when nothing is filled at all* (the sole member that can fire on emptiness). An **UNKNOWN fields-cell OR an UNKNOWN values member poisons it** (no fire). Fired polarity **OMISSION** on any empty fields-cell, un-instantiated declared tail, or empty values member — else VALUE.
- **`NotAll`** needs a filled fields-cell and fires iff **some filled cell's value is *not* in the set**. An UNKNOWN **values** member poisons; an UNKNOWN **fields**-cell is merely skipped — this is the **`No`-vs-`NotAll` asymmetry**. OMISSION only on the values side's account.
- An empty **values member** contributes nothing to the set (never a substituted `0`) but flags a fired `No`/`NotAll` as **OMISSION**. A `Having` filter is accepted on either side, drops rows **before** the per-cell classification, and escalates a fired result to **OMISSION unconditionally** ([§12](10-validation-and-polarity.md)).

> **Lean modelling note.** Model each quantifier as a fold over phase-appropriate `CellObservation`s (or a smaller operator-specific classification derived from them) and return `Verdict`, retaining `unknown` explicitly. The asymmetry is the crux: `No` becomes unknown on an UNKNOWN in *either* position, while `NotAll` does so only on an UNKNOWN *member*. Write the two folds separately, prove their actual clauses, and property-test them on shared inputs—they look like duals but are not.

### B.4 Scalar membership is a singleton specialization, not Boolean negation ⚠

`FieldValueIncludedInValueList(subject, members…)` lowers to one-subject `AtLeastOne`; `FieldValueNotIncludedInValueList(subject, members…)` lowers to one-subject `NotAll`, never to empty-firing `No`. An empty or formally unavailable subject therefore makes **both** scalar forms non-firing. With a present subject, `Included` fires **VALUE** iff at least one present member equals it, while `NotIncluded` fires iff no present member equals it. An empty field-valued member contributes no atom; if `NotIncluded` otherwise fires, that missing member makes the fire **OMISSION**. A formally unavailable member is skipped by `Included` but poisons `NotIncluded`. A fire against an all-literal member list is **VALUE**.

The subject and member list admit only the String, Enumeration, and Number families, and the member list is nonempty. Literal members must match the subject family: String literals are unrestricted decoded strings, Enumeration literals must belong to the selected stored or category projection's domain, and Number literals are grammar-level integers with an optional leading minus. A field-valued member list is nonempty, has the same base type as the subject, and rejects an exact reference repeated anywhere across the subject plus members. Enumeration stored access and named category access on one physical field are distinct references; category identity is retained, and no cross-declaration domain-containment or display-remapping gate is added.

Runtime equality follows the family's ordinary value boundary: normalized evaluated text for String, the selected stored/category token for Enumeration, and numeric equality after the ordinary scale-19 normalization for Number. Empty numeric member fields contribute no zero atom.

> **Lean modelling note.** Reuse the resolved value-list quantifiers: `Included → AtLeastOne`, `NotIncluded → NotAll`. Do not introduce Boolean negation or a second membership evaluator; those shortcuts lose the empty-subject and UNKNOWN-member asymmetries.

---

## Checklist for §7 + §8

- [ ] String `Length` and min/max limits count UTF-16 code units after CRLF→LF evaluation ingestion; no length-bearing path counts code points or graphemes.
- [ ] Condition and declared-field patterns share Java compilation plus kernel admission: the source-visible `PatternUtils` blacklist and the directly observed uppercase-`\P` exclusion; a condition-pattern failure draws `MVK_INVALID_PATTERN`; evaluation is anchored/whole-value Java-Pattern semantics under the Groovy-dynamic anchor; target-language divergences remain explicit; a fired pattern check is always **VALUE**.
- [ ] Raw-type String values remain available to presence predicates but every value window is rejected; the sole strict whole-condition `Length` form is eliminated into metadata and never runs.
- [ ] `supportedCharacters`: absent/empty list selects the BMP default, an empty entry is malformed, accepted entries are bounded and surrogate-free, configured combined entries match atomically with the exact overlap restriction, and every successful match advances.
- [ ] A declared custom field type preserves raw optional bounds, supplies effective `1`/`999`, locale, and stored-value mode to one pure registered-validator observation per relevant concrete cell, and preserves a rejection's project code and optional field-aware message across all consumers.
- [ ] `+` dispatches numeric-add vs string-concat by operand kind; date-shaped literals are dates, not concatenable strings.
- [ ] Enums compare **stored values**; direct-field comparability uses effective display remapping, treats identity labels as textless, and requires a consistent common-locale partial bijection between two display-bearing enums.
- [ ] `->` category read is **positional, many-to-one**.
- [ ] Multi-field value lists admit only String/Enumeration literals or same-base field-valued sides; Number has no multi-field literal form; Enumeration literals use the selected-domain union; exact references are unique across field-valued sides.
- [ ] Value-list quantifiers classify each cell three-way; `No` poisons on UNKNOWN cell **or** member, `NotAll` only on UNKNOWN **member**; `Having` escalates a fire to OMISSION. Scalar `Included` is singleton `AtLeastOne`, scalar `NotIncluded` is singleton `NotAll`, and neither fires on an empty or unavailable subject.
