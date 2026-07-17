# 06 — Strings, patterns, and enumerations (§7 + §8)

Two mostly-manageable areas with a few sharp edges: Unicode length counting, the enforced portable regex subset, enum comparability rules, and the three-way value-list quantifiers (whose `No`-vs-`NotAll` poison asymmetry is the one genuinely tricky part).

Empty behaviour (`== ""` never holds; `Length(empty) = 0`; patterns not evaluated on empty; value-list membership UNKNOWN on empty) is in [§2](03-empty-and-required.md).

---

## Part A — §7 Strings and patterns

- **`Length` and min/max-length checks count UTF-16 code units exactly.** There is no code-point folding or grapheme clustering in any length-bearing path. A decomposed combining sequence `e` + `U+0301` counts 2, and a supplementary-plane character would also count 2 code units, although realistic legal-character policies reject it first. Grapheme clustering appears only in legal-charset acceptance, never in a count.
- **`PatternMatched` / `PatternViolated`** evaluate the **whole** value (implicitly **anchored** — the pattern must match the entire string), use only the **regex subset portable across the code-generation target languages**, and can be a performance/security risk if written to backtrack (e.g. `(a+)+`). The portable subset is **enforced, not advisory**: a Java-valid lookbehind is rejected with `MVK_INVALID_PATTERN`, so a Java-side `Pattern.compile` success is a *necessary* condition only, never sufficient. A fired pattern comparison is always a **VALUE** error (there is no fillable branch); an empty string violates no pattern ([§2](03-empty-and-required.md)). Length and pattern consumers see the evaluation-normalized text: a permitted `"AB\r\nCD"` measures 5 UTF-16 code units and a whitespace-class pattern sees one `\n`, while the stored text remains unchanged ([§3](02-logic-and-formal-errors.md#b3-what-puts-a-cell-in-the-third-state)).
- **`+` is overloaded** — numeric **addition** between Number operands, string **concatenation** between strings. There is no general operand-dispatch rule beyond one pitfall: a string literal shaped like a date parses as a *date constant* and cannot be concatenated ([§6](05-dates-and-time.md)).

### A.1 Raw-type Strings (`noValueValidation`)

The String-only `noValueValidation` option declares a **raw type**. Its value remains in the document but is never interned for evaluation. Model validation closes every value window:

- comparisons, value lists, computation operands, coercions, and any other value operation are rejected with `MVK_INVALID_RAW_TYPE`;
- message interpolation of the value is rejected;
- `Length` is authorable only as the whole rule condition `Length(f) > c`, or the mirrored `c < Length(f)`, using strict GT/LT;
- every other `Length` shape, including computation preconditions, is rejected with `MVK_INVALID_LENGTH_OF_RAW_TYPE`.

The one legal `Length` shape is **not a runtime rule**. Code generation eliminates it in both strategies and lifts `(field, c)` into the generated meta-model's maximum-length metadata, so it never fires for either filled or empty values. Presence semantics over the same cell remain ordinary: `FieldFilled`, quantifiers, and counts can observe whether content exists without reading its value.

The JVM/JavaScript rule is UTF-16 code-unit length. a12-dmkits' [`AbsLengthDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/AbsLengthDiffTest.kt) differentially locks the BMP combining-sequence discriminator—decomposed `e` plus U+0301 counts as two rather than one grapheme—while supplementary-plane characters counting as two UTF-16 units is source-characterized and internally locked by Lean's [`StringLength` conformance cases](../A12Kernel/Conformance/StringLength.lean), not by retained kernel differential evidence. CRLF ingestion and raw-type closure are differentially locked by [`CrlfLengthNormalizationDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/CrlfLengthNormalizationDiffTest.kt) and [`NvvRawTypeDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/NvvRawTypeDiffTest.kt).

> **Lean modelling note.** Represent String length as UTF-16 code-unit count after the ingestion normalization described in [§3](02-logic-and-formal-errors.md#b3-what-puts-a-cell-in-the-third-state); do **not** use Unicode scalar count or grapheme clusters. For patterns, compile from a *restricted* pattern grammar (no lookbehind/lookahead, the portable subset) to a decidable matcher over the whole normalized string (anchored); pattern acceptance is a separate well-formedness check. The checked elaborator rejects every raw-type value window, while the one admitted strict `Length` declaration desugars to metadata and produces no core runtime rule. No additional runtime value state is needed because legal evaluation cannot read the raw value.

---

## Part B — §8 Enumerations

### B.1 Comparison is by stored value, and comparability depends on texts

- Rule conditions compare the **stored enumeration value**, not the displayed text: write `[Country] == "F"`, not `[Country] == "France"`.
- An enumeration that **defines localized texts** cannot be compared with a plain string, nor with an enumeration that has **no** texts; comparing two text-bearing enumerations also requires their values *and* texts to be mutually consistent.
- A plain string ↔ **texts-less** enum comparison **is** allowed — it is the *presence of display texts*, not the stored value, that governs comparability.

### B.2 Categories via `->`

Enumeration values can carry named **category** attributes, read with the `->` operator:

```
[Country -> AdministrationArea] != "EU"
```

The category mapping is **positional** (`values[i]` categorizes enum value *i*) and **many-to-one** — the comparison fires for *every* value sharing that category value. An empty enum rides the not-evaluated track, category hop or not.

> **Lean modelling note.** Give an enum type two parallel vectors — `values : Array String` and (optionally) `texts`, plus a category map `categories : String → Array String` — and derive comparability as a *typing rule* over `(hasTexts?, otherOperandKind)`: `textsBearing × plainString → ill-typed`; `textsLess × plainString → ok`; etc. Evaluation compares stored tokens; `->` is a lookup `value → category[value]` that then compares as a string. Positional many-to-one falls out of the vector representation directly.

### B.3 The value-list quantifiers — per-cell three-way classification ⚠

`AtLeastOne` / `No` / `NotAll` `…FieldValue(s)IncludedInValueList(f1, f2 In v1, v2, …)` expand **both** sides per cell (a starred entry contributes one cell per instantiated row) and classify each cell by the three-way state (filled / empty / not-check-relevant = UNKNOWN, [§3](02-logic-and-formal-errors.md)):

- **`AtLeastOne`** fires iff **some filled cell's value is in the set**. Empty and UNKNOWN cells and members are skipped outright; an empty value *set* → no fire. Fired polarity **VALUE**.
- **`No`** fires iff **no filled cell's value is in the set** — *including when nothing is filled at all* (the sole member that can fire on emptiness). An **UNKNOWN fields-cell OR an UNKNOWN values member poisons it** (no fire). Fired polarity **OMISSION** on any empty fields-cell, un-instantiated declared tail, or empty values member — else VALUE.
- **`NotAll`** needs a filled fields-cell and fires iff **some filled cell's value is *not* in the set**. An UNKNOWN **values** member poisons; an UNKNOWN **fields**-cell is merely skipped — this is the **`No`-vs-`NotAll` asymmetry**. OMISSION only on the values side's account.
- An empty **values member** contributes nothing to the set (never a substituted `0`) but flags a fired `No`/`NotAll` as **OMISSION**. A `Having` filter is accepted on either side, drops rows **before** the per-cell classification, and escalates a fired result to **OMISSION unconditionally** ([§12](10-validation-and-polarity.md)).

> **Lean modelling note.** Model each quantifier as a fold over phase-appropriate `CellObservation`s (or a smaller operator-specific classification derived from them) and return `Verdict`, retaining `unknown` explicitly. The asymmetry is the crux: `No` becomes unknown on an UNKNOWN in *either* position, while `NotAll` does so only on an UNKNOWN *member*. Write the two folds separately, prove their actual clauses, and property-test them on shared inputs—they look like duals but are not.

---

## Checklist for §7 + §8

- [ ] String `Length` and min/max limits count UTF-16 code units after CRLF→LF evaluation ingestion; no length-bearing path counts code points or graphemes.
- [ ] Patterns are **anchored/whole-value**, restricted to the **portable subset** (reject lookbehind etc. with `MVK_INVALID_PATTERN`); a fired pattern check is always **VALUE**.
- [ ] Raw-type String values remain available to presence predicates but every value window is rejected; the sole strict whole-condition `Length` form is eliminated into metadata and never runs.
- [ ] `+` dispatches numeric-add vs string-concat by operand kind; date-shaped literals are dates, not concatenable strings.
- [ ] Enums compared by **stored value**; comparability governed by **texts presence** (text-bearing ✗ plain string; texts-less ✓ plain string).
- [ ] `->` category read is **positional, many-to-one**.
- [ ] Value-list quantifiers classify each cell three-way; `No` poisons on UNKNOWN cell **or** member, `NotAll` only on UNKNOWN **member**; `Having` escalates a fire to OMISSION.
