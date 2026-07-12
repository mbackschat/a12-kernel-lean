# 06 — Strings, patterns, and enumerations (§7 + §8)

Two mostly-manageable areas with a few sharp edges: Unicode length counting, the enforced portable regex subset, enum comparability rules, and the three-way value-list quantifiers (whose `No`-vs-`NotAll` poison asymmetry is the one genuinely tricky part).

Empty behaviour (`== ""` never holds; `Length(empty) = 0`; patterns not evaluated on empty; value-list membership UNKNOWN on empty) is in [§2](03-empty-and-required.md).

---

## Part A — §7 Strings and patterns

- **Length counts Unicode combining sequences as multiple characters.** One visible glyph (a base letter + combining marks) can occupy several characters of a length limit. So `Length` and the min/max-length formal checks operate on **code units/combining pieces**, not grapheme clusters.
- **`PatternMatched` / `PatternViolated`** evaluate the **whole** value (implicitly **anchored** — the pattern must match the entire string), use only the **regex subset portable across the code-generation target languages**, and can be a performance/security risk if written to backtrack (e.g. `(a+)+`). The portable subset is **enforced, not advisory**: a Java-valid lookbehind is rejected with `MVK_INVALID_PATTERN`, so a Java-side `Pattern.compile` success is a *necessary* condition only, never sufficient. A fired pattern comparison is always a **VALUE** error (there is no fillable branch); an empty string violates no pattern ([§2](03-empty-and-required.md)).
- **`+` is overloaded** — numeric **addition** between Number operands, string **concatenation** between strings. There is no general operand-dispatch rule beyond one pitfall: a string literal shaped like a date parses as a *date constant* and cannot be concatenated ([§6](05-dates-and-time.md)).

> **Lean modelling note.** For length, model a string as its sequence of code units and define length as the count the engine uses (combining-sequence-inclusive) — do **not** reach for a grapheme-cluster count, which would disagree. For patterns, compile from a *restricted* pattern grammar (no lookbehind/lookahead, the portable subset) to a decidable matcher over the whole string (anchored); the acceptance of the *pattern itself* is a separate well-formedness check that must reject the non-portable constructs, mirroring `MVK_INVALID_PATTERN`.

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

> **Lean modelling note.** Model each quantifier as a fold over a list of `CellState` cells against a set of `CellState` members, returning a `firedAsValue | firedAsOmission | notFired` outcome (the three-way result of [§12](10-validation-and-polarity.md)). The asymmetry is the crux: `No` poisons on an UNKNOWN in *either* position, `NotAll` poisons only on an UNKNOWN *member*. Write the two folds separately and property-test them against each other on shared inputs — they *look* like duals but are not, and conflating them is the predictable bug.

---

## Checklist for §7 + §8

- [ ] String length counts combining sequences (not graphemes); length limits use the same count.
- [ ] Patterns are **anchored/whole-value**, restricted to the **portable subset** (reject lookbehind etc. with `MVK_INVALID_PATTERN`); a fired pattern check is always **VALUE**.
- [ ] `+` dispatches numeric-add vs string-concat by operand kind; date-shaped literals are dates, not concatenable strings.
- [ ] Enums compared by **stored value**; comparability governed by **texts presence** (text-bearing ✗ plain string; texts-less ✓ plain string).
- [ ] `->` category read is **positional, many-to-one**.
- [ ] Value-list quantifiers classify each cell three-way; `No` poisons on UNKNOWN cell **or** member, `NotAll` only on UNKNOWN **member**; `Having` escalates a fire to OMISSION.
