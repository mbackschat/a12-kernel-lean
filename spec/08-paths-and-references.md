# 08 — Paths and references (§10)

How a condition names a field. Mostly mechanical, with two things that matter for a faithful reimplementation: the **two-tier bare-name resolution order** (declaring group, then flag-gated model-wide uniqueness) and the fact that **rows are addressed by semantic key, never by position**.

Path resolution reads a cell *relative to the current repetition context* ([`01-data-model.md §2.1`](01-data-model.md#21-repetition-contexts-the-iteration-environment)); this file is about how a path string selects that cell.

---

## 1. Absolute, relative, and short-name references

- **Keyword-named fields must be quoted.** A field or group named like a keyword (`And`, `Date`, `Today`, …) is single-quoted in a path: `FieldFilled(Order/'Date')`.
- **`RuleGroup`** references the rule's own containing group as an entity: `GroupFilled(RuleGroup)` validates and **counts as referencing the error field** ([§9](07-repetition-and-iteration.md)); a `*` on it is rejected.
- Paths are **absolute** (`/Order/Quantity`) or **relative** (`../Other`). Relative paths within a rule's group are shorter and survive the group being moved.
- **The one combination that *requires* absolute:** a relative `..` up-navigation may **not** be combined with `*` (`MVK_INVALID_WILDCARD_REL` — "use the absolute path notation"). So reaching **upward *and* across all repetitions** must be written absolutely (e.g. `/A*/F`).
- A field may be referenced by a **bare short name** (`[Quantity]`). Direct lookup under the declaring group is always attempted; the model-wide fallback requires `fieldRefByShortNameAllowed`, whose kernel default is off.

---

## 2. Bare-name resolution order ⚠

A bare segment resolves in exactly two tiers — **declaring-group-first, then (flag-gated) model-wide unique field lookup:**

1. Look **directly under the rule's declaring group**.
2. Only on a miss, **and** for a relative reference with `fieldRefByShortNameAllowed` on, run a **model-wide unique field short-name lookup over fields only**:
   - more than one match ⇒ `MVK_FIELDNAME_NOT_UNIQUE` (**never a silent pick**);
   - zero matches ⇒ falls through to `MVK_INVALID_ENTITY`.
   The serialized condition **retains** the short name (resolution is not rewritten into a path).

There is **no implicit ancestor walk**. A field in an ancestor group is reachable only through explicit `../` navigation or, when its short name is model-wide unique, through the flag-gated fallback. The earlier observation that `[Tier]` from `/Subscription/Addons` bound an ancestor field was the fallback firing in a draft with the flag enabled; with the flag off, the same reference is rejected as `MVK_INVALID_ENTITY`.

The **named-ancestor** form remains separate: in a `..Name/rest` path the up-count comes **only** from the `..` tokens; the trailing `Name` merely *names* (and validates) the ancestor landed on — a matching `..Name/rest` resolves exactly like `../rest`.

The two-tier mechanism and both flag arms are locked in a12-dmkits' [`ShortNameRefDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/ShortNameRefDiffTest.kt) and [`PathLawsTest`](../../a12-rulekit/src/test/java/io/github/mbackschat/a12/dm/rulekit/validate/laws/PathLawsTest.java) (IF119).

> **Lean modelling note.** Resolution is a scoped name lookup with two tiers: (1) declaring group, (2) flag-gated model-wide unique field short name. Implement as `resolve : Path → DeclaringGroup → Model → Except ResolveError FieldRef`, returning a *distinct error* for the not-unique case (never a silent first-match). Do not add an implicit ancestor tier; parent lookup requires explicit `..`. The `..Name` name is a *validation label*, not an extra hop; compute the target purely from the `..` count.

---

## 3. The asterisk and `$`

- The **asterisk `*` flattens** a repeatable group into the list of its rows. **If an outer repeatable group uses `*`, every repeatable group below it in the path must also use `*`** (you cannot flatten an outer level while pinning an inner one).
- The **`$`** operator switches resolution to the complete captured outer repetition environment. The marked reference's resolved group/path selects the corresponding level's coordinate, so parent and nested-descendant `$` references may resolve through different row coordinates; correspondingly, `CurrentRepetition` over those paths may yield different indices. `$` may be used **only inside a filter condition**, and not every reference in the filter may be `$`-marked ([§9](07-repetition-and-iteration.md)).

(How a star *binds* the enclosing indices — the anchor rules — is [§9 part 4](07-repetition-and-iteration.md#4-where-a-star-binds--the-anchor-rules-); this section is only about the *path syntax* constraints.)

---

## 4. Rows are addressed by semantic key, never by position ⚠

The language has **no positional row addressing** — no `[Field At n]`, no neighbour offset.

- **`CurrentRepetition(G)`** *yields* an index to **compare** (or `$`-correlate), never one to **select** with. `CurrentRepetition(G) == n` **cannot stand alone**; it must be combined with a condition ensuring the repetition is filled.
- The **only row-selection form** is the **semantic index** `[Field For key]` (equivalently `Group For "value"`), which addresses a row by an **index-field value**.

The semantic index is **unsupported** in several combinations: multiple repetition layers, several index fields, under an asterisk, and with certain predicates.

Index-key identity belongs to the declared index field. For a **Number** index field, both each admitted stored key and the requested literal or field-valued key are normalized numerically before lookup, so decimal spellings such as `5` and `5.00` select the same row. For every non-Number index field, lookup uses exact internally stored text instead; a String key that visibly resembles a Number is not numerically normalized. Empty and formally invalid index keys do not become selectable entries, and duplicate participants are unavailable rather than resolved by row order.

### 4.1 What a semantic-index read yields

- A **matched, filled cell** reads its value.
- **No matching row** *and* a **matched-but-empty** cell **both read as the kind's empty value** ([§2](03-empty-and-required.md)) — a number reads the fillable `0` (so `[X For "k"] == 0` fires and types OMISSION), a string/date reads NOT-GIVEN. Crucially, a no-match is **empty, never "unknown"**.
- As a **presence** operand, an absent row is judged like an empty cell (**FALSE**) — `FieldNotFilled(X For "k")` **fires** when no row carries the key.
- A **malformed matched cell**, or a **formally-invalid key field**, reads **UNKNOWN**.

### 4.2 Per-lookup (validation) vs per-column (compute)

- **Validation-side** indexed reads are judged **per lookup**: a malformed key cell *elsewhere* in the column does **not** suppress a clean match; but an *unresolvable no-match* over a column that contains **any** not-check-relevant cell **suppresses** the referencing rule.
- **Compute-side** is **stricter — per column**: any invalid cell in the index column clears every reading computation ([§11](09-computations.md)).

> **Lean modelling note.** Make indexed lookup phase-aware and return a `CellObservation`, with **no match returning `empty`** rather than `unknown` or `poison`. This is the load-bearing difference from “missing ⇒ invalid,” and it is why `[X For "k"] == 0` and `FieldNotFilled(X For "k")` fire on absence. Keep the validation-per-lookup versus computation-per-column strictness as an explicit lookup policy: validation checks the selected cell plus the documented no-match invalid-column guard, while computation can poison from the index column. Keep `CurrentRepetition` as a value-producing operand conceptually shaped as `ResolvedRepeatableLevel → Env → Option RowIndex`: `$` chooses the captured outer `Env`, then the resolved level chooses its coordinate. It can only be compared; omit any positional-select constructor from the AST, and fail closed on a missing or ambiguous level binding.

---

## Checklist for §10

- [ ] Keyword-named segments quoted; `RuleGroup` = the rule's group and counts as an error-field reference; no `*` on it.
- [ ] `..` + `*` together is rejected (`MVK_INVALID_WILDCARD_REL`) — force absolute.
- [ ] Bare-name resolution: declaring group → flag-gated model-wide unique field lookup (distinct not-unique error, never a silent pick), with no implicit ancestor walk; `..Name` name is a validation label only.
- [ ] `*` flatten requires every lower repeatable level to also `*`.
- [ ] **No positional row addressing**; `CurrentRepetition` compares only and reads the named level from the selected candidate/outer environment; semantic index `[Field For key]` is the sole row selector, with its unsupported-combination restrictions.
- [ ] Semantic-index no-match = **empty** (not unknown); presence on absence = FALSE ⇒ `FieldNotFilled(X For "k")` fires; malformed matched cell / invalid key = UNKNOWN.
- [ ] Validation reads **per lookup**; compute reads **per column** (stricter).
