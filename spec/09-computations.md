# 09 — Computations (§11)

Computations write values into computed fields. They share the whole expression language with rules, so everything in §1–§10 applies — but computation adds its own hard parts:

1. **Every computation also generates a validation rule** over its complete alternative table; under overlapping guards this is deliberately not just “compare with the first selected result.”
2. Three outcomes per cell — **VALUE / CLEARED / ERRORED** — decided by operand states.
3. **Two kinds of "no value"**: a precondition-clear cascades as **EMPTY**; an invalidity-clear **POISONS** — and the poison is **read-driven and order-dependent**.
4. A computed value lands as a **string in the target's declared shape** (the *stored form*), which is what downstream sees.

This is the file to get exactly right if computed fields chain.

---

## 1. The ground rules

- **Every computation also generates a validation rule.** A filled computed field is checked against every holding alternative's guarded mismatch clause (exact shape in §6 below). With mutually exclusive preconditions this agrees with the first selected computation result; overlapping preconditions can make validation fire on a later alternative even when the stored value equals the first result. Assigning a time-dependent value like `Now` would therefore report an error as soon as time passes — which is *why* `Now` is forbidden in computations ([§6](05-dates-and-time.md)).
- **Scale must match.** The computed field's declared decimal scale must equal the operation's derived scale, or the model is rejected — wrap the calculation in a rounding construct to match ([§5](04-numbers-and-decimals.md)).
- **The computed field may not appear in a precondition *nor* in an operation** (both directions draw the same rejection). The ban is on a *direct field* reference; guarding a repeatable computed field via its **containing group** (`GroupFilled` / `CurrentRepetition` on the group) is legal.
- A **non-repeatable computed field is calculated even when all its inputs are empty**. A Number calculation stores the real value `0`; a String expression runs, but a final empty text stores nothing. A literal-bearing result such as `" "` does store. Add an `AllFieldsFilled(...)` precondition to suppress the calculation entirely.
- Indirect calculation **cycles** among computed fields are possible and not always easy to detect.

---

## 2. Separate operations, and the three outcomes

**Validation and computation are separate operations.** `validateFull` never computes first; the consumer composes the form-engine flow **compute → apply → validate**, where *apply* follows the placement-sensitive per-cell contract in [`01-data-model.md §4.3`](01-data-model.md#43-the-compute--apply--validate-flow).

Per computed cell the outcome is one of:

- **VALUE** — a value is produced;
- **CLEARED** — *no* value; any stale stored value is wiped (never left standing);
- **ERRORED** — a value the target cannot legally hold (e.g. digit overflow, a below-floor date), returned but flagged.

Which outcome an operand's state produces follows the per-kind split of [§2](03-empty-and-required.md), with compute's own twists:

| an operand that is… | NUMBER | DATE | STRING in a concatenation |
|---|---|---|---|
| **empty** | reads `0` → **VALUE** | operation not evaluated → **CLEARED** | contributes `""` inside the expression; the final result still passes through the root-store gate |
| **required and empty** | still `0` (the mandatory error is *validation's* concern, not compute's) | as empty → CLEARED | still `""` |
| **filled but formally invalid** | **CLEARED + poisons** the target for dependents (below) | CLEARED + poison (type-agnostic) | CLEARED + poison |

⚠ The guard consequence cuts both ways: over **DATE** operands an `AllFieldsFilled` precondition is *redundant* (a false precondition clears exactly as the unevaluated operation does), while over a **NUMBER** operand the same guard *changes behaviour* (guarded → CLEARED, where unguarded → computes `0`).

For String computations, replacing an empty operand by `""` is only the **per-operand expression rule**. The root store makes a second decision on the final result: a final empty String stores no value, regardless of whether it came from a bare copy, a literal, or an all-empty concatenation. It therefore yields CLEARED when a stale filled target exists and is otherwise silent; it is never a stored `""` VALUE. This empty-result gate runs **before** the target format check, so an empty final result aimed at a `minLength` target clears rather than becoming ERRORED. A no-value Date result similarly means that no operation produced a value, while Number has no empty result arm because empty-as-zero produces the real number `0`.

A final empty outcome behaves as though this computation produced nothing: a later computation targeting the same cell may still win, and dependents read the target as EMPTY. Delta reporting is decided afterward from the prior target state. ERRORED and poison are decided before the empty gate and are not swallowed by it.

The root-store decision and its precedence over target format checking are source- and dual-strategy-differential-locked in a12-dmkits' [`EmptyConcatStoreDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/EmptyConcatStoreDiffTest.kt) (IF123).

The STRING column above is the *concatenation* position. A **bare string copy** (`X = [S]`, one operand, no `+`) of an empty operand computes **nothing — CLEARED**, never a stored `""`. The `FieldValueAsString` coercion of a not-given read follows the same per-context split — a standalone copy CLEARS (the store path treats an empty string value as "no calculation was done"), a concatenation gets `""`; the coercion's operand must be a NUMBER/AMOUNT field (a string copies bare).

---

## 3. Two kinds of "no value" — the empty cascade vs the poison ⚠⚠

A CLEARED cell is not one thing; *why* it cleared decides what a downstream computation sees.

### 3.1 A precondition-clear cascades as EMPTY

A field whose own computation was cleanly unselected — because its `commonPrecondition` was false or no alternative matched — reads as **plainly empty** in a dependent: `FieldFilled(dep)` is false, a number operand reads empty-as-`0`.

The mechanism: a calculation run **strips every calculated field's *input* value from the working data**, so an un-computed calculated field reads **empty regardless of what the document stored**.

Do not put every domain-undefined numeric operation in this clean-empty class. Division by zero and runtime-invalid integral power belong to the poison class in §3.2 when the result remains in the numeric family: the shared invalid numeric result survives legal `Abs`, `Min`, `Max`, and `RoundAccounting` wrappers, marks a Number target invalid, emits `berechnungsWertFehler`, and makes a dependent read poison. A Date-valued consumer projects the same missing numeric amount differently: `AddDays(StartDate, RoundAccounting(div, 2))` produces no Date value, clears a stale Date target, and does not attach `berechnungsWertFehler` to that Date target. These are consuming-operation rules, not contradictory global classifications. Existing a12-dmkits focused controls confirm the division formal-error and dependent-read channels through both kernel routes; the equivalent invalid-power controls are requested under the synchronization ledger. Fresh no-value-output versus stale CLEARED remain only delta projections and do not imply a clean-empty Number target.

### 3.2 An invalidity-clear POISONS

Reading a **formally-invalid cell** (an invalid operand's target, a domain-invalid computed Number such as division by zero or runtime-invalid integral power, an ERRORED computed value, [§3](02-logic-and-formal-errors.md)'s third state generally) **throws** inside the computing instance: it **aborts**, skips its remaining alternatives, produces no value, and **is itself marked invalid** — so its dependents' reads poison in turn.

The poison is **read-driven, therefore order-dependent**:

- compute's `And`/`Or` collapse each clean condition result to whether it is known true and evaluate left-to-right. `And` skips its right side when the clean left is false or unknown; `Or` skips its right side when the clean left is true. A poison already encountered on the left aborts either connective. A bare-group field-fill quantifier consumes the canonical field-major, repetition-major stream defined by [the fill-quantifier clause](02-logic-and-formal-errors.md#a4-fill-quantifiers-group-scopes-and-the-two-iteration-ranges) and **stops at its deciding cell**. A reached invalid cell poisons; one *beyond* a connective or scan stop is **never read and never poisons**.
- `FirstFilledValue` is the one **stop-at-first** value combiner: it consumes its selection only until the first filled cell, so an invalid *tail* cell is invisible, while an invalid cell *before* the first given one clears the computation.
- A numeric arithmetic expression evaluates its **one-pass lowered tree**, not necessarily the authored tree, from left to right. At a binary node the left subtree is evaluated first and the right subtree is evaluated before the arithmetic method is applied. A domain-invalid numeric result such as division by zero or runtime-invalid integral power is a value-level invalid result rather than a thrown read, so it does not hide a later poisoned read; a poison already thrown by the left subtree aborts before the right subtree. A lowering rewrite can therefore change which of two poisoned field reads is encountered first.

Both cascade read-rules reach **inside** a downstream computation's `Having` filter and its preconditions' quantifiers — a silently-cleared upstream target reads EMPTY there; a poisoned one poisons the reading computation.

> **Lean modelling note.** Thread compute reads through an error effect, e.g. `Except Poison Value`, with **short-circuiting `And`/`Or`** that do *not* evaluate the right operand once the left decides (so an unread invalid cell never surfaces its `Poison`). This makes order-dependence a *consequence* of the evaluation order, exactly as in the engine — do **not** eagerly evaluate all operands and then combine, or you will poison on cells the engine never reads. Model the empty-cascade separately: **before** computing, replace every computed field's stored input with `empty` in the working document, so a not-yet-computed dependency reads empty (§3.1) rather than its stale stored value. These two mechanisms — pre-strip-inputs (empty cascade) and throw-on-read (poison) — are distinct and must both be present.

### 3.3 What compute *reports*

Compute reports a **delta against the input**, not a report-all: a **VALUE only on a typed change** (the computed value differs, by typed equality, from what was stored), **CLEARED only when the input cell was filled**, **ERRORED unconditionally**. (A reimplementation that reports *every* computed cell will disagree with the engine on the unchanged ones — project to changes before comparing.)

---

## 4. The stored form — a computed value lands as a string in the target's shape

A computed value is stored in the **target field's own declared format**:

- a **DATE** in that field's `format`, not ISO ([§6](05-dates-and-time.md));
- a **NUMBER** first receives a **scale-19 `HALF_UP` pre-round**, then follows one of two scale branches. On the ordinary **fit** branch, where the stripped natural scale does not exceed the target's `maxFractionalDigits`, it renders at `max(naturalScale, minFractionalDigits)` (`10` into a two-decimal field stores `10.00`) with **no length cap**. An over-15-digit fit result is therefore retained **in full** and is ERRORED by the ordinary target check, never re-rounded to pass it. On the **no-fit** branch, reachable in a legal model only when the computation suppresses `MVK_INVALID_COMPARE_DEC_PLACES`, the value renders with at most 16 significant digits when its integer part permits that bound and is marked ERRORED unconditionally; the reduced target check still supplies a more specific target cause when one fires. On both branches and at every magnitude, the stored text is plain dot-decimal notation and never exponent/scientific notation. The no-fit branch is an explicit warning-suppressed compatibility surface, not permission for an ordinary implementation to round every result to the target's maximum scale.

The stored form is **what downstream sees**: a dependent computation reads the padded string back, and the change-equality of §3.3 is **scale-sensitive** — a computed `7.00` over a stored `7` counts as a change. Target rejection retains its attempted stored form and reports ERRORED unconditionally. A domain-invalid expression such as legal rounded division by zero or runtime-invalid integral power is different: it produces no attempted stored value, marks the target invalid with `berechnungsWertFehler`, has no delta for a fresh target and CLEARED for a stale filled target, and poisons a dependent read.

A computed result is formal-checked with the **basic** format check only — type format plus declared constraints, **without** the charset / leading-blank / trailing-blank baseline that stored *input* values get — so a computed string starting or ending with a blank stores as a plain **VALUE**.

> **Lean modelling note.** Keep a Number target's exact decimal representation as `{unscaled, scale}` through target checking and typed change comparison: kernel V2 uses scale-sensitive decimal equality, so `7` and `7.00` differ even though their rational amounts agree. Render the normalized stored representation only at the document boundary in plain dot-decimal form, and parse that stored representation on downstream reads; any locale-specific decimal separator belongs to a separate display/materialization layer and does not alter stored text. Keep the computed-result formal check a *reduced* variant (no charset/blank baseline) distinct from the input formal check of [§3](02-logic-and-formal-errors.md).

---

## 5. Where a computation runs — scope and the parallel join

- A computation iterates over its **computed field's** repetition scope — where it *writes*, not where its node is declared — and an all-non-repeatable target computes exactly one instance even on an empty document (a non-repeatable group is implicitly present). The general law, shared with rules ([§9](07-repetition-and-iteration.md)): the iteration scope is the set of *referenced* repeatable fields, never the node's placement.
- The computed target field itself is statically forbidden anywhere in the computation's common precondition, alternative preconditions, or operations, including nested condition/filter syntax. This is an authoring error (`MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD`), not a runtime dependency cycle or an empty read. References to other computed fields remain ordinary scheduling dependencies; group-level constructs are checked by their own rules rather than being equated with a direct target-field reference.
- **Alternatives** evaluate top-to-bottom. Only a known-true precondition selects; a clean false or unknown precondition falls through; a poisoned read aborts the computation and skips the remaining alternatives. The **first selected alternative** supplies the operation and ends the scan—even if that operation later produces no value—while no selected alternative yields **CLEARED**. A missing precondition is legal only on the sole alternative; a multi-alternative table must guard every row. Mutual exclusivity is authoring discipline rather than a consistency gate: overlapping preconditions resolve at compute time to the **first declared**. This is distinct from model composition handing one field several separate computations: those run in document order and the first non-empty computation outcome wins.
- Operands reaching into **sibling indexed groups** run [§9](07-repetition-and-iteration.md)'s **parallel iteration**: rows join by the shared **index-field value**, never physical position; an unmatched side reads empty; the calculation never *creates* a repetition (a key present only on the side group computes nothing); and an **invalid index cell in *any* joined group clears *every* instance** of the computation (deliberately broader than strictly necessary).
- A **starred operand** read from an iterating row binds the enclosing row only for levels *strictly above* the first star — a same-group star spans **all** rows, which is also how one **poisoned sibling cell aborts every row's** dependent.
- A **semantic-index read is column-strict in compute**: any invalid cell in the index column (malformed, duplicated, or empty) clears *every* reading computation — even one whose key matches a clean row (broader than the validation side's per-lookup rule, [§10](08-paths-and-references.md)). Over a clean column the compute read equals the validation read (a no-match or matched-but-empty cell reads empty-as-`0`). A matched **formally-invalid** cell poisons per *read cell*: a sibling computation reading a clean cell of the same row stays a VALUE.

---

## 6. The implicit validation rule, precisely

The "also acts as a validation rule" ground rule has an exact generated shape:

```
FieldFilled(F) And <optional commonPrecondition> And
  ( (precond₁ And mismatch₁([F], operation₁)) Or
    (precond₂ And mismatch₂([F], operation₂)) Or … )
```

- It fires **only when the field is *filled*** and at least one alternative whose precondition holds **disagrees** with the stored value — with the **computation's own name** as the fired error code.
- Each alternative's mismatch is ordinary strict `!=` unless that alternative declares a `toleranceRangeOp`; in that case the generated rule preserves the named fixed `DiffersWithToleranceRange1 / 2 / 5 / 10` operator. Stored and computed values inside or exactly on that normalized tolerance band do not produce a mismatch firing.
- A **cleared-vs-stored** mismatch is deliberately **not** flagged (no tier's comparison holds).
- When the alternative preconditions are mutually exclusive, the one holding comparison describes the same operation that computation selects. If alternatives overlap, the paths deliberately differ: computation executes only the first holding operation, while the generated validation rule retains every holding alternative's mismatch disjunct and may therefore fire even when the stored field equals the first operation. This validation behavior is why authors must make tier preconditions mutually exclusive even though model consistency checking does not reject overlap.

The generated rule **anchors at the computed field**: its error entity is the target's absolute location (the `computedFieldRelPath` resolved from the computation node, even across sibling subtrees or roots), independent of the declaring container's instance content (an empty declaring container does *not* silence it). A cross-group computation into a *repeatable* target is unreachable (codegen-rejected).

> **Lean modelling note.** Generate this rule as a **desugaring** of the complete alternative table into an ordinary `Rule` (the same machinery as the "required" desugaring of [§4](03-empty-and-required.md)). Reuse the same condition and operation semantics, but do **not** reuse computation's first-match selector for the generated rule: it must retain one guarded mismatch disjunct per alternative. Prove agreement between selected computation and generated validation only under an explicit mutual-exclusivity assumption (or another sufficient condition such as equal results for every simultaneously holding alternative). The `FieldFilled(F) And …` gate and the "cleared-vs-stored not flagged" behavior fall out of the generated shape above.

---

## Checklist for §11

- [ ] `compute` returns an **outcome map** (VALUE/CLEARED/ERRORED), not a mutated document; `apply` is a separate step.
- [ ] Operand-state table (empty/required-empty/invalid × NUMBER/DATE/STRING-concat) reproduced; bare string copy CLEARS on empty (no stored `""`).
- [ ] **Empty cascade** via pre-stripping computed inputs; **poison** via throw-on-read with short-circuiting `And`/`Or`, stop-at-deciding-cell scans over the canonical bare-group expansion order, `FirstFilledValue` stop-at-first, and left-to-right evaluation of the one-pass lowered numeric tree.
- [ ] Cascades reach into downstream `Having`/preconditions.
- [ ] Reporting is a **delta** (VALUE on typed change, CLEARED on filled-input, ERRORED always).
- [ ] **Stored form**: scale-19 pre-round; ordinary fit branch padded to `minFractionalDigits` with no length cap ⇒ over-long full attempt ERRORED; warning-suppressed no-fit branch length-bounded at 16 significant digits where possible and unconditionally ERRORED; always plain dot-decimal with no exponent notation; reduced formal check (no charset/blank baseline); downstream reads the stored string with scale-sensitive equality.
- [ ] Scope = computed field's repetition scope; alternatives select the first known-true precondition and stop even when its operation produces no value; poison aborts; no match clears; a multi-alternative table has no unconditional default; multi-computation first-non-empty-wins remains separate.
- [ ] Computed-target self-reference is rejected across common/alternative preconditions and operations before evaluation or scheduling.
- [ ] Parallel join by index value; invalid index in any joined group clears **every** instance; semantic index **column-strict** in compute.
- [ ] Implicit validation rule generated with the exact all-alternatives shape, preserving each alternative's optional fixed tolerance operator; agreement with first-match computation is proved only under mutual exclusivity or another stated sufficient condition; anchors at the computed field.
