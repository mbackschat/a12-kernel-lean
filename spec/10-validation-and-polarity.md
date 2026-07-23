# 10 — The validation model and message polarity (§12)

Three topics, one of which (polarity) is a *whole second semantic dimension* a naive reimplementation omits entirely:

1. **Severity** (ERROR/WARNING/INFO) is pure message metadata — only ERROR invalidates.
2. **Message type** (VALUE vs OMISSION) is **computed from the data** via *directional fillability* and combines with Kleene truth in a verdict algebra that retains `unknown`.
3. **Full vs partial** validation — partial gates rules by a relevant set and treats out-of-set references as UNKNOWN.

If you only implement "does the rule fire", you have implemented *half* of validation. The engine also answers "*why*, and what repair helps" — that is the polarity, and it is load-bearing for the message a user sees.

---

## 1. Formal validation vs. rule validation

Two independent layers:

- **Formal validation** — the field-type checks the engine performs automatically (type, pattern, decimal places, required-by-checkbox, charset, blanks, …). These carry the internal sentinel path `formalePruefung` and make a field **"unknown"** while they stand ([§3](02-logic-and-formal-errors.md)).
- **Rule validation** — the author-written (and generated) rules. These **never** block a field from evaluation.

Formal validity is *prior* for every built-in read: a formally-invalid cell is UNKNOWN to predicates, comparisons, and aggregates that consume it. `CustomCondition` is the explicit host-SPI exception because its hidden read footprint is unavailable to the kernel; a reached callback receives the formal-invalid set and owns the decision for its necessary fields ([§14](11-messages-and-custom.md#part-b--14-customcondition--the-escape-hatch)).

## 2. Severity is metadata

A rule's severity (**ERROR / WARNING / INFO**) is metadata on the resulting message, **not part of evaluation** — the condition fires identically whatever the severity. Only **ERROR**-severity messages make the document invalid: a "no error occurred" check considers **only ERRORs** (warnings and infos may be present and it still passes). A firing WARNING therefore surfaces a message without failing validation — useful for "are you sure?" advisories.

> **Lean modelling note.** Keep severity out of the evaluation core entirely — attach it to the emitted `Message`. "Document valid?" = "no emitted message has severity ERROR". Never let severity influence firing.

---

## 3. Every fired message is typed — VALUE vs OMISSION ⚠⚠

Beyond severity, every message carries a **message type**:

- **OMISSION** — filling one or more currently-empty fields *could* satisfy the rule ("something is missing").
- **VALUE** — no fill can; only changing an entered value helps ("what you entered is wrong").

Because empty operands participate in so many firings ([§2](03-empty-and-required.md)), the type is what tells a user *which* repair to attempt. Internally, the evaluation result must also preserve a formally-invalid/suppressed **unknown** result; it is **not-fired / fired-as-value / fired-as-omission / unknown**, with its own `And`/`Or` algebra and (again) **no negation** combinator:

- under **`And`**, **omission wins** (filling could still rescue the whole rule);
- under **`Or`**, **value wins** (the value branch alone convicts).

> **Lean modelling note.** Model the full evaluation result as a unified verdict so `unknown` can never be mistaken for `notFired`:
> ```lean
> inductive Polarity where | value | omission
> inductive Verdict where
>   | notFired
>   | fired (polarity : Polarity)
>   | unknown
> -- conj: notFired dominates; then unknown; among two fires omission wins.
> -- disj: a fire dominates unknown/notFired; among fires value wins.
> ```
> The explicit tables live in [`../A12Kernel/Core.lean`](../A12Kernel/Core.lean). A suppressed branch contributes `unknown`, not `notFired`; strong-Kleene dominance then explains why a fired `Or` can decide despite an unknown sibling while a fired `And` cannot.

---

## 4. The directional-fill machinery behind the typing

The type is **not** a per-operator constant — it is computed from **directional fillability**: every operand carries *"could this result still grow / still shrink if something were filled"*, and the enclosing comparison's direction decides whether a fillable direction could clear the firing. The load-bearing pieces:

- **An empty number's fillability is asymmetric and sign-aware:** it can always **grow**, but can **shrink only if the field is *signed*** — and the trigger is `positivesOnly`, **not** `minValue`. So `[Unsigned] >= 0` fired on the empty substitution is a **VALUE** error (no fill breaks `>= 0` from above), while the signed twin is **OMISSION**.
- **Fill propagates through arithmetic and the value functions:** `+` combines both directions, `−` flips the subtrahend's, and `×`/`÷` use both current signs plus joint-direction terms. Power is not a parity-only rule: it dispatches by fixedness, base magnitude relative to `−1`, `0`, and `1`, exponent direction and parity, with reciprocal-first negative handling and conservative fallback branches. `Round*` preserves the flags, `Abs` transforms them with the value's sign, operand-list `Min`/`Max` combine them directionally, `RangeAsNumber` is grow-only. So `[F] != [A] + [B]` with an empty `B` types **OMISSION** — the right side can still move.
- **Each NUMBER aggregate combiner has its own directions after a present value enters the fold:** an incomplete `Sum` always grows and shrinks exactly when at least one missing contributing declaration is signed; signedness is attached to each omitted source, not selected once for the whole operand list. `MaxValue` is grow-only, and `MinValue` is shrink-only. The all-empty identity is the exception: if missingness exists but no present value entered the fold, the common result is `0` marked able to grow and shrink regardless of signedness or aggregate operator. A starred aggregate's missingness input includes every empty selected leaf and every open declared tail **at every reopened repeatable level from the first star downward**, checked per actual parent as specified in [§9](07-repetition-and-iteration.md#4-where-a-star-binds--the-anchor-rules-). Only exhaustion of every finite reopened level plus no empty selected leaf removes that input; an unbounded reopened level always retains it, while capacity above the first star remains bound and irrelevant. After a present value, the aggregate applies its combiner direction to this hierarchical missingness; with no present value, it participates in the both-directional all-empty branch.
- **The counts can only grow:** a fired `count >= n` is **VALUE** (no fill lowers a count), while `count < n` stays **OMISSION**.
- **Dates ride a *symmetric* combiner:** a fired date comparison types **OMISSION iff either side is not-given**, regardless of the comparison's direction.
- **An encountered `Having` filter escalates:** a fired quantifier over a filtered field star is **unconditionally OMISSION**, and so is a fired *comparison* consuming a filtered star (every value combiner marks a filtered result "not specified"). Filter encounter remains ordered for multi-operand `FirstFilledValue`: each operand slot marks its own filter immediately before that slot is scanned, and a terminal value or formal error prevents every later slot and its filter from being observed. The filtered **counts** are the exception — they escalate only when the filter actually *counted* a value; a kept-nothing count stays directional (grow-only).
- **A concatenation ORs the not-given flag across its parts:** a fired string comparison is **OMISSION iff any operand carries the flag** — so a concat containing *any* not-given read (an empty field, a no-match indexed read, a not-given coercion) types a fired mismatch OMISSION even though the concatenated string is non-empty.

For valid numeric operands `a` and `b`, write `Gₐ`/`Sₐ` for “can grow”/“can shrink,” and similarly for `b`. The exact ordinary-arithmetic propagation is:

| Result | Can grow | Can shrink |
|---|---|---|
| `a + b` | `Gₐ ∨ Gᵦ` | `Sₐ ∨ Sᵦ` |
| `a − b` | `Gₐ ∨ Sᵦ` | `Sₐ ∨ Gᵦ` |
| `a × b` | `(Gₐ ∧ Gᵦ) ∨ (Sₐ ∧ Sᵦ) ∨ (b > 0 ∧ Gₐ) ∨ (b < 0 ∧ Sₐ) ∨ (a > 0 ∧ Gᵦ) ∨ (a < 0 ∧ Sᵦ)` | `(Gₐ ∧ Sᵦ) ∨ (Sₐ ∧ Gᵦ) ∨ (b > 0 ∧ Sₐ) ∨ (b < 0 ∧ Gₐ) ∨ (a > 0 ∧ Sᵦ) ∨ (a < 0 ∧ Gᵦ)` |

Division rejects a current numeric-zero divisor before fillability is consulted. Otherwise it applies the multiplication table to `a × (1 / b)`, where `G(1 / b) = Sᵦ ∨ (b < 0 ∧ Gᵦ)` and `S(1 / b) = Gᵦ ∨ (b > 0 ∧ Sᵦ)`. The joint terms are load-bearing: two grow-only operands currently at zero produce a grow-only product even though neither current sign alone contributes.

Power first transforms a negative exponent by taking the precision-50 reciprocal of the base and swapping the exponent's directions; invalid `0`-negative, fractional, and out-of-range cases stop before polarity. For a valid nonnegative exponent, the kernel's conservative branch table is:

| Fixedness/value region | Result directions |
|---|---|
| fixed exponent `0`, or both operands fixed | fixed |
| fixed positive odd exponent | base directions |
| fixed positive even exponent | grow; shrink iff the base can move toward zero from its current sign |
| fixed base `> 1` | exponent directions |
| fixed base `= 1` | fixed |
| fixed base in `(0, 1)` | swapped exponent directions |
| fixed base `= 0`, exponent cannot shrink, exponent `> 0` | fixed |
| fixed base `= 0`, exponent cannot shrink, exponent `= 0` | shrink-only |
| fixed base `= 0`, exponent can shrink | grow-only |
| fixed base in `(−1, 0)`, exponent cannot shrink | shrink-only for even, grow-only for odd |
| fixed base in `(−1, 0)`, exponent can shrink | grow and shrink |
| fixed base `= −1` | shrink-only for even, grow-only for odd |
| fixed base `< −1`, exponent cannot grow | shrink-only for even, grow-only for odd |
| fixed base `< −1`, exponent can grow | grow and shrink |
| both operands variable, with `base > 1` and neither able to shrink | grow-only |
| every other both-variable case | grow and shrink |

This power table is the kernel's hand-written conservative metadata algorithm, not a theorem that the flags equal exact mathematical reachability. In particular, do not simplify it from intuition about parity. Invalidity and the separate “result is empty” provenance marker remain independent of these two direction bits.

The consuming comparison dispatches those directions per operator:

| Fired comparison | A legal fill could falsify it when… |
|---|---|
| `left > right` / `left >= right` | left can shrink **or** right can grow |
| `left < right` / `left <= right` | left can grow **or** right can shrink |
| `left == right` | either operand can move in either available direction |
| `left != right` | the currently smaller side can grow **or** the currently larger side can shrink |
| `DiffersWithToleranceRangeN(left, right)` | after independent scale-19 normalization, the currently smaller side can grow **or** the currently larger side can shrink toward the closed band |

The `!=` and tolerance arms are directional rather than “any operand is fillable.” For example, an empty unsigned number reads `0`; `0 != -1` fires **VALUE** because equality would require the unsigned empty side to shrink below zero, which it cannot do. The signed twin fires **OMISSION** because a signed empty can shrink. The same distinction applies outside a tolerance band: unsigned empty `0` versus `−2` at range 1 fires VALUE, while the same operand versus `+2` fires OMISSION because growing toward `+2` can close the gap. a12-dmkits' [`DirectionalPolarityDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/DirectionalPolarityDiffTest.kt) locks the sign-aware directional basis and `>=`/`<=` controls; its retained [`empty-polarity` corpus family](../../a12-rulekit/corpus/cases/empty-polarity/) locks these exact `!=` witnesses and their literal-direction controls.

> **Lean modelling note.** Attach two booleans to every evaluated *numeric* operand — `canGrow`, `canShrink` — seeded at the leaves (empty unsigned number: `canGrow=true, canShrink=false`; empty signed: both true; a filled value: neither, unless it feeds an aggregate with a fillable tail) and propagated by the operator table above. Supply aggregate missingness from the recursive reopened-tree completeness predicate of §9, not from one flattened row count or a preselected global bit. Apply the explicit comparison-direction dispatch, including the dedicated normalized-side `!=` arm, and type OMISSION exactly when a legal move can falsify the currently true error condition. Dates use a simpler `notGiven` bit with a *symmetric* rule; strings/concats OR a `notGiven` bit; counts are grow-only. This is a second interpreter pass structurally parallel to truth — budget for it from the start; retrofitting polarity onto a truth-only evaluator is painful.

### 4.1 The same rule fires either type

Because the type is computed from data, **one rule legitimately fires OMISSION on one document and VALUE on another**:

- `NotExactlyOneFieldFilled(A, B)` fired at **0 filled** is OMISSION (filling one reaches exactly one) but at **2 filled** is VALUE (no fill gets back to one).
- `FirstFilledValue` types OMISSION when the complete scan exhausts with missing declared capacity, an instantiated empty cell *precedes* the first filled one, a reached star contributes no concrete cell before a later selected value, or an encountered operand slot carries `Having` (empties *after* the first value are irrelevant). The combiner retains omitted-tail state separately for its all-exhausted identity, but the runtime's field-list wrapper presents a reached no-row star as a not-given prefix before moving to the next authored operand; this applies at flat and nested reopened levels. The operator is prefix-sensitive generally: operands after the first filled one are never read, so a formal error or filter there is invisible; a formal error before it suppresses the rule.
- `CurrentRepetition` is a structural row index no fill can change — a fired comparison against it is **always VALUE**.

---

## 5. Full vs. partial validation

`validateFull` checks the whole document. `validatePart(document, relevantSet)` checks a relevant subset and guarantees only **one direction**: it never reports an error fixable only *outside* the subset. It does **not** guarantee a complete check of the relevant fields themselves — some checks may be skipped for performance (an implementation detail that may change). A document passing a partial validation can still fail a full one. A field referenced by a rule but living on another screen is excluded from the relevant set **unless it has the `Global` flag**.

Verified mechanics:

- **Filtered rules are skipped first in kernel 30.8.1.** If the elaborated rule contains any `Having` filter, partial-with-3VL validation returns from that rule before error-field relevance, iteration, correlation, or condition evaluation. Full validation still evaluates the rule normally. This is a versioned kernel profile, not a guarantee that later kernels expose the same public skip set.
- **Rule-gating by the error field.** A rule (including the auto-generated formal/mandatory/unique checks) runs **only when its error-field instance is in the relevant set**. Of the rules that run, a **non-relevant referenced instance is three-valued UNKNOWN**, and Kleene logic decides — `true Or Unknown` still fires (no value could prevent it), `true And Unknown` is suppressed.
- **Global fields are auto-added** to the relevant set (by the runtime layer at the `validatePart` boundary, wildcarded at all repetitions) — so a rule whose error field is global runs even when the caller's set omits it.
- **A starred aggregate's relevance is per operator.** The all-rows aggregates (`Sum`, `MaxValue`, `MinValue`, `NumberOfDifferentValues`, `SumOfProducts`) evaluate only when the starred level is **wildcarded** (or a relevant ancestor covers it) — enumerating every concrete row still leaves them UNKNOWN — while `FirstFilledValue` is **order-aware** (UNKNOWN only when a non-relevant cell precedes the first filled one).
- **A starred value-list entry also retains extent relevance.** Its instantiated cells are filtered by concrete relevance, but only wildcard/ancestor coverage establishes that the whole star is relevant. The extent-unknown fact follows the quantifier's side-specific UNKNOWN rule: `AtLeastOne` ignores it, `No` is suppressed, and `NotAll` ignores it on the fields side but is suppressed on the values side.
- **Group presence has asymmetric relevance.** Any relevant descendant gives its ancestors partial relevance, and an admitted filled descendant in that slice can prove `GroupFilled`. `GroupNotFilled` requires full relevance of the group plus no admitted content and no error; one relevant empty descendant cannot prove absence. Explicit relevance of the group or an ancestor, or complete descendant-field coverage across deeper repeatable axes, supplies full relevance.
- **A relevant instance is always evaluated** — partial validation **overrides the content gate** of [§2](03-empty-and-required.md), firing empty-as-`0` even on an empty or **phantom** relevant row. Uniqueness checks need the duplicate **partner** relevant too because duplicate relations are built from relevant fields only. For `RepetitionNotUnique`, every component cell of every composite key must be relevant before its row can participate; if any component is nonrelevant, that row is excluded, while an independently decisive relevant branch in the surrounding `And`/`Or` tree can still fire ([§9](07-repetition-and-iteration.md#6-repetitionnotunique-precisely)).
- **A missing index field with a declared default has phase-specific staging.** The default is the S-value stored token of an ordinary closed Enumeration index. One instance is eligible only when the index field is not explicitly mandatory, its repeatable group has exactly one physically instantiated row under the current parent, and that row has no explicit index value. Full validation injects the stored S-value into its transient evaluation cache before index mandatory/uniqueness and authored-rule evaluation; it does not mutate the immutable document. Partial validation does not inject it: the same eligible missing index cell is made unavailable for that call without emitting `mandatoryField` or `uniqueIndex`, so dependent conditions see UNKNOWN and cannot create an error that full validation would not report. Multiple sibling rows, an explicitly mandatory index, an explicit value, or a non-Enumeration index receives no default. This silent suppression is distinct from a generated finding and does not instantiate a phantom row.

> **Lean modelling note.** Model kernel 30.8.1 partial validation as an ordered three-stage contract: (1) skip an elaborated rule containing any `Having` filter; (2) otherwise emit/evaluate the rule only if its error-field instance belongs to the relevant set after global augmentation; (3) during that evaluation, read an out-of-set or call-locally unavailable reference as `notCheckRelevant`-style **UNKNOWN** and let Kleene logic decide. Derive group relevance separately as `NONE`/`PARTIAL`/`FULL`; do not infer definite absence from one relevant empty child. The starred-aggregate "only when wildcarded" rule, phantom-row evaluation, and index-default suppression are the other easy-to-miss pieces: the aggregate stays UNKNOWN unless the whole starred level is covered, a phantom relevant row is still evaluated and may fire through empty-as-zero, and the partial index-default path produces unavailability rather than a physical/defaulted cell or generated message. Keep relevance as wildcardable cell and group patterns rather than a flat cell list.

---

## Checklist for §12

- [ ] Severity is message metadata; only ERROR invalidates; firing is severity-independent.
- [ ] Every condition result preserves `notFired`, `fired VALUE`, `fired OMISSION`, and `unknown`; `And`→not-fired dominates then omission-wins among fires, `Or`→a fire dominates then value-wins among fires; no negation.
- [ ] Numeric operands carry `canGrow`/`canShrink`, seeded sign-aware (trigger = `positivesOnly`), propagated through arithmetic/functions/aggregates; reopened-star missingness is checked hierarchically per actual parent and unbounded reopened levels stay open; `!=` and tolerance dispatch by normalized gap direction; counts grow-only; dates symmetric `notGiven`; concat ORs `notGiven`; `Having` escalates (counts excepted).
- [ ] The same rule can type either way per document (`NotExactlyOneFieldFilled`, `FirstFilledValue` prefix-sensitivity, `CurrentRepetition` always VALUE).
- [ ] Kernel 30.8.1 `validatePart` first skips every rule containing `Having`, then gates unfiltered rules by relevant error field, then reads out-of-set refs as UNKNOWN; auto-add globals; derive group `NONE`/`PARTIAL`/`FULL` relevance with positive-presence/negative-absence asymmetry; all-rows aggregates and the extent fact of starred value-list entries remain UNKNOWN unless wildcarded; phantom relevant rows evaluated; uniqueness needs the partner relevant, RNU requires every composite-key component of every participating row relevant, and a missing defaulted index becomes silently unavailable rather than injected or reported.
