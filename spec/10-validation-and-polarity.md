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

> **Non-normative implementation note.** Keep severity out of the evaluation core entirely — attach it to the emitted `Message`. "Document valid?" = "no emitted message has severity ERROR". Never let severity influence firing.

---

## 3. Every fired message is typed — VALUE vs OMISSION ⚠⚠

Beyond severity, every message carries a **message type**:

- **OMISSION** — filling one or more currently-empty fields *could* satisfy the rule ("something is missing").
- **VALUE** — no fill can; only changing an entered value helps ("what you entered is wrong").

Because empty operands participate in so many firings ([§2](03-empty-and-required.md)), the type is what tells a user *which* repair to attempt. Internally, the evaluation result must also preserve a formally-invalid/suppressed **unknown** result; it is **not-fired / fired-as-value / fired-as-omission / unknown**, with its own `And`/`Or` algebra and (again) **no negation** combinator:

- under **`And`**, **omission wins** (filling could still rescue the whole rule);
- under **`Or`**, **value wins** (the value branch alone convicts).

> **Non-normative implementation note.** Model the full evaluation result as a unified verdict so `unknown` can never be mistaken for `notFired`:
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

The public validation finding projection emits a message only for `fired`; both `notFired` and `unknown` yield no finding. Their distinction remains part of the executable semantics because enclosing `And`/`Or` consumers can distinguish them, but a terminal leaf result with no such consumer is not independently message-observable.

---

## 4. The directional-fill machinery behind the typing

The type is **not** a per-operator constant — it is computed from **directional fillability**: every operand carries *"could this result still grow / still shrink if something were filled"*, and the enclosing comparison's direction decides whether a fillable direction could clear the firing. The load-bearing pieces:

- **An empty number's fillability is asymmetric and sign-aware:** it can always **grow**, but can **shrink only if the field is *signed*** — and the trigger is `positivesOnly`, **not** `minValue`. So `[Unsigned] >= 0` fired on the empty substitution is a **VALUE** error (no fill breaks `>= 0` from above), while the signed twin is **OMISSION**.
- **Fill propagates through arithmetic and the value functions:** `+` combines both directions, `−` flips the subtrahend's, and `×`/`÷` use both current signs plus joint-direction terms. Power is not a parity-only rule: it dispatches by fixedness, base magnitude relative to `−1`, `0`, and `1`, exponent direction and parity, with reciprocal-first negative handling and conservative fallback branches. `Round*` preserves the flags, `Abs` transforms them with the value's sign, operand-list `Min`/`Max` combine them directionally, `RangeAsNumber` is grow-only. So `[F] != [A] + [B]` with an empty `B` types **OMISSION** — the right side can still move.
- **Each NUMBER aggregate combiner has its own directions after a present value enters the fold:** an incomplete `Sum` always grows and shrinks exactly when at least one missing contributing declaration is signed; signedness is attached to each omitted source, not selected once for the whole operand list. `MaxValue` is grow-only, and `MinValue` is shrink-only. The all-empty identity is the exception: if missingness exists but no present value entered the fold, the common result is `0` marked able to grow and shrink regardless of signedness or aggregate operator. A starred aggregate's missingness input includes every empty selected leaf and every open declared tail **at every reopened repeatable level from the first star downward**, checked per actual parent as specified in [§9](07-repetition-and-iteration.md#4-where-a-star-binds--the-anchor-rules-). Only exhaustion of every finite reopened level plus no empty selected leaf removes that input; an unbounded reopened level always retains it, while capacity above the first star remains bound and irrelevant. After a present value, the aggregate applies its combiner direction to this hierarchical missingness; with no present value, it participates in the both-directional all-empty branch.
- **The counts can only grow:** a fired `count >= n` is **VALUE** (no fill lowers a count), while `count < n` stays **OMISSION**.
- **Dates ride a *symmetric* combiner:** a fired date comparison types **OMISSION iff either side is not-given**, regardless of the comparison's direction.
- **An encountered `Having` filter can escalate:** value-list polarity follows its operator-specific traversal. Fields-side `AtLeastOne`/`NotAll` use the deciding witness's filter, fields-side `No` retains every reached filter on its exhausted absence scan, values-side `AtLeastOne` retains a filter only when that operand selected a present member, and values-side `No`/`NotAll` retain reached filter/missing potential from their complete values pass. A fired *comparison* consuming a filtered star remains OMISSION because its value combiner marks the filtered result not specified. Filter encounter is likewise ordered for multi-operand `FirstFilledValue`: each operand slot marks its own filter immediately before that slot is scanned, and a terminal value or formal error prevents every later slot and its filter from being observed. Filtered **counts** escalate shrinkability only when the filter actually counted a matching value; a kept nonmatch stays grow-only. **`FieldValuesNotUnique` escalates on a positionally reached filter**: its scan walks operands in authored order, marks a filter when a filtered operand yields a value that is *actually compared* — mere specifiedness is not enough, so a present-but-unconvertible cell does not mark it, and answers the moment it detects a duplicate. A firing is therefore omission-polar exactly when a filtered operand's compared value was collected at or before the duplicate — *even when every retained value is filled*, because the filter selects which values are compared — and value-polar otherwise. A filter authored **after** the duplicate-detecting value never retypes it, and a filtered operand that contributes only empty or unconvertible cells never marks anything, so the escalation is not a static "some operand is filtered" test; the two accounts agree on a single operand and on a uniformly filtered or uniformly unfiltered list. This is distinct from the filtered count-rule cases above: no missing potential in the selected cells escalates it, since a skipped empty or an uninstantiated declared row can only add a later duplicate, never clear the present one.
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

> **Non-normative implementation note.** Attach two booleans to every evaluated *numeric* operand — `canGrow`, `canShrink` — seeded at the leaves (empty unsigned number: `canGrow=true, canShrink=false`; empty signed: both true; a filled value: neither, unless it feeds an aggregate with a fillable tail) and propagated by the operator table above. Supply aggregate missingness from the recursive reopened-tree completeness predicate of §9, not from one flattened row count or a preselected global bit. Apply the explicit comparison-direction dispatch, including the dedicated normalized-side `!=` arm, and type OMISSION exactly when a legal move can falsify the currently true error condition. Dates use a simpler `notGiven` bit with a *symmetric* rule; strings/concats OR a `notGiven` bit; counts are grow-only. This is a second interpreter pass structurally parallel to truth — budget for it from the start; retrofitting polarity onto a truth-only evaluator is painful.

### 4.1 The same rule fires either type

Because the type is computed from data, **one rule legitimately fires OMISSION on one document and VALUE on another**:

- `NotExactlyOneFieldFilled(A, B)` fired at **0 filled** is OMISSION (filling one reaches exactly one) but at **2 filled** is VALUE (no fill gets back to one).
- `FirstFilledValue` types OMISSION when the complete scan exhausts with missing declared capacity, an instantiated empty cell *precedes* the first filled one, a reached star contributes no concrete cell before a later selected value, or an encountered operand slot carries `Having` (empties *after* the first value are irrelevant). The combiner retains omitted-tail state separately for its all-exhausted identity, but the runtime's field-list wrapper presents a reached no-row star as a not-given prefix before moving to the next authored operand; this applies at flat and nested reopened levels. The operator is prefix-sensitive generally: operands after the first filled one are never read, so a formal error or filter there is invisible; a formal error before it suppresses the rule.
- `CurrentRepetition` is a structural row index no fill can change — a fired comparison against it is **always VALUE**.
- A **starred operand** in a computation's operand set normally types that computation's implicit self-validation message **OMISSION**, and the reason is the grow-only rule above rather than anything about the star: the operand's extent can gain a row. **Declared capacity is the boundary.** With the starred group holding five of five declared rows and every cell filled, `NumberOfFilledGroups(Rows*)`, a mixed `NumberOfFilledGroups(Fixed, Rows*)`, and `Sum(Rows*/Value)` all type VALUE; at four of five, all three type OMISSION while a wildcard-free `NumberOfFilledGroups(Fixed, Other)` in the same run stays VALUE. One row of remaining capacity is the whole difference ([checkpoint](../docs/SOURCES.md#src-starred-operand-message-polarity)).
- **Headroom is read per operator against its own quantity, not once per operand.** At capacity with every row *empty*, one document splits them: the two counts type VALUE, because a count grows only by rows and no row can be added, while `Sum(Rows*/Value)` over the same starred group types OMISSION, because a row's empty cell can still be filled. So an implementation tracks growth per evaluated quantity, and "a starred operand can never reach all-filled" is false — exhausting capacity reaches it.

---

## 5. Full vs. partial validation

`validateFull` checks the whole document. `validatePart(document, relevantSet)` checks a relevant subset and guarantees only **one direction**: it never reports an error fixable only *outside* the subset. It does **not** guarantee a complete check of the relevant fields themselves — some checks may be skipped for performance (an implementation detail that may change). A document passing a partial validation can still fail a full one. A field referenced by a rule but living on another screen is excluded from the relevant set **unless it has the `Global` flag**.

Verified mechanics:

- **Filtered rules are skipped first in kernel 30.8.1.** If the elaborated rule contains any `Having` filter, partial-with-3VL validation returns from that rule before error-field relevance, iteration, correlation, or condition evaluation. Full validation still evaluates the rule normally. This is a versioned kernel profile, not a guarantee that later kernels expose the same public skip set.
- **Rule-gating by the error field, compared at the levels the rule's iteration BOUND.** A rule (including the auto-generated formal/mandatory/unique checks) runs only when its error field is in the relevant set **at the repetition levels the rule's iteration actually bound**. Which levels those are follows from the rule's ITERATION as [§9](07-repetition-and-iteration.md) already defines it: reference-driven, not decided by where the rule is declared. Bound levels must match exactly, which gates a per-row rule to its relevant rows. Levels below them were never chosen by any iteration: the kernel defaults them to the first repetition for the message pointer and does not require the relevant set to name that repetition, so a rule that reports into a repeatable group it does not iterate runs when **any** of that group's rows is relevant. The error path itself must still be relevant somewhere under the bound levels; a relevant sibling field is not enough. Under parallel iteration an **unmatched** side's own level counts as unbound too because no row was chosen there, and the pointer carries the `-5` sentinel ([§9](07-repetition-and-iteration.md#2-parallel-iteration--joining-two-repeatable-groups-by-key)). Of the rules that run, a **non-relevant referenced instance is three-valued UNKNOWN**, and Kleene logic decides: `true Or Unknown` still fires (no value could prevent it), while `true And Unknown` is suppressed.
- **Global fields are auto-added** to the relevant set (by the runtime layer at the `validatePart` boundary, wildcarded at all repetitions) — so a rule whose error field is global runs even when the caller's set omits it.
- **The relevant-set wildcard is explicit `IIdentifier.ALL_INDICES` (`0`).** It means every repetition at that level and is the wildcarded state used by global-field augmentation and the starred-aggregate rules below. An omitted index or `1` is the concrete first repetition, never all rows; conflating those spellings silently narrows partial validation to row 1.
- **A starred aggregate's relevance is per operator, and the operator list is measured rather than inferred from the family.** For an operand field, partial relevance first normalizes the caller's set: a relevant group contributes a pattern for every descendant field by retaining the group's coordinates and wildcarding the deeper coordinates; within one field, a broader wildcard pattern removes every narrower pattern it encompasses; patterns certainly outside the current iteration subtree are then ignored. The all-rows aggregates (`Sum`, `MaxValue`, `MinValue`, `NumberOfDifferentValues`) evaluate only when that retained set is nonempty and **every retained pattern wildcards every repeatable level the operand reopens**, from the first starred level downward per the star-binding anchor of [§9](07-repetition-and-iteration.md#4-where-a-star-binds--the-anchor-rules-), asked separately for each row of the rule's iteration scope. One wildcard does not override concrete siblings that survive normalization; a broader wildcard that encompasses them removes them before the gate. Enumerating every concrete row still leaves these aggregates UNKNOWN. `SumOfProducts` reaches neither that combiner nor its survey and carries a weaker completeness gate: it evaluates when the iteration row's starred extent is covered as a complete cross-product, taken over the union of the relevant entities addressing that row, and is UNKNOWN under a partial enumeration. `FirstFilledValue` is order-aware (UNKNOWN only when a non-relevant cell precedes the first filled one) and likewise evaluates under concrete rows. Do not extend one operator's gate to another by syntactic resemblance.
- **A starred value-list entry retains extent relevance under its own, weaker gate.** Its instantiated cells are classified individually **and filtered by concrete relevance**: a cell outside the relevant set contributes no available concrete value to the scan, independently of the extent question. Its complete extent is established as soon as **one** relevant identifier covering the entry wildcards every repeatable level the entry reopens, asked per iteration row over the levels fixed by the first-star anchor. Concrete identifiers surviving beside that wildcard do **not** take the extent away; this is exactly where the gate differs from the all-rows aggregates' universal test over the reduced identifier set. Enumerating rows concretely with no wildcard anywhere still leaves the extent UNKNOWN. The extent-unknown fact then follows the quantifier's side-specific UNKNOWN rule: `AtLeastOne` ignores it on either side, `No` is suppressed on either side, and `NotAll` ignores it on the fields side but is suppressed on the values side.
- **The three direct starred count loops select their extent independently.** `NumberOfFilledFields(F*)` has the all-rows reduced-universal outcome pattern. `NumberOfFilledGroups(G*)` has a fifth pattern in which only the concrete-field plus wildcard-group selection fires. Numeric `NumberOfValueInFields(v In F*)` has the existential value-list outcome pattern. The exact positive-document outcomes are:

| relevance selection | `NumberOfFilledFields` | `NumberOfFilledGroups` | numeric `NumberOfValueInFields` |
|---|---:|---:|---:|
| field wildcard alone | fires | silent | fires |
| field wildcard plus both concrete group rows | silent | silent | fires |
| field wildcard plus a concrete identifier for that field | fires | silent | fires |
| concrete field identifier plus wildcard group | fires | fires | fires |
| all-semantic field wildcard plus concrete group rows | fires | silent | fires |
| field wildcard plus physical-root concrete group rows | silent | silent | fires |
| both concrete group rows only | silent | silent | silent |
| row 1 only | silent | silent | silent |
| row 2 only | silent | silent | silent |

  Under wildcard relevance, two nonmatching filled quantities fire only the filled-field and filled-group rules, two instantiated empty rows fire only the filled-group rule, and no rows fire none. These controls keep count content separate from extent relevance. The String/Enumeration `NumberOfValueInFields` overload shares the same Kernel loop by source inspection, but its partial runtime matrix remains externally unmeasured.
- **Group presence has asymmetric relevance.** Any relevant descendant gives its ancestors partial relevance, and an admitted filled descendant in that slice can prove `GroupFilled`. `GroupNotFilled` requires full relevance of the group plus no admitted content and no error; one relevant empty descendant cannot prove absence. Explicit relevance of the group or an ancestor, or complete descendant-field coverage across deeper repeatable axes, supplies full relevance.
- **A relevant instance is always evaluated**: partial validation **overrides the content gate** of [§2](03-empty-and-required.md), firing empty-as-`0` even on an empty or **phantom** relevant row. Uniqueness checks need the duplicate **partner** relevant too because duplicate relations are built from relevant fields only, and so does every **ordinary rule reading that cell**, since a `uniqueIndex`-compromised cell is UNKNOWN for any rule referencing it. Omit the partner from the relevant set and the cell is clean, so the rule runs. For `RepetitionNotUnique`, every component cell of every composite key must be relevant before its row can participate; if any component is nonrelevant, that row is excluded, while an independently decisive relevant branch in the surrounding `And`/`Or` tree can still fire ([§9](07-repetition-and-iteration.md#6-repetitionnotunique-precisely)).
- **Parallel iteration is keyed by RELEVANT index cells.** The outer join of [§9](07-repetition-and-iteration.md#2-parallel-iteration--joining-two-repeatable-groups-by-key) takes its keys from each group's index field, and under partial validation that cache is built from the relevant cells only, the same restriction uniqueness relies on. A relevant set naming a joined group's payload field but **not** its index field therefore produces no keys, no iterations, and no messages, however relevant everything else is; a relevant *group* supplies its own index cell and so keeps its iteration. Leaving one group's index cell out while the other side still supplies the key does not remove the iteration: that group becomes the unmatched "not specified" side and the message reports at the `-5` sentinel.
- **An evaluation-empty index field with a declared default has phase-specific staging.** The default is the S-value stored token of an ordinary closed Enumeration index. One instance is eligible only when the index field is not explicitly mandatory, its repeatable group has exactly one physically instantiated row under the current parent, and that row's index is clean-empty—either physically absent or physically present-empty—rather than carrying an admitted explicit value. Full validation injects the stored S-value into its transient evaluation cache before index mandatory/uniqueness and authored-rule evaluation; it does not mutate the immutable document. Partial validation does not inject it: the same eligible empty index cell is made unavailable for that call without emitting `mandatoryField` or `uniqueIndex`, so dependent conditions see UNKNOWN and cannot create an error that full validation would not report. Multiple sibling rows, an explicitly mandatory index, an admitted explicit value, or a non-Enumeration index receives no default; a formally invalid explicit value remains unavailable and never exposes the S-value to authored evaluation. This silent suppression is distinct from a generated finding and does not instantiate a phantom row.

> **Non-normative implementation note.** Model kernel 30.8.1 partial validation as an ordered three-stage contract: (1) skip an elaborated rule containing any `Having` filter; (2) otherwise emit/evaluate the rule only if its error field belongs to the relevant set after global augmentation, compared at the levels the rule's iteration bound and with deeper levels treated as wildcards; (3) during that evaluation, read an out-of-set or call-locally unavailable reference as `notCheckRelevant`-style **UNKNOWN** and let Kleene logic decide. Two stage-(2) mistakes are easy and silent: testing one concretely resolved error pointer disables every rule reporting into a repeatable group it does not iterate, while taking bound levels from the rule's declared group instead of its actual iteration over-fires rules whose references iterate deeper than their declaration. Derive the bound levels from the same iteration decision §9 specifies. Derive group relevance separately as `NONE`/`PARTIAL`/`FULL`; do not infer definite absence from one relevant empty child. Normalize relevance for each operand field before asking the starred-extent question: expand relevant groups to descendant-field patterns, remove every pattern encompassed by a broader wildcard pattern, and then filter patterns certainly outside the current iteration subtree. The **four combiner aggregates** are known only when the remaining set is nonempty and **every** remaining pattern wildcards every level the operand reopens for the iteration row being evaluated. The **starred value-list extent** is known as soon as **one** covering pattern does; do not share one predicate between the two, because a single shared predicate is a measured defect in both directions. The local direct-count account reuses those predicates by operator and operand path: filled fields use the reduced-universal field path, filled groups use the reduced-universal group path to reproduce the fifth observed pattern, and value count uses the existential field path. This is an executable account of the outcomes, not a claim that the Kernel implements those predicates internally. An implementation that answers once per star path rather than per iteration row, or derives reopened levels from the path's deepest repeatable level rather than its first star, is wrong on measured cases for both. Keep `SumOfProducts`' union-based complete-cross-product gate and `FirstFilledValue`'s ordered prefix gate separate. A phantom relevant row is still evaluated and may fire through empty-as-zero, while the partial index-default path produces unavailability rather than a physical/defaulted cell or generated message. Keep relevance as wildcardable cell and group patterns rather than a flat cell list.

---

## Checklist for §12

- [ ] Severity is message metadata; only ERROR invalidates; firing is severity-independent.
- [ ] Every condition result preserves `notFired`, `fired VALUE`, `fired OMISSION`, and `unknown`; `And`→not-fired dominates then omission-wins among fires, `Or`→a fire dominates then value-wins among fires; no negation.
- [ ] Numeric operands carry `canGrow`/`canShrink`, seeded sign-aware (trigger = `positivesOnly`), propagated through arithmetic/functions/aggregates; reopened-star missingness is checked hierarchically per actual parent and unbounded reopened levels stay open; `!=` and tolerance dispatch by normalized gap direction; counts grow-only; dates symmetric `notGiven`; concat ORs `notGiven`; `Having` escalates (counts excepted).
- [ ] The same rule can type either way per document (`NotExactlyOneFieldFilled`, `FirstFilledValue` prefix-sensitivity, `CurrentRepetition` always VALUE).
- [ ] Kernel 30.8.1 `validatePart` first skips every rule containing `Having`, then gates unfiltered rules by relevant error field at the iteration-bound levels with deeper levels wildcarded, then reads out-of-set refs as UNKNOWN; auto-add globals; derive group `NONE`/`PARTIAL`/`FULL` relevance with positive-presence/negative-absence asymmetry; all-rows aggregates remain UNKNOWN unless, after group-to-field expansion, wildcard-dominance reduction, and current-subtree filtering, **every retained identifier wildcards every level the operand reopens**, asked per evaluated iteration row; a starred value-list entry's extent instead needs only **one** covering identifier to wildcard those levels, and surviving concrete siblings do not suppress it; `SumOfProducts` remains UNKNOWN unless the row's starred extent is a complete cross-product over the **union** of addressing entities; `FirstFilledValue` is order-aware; phantom relevant rows are evaluated; uniqueness and every ordinary read of a `uniqueIndex`-compromised cell need the partner relevant; partial parallel keys come only from relevant index cells; RNU requires every composite-key component of every participating row relevant; and an eligible absent or present-empty defaulted index becomes silently unavailable rather than injected or reported.
