# 10 — The validation model and message polarity (§12)

Three topics, one of which (polarity) is a whole second semantic dimension beside truth:

1. **Severity** (ERROR/WARNING/INFO) is pure message metadata — only ERROR invalidates.
2. **Message type** (VALUE vs OMISSION) is **computed from the data** via *directional fillability* and combines with Kleene truth in a verdict algebra that retains `unknown`.
3. **Full vs partial** validation — partial gates rules by a relevant set and treats out-of-set references as UNKNOWN.

The engine answers both "does the rule fire" and "*why*, and which repair helps"; the second answer is the polarity, and it decides the message a user sees.

---

## 1. Formal validation vs. rule validation

Two independent layers:

- **Formal validation** — the field-type checks the engine performs automatically (type, pattern, decimal places, required-by-checkbox, charset, blanks, …). These carry the internal sentinel path `formalePruefung` and make a field **"unknown"** while they stand ([§3](02-logic-and-formal-errors.md)).
- **Rule validation** — the author-written (and generated) rules. These **never** block a field from evaluation.

Formal validity is *prior* for every built-in read: a formally-invalid cell is unavailable to the predicates, comparisons, and aggregates that consume it, each consumer class settling it as [§1 B.2](02-logic-and-formal-errors.md#b2-the-three-cell-states--the-third-one-is-not-empty) states. `CustomCondition` is the explicit host-SPI exception because its hidden read footprint is unavailable to the kernel; a reached callback receives the formal-invalid set and owns the decision for its necessary fields ([§14](11-messages-and-custom.md#part-b--14-customcondition--the-escape-hatch)).

## 2. Severity is metadata

A rule's severity (**ERROR / WARNING / INFO**) is metadata on the resulting message, **not part of evaluation** — the condition fires identically whatever the severity. Only **ERROR**-severity messages make the document invalid: a "no error occurred" check considers **only ERRORs** (warnings and infos may be present and it still passes). A firing WARNING therefore surfaces a message without failing validation.

> **Non-normative implementation note.** Keep severity out of the evaluation core entirely — attach it to the emitted message. "Document valid?" = "no emitted message has severity ERROR".

---

## 3. Every fired message is typed — VALUE vs OMISSION ⚠⚠

Beyond severity, every message carries a **message type**:

- **OMISSION** — filling one or more currently-empty fields *could* satisfy the rule ("something is missing").
- **VALUE** — no fill can; only changing an entered value helps ("what you entered is wrong").

Because empty operands participate in so many firings ([§2](03-empty-and-required.md)), the type tells a user which repair to attempt.

**The verdict domain.** Every condition result is one of **not-fired**, **fired-as-VALUE**, **fired-as-OMISSION**, or **unknown** (a formally-invalid, non-relevant or otherwise suppressed result). A suppressed branch contributes `unknown`, never `notFired`. The connectives combine verdicts with their own algebra, and there is **no negation** combinator:

| Connective | Dominance | Between two fires |
|---|---|---|
| `And` | `notFired` dominates; then `unknown` | **omission wins** (filling could still rescue the whole rule) |
| `Or` | a fire dominates `unknown` and `notFired`; then `unknown` dominates `notFired` | **value wins** (the value branch alone convicts) |

Strong-Kleene dominance is why a fired `Or` can decide despite an unknown sibling while a fired `And` cannot.

**Projection.** The public validation finding projection emits a message only for `fired`; both `notFired` and `unknown` yield no finding. The algebra keeps them apart, because `And` and `Or` combine them differently, but no composed rule makes the difference observable as a message.

> **Non-normative implementation note.** Model the full evaluation result as one verdict type so `unknown` can never be mistaken for `notFired`, for example `inductive Polarity | value | omission` and `inductive Verdict | notFired | fired (p : Polarity) | unknown`, with conjunction and disjunction written as the two explicit tables above.

### 3.1 Truth testing and message classification

**Two passes.** An ordinary rule first tests whether its complete condition is known true. This Boolean pass visits leaves in authored order: `And` skips its right side after false or unknown; `Or` skips its right side after true. If the complete condition is true and its authored constructs **enable** classification (table below), the rule evaluates every condition leaf again in authored order and combines their verdicts with the polarity algebra of §3. This second pass is eager across both connectives. A false complete first-pass result runs no classification, including when an earlier omission-valued leaf made an `Or` true. When classification is disabled, the first pass's skipped branches remain unreached and a firing is a VALUE message.

**Enablement is static.** A rule enables classification exactly when at least one of its condition leaves enables it. The decision depends on the authored leaf, never on the current document's eventual message type: field-value operations enable the pass even when the current values are present. Every condition leaf belongs to one enablement class, and every operand of a comparison to one operand class; [the operator reference](14-operator-reference.md#classification-enablement) assigns each operator its class, and the assignment is closed.

| Leaf class | The leaf enables classification |
|---|---|
| `enables` | always |
| `never` | never |
| `unless root` | unless an operand is a root group, a starred root group included; a keyed group operand enables |
| `with Having` | only when an operand carries `Having`, on either side of a value-list quantifier |
| `with field member` | only when its value list contains a field-value operation; a literal-only list does not |
| `field-dependent` | exactly when at least one operand is a field source |

| Operand class | Meaning |
|---|---|
| `field source` | reads a document field, directly or through the operator |
| `constant source` | reads no document field |
| `transparent` | a field source exactly when one of its own operands is one |

A **root group** is a group at the top of the model tree. A parallel rule's leaves follow the same classes. A constructed `Date(...)` validity leaf enables because its admission already requires an immediate field component ([§6](05-dates-and-time.md)). Plural `No` / `NotAll` / `AtLeastOne` share one pure verdict, but that does not make these authored forms interchangeable in a condition that can fail at runtime, because their enablement differs. Measured members: a child-group `GroupFilled` guard and `FieldNotFilled` enable the pass, while unfiltered `FieldFilled`, a field-free `Now` comparison and `CustomCondition` do not. The same measurements cover Number and String comparison prefixes, false and unknown guards and a false complete condition after a true omission prefix, consistent with these classes and the pass order. On the parallel carrier only the fill quantifier is measured. The root arm of `unless root` and the singular value-list membership class rest on source reading, and the other assignments are unmeasured.

**A runtime failure fails the rule, not the validation.** A runtime failure reached in either pass — a reached unresolvable DateTime label in a comparison, or a reached `CustomCondition` name no factory resolves — reaches the same enclosing rule handler. It does not become an ordinary unknown operand or truth-valued leaf, and no later connective can suppress a failure already reached: a later false `And` operand does not. The handler reports one VALUE message with the rule's own code at the iterator's **first** error address, even when the failing leaf was reached in a later row; for an unresolved custom-condition name the message's referenced and fill-to-fix sets are empty. A repeatable rule evaluates no later row; ordinary fired verdicts continue iteration, and a failed rule does not stop independent rules. Under partial validation the iterator's first address is where the compressed error-field selector starts it ([§5.2](#52-which-rules-run-and-where)). Measured on `CustomCondition`: the messages of rows that fired before the failing row stand; a parallel rule reports at the error address of the join's first row, an unmatched one with its `UNKNOWN` coordinate included, keeps no message of a joined row that fired before the reaching row, evaluates no later joined row, and below a repeatable outer row no later outer row either. The temporal case is measured with absent, malformed and valid fields in a nonempty Berlin document; it does not change validation's enclosing content or relevance gates.

**Reachability therefore follows the two passes.** A true `FieldFilled(Flag)` disjunct hides a failing `Now` comparison when no classification-enabling construct occurs, while adding a child-group presence guard reaches that comparison during classification and fails the rule. A `CustomCondition` name is reached, and its callback called, by the same rule: a false conjunct ahead of it leaves it unreached and the rule silent, and so does a disjunct already true when the tree needs no classification pass, while a holding tree that needs one evaluates again past that disjunct, so `FieldNotFilled(Stage) Or CustomCondition X` reaches the name with `Stage` empty or filled ([§14](11-messages-and-custom.md#part-b--14-customcondition--the-escape-hatch)).

Sources: [classification matrix](../docs/sources/temporal-runtime-fold-probes.md#src-compositional-temporal-disposition), [custom-condition call checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-custom-condition-calls), [parallel reach checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-k22-parallel-custom-reach), [inbound KF52](../docs/sources/inbound-handbacks.md#inbound-2026-10-09-reconciliation).

---

## 4. The directional-fill machinery behind the typing

**General rule.** The type is **not** a per-operator constant. Every evaluated operand carries its *directional fillability* — whether filling something currently empty could still make it **grow** and whether it could still make it **shrink** — and the consuming comparison decides from those directions whether a legal fill could falsify the currently true error condition. A fired leaf types **OMISSION** exactly when such a fill exists, otherwise **VALUE**. Numeric operands carry the two directions; Date/Time/DateTime operands and Strings carry a single *not-given* bit instead (below). Invalidity and the separate "result is empty" provenance marker are independent of the direction bits.

#### Leaf seeds

| Operand | Grow | Shrink |
|---|---|---|
| empty **unsigned** Number field (`positivesOnly`; the trigger is `positivesOnly`, **not** `minValue`) | yes | no |
| empty **signed** Number field | yes | yes |
| a filled value, a literal, `BaseYear`, `CurrentRepetition` | no | no |
| `RangeAsNumber` over a missing source ([§5](04-numbers-and-decimals.md#4-other-numeric-constraints)) | yes | no |
| `RangeAsNumber` over a filled source, including a non-digit or overshooting `0` | no | no |
| `FieldValueAsNumber` over a missing source ([§5](04-numbers-and-decimals.md#4-other-numeric-constraints)) | yes | yes |

So `[Unsigned] >= 0` fired on the empty substitution is a **VALUE** error (no fill breaks `>= 0` from above), while the signed twin is **OMISSION**.

#### Propagation through arithmetic and the value functions

For valid numeric operands `a` and `b`, write `Gₐ`/`Sₐ` for "can grow"/"can shrink," and similarly for `b`:

| Result | Can grow | Can shrink |
|---|---|---|
| `a + b` | `Gₐ ∨ Gᵦ` | `Sₐ ∨ Sᵦ` |
| `a − b` | `Gₐ ∨ Sᵦ` | `Sₐ ∨ Gᵦ` |
| `a × b` | `(Gₐ ∧ Gᵦ) ∨ (Sₐ ∧ Sᵦ) ∨ (b > 0 ∧ Gₐ) ∨ (b < 0 ∧ Sₐ) ∨ (a > 0 ∧ Gᵦ) ∨ (a < 0 ∧ Sᵦ)` | `(Gₐ ∧ Sᵦ) ∨ (Sₐ ∧ Gᵦ) ∨ (b > 0 ∧ Sₐ) ∨ (b < 0 ∧ Gₐ) ∨ (a > 0 ∧ Sᵦ) ∨ (a < 0 ∧ Gᵦ)` |
| `Min(a, b)` (operand list) | `Gₐ` if `a < b`; `Gᵦ` if `b < a`; `Gₐ ∧ Gᵦ` on a tie | `Sₐ ∨ Sᵦ` |
| `Max(a, b)` (operand list) | `Gₐ ∨ Gᵦ` | `Sₐ` if `a > b`; `Sᵦ` if `b > a`; `Sₐ ∧ Sᵦ` on a tie |
| `Abs(a)` | `Gₐ ∨ Sₐ` | `Gₐ` if `a < 0`; none if `a = 0`; `Sₐ` if `a > 0` |
| `RoundDown`/`RoundUp`/`RoundAccounting(a, …)` | `Gₐ` | `Sₐ` |

The joint terms are load-bearing: two grow-only operands currently at zero produce a grow-only product even though neither current sign alone contributes. An operand-list `Min`/`Max` over more than two operands folds these rules pairwise in authored order; `Abs` and rounding apply to the completed child, an extremum included, not per operand ([§5](04-numbers-and-decimals.md#4-other-numeric-constraints)). So `[F] != [A] + [B]` with an empty `B` types **OMISSION** — the right side can still move. The operand-list `Min`/`Max` and `Abs` rows are unmeasured.

**Division** rejects a current numeric-zero divisor before fillability is consulted. Otherwise it applies the multiplication table to `a × (1 / b)`, where `G(1 / b) = Sᵦ ∨ (b < 0 ∧ Gᵦ)` and `S(1 / b) = Gᵦ ∨ (b > 0 ∧ Sᵦ)`.

**Power** is not a parity-only rule. It first transforms a negative exponent by taking the precision-50 reciprocal of the base and swapping the exponent's directions; invalid `0`-negative, fractional, and out-of-range cases stop before polarity. For a valid nonnegative exponent the kernel's conservative branch table is:

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

This power table is the kernel's hand-written conservative metadata algorithm, not a theorem that the flags equal exact mathematical reachability; do not simplify it from intuition about parity.

#### Number aggregates

Each NUMBER aggregate combiner has its own directions **after a present value enters the fold**:

| Aggregate | Directions with missingness and at least one present value |
|---|---|
| `Sum` | always grows; shrinks exactly when at least one missing contributing declaration is signed — signedness is attached to each omitted source, not selected once for the whole operand list |
| `MaxValue` | grow-only |
| `MinValue` | shrink-only |

**The all-empty identity is the exception:** if missingness exists but no present value entered the fold, the common result is `0` marked able to grow and shrink regardless of signedness or aggregate operator ([§2](03-empty-and-required.md)). Without missingness the result is fixed.

**Missingness is hierarchical.** A starred aggregate's missingness input includes every empty selected leaf and every **open declared tail** — a declared repetition slot the document does not instantiate — **at every reopened repeatable level from the first star downward**, checked per actual parent as specified in [§9](07-repetition-and-iteration.md#4-where-a-star-binds--the-anchor-rules-). Only exhaustion of every finite reopened level plus no empty selected leaf removes that input; an unbounded reopened level always retains it, while capacity above the first star remains bound and irrelevant.

#### Counts and headroom

**A count can only grow, and only while it has headroom.** No fill lowers a count, so a fired `count >= n` is **VALUE**. A fired `count < n` is **OMISSION** while the count has headroom and **VALUE** once its headroom is exhausted, when the count is fixed. Headroom is read per operator against its own quantity, not once per operand:

| Count | Headroom (can grow) |
|---|---|
| `NumberOfFilledFields` | the count is below its declared extent: the number of slots the operands can hold, a repeatable descendant's declared rows included |
| `NumberOfValueInFields` | an empty selected cell, or an open declared tail |
| `NumberOfDifferentValues` | an empty selected cell (unmeasured), or an open declared tail |
| `NumberOfFilledGroups` | the value is below its extent: one per fixed operand plus, per starred operand, the product of the declared capacities it ranges over ([§1 A.4.8](02-logic-and-formal-errors.md#a48-numberoffilledgroups)) |

A group count grows only by rows, so at capacity with every row empty the count is fixed, while `Sum` over the same starred group still grows because a row's empty cell can be filled. A count over a fixed group below a star grows by content in any instance. **A group count's declared extent multiplies the capacities of every reopened repetition level.** Bound ancestors contribute no factor, and repeatable descendants below the counted group do not enlarge it: `NumberOfFilledGroups(Rows*/Items*)` over two capacity-two levels has extent four, so two instantiated Items rows leave growth available even when they exhaust one parent's Items capacity. A fixed group below those stars uses the same product but counts content rather than structural terminal rows. The same extent determines count polarity in full and partial validation and in implicit computation validation.

#### Dates, times and Strings: the not-given bit

**Dates ride a symmetric combiner:** a fired Date/Time/DateTime comparison types **OMISSION iff either side is not-given**, regardless of the comparison's direction. A Date/Time/DateTime `MinValue`/`MaxValue` is not-given when an empty selected operand, an open declared tail or a reached `Having` filter occurs in its selection; these extremum conditions are unmeasured.

**A concatenation ORs the not-given flag across its parts:** a fired string comparison is **OMISSION iff any operand carries the flag** — so a concat containing *any* not-given read (an empty field, a no-match indexed read, a not-given coercion) types a fired mismatch OMISSION even though the concatenated string is non-empty.

#### A reached `Having` filter

A filter selects which values a quantity sees, so a **reached** filter adds movement. Encounter is per operator, never a static "some operand is filtered" test. Each carrier's effect is one of the classes below; [the operator reference](14-operator-reference.md#having-filter-effect) assigns each operator its class.

| Filter-effect class | Effect of a reached filter |
|---|---|
| `full movement` | every available result can grow and shrink, even when the unfiltered combiner would be fixed or one-directional; a fired comparison consuming it is therefore OMISSION |
| `not-given` | the result is not-given |
| `match shrink` | grows; shrinks only when a currently counted match was selected through a filter — a kept non-match stays grow-only |
| `filled shrink` | grows and shrinks when a filtered operand contributes a filled cell; otherwise the ordinary headroom rule (unmeasured) |
| `slot mark` | over multiple operands, each operand slot marks its own filter immediately before that slot is scanned; a terminal value or formal error prevents every later slot and its filter from being observed ([§4.1](#41-the-same-rule-fires-either-type)) |
| `deciding witness` | the value-list quantifier's own traversal decides: fields-side `AtLeastOne`/`NotAll` use the deciding witness's filter, fields-side `No` retains every reached filter on its exhausted absence scan, values-side `AtLeastOne` retains a filter only when that operand selected a present member, and values-side `No`/`NotAll` retain reached filter/missing potential from their complete values pass |
| `positional` | below |

**`FieldValuesNotUnique` escalates on a positionally reached filter.** Its scan walks operands in authored order, marks a filter when a filtered operand yields a value that is *actually compared* — mere specifiedness is not enough, so a present-but-unconvertible cell does not mark it — and answers the moment it detects a duplicate. A firing is therefore OMISSION exactly when a filtered operand's compared value was collected at or before the duplicate — *even when every retained value is filled*, because the filter selects which values are compared — and VALUE otherwise. A filter authored **after** the duplicate-detecting value never retypes it, and a filtered operand that contributes only empty or unconvertible cells never marks anything; the positional and the static account agree on a single operand and on a uniformly filtered or uniformly unfiltered list. No missing potential in the selected cells escalates it, since a skipped empty or an uninstantiated declared row can only add a later duplicate, never clear the present one.

Measured: filtered `Sum`, `MinValue`, `MaxValue`, `NumberOfDifferentValues`, and the Number, String, Boolean and Confirm value counts typed a fired comparison OMISSION on every measured document, in-capacity controls where the filter excluded nothing included, while the unfiltered analogues typed VALUE on the corresponding documents. The value counts' shrink-only-through-a-filtered-match condition rests on source reading; whether a filtered value count whose filter counted no match types VALUE on a comparison that only a shrink would falsify is **unmeasured**.

#### The comparison dispatch

The consuming comparison dispatches those directions per operator:

| Fired comparison | A legal fill could falsify it when… |
|---|---|
| `left > right` / `left >= right` | left can shrink **or** right can grow |
| `left < right` / `left <= right` | left can grow **or** right can shrink |
| `left == right` | either operand can move in either available direction |
| `left != right` | the currently smaller side can grow **or** the currently larger side can shrink |
| `left DiffersWithToleranceRangeN right` | after independent scale-19 normalization, the currently smaller side can grow **or** the currently larger side can shrink toward the closed band |

The `!=` and tolerance arms are directional rather than "any operand is fillable." An empty unsigned number reads `0`; `0 != -1` fires **VALUE** because equality would require the unsigned empty side to shrink below zero, which it cannot do. The signed twin fires **OMISSION** because a signed empty can shrink. The same distinction applies outside a tolerance band: unsigned empty `0` versus `−2` at range 1 fires VALUE, while the same operand versus `+2` fires OMISSION because growing toward `+2` can close the gap.

Sources: a12-dmkits [`DirectionalPolarityDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/DirectionalPolarityDiffTest.kt) (the sign-aware directional basis and `>=`/`<=` controls) and its retained [`empty-polarity` corpus family](../../a12-rulekit/corpus/cases/empty-polarity/) (the exact `!=` witnesses and literal-direction controls); no local record holds these. [Filled-field count nested capacity](../docs/sources/group-list-and-capacity-probes.md#src-filled-field-count-nested-capacity), [filtered starred-field capacity checkpoint](../docs/sources/group-and-iteration-probes.md#src-filtered-starred-field-capacity), [starred-operand polarity checkpoint](../docs/sources/group-and-iteration-probes.md#src-starred-operand-message-polarity), [ancestor-starred group-count checkpoint](../docs/sources/group-list-and-capacity-probes.md#src-ancestor-starred-group-count-computation), [nested group-count checkpoint](../docs/sources/group-count-topology.md#src-nested-group-count).

> **Non-normative implementation note.** Attach `canGrow`/`canShrink` to every evaluated numeric operand, seeded at the leaves and propagated by the tables above; give temporal operands and Strings a `notGiven` bit. Supply aggregate missingness from the recursive reopened-tree completeness predicate of §9, not from one flattened row count or a preselected global bit. Apply the explicit comparison-direction dispatch, including the dedicated normalized-side `!=` arm. This is a second interpreter pass structurally parallel to truth — budget for it from the start; retrofitting polarity onto a truth-only evaluator is painful.

### 4.1 The same rule fires either type

Because the type is computed from data, **one rule legitimately fires OMISSION on one document and VALUE on another**:

- `NotExactlyOneFieldFilled(A, B)` fired at **0 filled** is OMISSION (filling one reaches exactly one) but at **2 filled** is VALUE (no fill gets back to one).
- **`FirstFilledValue` is prefix-sensitive.** It types OMISSION when the complete scan exhausts with an open declared tail, an instantiated empty cell *precedes* the first filled one, a reached star contributes no concrete cell before a later selected value, or an encountered operand slot carries `Having`; empties *after* the first value are irrelevant. The combiner retains open-tail state separately for its all-exhausted identity, but a reached no-row star is presented as a not-given prefix before moving to the next authored operand, at flat and nested reopened levels. Operands after the first filled one are never read, so a formal error or filter there is invisible; a formal error before it suppresses the rule.
- **Missing-prefix provenance survives nesting and expansion.** A bare nested `FirstFilledValue` retains empty coordinates before the first filled leaf: if an earlier parent has an empty or omitted inner group, a value selected under a later parent carries missing-prefix provenance, and the measured String, Number and Boolean equality rules emit OMISSION rather than VALUE. The same provenance survives group declaration expansion and extents below a selected semantic-index row: an empty earlier declaration or nested branch precedes the later selected value. Empty branches after a selected value do not change its classification. Flattening only the existing leaf rows loses this distinction.
- A **clean no-match from a reached semantic-index operand** contributes a not-given prefix to `FirstFilledValue`: if a later operand supplies the first filled value and the comparison fires, it types **OMISSION**. A filled prefix that terminates before the indexed operand acquires no omission from that unreached no-match.
- `CurrentRepetition` is a structural row index no fill can change — a fired comparison against it is **always VALUE**. Whether a comparison against a fillable partner can type OMISSION is **unmeasured**.
- **Declared capacity is the boundary of a starred operand's headroom.** With the starred group holding five of five declared rows and every cell filled, `NumberOfFilledGroups(Rows*)`, a mixed `NumberOfFilledGroups(Fixed, Rows*)`, and `Sum(Rows*/Value)` all type VALUE; at four of five, all three type OMISSION while a wildcard-free `NumberOfFilledGroups(Fixed, Other)` in the same run stays VALUE. One row of remaining capacity is the whole difference, and the reason is the grow-only rule of §4 rather than anything about the star. Measured on the computation's implicit self-validation message (§4.2).
- **Headroom is per quantity.** At capacity with every row *empty*, the two counts type VALUE, because a count grows only by rows and no row can be added, while `Sum(Rows*/Value)` over the same starred group types OMISSION, because a row's empty cell can still be filled. So "a starred operand can never reach all-filled" is false — exhausting capacity reaches it. With both declared batches instantiated and every `Seal` empty, `NumberOfFilledGroups(Batches*/Seal)` types OMISSION where `NumberOfFilledGroups(Batches*)` over the same rows types VALUE. Measured on the computation's implicit self-validation message (§4.2).

Sources: [semantic-index comparison checkpoint](../docs/sources/inbound-group-operand-batches.md#src-selected-typed-comparisons), [first-filled empty-prefix checkpoint](../docs/sources/computation-scheduling-probes.md#src-first-filled-empty-prefix), [starred-operand polarity checkpoint](../docs/sources/group-and-iteration-probes.md#src-starred-operand-message-polarity), [ancestor-starred group-count checkpoint](../docs/sources/group-list-and-capacity-probes.md#src-ancestor-starred-group-count-computation), [nested group-count checkpoint](../docs/sources/group-count-topology.md#src-nested-group-count).

### 4.2 The computation's implicit self-validation message

The implicit message is a generated validation rule comparing the computed value with the stored one ([§11](09-computations.md#6-the-implicit-validation-rule-precisely)). Its type, `referenced` and `fillToFix` channels follow these rules:

- **A starred operand** in a computation's operand set normally types the message **OMISSION**, because the operand's extent can gain a row; at declared capacity the §4.1 witnesses apply.
- **The type is the ordinary directional rule applied to the computed-versus-stored inequality, with the stored side fixed.** Headroom is necessary but not sufficient: OMISSION also requires that growth move the quantity *toward* the stored value. A grow-only count below capacity with every cell filled types VALUE when its computed `3` already exceeds a seed of `1`, and OMISSION on the same document at a seed of `9`. The stored side's fixity is what the at-capacity documents show, since a stored side able to move would have typed them OMISSION.
- **The `referenced` channel carries each operand's own reach**, together with the computed target. A **group** operand names the fields anywhere in its subtree, at any depth and however many there are — a shell whose only field lies two levels below it names that field, and a group owning two fields names both. A **field** operand names that field alone: a `Sum` over one flattened field in the same message set does not name its sibling. The extent follows the authored operand's reach and must not be widened from a field operand to its enclosing group. For the group-count operator both operand forms use the one group extent, leaving a fixed operand and a starred one indistinguishable in the field set; what distinguishes them there is the coordinates.
- **`referenced` is an authored-shape inventory, not a reached-cell trace, and it is invariant under filling.** For a starred operand the set is byte-identical between a document with no instantiated row and one with four rows whose every cell is filled; a read-derived inventory would be empty in the first and enumerate every reached cell in the second. A group the evaluator cannot read is named all the same. One message carries two pointer spellings: a repetition-free address bare, and one crossing a repeatable group carrying its axes, where the starred axis is **unbound** rather than a row index — it stays at the same unbound value whether zero or four rows exist. These channels are sets, so no order is specified.
- **`fillToFix` is all of `referenced` or none of it**, never a proper subset: empty on every VALUE message, the whole referenced set on every OMISSION one, the computed target's own pointer included. A listed pointer is not a claim that the cell is empty: a target typing OMISSION on row headroom alone with every referenced cell filled lists each of those filled pointers. This is an exact projection for the computation's implicit message, sharpening the general non-minimality note of [the data model](01-data-model.md#31-rules-validation); it is not established for authored rule messages, whose operator-specific projections stay as recorded.
- **No message where an operand group holds only malformed content.** Such a group leaves the computation with its count written and **no** implicit message, measured for a fixed group, direct and nested, and for a fixed group below a star. The whole target loses it, a starred row count in the same operand list included, while a separate target counting starred rows in the same document keeps its own. Beside an admitted value the same malformed cell keeps the message, so a formal error alone does not suppress it. For a fixed group below a star one such instance suffices, even beside a filled one, while one in an over-limit row suppresses nothing. Validation leaves a malformed-only fixed group undecided, which accounts for the absence; for the below-star form that validation premise is inferred, not measured. Measured on one formal cause, unparseable Number text.

Sources: [starred-operand polarity checkpoint](../docs/sources/group-and-iteration-probes.md#src-starred-operand-message-polarity), [nested-descendant group-count runtime checkpoint](../docs/sources/group-and-iteration-probes.md#src-nested-descendant-group-count-runtime), [ancestor-starred group-count checkpoint](../docs/sources/group-list-and-capacity-probes.md#src-ancestor-starred-group-count-computation).

---

## 5. Full vs. partial validation

`validateFull` checks the whole document. `validatePart(document, relevantSet)` checks a relevant subset and guarantees only **one direction**: it never reports an error fixable only *outside* the subset. It does **not** guarantee a complete check of the relevant fields themselves — some checks may be skipped for performance (an implementation detail that may change). A document passing a partial validation can still fail a full one.

A partial call is one algorithm in four parts: the relevant set as wildcardable patterns (§5.1); which rules run and at which rows (§5.2); how each read is judged (§5.3–§5.5); and the group and parallel forms (§5.6–§5.7). The rules below are the kernel 30.8.1 profile.

### 5.1 The relevant set

**Relevance comes only from the caller's set and the `Global` flag.** A field a rule references is relevant only where the caller's relevant set covers it or the field carries the `Global` flag; a host typically passes the fields of one screen. Global fields are auto-added by the runtime layer at the `validatePart` boundary, wildcarded at all repetitions, so a rule whose error field is global runs even when the caller's set omits it.

**A relevant entity is a pattern.** It names a model path and carries one coordinate per path segment — every group segment, repeatable or not, and the terminal field segment. Coordinate `0` (`IIdentifier.ALL_INDICES`) is the wildcard: every repetition at that level. A positive coordinate is concrete; an omitted index or `1` is the concrete first repetition, never all rows, and conflating those spellings silently narrows partial validation to row 1. Coordinates are compared literally at every segment, the root included: `0` encompasses every row and `1` names the one root, so a root `1` and a root `0` are different patterns even though both cover the single root instance.

**Group expansion.** A relevant group contributes, for each descendant field, a pattern that retains the group's own coordinates and wildcards every deeper segment. A descendant pattern never projects upward onto an ancestor, except in the group count's cut-back ([§5.6](#56-group-presence-and-group-counts)).

**Cell cover.** A pattern covers a concrete cell when its path is the cell's field path or an ancestor's, and at every segment its coordinate is `0` or equals the cell's coordinate there — `1` at a non-repeatable segment, the terminal field's included. Different patterns may cover different cells.

**Where the terminal field's coordinate matters.** It takes part in cell cover and declared-slot coverage as `0` or `1` (unmeasured); it is compared literally in wildcard dominance ([§5.4](#54-the-extent-of-a-multi-cell-operand)), so a field wildcard `[1,0,1]` removes a concrete `[1,1,1]` but not a group row expanded to `[1,1,0]`; and the group-absence coverage of [§5.6](#56-group-presence-and-group-counts) ignores it while retaining the field's identity.

**Relevance is not availability.** Relevance is a property of the call; formal validity is a property of the cell. A formally invalid cell is unavailable in both kinds of validation — every built-in read settles it as [§1 B.2](02-logic-and-formal-errors.md#b2-the-three-cell-states--the-third-one-is-not-empty) states for its consumer class — while its relevance still counts wherever the dispatch of §5.2 consults relevance. Under `validatePart` with the whole group relevant, three documents agree cell for cell with `validateFull`, the malformed one included. Whether the Kernel additionally drops such a cell from an internal relevant list is not observable through these results. How an unavailable member of an operand list settles a quantifier is owned by [§1 A.4.3](02-logic-and-formal-errors.md#a43-classifying-a-slot): it stays in the list and settles nothing.

Sources: [K22 runtime R7](../docs/sources/group-count-topology.md#src-k22-runtime-r7) (`rA`, the literal root coordinate), [K22 runtime R11](../docs/sources/group-count-topology.md#src-k22-runtime-r11), [erroneous-member checkpoint](../docs/sources/inbound-group-operand-batches.md#src-erroneous-member-quantifier-undecidable).

### 5.2 Which rules run, and where

A partial call admits a rule in this order:

1. **An empty relevant set produces no message at all**, not even for a rule whose error field is otherwise gated in.
2. **Filtered rules are skipped first.** If the elaborated rule contains any `Having` filter, partial validation returns from that rule before error-field relevance, iteration, correlation, or condition evaluation. Full validation still evaluates the rule normally. This is the kernel 30.8.1 profile, not a guarantee that later kernels expose the same skip set.
3. **A rule whose error entity is a group** reports nothing in a partial call. Whether a partial call reports a rule whose error entity is the root is unmeasured.
4. **The error field gates the rule at the levels its iteration bound.** A rule — the generated formal, mandatory and unique checks included — runs only when its error field is relevant **at the repetition levels the rule's iteration actually bound**. Those levels follow from the rule's iteration as [§9](07-repetition-and-iteration.md) defines it: reference-driven, not decided by where the rule is declared. The relevant patterns reaching the error path (projected as in §5.1) are first **compressed into one selector**, every coordinate on which they differ becoming a wildcard, and the bound levels must match that selector at the current row. One pattern therefore gates a per-row rule to its own row, two parts of one line admit every part of that line, and two parts of different lines admit every part of every line, so a condition that holds without the error field's own cell fires on rows the call never names. A formally invalid relevant cell still takes part in the compression while the rule reads it as UNKNOWN. Levels below the bound ones were never chosen by any iteration: the kernel defaults them to the first repetition for the message pointer and does not require the relevant set to name that repetition, so a rule that reports into a repeatable group it does not iterate runs when **any** of that group's rows is relevant. The error path itself must still be relevant somewhere under the bound levels; a relevant sibling field is not enough. Parallel rules compress the same way and add the conditions of §5.7; their unmatched error side still carries the `-5` sentinel ([§9](07-repetition-and-iteration.md#2-parallel-iteration--joining-two-repeatable-groups-by-key)).
5. **The iterator starts where the compressed selector starts it:** at the row all the error field's selectors name, or at the first row of the iteration domain when they name different rows or none. This start is the "first error address" a failing rule reports at ([§3.1](#31-truth-testing-and-message-classification)).
6. **The rows a partial call walks are the declared-capacity domain full validation walks, with the content gate overridden.** A relevant instance is always evaluated: partial validation **overrides the content gate** of [§2](03-empty-and-required.md), firing empty-as-`0` even on an empty or **phantom** relevant row. `[Qty] < 100` declared in a three-row `Items` fires at all three declared rows of an empty document, where full validation fires none.

**The generated mandatory check reads only its own cell**, so a row reached only through compression stays silent there: lines 1 and 3 relevant around an empty required cell in line 2 report nothing, and line 2 relevant reports it.

Sources: [ordinary partial dispatch checkpoint](../docs/sources/group-count-topology.md#src-k22-ordinary-partial-dispatch), [partial dispatch merge checkpoint](../docs/sources/group-count-topology.md#src-k22-partial-dispatch-merge), [inbound 2026-10-25](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-25), [partial channel checkpoint](../docs/sources/group-count-topology.md#src-k22-partial-channel), [partial-coverage group operands](../docs/sources/group-list-and-capacity-probes.md#src-partial-coverage-group-operands), [inbound 2026-10-23](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-23) (KF603, group targets), [custom-condition call checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-custom-condition-calls) (iterator start).

### 5.3 Reading a cell under a relevant set

**A non-relevant referenced instance is UNKNOWN, and Kleene logic decides.** Of the rules that run, a cell no relevant pattern covers is unavailable and settled per consumer class as a formally invalid cell is; a scalar read answers UNKNOWN: `true Or Unknown` still fires (no value could prevent it), while `true And Unknown` is suppressed. The original, uncompressed relevant set governs every condition read; neither the compressed dispatch selector, the rule's declaring group nor its projected message row replaces it. Multi-cell operands add an extent judgment (§5.4).

**Partial validation gates the formal-error channel by the same coverage, except over-repetition.** A malformed cell reports its own formal finding under `validatePart` only when that cell is in the relevant set, while `validateFull` reports it either way. Over-repetition findings are the exception and are not narrowed: any nonempty relevant selection reports the full set ([§3 Over-repetition](02-logic-and-formal-errors.md#over-repetition)). A consumer must therefore not read a partial run's formal findings as the document's formal state.

**A structural repetition coordinate is not a reference.** `CurrentRepetition(G)` answers from the row the rule is iterating rather than from a cell, so the relevant set never makes it UNKNOWN. Under a coverage naming only its error field, a rule reading that coordinate answers exactly as under full validation — not fired on the first row, fired on the second — while a rule identical in every other respect that reads a *field* in the same operand position goes UNKNOWN on both rows. The error-field gate of §5.2 is still checked per row and runs first, so a coverage naming neither the error field nor anything conferring relevance on it reports nothing. Measured at one repetition level; deeper levels are unmeasured.

**Uniqueness needs the partner relevant.** Duplicate relations are built from relevant fields only, so a `uniqueIndex` check needs the duplicate **partner** relevant too, and so does every **ordinary rule reading that cell**, since a `uniqueIndex`-compromised cell is UNKNOWN for any rule referencing it. Omit the partner from the relevant set and the cell is clean, so the rule runs. For `RepetitionNotUnique`, every component cell of every composite key must be relevant before its row can participate; if any component is non-relevant, that row is excluded, while an independently decisive relevant branch in the surrounding `And`/`Or` tree can still fire ([§9](07-repetition-and-iteration.md#6-repetitionnotunique-precisely-)).

**An evaluation-empty index field with a declared default has phase-specific staging.** The default is the S-value stored token of an ordinary closed Enumeration index. One instance is eligible only when the index field is not explicitly mandatory, its repeatable group has exactly one physically instantiated row under the current parent, and that row's index is clean-empty — either physically absent or physically present-empty — rather than carrying an admitted explicit value. Full validation injects the stored S-value into its transient evaluation cache before index mandatory/uniqueness and authored-rule evaluation; it does not mutate the immutable document. Partial validation does not inject it: the same eligible empty index cell is made unavailable for that call without emitting `mandatoryField` or `uniqueIndex`, so dependent conditions see UNKNOWN and cannot create an error that full validation would not report. Multiple sibling rows, an explicitly mandatory index, an admitted explicit value, or a non-Enumeration index receives no default; a formally invalid explicit value remains unavailable and never exposes the S-value to authored evaluation. This silent suppression is distinct from a generated finding and does not instantiate a phantom row.

Sources: [repetition-operand partial relevance checkpoint](../docs/sources/group-and-iteration-probes.md#src-repetition-operand-partial-relevance).

### 5.4 The extent of a multi-cell operand

A multi-cell operand (an aggregate, count, list or quantifier) is judged twice: its **cells** are read under §5.3, and its **extent** — whether the call covers enough of the operand's declared slots for the result to be decided — is judged by one of the predicates below. **Which predicate an operator uses is per operator, and is not inferable from family resemblance.**

**Normalization.** For each operand field, and for each row of the rule's iteration scope separately: (1) expand relevant groups to descendant-field patterns (§5.1); (2) **wildcard dominance** — within one field, remove exact duplicates and every pattern a broader pattern encompasses, where a pattern encompasses another of the same path when at every segment its coordinate is `0` or equal to the other's; (3) ignore patterns certainly outside the current iteration subtree, that is, concrete at a bound level where the current row differs. The operand's **reopened levels** are its repeatable levels from the first starred level downward, per the star-binding anchor of [§9](07-repetition-and-iteration.md#4-where-a-star-binds--the-anchor-rules-), not from the path's deepest repeatable level.

**The extent predicates:**

| Predicate | Decided when |
|---|---|
| **all-rows** | the normalized set is nonempty and **every** retained pattern wildcards every reopened level. One wildcard does not override concrete siblings that survive normalization; a broader wildcard that encompasses them removes them before the test. Enumerating every concrete row still leaves the result UNKNOWN. |
| **declared slots** | the union of the patterns covers **every declared slot** of the operand: at each finite reopened level every coordinate up to capacity is covered, by a concrete coordinate or a wildcard; an unbounded level needs a wildcard; a non-repeatable segment needs `0` or `1`; a bound level is fixed at the current row. One wildcard covering the whole extent suffices; covering only instantiated rows is insufficient when declared slots remain uncovered, an absent trailing row included. |
| **per slot** | no extent judgment: each declared slot, missing ones included, is asked individually. A covered missing slot is empty; an uncovered slot is neither a filled nor an empty witness. |
| **ordered prefix** | the scan is UNKNOWN only when a non-relevant slot precedes the first filled one; it evaluates under concrete rows. |
| **complete cross-product** | a weaker completeness gate: each operand's declared starred extent is covered as a complete cross-product, taken over the **union** of the relevant entities addressing that row; it is UNKNOWN under an enumeration covering only present rows when declared slots remain. Independently keyed parents and missing selections follow the [product extent account](07-repetition-and-iteration.md#4-where-a-star-binds--the-anchor-rules-). |
| **group-count walk** | the four steps of §5.6. |
| **group relevance** | the `NONE`/`PARTIAL`/`FULL` judgment of §5.6. |
| **none** | no extent judgment: a non-relevant member is skipped exactly as a formally invalid one is ([§3 B.2](02-logic-and-formal-errors.md#b2-the-three-cell-states--the-third-one-is-not-empty)), and known values are compared even under incomplete extent. |

These predicates specify outcomes, not the Kernel's internal structure. Which predicate each multi-cell operator uses is assigned in [the operator reference](14-operator-reference.md#partial-extent). Under **ordered prefix** the relevance of each reached missing slot is checked before a later value can decide the prefix. An operator using the **complete cross-product** reaches neither the all-rows combiner nor its survey. Under **declared slots** a value-list quantifier's relevant concrete cells remain available witnesses under incomplete extent, and its extent uncertainty is consumed as below. Multi-cell date-range overlap has no stated predicate; its extent is unmeasured. The **none** predicate is unmeasured under a relevant set.

**A starred group operand is asked field by field.** It evaluates only when every field the group contains passes the operator's own field predicate at that field's own path, so field patterns alone establish the extent and a pattern on a descendant group covers the fields below it, while the group path itself is never the target. Measured on `Sum`, `MaxValue` and numeric `NumberOfValueInFields`; `MinValue`, `NumberOfDifferentValues` and `SumOfProducts` over a group operand, a multi-star group operand and a starred group containing a nested repeatable group are unmeasured. `MinValue` and `NumberOfDifferentValues` over a group operand follow the same field-by-field rule by default; no rule is stated for `SumOfProducts` over a group operand.

**Field-fill quantifiers per slot.** `AtLeastOneFieldFilled` and `MoreThanOneFieldFilled` can fire from covered values despite uncovered siblings, `NotAllFieldsFilled` can fire from a covered missing slot, and `AllFieldsFilled` and `NoFieldFilled` need every slot that could defeat their conclusion decided. `NotExactlyOneFieldFilled` and `FieldsNotCollectivelyFilled` retain the combinations of [§1 A.4](02-logic-and-formal-errors.md#a4-fill-quantifiers-group-scopes-and-the-two-iteration-ranges). This applies to starred fields and to the field-by-field expansion of starred or keyed groups; keyed selections add §5.5. Keep this per-slot account separate from the all-rows and cross-product predicates.

**Value-list quantifiers consume extent uncertainty side-specifically.** For finite starred field and group operands the union of relevant patterns may cover every declared slot with concrete coordinates. An extent-unknown side is consumed like an UNKNOWN on that side: `AtLeastOne` ignores it on either side, `No` is suppressed on either side, and `NotAll` ignores it on the fields side but is suppressed on the values side. Formal unavailability retains the separate quantifier policy. The runtime's additional all-USB relevance gate concerns its separate USB iteration dimension; it must not be generalized into a wildcard requirement at every ordinary repeated group.

**The three direct starred count loops select their extent independently,** each by the predicate [the operator reference](14-operator-reference.md#partial-extent) assigns it. The exact positive-document outcomes over a two-row `Items*` (50) of a `Tag` and a `Qty`, whose `Tag` no selection names, are:

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

Under wildcard relevance, two non-matching filled quantities fire only the filled-field and filled-group rules, two instantiated empty rows fire only the filled-group rule, and no rows fire none; these controls keep count content separate from extent relevance. The String/Enumeration and admitted Boolean/Confirm `NumberOfValueInFields` overloads share the Number count's loop by source inspection. Boolean constants are resolved to the admitted declaration's label before entering the token overload; their static kind and label gates remain separate. String and Boolean value counts answer a column wildcard beside concrete group rows as the Number count does, and concrete group rows covering the whole declared capacity make a String or Boolean column relevant without its wildcard, as they do for the value-list quantifiers; the Number count is not separately measured under that coverage. With the literal root coordinate of §5.1: an all-semantic field wildcard fires the filled-field, value-count and `Sum` rules beside physical-root group rows `[1,1]` and `[1,2]` as it does beside `[0,1]` and `[0,2]`; a concrete field beside the physical-root group wildcard `[1,0]` fires all five rules as it does beside `[0,0]`; and a field wildcard rooted at `1` stays silent on the filled-field, filled-group and `Sum` rules beside group rows of either root form.

**A shift amount takes the predicate its operator takes as a comparison operand.** `AddDays(Low, Sum(Rows*/N))` evaluates in a partial call only where `Rows/N` or its group is wildcard-relevant; one concrete row, or concrete group rows beside the field wildcard, leaves the shifted date unavailable, as the same `Sum` is as a comparison operand, and `MaxValue`, `MinValue`, `NumberOfDifferentValues` and `NumberOfFilledFields` amounts take the same all-rows predicate. A Number, String or Boolean value count takes the declared-slot predicate, so concrete group rows beside the column wildcard still evaluate it, and `NumberOfFilledGroups(Rows*)` takes its group-count walk, so one column's wildcard or a malformed first instance leaves it unavailable while every member column's wildcard or the group wildcard evaluates it. On every measured relevance set each amount answers as its comparison twin. A filtered amount skips its rule in every partial call, as every filtered rule does (§5.2). A keyed difference operand such as `DifferenceInDays(Rows/D For Key, Low)` needs the index column and the selected row's cell relevant (§5.5).

Sources: [inbound 2026-09-24b partial group extent](../docs/sources/inbound-handbacks.md#inbound-2026-09-24b-kf464-partial-group-extent), [reviewed KF527 handback](../docs/sources/inbound-handbacks.md#inbound-2026-10-09-extensions), [capacity-two/three list controls](../docs/sources/group-list-and-capacity-probes.md#src-partial-list-declared-extent), [inbound 2026-09-24b partial group count](../docs/sources/inbound-handbacks.md#inbound-2026-09-24b-kf464-partial-group-count), [K22 runtime R7](../docs/sources/group-count-topology.md#src-k22-runtime-r7) (`rA`, `rC`), [K22 runtime R9](../docs/sources/group-count-topology.md#src-k22-runtime-r9), [K22 runtime R11](../docs/sources/group-count-topology.md#src-k22-runtime-r11) (`CV2`, `CB7`), [Boolean value-count partial loop](../docs/sources/group-and-iteration-probes.md#src-boolean-value-count-partial-loop).

### 5.5 A selection that resolves to no row

A keyed read, a semantic-index read and a parallel join each select a row by key. Under a relevant set:

- **Key lookup uses only relevant index cells.** A key read from a field needs that key field relevant beside the group; otherwise the selection is UNKNOWN.
- **A matched key reads the selected row.** The read is decided exactly when both the row's index cell and the target are covered at that row, a concrete row pattern included; the key column alone decides nothing. A matched key binds that parent's concrete coordinate, and lower declared slots below it follow the consumer's own extent predicate (§5.4) — for the list quantifiers, complete concrete coverage of the lower declared capacity suffices; coverage under another parent does not. `GroupFilled` of the keyed group is the exception: it is decided from the key column, because the row is filled through its key.
- **A selection that resolves to no row is definite absence only under wildcard coverage of the selection level.** The relevant set must wildcard the selected level both for the index column and for the read target — through the target's own pattern, its group, or every field of the group — and the index column must be formally available. Concrete coordinates never cover the unresolved level, whether they name the key column, every existing row, or both: covering the rows that exist does not decide a no-match, and enumerating physical parents does not bind an absent selection. Lower declared slots below the missing parent may still be covered by a union of concrete patterns. Otherwise the read is UNKNOWN, and an unknown selection stays unavailable.

The consumers instantiate this rule:

| Consumer | Specifics |
|---|---|
| scalar keyed read | measured with every rule firing under full validation, keyed by a text literal, on a group whose index field is a Number and on one whose index field is a String, which decide alike. Measured coverages: a group wildcard or every field wildcarded decides; the key column, the existing rows, or both stay UNKNOWN; a key read from a field. Unmeasured: a target covered without its row's index cell, a no-match under index and target wildcards alone, and the formal-availability condition on the index column |
| field-fill quantifiers over a keyed selection | when the key selects no parent, the target slots are empty only under patterns wildcarding that parent |
| selected value lists | relevant keys, index cells and available target witnesses remain separate requirements; measured for Number and String lower field and starred-group operands under one String index; count and aggregate gates remain distinct |
| `AtLeastOneGroupFilled` / `NoGroupFilled` below a semantic index | §5.6; a missing selected parent proves no negative predicate from index coverage alone |
| `FirstFilledValue` over a keyed group operand's fields | the key column must be covered beside the first filled cell (§5.4 ordered prefix) |
| unmatched parallel side | §5.7 |

The order-aware `FirstFilledValue` account holds over separately named operands, over a group operand's fields, and over a category read alike: an empty uncovered first operand leaves it UNKNOWN although a later filled one is covered, while a covered filled first operand decides it whatever follows, measured on separately named operands and over a keyed group operand's fields.

Sources: [inbound 2026-09-24b keyed partial read](../docs/sources/inbound-handbacks.md#inbound-2026-09-24b-keyed-partial-read), [inbound 2026-09-25 keyed group walk](../docs/sources/inbound-handbacks.md#inbound-2026-09-25-keyed-group-walk), [selected-list declared-extent checkpoint](../docs/sources/group-list-and-capacity-probes.md#src-selected-list-declared-extent), [keyed starred predicates](../docs/sources/group-count-topology.md#src-keyed-star-predicates), [reviewed KF527 handback](../docs/sources/inbound-handbacks.md#inbound-2026-10-09-extensions).

### 5.6 Group presence and group counts

**Group relevance has three levels.** For one concrete group instance: `NONE` when no relevant pattern touches it; `FULL` when a pattern names the group or an ancestor, or when the union of patterns covers every descendant field across all deeper repetitions; otherwise `PARTIAL`. Any relevant descendant gives its ancestors partial relevance. For full coverage, all concrete positions of a finite repeatable child can jointly supply it, whether selected as groups or through their complete descendant fields; the same requirement applies at each deeper repeated level, even when the document holds fewer rows, and an unbounded level needs a wildcard. Duplicate coordinates, over-limit replacements, missing fields and incomplete nested combinations do not complete coverage. In this absence-coverage judgment fixed descendant groups require coordinate `1` or wildcard, while the terminal field's coordinate is ignored and its identity retained: coordinate two on a fixed descendant group prevents full coverage, coordinate two on the terminal field does not. This full-relevance product is shared by the negative group predicates and the group count's first-instance gate; their separate presence and extent policies still apply.

**Group presence is asymmetric.** An admitted filled descendant in a covered slice proves `GroupFilled`, however its uncovered siblings read. `GroupNotFilled` requires `FULL` relevance plus no admitted content and no error; one relevant empty descendant cannot prove absence, so a member nobody covers is UNDECIDED rather than empty. The predicates are ordinary three-valued quantifiers over this per-group presence: `GroupFilled` and `AtLeastOneGroupFilled` are decided by one covered filled member, and `NotAllGroupsFilled` by one **settled unfilled** member — it stays silent when the only uncovered fields are the ones that would settle it, and fires as soon as some member is fully covered and empty even though another operand field is still outside the set.

**Starred group predicates retain missing positions.** `AtLeastOneGroupFilled` and `NoGroupFilled` combine fixed groups and starred group positions through the same three-way presence classification. Reopened declared coordinates remain observable even when no row exists: an uncovered missing position is unavailable, not empty. A relevant descendant makes an instantiated repeatable terminal visible as structural content, even when that descendant is empty. One filled position decides the positive predicate despite unavailable peers; the negative predicate needs every position empty and available. Measured on single-level fixed, repeated and independent starred operands, both orders, with coverage and capacity controls.

**A semantic index binds the selected parent without consuming lower group stars.** `AtLeastOneGroupFilled` and `NoGroupFilled` apply the same declared-position presence judgment below that parent: terminal rows supply structural content, while fixed below-star groups need admitted descendant content. Under a missing selected parent the indexed level must be wildcarded and the lower declared positions covered (§5.5); complete concrete lower-slot coverage suffices for finite capacities, but concrete parent coordinates cannot replace that wildcard.

**`NumberOfFilledGroups` is decided on the counted group's own instances** rather than on its fields, and is UNKNOWN when any step fails for any operand, a list mixing a starred and a fixed operand included, each way round:

1. **The group's own patterns settle the extent.** They are the relevant patterns at or above the counted group together with every relevant descendant pattern **cut back** to the group's depth, restricted to the current iteration subtree and reduced by wildcard dominance as a field's are. The set must be nonempty and every member must wildcard every repeatable level the operand reopens. A field named concretely in every declared row therefore decides the group count where `NumberOfFilledFields` over the same group, which asks that field itself, stays UNKNOWN; a concrete pattern left at a reopened level makes the count UNKNOWN even when every instance is wholly covered.
2. **The first declared instance must be `FULL` and not erroneous.** Covering only the second row leaves the count UNKNOWN although both rows are filled, and a covered malformed value makes the first instance erroneous where the same value in a later instance does not. A fixed group is its own first instance, so a fixed operand group needs total coverage: every field of it relevant (or the group or an ancestor named), while a field the condition does not reference may stay outside the set. A descendant rejected for exceeding declared repetition capacity reports a structural finding but never enters the invalid-field cache, so it does not make an ancestor group erroneous; an in-capacity malformed descendant does.
3. **Every declared instance the document lacks must be `FULL`.** The walk visits every declared coordinate up to capacity, not only the held rows, so naming a field in the two held rows of four leaves the count UNKNOWN.
4. **Every held instance must have decided presence.** Relevant admitted content counts, including content beside an independent error in a later instance. Fully relevant clean absence contributes zero. A later malformed-only instance or partly covered instance without visible admitted content makes the whole count UNKNOWN, rather than contributing zero. A repeatable instance's instantiated row is content, so an empty row counts. The first-instance gate above remains stricter.

The count is thus the one group operator that needs complete coverage, where the presence predicates are decided by single covered members. Two reopened levels, nested repeatable descendants and one bound ancestor above them are calibrated. Excluding a malformed field from first-instance coverage leaves the same silence as healthy input under that incomplete coverage; it does not isolate error filtering from relevance. Whether a held instance can go unreached once the extent passes is unmeasured; step 4 applies to every held instance by default.

Sources: [group relevance union](../docs/sources/group-count-topology.md#src-group-relevance-union), [fixed-suffix coverage](../docs/sources/group-count-topology.md#src-group-fixed-suffix-coverage), [partial-coverage group operands](../docs/sources/group-list-and-capacity-probes.md#src-partial-coverage-group-operands), [mixed group predicates](../docs/sources/group-count-topology.md#src-mixed-group-predicates), [keyed starred predicates](../docs/sources/group-count-topology.md#src-keyed-star-predicates), [inbound 2026-09-24b partial group count](../docs/sources/inbound-handbacks.md#inbound-2026-09-24b-kf464-partial-group-count), [inbound 2026-09-24d mixed group count](../docs/sources/inbound-handbacks.md#inbound-2026-09-24d-mixed-group-count), [bound nested count](../docs/sources/group-count-topology.md#src-bound-nested-count), [`SPEC-2026-09-24-04`](https://github.com/mbackschat/a12-kernel-lean/blob/e2bc04e5cefbcce7b380a1c8f0687b5c2cd4a730/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-09-24-04) (unreached held instance).

### 5.7 Parallel iteration under partial validation

- **Parallel iteration is keyed by relevant index cells.** The outer join of [§9](07-repetition-and-iteration.md#2-parallel-iteration--joining-two-repeatable-groups-by-key) takes its keys from each group's index field, and under partial validation that cache is built from the relevant cells only, the same restriction uniqueness relies on. A relevant set naming a joined group's payload field but **not** its index field therefore produces no keys, no iterations, and no messages, however relevant everything else is; a relevant *group* supplies its own index cell and so keeps its iteration. Leaving one group's index cell out while the other side still supplies the key does not remove the iteration: that group becomes the unmatched "not specified" side and the message reports at the `-5` sentinel.
- **Parallel dispatch compresses error-field relevance before reading leaves.** Ancestor selections project onto the error field; differing coordinates across its selected patterns become wildcards in the dispatch envelope. When the parallel rule also has ordinary outer iteration, a concrete coordinate at the parallel key slot cannot satisfy that slot's iteration bound and suppresses the rule. Two distinct concrete row selectors therefore may permit dispatch where either alone suppresses it. Without ordinary outer iteration, concrete joined-row selectors still permit dispatch. **A level the error field reopens below its joined group bounds dispatch as an ordinary outer level does:** with the error field `Lines/Parts/Count` below the joined `Lines`, a concrete line selector suppresses the rule, with or without concrete parts and also for two parts of one line, while parts of two different lines compress to a wildcard line and dispatch. The compressed coordinate at each level below the joined group still narrows the rows the rule visits: part 2 of line 1 and part 2 of line 3 run part 2 of every line and no first part, even for a condition that would fire there without the error field's cell, and leaf relevance then limits the firing parts to the relevant ones. The original, uncompressed relevant set governs every condition read (§5.3).
- **An unmatched side follows §5.5.** A missing side is definite empty only when its index column is formally available and both its index field and the referenced field wildcard-cover the unknown joined repetition; selecting every currently instantiated index row separately does not cover it. Otherwise the read is UNKNOWN, even though a far-side positive branch may still emit at the unknown error coordinate. For a missing group, an ancestor selection or complete wildcard descendant-field coverage can establish full group relevance; an explicit group selector is not required.
- **One-sided parallel frames retain the declared iteration domain.** The ordinary frame uses the same small declared-product versus occupied-prefix traversal as full ordinary validation, with the parallel key slot contributing no numeric bound. Far-side keys can drive evaluations in uninstantiated frame slots. Full and partial calls share that domain; partial dispatch and leaf relevance then apply independently.

Sources: [nested-join partial checkpoint](../docs/sources/model-structure-and-declaration-probes.md#src-k22-nested-join-partial), [partial dispatch merge checkpoint](../docs/sources/group-count-topology.md#src-k22-partial-dispatch-merge), [inbound 2026-10-25](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-25), [partial parallel captures](../docs/sources/model-structure-and-declaration-probes.md#src-partial-parallel) (scope/root/union and 3/6-frame controls).

> **Non-normative implementation note.** Model partial validation as the ordered contract of §5.2 followed by per-read judgment: skip filtered rules; gate the rule by the compressed error-field selector at the bound levels with deeper levels ignored; then read every non-covered or call-locally unavailable reference as UNKNOWN and let Kleene logic decide. Two dispatch mistakes are easy and silent: testing one concretely resolved error pointer disables every rule reporting into a repeatable group it does not iterate, while taking bound levels from the rule's declared group instead of its actual iteration over-fires rules whose references iterate deeper than their declaration. Keep relevance as wildcardable patterns rather than a flat cell list, derive group relevance as `NONE`/`PARTIAL`/`FULL`, and never infer definite absence from one relevant empty child. Implement the all-rows and the declared-slot predicates separately: sharing one predicate between them is wrong in both directions. Ask every extent predicate per iteration row and from the operand's first star; answering once per star path, or from the path's deepest repeatable level, is wrong on measured cases. A phantom relevant row is still evaluated and may fire through empty-as-zero, while the partial index-default path produces unavailability rather than a defaulted cell or generated message.

---

## Checklist for §12

- [ ] Severity is message metadata; only ERROR invalidates; firing is severity-independent.
- [ ] Every condition result preserves `notFired`, `fired VALUE`, `fired OMISSION`, and `unknown`; `And`→not-fired dominates, then unknown, then omission-wins among fires; `Or`→a fire dominates, then value-wins among fires; no negation.
- [ ] A true rule runs the eager classification pass exactly when one of its leaves enables it, by the §3.1 classes as [the operator reference](14-operator-reference.md#classification-enablement) assigns them; a runtime failure reached in either pass fails the rule with one VALUE message at the iterator's first error address.
- [ ] Numeric operands carry `canGrow`/`canShrink`, seeded sign-aware (trigger = `positivesOnly`), propagated through arithmetic, operand-list `Min`/`Max`, `Abs`, rounding and aggregates; reopened-star missingness is checked hierarchically per actual parent and unbounded reopened levels stay open; `!=` and tolerance dispatch by normalized gap direction; counts grow only while headroom remains and are fixed at an exhausted extent; dates and temporal extrema use a symmetric `notGiven`; concat ORs `notGiven`; a reached `Having` escalates by the §4 filter-effect classes as [the operator reference](14-operator-reference.md#having-filter-effect) assigns them.
- [ ] The same rule can type either way per document (`NotExactlyOneFieldFilled`, `FirstFilledValue` prefix-sensitivity and missing-prefix provenance, `CurrentRepetition` VALUE with a fillable partner unmeasured).
- [ ] Kernel 30.8.1 `validatePart`: an empty set reports nothing; every rule containing `Having` is skipped first; a group error entity reports nothing; unfiltered rules are gated by the compressed relevant error-field selector at the iteration-bound levels with deeper levels ignored, and the iterator starts where that selector starts it; the declared-capacity rows are walked with the content gate overridden (phantom relevant rows are evaluated); out-of-set refs read UNKNOWN under the uncompressed set; globals are auto-added; patterns compare coordinates literally, the root and terminal field included.
- [ ] Multi-cell extents follow the §5.4 predicates as [the operator reference](14-operator-reference.md#partial-extent) assigns them: all-rows (every retained pattern, after group expansion, wildcard dominance and subtree filtering, wildcards every reopened level, per iteration row); declared-slot coverage by the union of patterns; per slot; ordered prefix; union cross-product; the four-step group-count walk; `NONE`/`PARTIAL`/`FULL` group relevance with positive-presence/negative-absence asymmetry; none.
- [ ] A selection resolving to no row is definite absence only when the index column and the read target wildcard-cover the selected level; partial parallel keys come only from relevant index cells; uniqueness and every ordinary read of a `uniqueIndex`-compromised cell need the partner relevant; RNU requires every composite-key component of every participating row relevant; cell-conversion formal findings are gated by coverage while over-repetition findings are not; and an eligible absent or present-empty defaulted index becomes silently unavailable rather than injected or reported.
