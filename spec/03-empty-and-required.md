# 03 — Empty values and the "required" property (§2 + §4)

Two joined topics:

- **§2** — how an *unspecified* operand behaves. A document spends most of its life half-empty, and the same comparison shape changes meaning with the operand's type, so this is where most real-world rule bugs start.
- **§4** — the "required" property, which is not a runtime flag but *expands into a generated rule* and *manifests as a formal error* — so it is really a §2/§3 topic wearing an editor hat.

The third cell state (formally invalid) is [§3](02-logic-and-formal-errors.md#part-b--3-formal-errors-and-the-unknown-state)'s subject; here "empty" always means *unspecified*, never *invalid*.

---

## Part A — §2 Non-specified (empty) values

### A.1 The per-kind default

**An empty operand reads its kind's default.** The default tier has exactly eight primitive kinds:

| Field type | Unspecified value in a comparison |
|---|---|
| **number** | a default of **`0`** is substituted |
| **confirm** | treated as **`False`** |
| **boolean, string, enumeration, date, time, date-time** | the comparison is **not evaluated** (no error, no fire) |

Three further model types read as follows when empty: an empty DateFragment or DateRange operand leaves the comparison **not evaluated**, and an empty Custom field reads as the String kind, so its comparison is **not evaluated** too. Measured on `==` and `!=`: two DateFragment or two DateRange fields fire neither with both sides empty nor with only the right side empty, while the same `!=` fires once both sides hold different values, and a Custom field compared with a String literal fires neither when empty. A left-empty DateFragment or DateRange side beside a filled right side is unmeasured. Other model types belong to their own type-family or registered-validator clauses; the eight-kind header does not define them. An operator may override the default for its own operands: A.2 defines the override classes.

```
[Amount] < 100          -- number: FIRES on an empty Amount, because 0 < 100
[Date] > "01.01.2022"   -- date: does NOT fire on an empty Date (not evaluated)
```

⚠ This is the trap. To avoid flagging an empty number, guard it:

```
FieldFilled(Amount) And [Amount] < 100
```

**A substituted value carries provenance for typing a fired comparison** ([§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing)). The Number `0` is directionally fillable, sign-aware by the leaf seeds of §12 §4. The Confirm `False` is marked not-given, so a fired comparison over an empty Confirm is OMISSION: `[K] != True` fires OMISSION with `K` empty. No single provenance bit serves every consumer: Number expressions and Number aggregates carry grow and shrink directions, a count grows while its headroom lasts, Date, Time and DateTime operands carry a symmetric not-given bit, a concatenation combines its parts' not-given bits, and a filtered consumer follows its own family rule, each as §12 §4 states.

Two riders:

- **The `0` substitution does not reach the `MaxValue`/`MinValue` aggregates.** A.2 states their split from the operand-list `Min`/`Max`, and A.3 their all-empty identity.
- **There is no empty String semantic value.** A physically placed raw `""` becomes present-empty at the [evaluation-ingestion boundary](01-data-model.md#2-document--an-instance-of-the-tree), not a filled zero-length String and not an absent placement. A String comparison is not evaluated, for both `==` and `!=`, when either operand's value is the empty text: a literal `""`, an empty field, an empty coercion result, or a concatenation whose parts are all empty. So `[F] == ""` is never satisfied, even when `F` is unfilled, and neither is `[F] != ""`. Use `FieldNotFilled(F)` to test whether the field has an evaluation value.

> **Non-normative implementation note.** Separate whether an operand is evaluated from the provenance the later polarity calculation needs ([§12](10-validation-and-polarity.md)):
> ```lean
> inductive OperandRead (Provenance : Type) where
>   | value (v : Value) (provenance : Provenance)
>   | notEvaluated                       -- string/date/bool/enum empty ⇒ the comparison yields notFired
> ```
> Then a comparison over any `notEvaluated` operand short-circuits to not fired. Give each consumer the provenance shape stated above rather than one universal `given` bit.

Sources: [shared String expressions](../docs/sources/evaluation-and-application-routes.md#src-string-expression-family), [negation pair grid](../docs/sources/evaluation-and-application-routes.md#src-negation-pair-grid), [inbound 2026-10-27](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-27).

### A.2 Where an operator overrides its kind's default

**The per-kind table is only the default.** An operator may route an empty operand through its own door, so the *same* empty field gets the free pass in one position and is evaluated in the next. Every operator reads an empty operand by exactly one of the classes below; the [operator reference](14-operator-reference.md#empty-read) assigns each operator its class in column N, per operand slot where its slots differ.

<a id="the-empty-read-classes"></a>

| Class | An empty operand or cell… |
|---|---|
| `kind default` | reads the default of A.1: Number the fillable `0`, Confirm `False`, the other primitive kinds not evaluated, which leaves the enclosing comparison not evaluated |
| `presence` | is the condition the predicate tests: an empty field is not filled ([§1 A.4](02-logic-and-formal-errors.md#a4-fill-quantifiers-group-scopes-and-the-two-iteration-ranges)), and a group without admitted content is not filled ([§9 §5.1](07-repetition-and-iteration.md#51-group-presence)) |
| `empty text` | contributes the empty text `""` to its String expression, which is evaluated; the result then meets A.1's String rule as a comparison operand and the root-store rule of [§11 §2](09-computations.md#2-separate-operations-and-the-three-outcomes) as a computed result |
| `fillable zero` | reads the Number `0` with missing provenance and is evaluated, so the enclosing comparison can fire; [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing) gives its directions |
| `not evaluated` | makes the predicate fire in neither polarity |
| `value-list` | supplies no value to the membership test: [§8 B.3](06-strings-and-enumerations.md#b3-the-value-list-quantifiers--per-cell-three-way-classification-) and [§8 B.4](06-strings-and-enumerations.md#b4-scalar-membership-is-a-singleton-specialization-not-boolean-negation-) classify each cell |
| `not counted` | is never counted, and leaves the count growable while it has headroom |
| `skipped` | takes no part in the fold, scan or compared set; a selection left with no value yields the all-empty identity of A.3 |
| `incomplete` | leaves the construction incomplete, with the consequences [§6 §3.5](05-dates-and-time.md#35-reasons-and-their-composition) and [§6 §3.6](05-dates-and-time.md#36-valid-and-invalid-over-date) state |
| `no value` | makes the result valueless with its not-given reason: a consumer reads it as an empty operand of the result's kind, and a computation yields a clean no value ([§11 §2](09-computations.md#2-separate-operations-and-the-three-outcomes)) |
| `key row` | takes part in [§9 §6.2](07-repetition-and-iteration.md#62-the-duplicate-relation)'s duplicate relation: an all-empty key row is skipped, and among participants an empty key component matches an empty one |
| `callback` | reaches the callback as the data view of [§14 B.3](11-messages-and-custom.md#b3-the-invocation) presents it |
| `n/a` | — the operator reads no cell |

The classes that deviate from the kind default carry these rules:

- **`empty text`.** An empty part of a `+` concatenation concatenates as `""`, so the enclosing comparison **is** evaluated: `[Full] != [First] + " " + [Last]` mis-fires on empty parts unless guarded. `RangeAsString` over an empty source yields the empty text ([§11 §1](09-computations.md#1-the-ground-rules)), and `FieldValueAsString` contributes `""` inside a concatenation ([§11 §2](09-computations.md#2-separate-operations-and-the-three-outcomes)).
- **`fillable zero`.** `Length(F)` reads length **`0`**, evaluated — the String family's own empty-as-`0` backdoor, which needs a `FieldFilled` guard like a number. The Date and Time extractors (`DayFromDate`, …) and the differences read the fillable **`0`**, in validation and in computation alike, so the enclosing comparison is evaluated and can fire ([§6 §2.1](05-dates-and-time.md#21-what-the-operations-produce)). `RangeAsNumber` and `FieldValueAsNumber` over a missing source yield `0` ([§5 §4.5](04-numbers-and-decimals.md#45-number-valued-sources)), and a `SumOfProducts` empty cell supplies `0` with its own declaration's missingness ([§9 §3.8](07-repetition-and-iteration.md#38-sumofproducts)).
- **`not evaluated`.** `PatternMatched` and `PatternViolated` are not evaluated on an empty operand for a nonempty pattern source; an [empty authored pattern](06-strings-and-enumerations.md#pattern-admission-and-execution) instead fails when reached. Test absence with `FieldNotFilled`. `Valid` and `Invalid` over a named type fire for neither polarity on an empty operand ([§6 §3.7](05-dates-and-time.md#37-valid-and-invalid-over-a-named-type)), and `AtLeastOneDateRangeOverlaps` over an empty scalar does not fire ([§6 §8.6](05-dates-and-time.md#86-overlap-evaluation)).
- **`value-list`.** An empty subject makes neither the "included" nor the "not-included" form fire. An empty numeric list *entry* never matches: the `0` substitution does not apply to entries.

#### The count family

**A cell count never counts an empty cell.** The cell counts are `NumberOfFilledFields`, `NumberOfValueInFields` and `NumberOfDifferentValues`; `NumberOfFilledGroups` reads group presence instead ([§1 A.4.8](02-logic-and-formal-errors.md#a48-numberoffilledgroups)). `NumberOfValueInFields(0 In …)` does *not* count an empty number as a match for `0`. A fired comparison over a count is typed by [§12 §4's counts and headroom](10-validation-and-polarity.md#counts-and-headroom).

- **An all-empty operand list still counts `0`** and compares normally.
- **A formally invalid operand makes a cell count unavailable** rather than being skipped or counted as filled, so no comparison against it fires; column V of the [operator reference](14-operator-reference.md#unavailable-read-in-validation) gives each count's class. Emptiness and invalidity are therefore not one state here. Measured on `NumberOfFilledFields`: a filled cell beside an invalid one fired none of three rules comparing the count to `0`, `1` and `2`. `NumberOfDifferentValues` is unavailable over an invalid cell too: as for `NumberOfFilledFields`, an `Or` beside a true part still fires while an `And` with a true part stays silent ([§3 B.2](02-logic-and-formal-errors.md#b2-the-three-cell-states--the-third-one-is-not-empty)). `NumberOfValueInFields`' invalid read is unmeasured.
- **A fixed group operand expands to its fields** for both `NumberOfValueInFields` and `NumberOfFilledFields`, recursively, as [§1 A.4.1](02-logic-and-formal-errors.md#a41-operand-expansion) states. The count's headroom is read over that expansion ([§12 §4](10-validation-and-polarity.md#counts-and-headroom)). Reading the valueless group path itself as one empty cell is not equivalent. A field held only in a nested non-repeatable subgroup below the fixed group operand is counted as a direct field is, measured for both counts.

#### Operand-list `Min`/`Max` against the aggregates

**The operand-list `Min([A],[B])` / `Max(…)` read an empty operand by its kind.** An empty **NUMBER** operand is substituted `0` and **competes in the fold**, so the `0` can win; an empty **DATE**, **TIME** or full-component **DATETIME** operand is **skipped**, so the temporal-value-bearing side wins.

**The field-list and starred aggregates `Sum` / `MaxValue` / `MinValue` drop the empty cell from the fold**: `MaxValue(-5, empty)` is `-5`, with no `0` folded in. `Sum` reads it as `0`, which for a sum is the same thing.

These two rules are one design split seen from both sides: `0` is `Sum`'s neutral element but not min/max's, which is *why* the aggregates must drop empties where `Sum` may fold them.

Measured scope: the classes rest on the clauses each bullet names; [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing) records which of their typings are measured, and the String expression grid measures `empty text` on concatenation, `RangeAsString` and Number `FieldValueAsString`.

Sources: [shared String expressions](../docs/sources/evaluation-and-application-routes.md#src-string-expression-family), [inbound 2026-10-27](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-27).

### A.3 What an all-empty selection folds to (the aggregate identities)

"One operand empty" (A.2) and "the *whole* selection empty" are different questions. **Each aggregate has a defined identity for the all-empty case**, which applies wherever the rule is evaluated at all: inside an instance that holds other content, or one the gate of A.4 admits.

| Consumer | All-empty result |
|---|---|
| NUMBER `Sum`, `MaxValue`, `MinValue` | the both-directionally fillable `0`, not "undefined": when no present value entered the fold, the identity can grow and shrink regardless of field signedness or which of the three aggregates it is. The ordinary per-combiner directions apply only after at least one present value has entered the fold |
| DATE, TIME and full-component DATETIME `MinValue`/`MaxValue` and operand-list `Min`/`Max` | *no value*: a comparison against it never fires, and a *computation* of it CLEARS its target |
| `FirstFilledValue` | follows its result *kind*: an all-empty NUMBER selection yields the fillable `0`; BOOLEAN, CUSTOM, STRING, ENUMERATION, DATE, DATE_FRAGMENT, TIME, full-component DATETIME and DATE_RANGE yield *no value* (NOT-GIVEN), so a computation clears its target |
| the counts | `0`, compared normally (A.2) |

Thus, in an instance holding other content, `MaxValue(A,B) == 0` fires with both empty, `MinValue(Items*/Count) == 0` fires on a group with *no rows at all*, and `Sum` over an all-empty list is likewise `0`. A selection that a `Having` filter or the capacity projection has emptied folds to the same identity ([§9 §3.3](07-repetition-and-iteration.md#33-selection-what-a-filter-keeps), [§9 §4.3](07-repetition-and-iteration.md#43-capacity-rows-beyond-the-declared-repeatability)). `FirstFilledValue`'s operand admission and scan are [§9 §3.5](07-repetition-and-iteration.md#35-entity-list-operand-admission) and [§9 §3.7](07-repetition-and-iteration.md#37-group-operands-and-first-filled-selection-at-evaluation)'s, and its prefix provenance is [§12 §4.1](10-validation-and-polarity.md#41-the-same-rule-fires-either-type)'s.

⚠ This identity is treacherous because it hides under most thresholds: `0` and "not evaluated" produce the *same* non-fire for `MaxValue(…) > 3`, so a wrong mental model survives every such rule and only surfaces where `0` itself satisfies the comparison — `MinValue(…) < 10` is the shape that finally distinguishes them.

### A.4 The row gate — where the substitutions stop

**Under full validation, a rule is evaluated at an instance without content only when it can fire there.** Everything in A.1–A.3 happens inside a content-bearing instance. At an instance without content a rule is evaluated only when one of these holds; otherwise it is not evaluated there and stays silent:

1. its condition **can fire on empty**, by the structural predicate below;
2. a comparison in its condition holds a **lifting count on its small side**;
3. the rule has one of the [rule shapes that skip the gate](#rule-shapes-that-skip-the-gate).

**What counts as content.** An **instantiated repeatable row is itself content**: a created-but-blank repeat row *is* evaluated, so per-row empty-as-`0` fires on every such row. A non-repeatable group's bare structural presence is *not* content. The root instances a rule is dispatched to are [§9 §1.3](07-repetition-and-iteration.md#13-evaluation-domains)'s.

**A comparison of field reads alone within one root never fires on a truly blank instance**, so the empty-as-`0` readings of A.1 and A.2 presuppose some sibling content: `[W] < 5` stays silent over a blank root.

#### The structural predicate

**Every condition leaf either can fire on empty or is content only, and the connectives compose it:** an `And` can fire on empty when both its parts can, an `Or` when either part can. Column B of the [operator reference](14-operator-reference.md#content-gate) assigns each leaf its class.

- Measured `fires on empty` members, each firing over a blank root: `FieldNotFilled`, `NoFieldFilled`, `NotAllFieldsFilled`, `NotExactlyOneFieldFilled`, `GroupNotFilled`, `NoGroupFilled`, `NotAllGroupsFilled`, `NoFieldValueIncludedInValueList` and `Invalid` over `Date(...)`. A [`CustomCondition`](11-messages-and-custom.md#b3-the-invocation) leaf can fire on empty because its hidden dependencies are not represented in the condition.
- Measured composition: an `Or` with one part that can fire on empty can fire on empty (`AllFieldsFilled(…) Or NoFieldFilled(…)`, `FieldNotFilled(…) Or FieldFilled(…)`). An `And` of two parts that can fire on empty can fire on empty (`FieldNotFilled(Email) And FieldNotFilled(Note)` fires over a blank document, its root absent or present and empty), while an `And` with a content-only part cannot (`[Email] == "e" And FieldNotFilled(Note)` stays silent there and fires once `Email` holds `e`).
- Every other leaf is content only; the field-read comparison above is the measured case, and the other content-only assignments are unmeasured.

#### Counts lift the gate without composing

**A comparison holding a `NumberOfFilledFields`, `NumberOfFilledGroups` or `NumberOfDifferentValues` count on its small side lifts the gate from anywhere in the condition.** The small side is the operand the comparison's error condition needs small. The count may stand at any depth inside that operand, beneath `+` or `Abs` alike. A count on the large side alone does not lift the gate.

| Comparison | Small side |
|---|---|
| `<`, `<=` | the left |
| `>`, `>=` | the right |
| `==`, `!=` | either |
| `DiffersWithToleranceRange1`, `2`, `5`, `10` | either (measured on `DiffersWithToleranceRange1`) |

**The lift does not compose:** beneath `And` beside a part that cannot fire on emptiness it still lifts the gate. Over a blank root:

| Condition | Over a blank root |
|---|---|
| `NumberOfFilledFields(A, W) < 1 And NumberOfFilledFields(A, W) >= 0` | fires |
| `NumberOfFilledFields(A, W) >= 0 And NumberOfFilledFields(A, B) >= 0` | silent |
| `NumberOfFilledGroups(G1, G2) < 2` | fires |
| `NumberOfFilledGroups(G1, G2) + [W] < 2` | fires, reading its empty `W` as `0` |
| `2 > NumberOfFilledGroups(G1, G2) + [W]`, `… != 1`, `Abs(…) < 2` | fire |
| `1 >= NumberOfFilledFields(A, W)`, `NumberOfFilledFields(A, W) <= 1` | fire |
| `NumberOfFilledGroups(G1, G2) + [W] >= 0`, `0 <= …` | silent |

Measured on fixed operands, one root, connectives one level deep and Number operands of `NumberOfDifferentValues`. A tolerance comparison lifts the gate with a `NumberOfFilledFields` count on either side, measured on `DiffersWithToleranceRange1`, where the same comparison over a field read and `+` stays silent over a blank root. A starred count and the root-group count are unmeasured. Every other operand, `NumberOfValueInFields` included, does not lift the gate (unmeasured beyond field reads and `+`).

#### Rule shapes that skip the gate

Two rule shapes skip the gate whatever their condition:

- **A rule reading a second root** is evaluated without content: `[/Other/O] + [W] < 5` fires on every measured document.
- **A rule that does not iterate the repeatable root holding its error field** fires once, at that root's first row ([§9 §1](07-repetition-and-iteration.md#1-when-a-rule-iterates-and-where-its-error-lands)): `Sum(/Rep*/P) < 5` reporting on `P` fires on a blank document too.

#### Where the gate does not apply

Partial validation overrides the gate entirely: a *relevant* instance is always evaluated, even empty or phantom ([§12 §5.2](10-validation-and-polarity.md#52-which-rules-run-and-where)). The gate is validation's: a computation precondition has none ([§11](09-computations.md#5-where-a-computation-runs--scope-and-the-parallel-join)).

#### The content-gate classes

| Class | Kind | Meaning |
|---|---|---|
| `fires on empty` | condition leaf | can hold at an instance without content; composes through `And`/`Or` |
| `content only` | condition leaf | does not let the rule run without content by itself |
| `small-side lift` | comparison | content only, and lifts the gate from the whole condition when a `lifting count` stands on its small side |
| `either-side lift` | comparison | as `small-side lift`, with either operand the small side (measured on `DiffersWithToleranceRange1`) |
| `lifting count` | operand | lifts the gate from a comparison's small side |
| `no lift` | operand or operation | never lifts the gate; a `lifting count` beneath it still lifts |
| `n/a` | — | a connective, which composes its parts as above, or an operator with no admitted witness |

> **Non-normative implementation note.** The row gate is easy to miss and produces "fires on a blank document" bugs. Evaluate a rule at an instance under full validation when `hasContent(instance) ∨ firesOnEmpty(cond) ∨ smallSideCount(cond) ∨ skipsGate(rule)`, where `firesOnEmpty` is the leaf class folded with `∧` for `And` and `∨` for `Or`, `smallSideCount` is tested over the whole condition, never through the connectives, and `skipsGate` recognizes the two rule shapes above. Treat an instantiated repeatable row as `hasContent := true` by construction. This eligibility says only that a `CustomCondition` callback may be reached; its supplied relevance and formal-invalid context still decide what it returns.

Sources: [group-count gate](../docs/sources/group-list-and-capacity-probes.md#src-group-count-empty-gate), [rule-bucket gate](../docs/sources/group-list-and-capacity-probes.md#src-rule-bucket-empty-gate), [count beneath `And`](../docs/sources/group-list-and-capacity-probes.md#src-empty-gate-count-beneath-and), [inbound 2026-10-02 rule buckets](../docs/sources/inbound-handbacks.md#inbound-2026-10-02-rule-buckets), [negation pair grid](../docs/sources/evaluation-and-application-routes.md#src-negation-pair-grid), [negation pair supplement](../docs/sources/evaluation-and-application-routes.md#src-negation-pair-supplement), [blank-root dispatch](../docs/sources/model-structure-and-declaration-probes.md#src-blank-root-dispatch-k06), [inbound 2026-10-27](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-27).

---

## Part B — §4 The "required" property

The editor's "required" checkbox is not a runtime flag you evaluate. It **expands into a generated rule** and **manifests as a formal error**. You (the reimplementer) receive the generated rule; model it, not a checkbox.

### B.1 The generated rule, precisely

The checkbox expands into an **auto-generated rule** — conventionally named `vk_vk<field>_req`, error code `mandatoryField`, severity **ERROR**, message type **OMISSION** — whose condition is decided by the field's lowest repeatable ancestor:

| Field situation | Generated condition |
|---|---|
| absolutely required, no repeatable ancestor | `FieldNotFilled(field)` — **unconditional** (fires even on an un-instantiated document) |
| under a repeatable ancestor `R` | `GroupFilled(R) And FieldNotFilled(field)` — per instantiated row |
| "Parent-filled = yes" option | `GroupFilled(parent) And FieldNotFilled(field)` |

The **"Only if the Parent Group is filled"** option changes *which* group is referenced: the field's direct parent group instead of its lowest repeatable ancestor. For a field directly below a root group the parent is that root group (unmeasured). For a nested field the referenced group differs between the two modes. In this fixture `A` is a non-repeatable group with no repeatable ancestor, and `K` is a non-repeatable group nested in the repeatable group `C`:

| Field (location) | Parent-filled = **no** | Parent-filled = **yes** |
|---|---|---|
| `F1` (in group `A`) | `FieldNotFilled(F1)` | `GroupFilled(A) And FieldNotFilled(F1)` |
| `F5` (in group `K`, nested in the repeatable `C`) | `GroupFilled(C) And FieldNotFilled(F5)` | `GroupFilled(K) And FieldNotFilled(F5)` |

"The parent is filled" uses the *same formally admitted content* notion as `GroupFilled` ([§9 §5.1](07-repetition-and-iteration.md#51-group-presence)): a **repeatable** parent counts a created-but-empty row, so a conditionally required field can flag a row the user added but left blank; a **non-repeatable** parent counts a formally admitted valued descendant or an instantiated repeatable descendant row. A malformed, custom-invalid or constraint-invalid value that formal conversion rejects is not content and therefore does not activate an empty required sibling. A duplicate index value does activate it, because the value is admitted before uniqueness marks the error; creating an over-limit repeat row likewise supplies structural ancestor content even though that row receives its separate structural diagnostic and ordinary-rule suppression.

**Iteration and relevance of the generated rule.** The rule runs once per **instantiated, in-capacity** row of the field's own repeatable scope: a repeatable group with no rows draws no `mandatoryField`, declared-but-uninstantiated rows draw none although authored rules may still iterate them, and an over-capacity row draws none. Under partial validation the rule runs only where the selection covers the field itself, and its group gate reads only the selected content: a parent whose admitted content lies entirely outside the selection does not count as filled, so the parent-relative requirement does not fire and the empty field stays evaluable to authored rules. An empty selection evaluates no generated rule.

Sources: [generated requiredness](../docs/sources/model-structure-and-declaration-probes.md#src-generated-requiredness-k14).

### B.2 Required manifests as a *formal error*

A required-by-checkbox, unfilled field eventually produces a **formal error** — so the field becomes "unknown" to authored validation rules ([§3](02-logic-and-formal-errors.md#b3-what-puts-a-cell-in-the-third-state)). That is *stronger* than the equivalent author-written `FieldNotFilled(F)`, which leaves the field evaluable. The required-and-empty "unknown" is branch-scoped like any formal error: `[ReqNum] < 100` is suppressed, but `[ReqNum] < 100 Or <VALUE-true>` still fires.

**The generated rule and the formal finding are two stages, not one eager check.** Start with the base checked cells, where the base formal check has applied only the ordinary local checks. Evaluate the generated mandatory condition against that base view and retain its `mandatoryField` hit and message. Only on a hit, and only after retaining the message, annotate the empty target cell with the validation-scoped required finding that subsequent authored rules observe. If the annotation came first, the generated rule's own `FieldNotFilled(F)` would read UNKNOWN, suppress itself, and never produce the mandatory message: requiredness would be defined by a circular self-suppression.

⚠ **The compute/validate asymmetry.** For *validation*, a required-and-empty cell is UNKNOWN (a formal error). For *computation*, the same cell reads as **plainly empty** (a number reads `0`) — compute does not treat "required" as invalidity. This asymmetry is load-bearing in [§11](09-computations.md).

### B.3 The "mandatory" star is a heuristic, not ground truth

Some UIs show a star for mandatory fields, computed by a fixed "star method" that inspects a fixed set of constructs. **Starred fields are always mandatory, but not every mandatory field is starred** — deciding mandatoriness in general is not effectively decidable. A missing star therefore does **not** imply optional. This is a UI concern: a reimplementation of *evaluation* can ignore the star entirely, since only the generated rule matters.

### B.4 The index field's auto-generated checks — mandatory *and* unique

**A repeatable group's `indexFieldName` arms two automatic checks, with no authored rule:**

- the index field is **auto-required** (parent-filled semantics), drawing `mandatoryField` on an empty index cell;
- its values are auto-checked for **uniqueness**: the engine emits `uniqueIndex` on **every** row whose non-empty index value duplicates another's (*not* all-but-first), scoped **per parent row**, as a **VALUE** error. An empty index value is *excluded* from the uniqueness check and draws `mandatoryField` instead.

A non-repeatable group may also nominate an index field; that nomination is admitted, and a message's `index(...)` parameter reads it ([§13 A.9](11-messages-and-custom.md#a9-the-index-terminal)). It arms the mandatory check and not the uniqueness check. An empty nominated field in a present non-repeatable group draws `mandatoryField`, OMISSION, at that field, measured on a group directly under the root and on one inside a repeatable group, each holding only another field; where that inner group is absent nothing is drawn. Two such inner groups in different rows of the enclosing repeatable group carrying one key value draw nothing. The same documents without the nominations draw nothing. Whether the empty nominated field then enters the third state for authored rules is unmeasured.

**A duplicate-flagged cell enters the third state ([§3](02-logic-and-formal-errors.md#b3-what-puts-a-cell-in-the-third-state)) field-locally.**

- In validation, rules reading *that* field on those rows are suppressed (UNKNOWN, branch-scoped), while a sibling field's rules on the same rows still fire; and an aggregate or count over a starred index column carrying any duplicated or mandatory-empty cell is non-evaluable.
- In computation, a reached read of the duplicate cell poisons ([§11 §3.2](09-computations.md#32-an-invalidity-clear-poisons)), and a semantic-index read is column-strict: any duplicated, malformed or empty cell in the index column clears every computation reading that column ([§11 §5.4](09-computations.md#54-parallel-joins)).

Because the engine generates both checks, a model must **not** also author the equivalent rules — they would double up. The index field is also the join key for parallel iteration and the semantic index ([§9](07-repetition-and-iteration.md#2-parallel-iteration--joining-two-repeatable-groups-by-key)).

**Index and sort nomination admission** — how an index or sort nomination is bound and which class it draws — is [data model §1.3](01-data-model.md#index-and-sort-nomination-admission)'s.

> **Non-normative implementation note.** Treat "required" and "index field" as *desugaring passes* over the model that emit ordinary generated rules **plus** staged checked-cell annotations from [§3 B.3](02-logic-and-formal-errors.md#b3-what-puts-a-cell-in-the-third-state). A `required` flag emits a `mandatoryField` rule with the ancestor-decided condition. Validation evaluates that rule on the base checked cells, derives the referenced group's admitted-content, error and relevance state, retains any hit and message, and only on a hit adds the required finding to the empty target for authored-rule observation; computation ignores this validation-scoped annotation. An `indexFieldName` emits the mandatory rule and the per-parent-row uniqueness check, marking *all* duplicate participants not check-relevant, and registers the join key. Desugaring keeps the evaluator's core small and mirrors how the engine treats these as generated, not special-cased.

Sources: [inbound 2026-09-27a index and sort lookup](../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-index-and-sort-lookup), [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), [inbound 2026-10-27](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-27).

---

## Checklist for §2 + §4

- [ ] Operand reads separate "not evaluated" from evaluated substitutions and carry consumer-appropriate provenance: a not-given bit only for symmetric consumers such as Confirm, directional `canGrow`/`canShrink` where [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing) requires it.
- [ ] The primitive default tier is exactly Number→`0`, Confirm→`False`, and Boolean/String/Enumeration/Date/Time/DateTime→not evaluated; other type families and operator deviations remain explicit clauses.
- [ ] A String comparison operand whose value is the empty text, an all-empty concatenation included, is not evaluated for `==` and `!=`.
- [ ] Each operator reads an empty operand by its column N class of the [operator reference](14-operator-reference.md#empty-read), as A.2 defines the classes.
- [ ] Counts never count an empty cell, stay growable while headroom remains and type by §12 §4's headroom table; a formally invalid operand makes the count unavailable.
- [ ] All-empty aggregate **identities** per kind (NUMBER→`0`, DATE/TIME/DATETIME min/max→no value; `FirstFilledValue` NUMBER→`0` and every other admitted result kind→no value), the same for a filter- or capacity-emptied selection.
- [ ] The **row gate**: substitutions only inside content-bearing instances; instantiated repeatable rows *are* content; a rule runs without content when its leaves compose to `fires on empty` under `And`/`Or`, when a lifting count stands on a comparison's small side anywhere in the condition, when it reads a second root, or when it does not iterate the repeatable root holding its error field.
- [ ] `required` desugars to the ancestor-decided generated rule; its group gate uses formally admitted content rather than raw placement, validation retains the message on base checked cells before adding the target's validation-scoped required finding, and computation reads the cell empty.
- [ ] A repeatable group's `indexFieldName` desugars to mandatory + per-parent-row uniqueness (every duplicate flagged) and registers the join key; a duplicate cell is UNKNOWN in validation and poisons a computation read.
