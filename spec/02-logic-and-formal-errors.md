# 02 — Logic, truth values, and the "unknown" state (§1 + §3)

This chapter owns the evaluation model every later chapter builds on. Two mechanisms interlock:

- **§1 — truth and connectives.** A condition evaluates to TRUE, FALSE or UNKNOWN. `And` and `Or` are strong-Kleene connectives, the language has no generic negation, and mixing the two connectives needs explicit brackets.
- **§3 — the third cell state.** A cell carrying a formal finding is neither filled nor empty. Validation reads it as UNKNOWN; computation reads it as poison.

UNKNOWN never originates in a connective: it enters only when an operand reads a third-state cell or another UNKNOWN source, and the strong-Kleene tables decide how far it reaches. A two-state, `Option`-style cell value cannot express this language.

---

## Part A — §1 Truth values and logical evaluation

<a id="a1-connectives-are-two-valued-parentheses-are-mandatory"></a>
### A.1 Connectives and mandatory parentheses

**Rule.** `And` and `Or` are the only connectives. Neither has precedence over the other: mixing them without brackets is a parse error, `MVK_BRACKET_MISSING`, not a default grouping.

```
( FieldFilled(A) And [A] <= 0 ) Or FieldNotFilled(B)      -- ok
FieldFilled(A) And [A] <= 0 Or FieldNotFilled(B)          -- rejected at parse time
```

The two bracketings mean different things, so a parser rejects the unbracketed mix rather than picking a precedence.

**The connectives introduce no truth value of their own.** Their truth tables are the strong-Kleene tables of [B.5](#b5-the-strong-kleene-tables-the-exact-algebra) over TRUE, FALSE and UNKNOWN; the third value comes only from operands. A validation condition's result is one of four verdicts: not fired, fired VALUE, fired OMISSION, or UNKNOWN. Its truth component follows B.5. Its message type follows two combination rules owned by [§12](10-validation-and-polarity.md#3-every-fired-message-is-typed--value-vs-omission-): under `And` OMISSION wins among fired operands, and under `Or` VALUE wins.

**FALSE and UNKNOWN are indistinguishable through any composed rule.** A rule emits a message exactly when its verdict is fired. Because the language has no negation, `And` and `Or` absorb a not-fired operand and an UNKNOWN operand identically: replacing UNKNOWN by not-fired in any leaf never changes whether, or with which type, the whole condition fires. No document can therefore separate two accounts of a leaf that differ only between FALSE and UNKNOWN; only an account difference that changes a fired result is observable.

### A.2 There is no `Not`

**Rule.** The language has no generic negation operator. Every negative check is a dedicated predicate with its own evaluation clause, so negation over UNKNOWN never needs to be defined.

**Positive/negative predicate pairs are not always complements.** `NotP ≡ ¬P` cannot be assumed:

| Predicate | Holds when |
|---|---|
| `NotAllFieldsFilled(L)` (paired with `AllFieldsFilled(L)`) | at least one field is unspecified, including when none is filled |
| `FieldsNotCollectivelyFilled(L)` | at least one but not all are filled; it excludes the all-empty case, so it is not the negation of "all filled" |
| `NotExactlyOneFieldFilled(A, B, C)` | 0 filled and 2+ filled |

```
NotExactlyOneFieldFilled(A, B, C)   -- satisfied at 0 filled AND at 2+ filled
```

Over a third-state cell both members of a pair can be UNKNOWN ([A.4](#a4-fill-quantifiers-group-scopes-and-the-two-iteration-ranges), [B.2](#b2-the-three-cell-states--the-third-one-is-not-empty)).

> **Non-normative implementation note.** Do not model predicates as `p` and `Not p`. Give each predicate its own constructor and evaluation clause, and treat the non-complementary pairs as distinct predicates that happen to read related. No negation combinator is needed, which avoids choosing a negation for UNKNOWN.

### A.3 Boolean is a three-state field *type* (distinct from three-valued logic)

The **logic** carries an UNKNOWN value. Separately, the **Boolean field type** has three states: not filled, `True`, `False`.

```
[Flag] == True       -- holds iff Flag is filled AND its value is True
[Flag] == False      -- holds iff Flag is filled AND its value is False
FieldFilled(Flag)    -- holds iff Flag has any value (True or False)
```

So `[Flag] == True` is not `FieldFilled(Flag)`, and an unset Boolean satisfies neither `== True` nor `== False`. To say "not confirmed" for a Confirm field, write `[Confirm] != True`.

**Confirm and Boolean differ on the empty case.** An unspecified Confirm reads `False` in a comparison; an unspecified Boolean leaves the comparison not evaluated ([§2](03-empty-and-required.md)). Condition syntax spells the literals with a capital letter, `True`/`False` ([§12](12-concrete-syntax.md)).

**Stored tokens.** The storage tier and the formal check use exact lowercase tokens, after one reader step:

1. The document reader maps a stored token that equals `true` or `false` under Java's `equalsIgnoreCase` (JDK 21) onto that exact token. So `TRUE` and `tRuE` read as true, and `fal` + U+017F + `e`, whose long s folds onto `s`, reads as false.
2. The formal check then compares case-sensitively:

| Type | Accepted stored tokens | Every other nonempty token |
|---|---|---|
| Boolean | `true`, `false` | formal error `feldJaNeinFalsch` |
| Confirm | `true` (or unspecified) | formal error `feldJaFalsch`, `false` included, consistent with a checkbox whose only value is True |

Measured cases of the fold: a lone long s draws `feldJaNeinFalsch`, and `" true"` draws the leading-blank finding `fuehrendesBlank`. Over every JDK 21 code point (an enumeration, not a Kernel run), the long s is the only character outside ASCII that the fold matches to a letter of either word; a lone U+0130 or U+212A, which fold onto `i` and `k`, draws what a lone long s draws.

**Alternative tokens are ignored.** A model may declare an alternative `notInDCustomTrueValue` for either type and an alternative Boolean `notInDCustomFalseValue`, but validation ignores them: those declarations are `@NotInD`, and no configuration channel that carries them into the formal check is known; honouring them diverges from the Kernel.

**Do not import casing from a neighbouring layer.** A host may case-fold while ingesting a document, and comparison of an already-stored value may case-fold, but neither makes the storage formal check case-insensitive.

Sources: [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), [inbound 2026-10-22](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-22).

### A.4 Fill quantifiers: group scopes and the two iteration ranges

This section owns the **field-fill quantifiers** `AllFieldsFilled`, `NoFieldFilled`, `AtLeastOneFieldFilled`, `MoreThanOneFieldFilled`, `NotExactlyOneFieldFilled`, `NotAllFieldsFilled`, `FieldsNotCollectivelyFilled`; the **group-list quantifiers** `AllGroupsFilled`, `NoGroupFilled`, `AtLeastOneGroupFilled`, `NotAllGroupsFilled`, `GroupsNotCollectivelyFilled`; the count `NumberOfFilledGroups`; and the operand slot of `FieldFilled`/`FieldNotFilled`. The general mechanism is the same for all of them: expand the operands into a slot stream (A.4.1) over a range (A.4.2), classify each slot (A.4.3), and decide from the classification, by an unordered tally in validation and by an ordered scan in computation.

#### A.4.1 Operand expansion

**A group operand means every field inside it, recursively.** A field-fill quantifier over a group expands to the quantifier over every descendant field, through nested subgroups. A repeatable group in the operand carries its `*` onto each descendant. A mixed group-and-field operand list is legal. Value aggregates (`Sum`, `MinValue`, `MaxValue`, `NumberOfDifferentValues`) over a starred group expand the same way, and so does a group operand of `NumberOfFilledFields` or `NumberOfValueInFields`. `NumberOfFilledFields`' slot capacity multiplies through a repeatable descendant. A field held only in a nested non-repeatable subgroup of a fixed group operand is counted by either count exactly as a field held directly in it: a value only in that subgroup's field counts `1`, as a value only in the group's own field does, and an empty group counts `0`.

**The iterated repeatable group as an operand.** The repeatable group a rule iterates, named by path or as `RuleGroup`, is such an operand for `NumberOfFilledFields` and the field-fill quantifiers. It is bound at the error field's row and reads that row's own fields, its fixed descendants and each instance of a repeatable descendant, so `AllFieldsFilled(RuleGroup)` needs every declared row of that descendant. Alone, `NumberOfFilledFields(RuleGroup) < 1` and `NoFieldFilled(RuleGroup)` draw `MVK_NEG_CONDITION_IN_ITERATION`, while `NumberOfFilledFields(RuleGroup) > 0` and `AtLeastOneFieldFilled(RuleGroup)` are admitted.

**Stream order.** A bare-group field-fill quantifier expands to a field-major, repetition-major stream. Descendant fields occur in the recursive model declaration order of [§1](01-data-model.md#1-model--a-typed-tree), and one field is completed before the next. Its instantiated repetitions occur in repetition order; when the operator uses the declared range, that field's declared-but-uninstantiated repetitions follow immediately as empty slots before the next descendant field. An instantiated-range operator adds no declared omissions. Computation consumes this order through its operator-specific deciding scan (A.4.6). Validation's externally visible result is determined by the final classification counts (A.4.4); its physical read order and unread suffix are not established.

Sources: [RuleGroup field-fill checkpoint](../docs/sources/group-count-topology.md#src-rulegroup-field-fill), [nested-capacity checkpoint](../docs/sources/group-list-and-capacity-probes.md#src-filled-field-count-nested-capacity), [inbound 2026-10-27](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-27).

#### A.4.2 The two iteration ranges

A starred scope has two ranges. The **declared range** runs to the group's `repeatability`, an uninstantiated repetition reading as an empty slot. The **instantiated range** is the in-capacity instantiated rows. On a non-repeatable scope the two coincide. Each field-fill quantifier fixes its range:

| Quantifier | Range |
|---|---|
| `AllFieldsFilled`, `NotAllFieldsFilled` | declared — so `AllFieldsFilled(G*)` holds only when every declared row is filled |
| `AtLeastOneFieldFilled`, `NoFieldFilled`, `MoreThanOneFieldFilled`, `NotExactlyOneFieldFilled` | instantiated |
| `FieldsNotCollectivelyFilled` | mixed: ≥ 1 filled over the instantiated range and ≥ 1 empty over the declared range |

**The range is the operand's evaluation domain, not every cell it could address.** A cell in a row beyond its group's declared repeatability is outside both ranges ([§9](07-repetition-and-iteration.md)): it neither counts nor makes a tally unavailable. A malformed cell separates this from a classification fact: one index below capacity it makes a value aggregate non-evaluable, one index above it does not.

> **Non-normative implementation note.** Declared versus instantiated range is a semantic fork, not an optimisation; encode both. Give a repeatable group both its `repeatability` and its actual row count, and let each quantifier state which range it folds over: `AllFieldsFilled` over the 1-based `1 .. repeatability` (missing rows empty), `AtLeastOneFieldFilled` over `1 .. rowCount` (empty when `rowCount = 0`).

#### A.4.3 Classifying a slot

Each slot in the range is classified once:

| Slot | Validation | Computation |
|---|---|---|
| a formally valid value | FILLED — even without a concrete scalar projection, so a valid `DAY_OPTIONAL` value with an omitted day is FILLED | filled |
| a clean empty cell | EMPTY | empty |
| a declared-but-uninstantiated slot (declared range only) | an omission `d`, which the declared-range firing conditions treat like EMPTY | a clean declared absence, not a value read |
| a third-state cell ([B.2](#b2-the-three-cell-states--the-third-one-is-not-empty)) or a non-relevant cell under partial validation | UNAVAILABLE — neither FILLED nor EMPTY | a reached third-state slot poisons the computation instance |

**An unavailable member stays in the list and settles nothing.** It is not dropped from the operand list, counted filled, or counted empty. A fill quantifier is therefore decided exactly when the members whose state is known already settle it: a known filled member settles an existential, a known empty member settles a negation, and only a verdict that needs the unavailable member's own state stays undecided. `NumberOfFilledFields` is not a quantifier in this sense: it is an all-cells consumer and is UNKNOWN whenever a member is unavailable ([B.2](#b2-the-three-cell-states--the-third-one-is-not-empty)). Over a three-member list with one malformed member and two filled, `AtLeastOneFieldFilled` fires while `AllFieldsFilled`, `NotAllFieldsFilled`, `NumberOfFilledFields == 3` and `== 2` all stay silent; with the other two empty instead, `NotAllFieldsFilled` fires and the existential is silent. Dropping the member would fire the universal, counting it filled would satisfy `== 3`, and counting it empty would fire the negation and `== 2`; none occurs. Measured on a malformed Number and an out-of-calendar Date.

Sources: [erroneous-member checkpoint](../docs/sources/inbound-group-operand-batches.md#src-erroneous-member-quantifier-undecidable).

#### A.4.4 Validation: the unfiltered field-fill tally

For unfiltered validation, let `t` be the number of known FILLED instantiated cells, `e` the known EMPTY instantiated cells, `u` the UNAVAILABLE instantiated cells (formally invalid or non-relevant), and `d` the declared-but-uninstantiated omissions. The leaf exposes only `TRUE_WF` (VALUE), `TRUE_AF` (OMISSION), or the single collapsed `FALSE_OR_UNKNOWN`; the Kernel-visible result does not distinguish hidden false from unknown ([A.1](#a1-connectives-are-two-valued-parentheses-are-mandatory)).

| Validation predicate | Range | Fires when | Unfiltered polarity |
|---|---|---|---|
| `AllFieldsFilled` | declared | `e = 0 ∧ u = 0 ∧ d = 0` | VALUE |
| `NoFieldFilled` | instantiated | `t = 0 ∧ u = 0` | OMISSION |
| `AtLeastOneFieldFilled` | instantiated | `t ≥ 1` | VALUE |
| `MoreThanOneFieldFilled` | instantiated | `t ≥ 2` | VALUE |
| `NotAllFieldsFilled` | declared | `e + d ≥ 1` | OMISSION |
| `NotExactlyOneFieldFilled` | instantiated | `(t = 0 ∧ u = 0) ∨ t ≥ 2` | OMISSION in the zero-filled region; VALUE in the at-least-two region |
| `FieldsNotCollectivelyFilled` | instantiated fill plus declared empty | `t ≥ 1 ∧ e + d ≥ 1` | OMISSION |

Empty-row eligibility is a separate whole-condition gate ([§2](03-empty-and-required.md#a4-the-row-gate--where-the-substitutions-stop)), and `Having` can change both the selected range and the firing polarity (A.4.5), so neither is part of this table.

#### A.4.5 Validation: filtered field-fill lists

**Rule.** A filtered operand applies its filter to the range its predicate asks for, and only a TRUE filter result keeps a slot. Operand order is retained.

- In a **declared-range** predicate the filter is also evaluated at missing declared coordinates, where absent fields read empty without creating rows; a kept missing slot contributes an omission.
- In an **instantiated-range** predicate a missing coordinate never enters the tally, whatever the filter would answer there. Whether the filter is nevertheless executed at such a coordinate, which matters only for a filter whose evaluation can fail at runtime, follows the traversal extent of [§9 §3.9](07-repetition-and-iteration.md#39-filter-traversal).

Measured cases, with `Rows` of maximum 2 and only its first row filled: `AllFieldsFilled(Rows*/R Having CurrentRepetition(Rows) == 1)` fires, while replacing `== 1` by `> 0` keeps the missing second slot selected and prevents it. A value filter `[Rows/R] > 0` drops that missing slot. With no rows, the coordinate-selected first slot remains missing, while the value-selected range is empty and `AllFieldsFilled` fires vacuously. A malformed selected Number remains UNAVAILABLE, suppressing `NoFieldFilled`; a filter that drops it removes it from the range. Measured on one finite repeatable level; nested and unbounded declared-range selection are unmeasured.

Over the selected ranges the firing conditions of A.4.4 apply unchanged. Polarity keeps track of which authored operands supplied the deciding filled witnesses:

| Filtered or mixed field-fill predicate | Polarity when it fires |
|---|---|
| `AllFieldsFilled` | OMISSION if any operand carries a filter, including a filter selecting nothing; otherwise VALUE |
| `AtLeastOneFieldFilled` | the first operand supplying a known filled cell decides: OMISSION if it is filtered, otherwise VALUE |
| `MoreThanOneFieldFilled` | OMISSION if either of the first two known filled witnesses comes from a filtered operand; otherwise VALUE |
| `NotExactlyOneFieldFilled` | OMISSION in the zero-filled, no-unavailable region; otherwise the deciding-two rule of `MoreThanOneFieldFilled` |
| `NoFieldFilled`, `NotAllFieldsFilled`, `FieldsNotCollectivelyFilled` | OMISSION |

A filtered operand with no filled witness cannot change a positive threshold's polarity, nor can an operand after the decision. Swapping a filled direct operand with a filled filtered operand can therefore change `AtLeastOneFieldFilled` from VALUE to OMISSION without changing whether it fires.

**Partial validation skips every rule carrying a filter** before any other admission step; [§12](10-validation-and-polarity.md#5-full-vs-partial-validation) owns that ordered admission.

Sources: [filtered field-fill grid](../docs/sources/group-list-and-capacity-probes.md#src-filtered-field-fill-ranges).

#### A.4.6 Computation: ordered field-fill scans

Computation evaluates each quantifier as an ordered scan over the canonical slot stream of A.4.1. A declared-but-uninstantiated slot is a clean declared absence, not a value read.

| Computation predicate | Ordered decision |
|---|---|
| `AllFieldsFilled` | Scan the declared range; first empty or uninstantiated slot → not true; exhaustion → holds. |
| `NotAllFieldsFilled` | Scan the declared range; first empty or uninstantiated slot → holds; exhaustion → not true. |
| `NoFieldFilled` | Scan instantiated slots; first filled slot → not true; exhaustion → holds. |
| `AtLeastOneFieldFilled` | Scan instantiated slots; first filled slot → holds; exhaustion → not true. |
| `MoreThanOneFieldFilled` | Scan instantiated slots; second filled slot → holds; exhaustion with zero or one → not true. |
| `NotExactlyOneFieldFilled` | Run the `NoFieldFilled` decision first; if a filled slot exists, restart and run the `MoreThanOneFieldFilled` decision. Zero or at least two filled slots hold; exactly one does not. |
| `FieldsNotCollectivelyFilled` | Run the instantiated `AtLeastOneFieldFilled` decision first; if a filled slot exists, restart and run the declared-range `NotAllFieldsFilled` decision. It holds exactly when both witnesses exist. |

**Poison is read-driven.** Every reached third-state slot poisons the computation instance. Each component scan stops at its own result, but a successful first stage of either composite starts its second scan again from the beginning. Only a suffix after the full predicate's final decision is unread, and an unread slot never poisons.

**Filters in computation.** A filtered operand applies its scan's range before selecting candidates. A declared-range scan evaluates its filter at missing declared coordinates, where absent fields read empty without creating rows; an instantiated-range scan does not visit those coordinates. A coordinate filter can therefore retain missing declared slots while a positive-value filter drops them. Each component scan uses the [computation iterator's kept-successor lookahead](07-repetition-and-iteration.md#3-the-filter-having-the--correlation-and-aggregation): a reached filter failure can abort before the pending target is observed, but a deciding result leaves later filters and payloads unread. A composite starts its second range and iterator afresh, preserving authored operand order and fresh computed filter values.

Sources: [field-fill computation guard grid](../docs/sources/computation-scheduling-probes.md#src-field-fill-computation-guards).

#### A.4.7 Group-list quantifiers

**Rule.** A group-list quantifier classifies each resolved operand as definitely filled (`pₜ`), definitely empty (`pₑ`) or in neither bucket (`pᵤ`), and decides from that common tally without treating "neither" as empty. Field and group operands may be mixed:

| Operand | Contributes |
|---|---|
| a field | its checked presence: filled when it has a value, empty when cleanly empty, neither when third-state or not relevant |
| an ordinary (unstarred) group | the validation group product state of [§9](07-repetition-and-iteration.md#5-groupfilled-and-the-other-repetition-rules), not a Boolean descendant scan: definitely filled when admitted content is observed in a relevant slice; definitely empty only when the whole group is relevant, contentless and error-free; otherwise neither, unless admitted content already establishes positive presence |
| a starred repeatable group `G*` (only `NoGroupFilled`, `AtLeastOneGroupFilled`) | one definitely filled item per instantiated in-capacity row; a created-but-empty in-capacity row counts as filled group content ([§9](07-repetition-and-iteration.md)); over-limit rows and zero rows contribute nothing |
| a non-repeatable group below starred ancestors, such as `Sections*/Items*/Details` | one ordinary group-product classification per selected in-capacity ancestor environment: the stars select the `Sections`/`Items` environments and `Details` is classified independently in each. Instantiating an ancestor row does not by itself fill `Details`; admitted scalar content or an instantiated repeatable descendant does, while malformed-only content is unavailable |

The capacity boundary of the starred form is separated without a sparse row topology by two symmetric non-repeatable descendants, one populated only below an in-capacity parent row and the other only below an over-limit parent row: the first satisfies `AtLeastOneGroupFilled`, the second satisfies `NoGroupFilled`. Partial validation uses the same in-capacity rule; retained Kernel evidence covers exact-row relevance on the one-level `/Order/Lines*` carrier, selecting an in-capacity row versus an over-limit row.

| Validation predicate | Fires when | Unfiltered polarity |
|---|---|---|
| `AllGroupsFilled` | `pₑ = 0 ∧ pᵤ = 0` | VALUE |
| `NoGroupFilled` | `pₜ = 0 ∧ pᵤ = 0` | OMISSION |
| `AtLeastOneGroupFilled` | `pₜ ≥ 1` | VALUE |
| `NotAllGroupsFilled` | `pₑ ≥ 1` | OMISSION |
| `GroupsNotCollectivelyFilled` | `pₜ ≥ 1 ∧ pₑ ≥ 1` | OMISSION |

A fixed singleton operand of `NoGroupFilled` or `AtLeastOneGroupFilled` has the semantics of the corresponding scalar field or group presence predicate. Static admission of these operands is in A.4.9.

Sources: [starred group-quantifier capacity checkpoint](../docs/sources/group-list-and-capacity-probes.md#src-starred-group-quantifier-capacity).

#### A.4.8 `NumberOfFilledGroups`

**Rule.** `NumberOfFilledGroups` folds over **authored operand positions**, adding one contribution per position; it never deduplicates the groups those positions name. Two terms are kept apart below: the count's **value**, and its **extent**, the largest value the operands can reach given the declared capacities.

**Operand contributions:**

| Operand form | Validation contribution | Computation contribution |
|---|---|---|
| fixed group (one declared entity, not one per descendant) | 1 when definitely filled, 0 when definitely empty; an undecided operand makes the whole count UNKNOWN | 1 when it holds content, else 0; never UNKNOWN, never poison |
| starred repeatable group `G*` | its in-capacity instantiated row count | its in-capacity instantiated row count |
| fixed group below a starred level, such as `Batches*/Seal` | one per selected in-capacity environment whose terminal is filled — the environments, not the ancestor rows: a batch with an instantiated but empty `Seal` adds nothing, as does a batch holding only its own field | one per in-capacity environment whose terminal holds content |
| the repeatable group bound by the error field's row, written without `*` | that row's instance: zero or one, as a fixed operand | — |

**Content of a group instance is read over its whole subtree, at any depth, and has two constituents, either sufficient:** an admitted descendant cell anywhere in the subtree, or an instantiated row in a repeatable descendant at any repetition depth. Measured instances: a group owning no direct field, whose only field lies two levels down, counts when that field is filled and drops out when it is emptied, on both arms separately. One row carrying no filled cell makes the group count, and removing it drops the count. A shell whose only content is a repeatable group containing a second repeatable group counts on one instantiated leaf row with an empty cell. The outer row alone is content: a shell whose repeatable descendant holds one row with no inner row counts, whether the document omits the inner group key or writes an explicitly empty inner list, against a no-row control. On one operand owning both a non-repeatable and a repeatable descendant, the cell alone counts, the empty row alone counts, and neither does not count. Row depth is measured at two repetition levels. The scalar group predicates of [§9](07-repetition-and-iteration.md#5-groupfilled-and-the-other-repetition-rules) use the same content notion.

**Validation arm.**

- A fixed operand is read through the same definitely-filled / definitely-empty / undecided decision as the group-list tally (A.4.7). **A formal error blocks only the negative answer:** a group holding admitted content counts as filled however its other descendants failed, and only a group with no admitted content is left undecided by one. Over a filled sibling group, an operand carrying a filled cell beside a malformed one counts exactly as the clean control does, while the same operand holding only the malformed cell makes the whole count UNKNOWN rather than dropping it. Neither operand position nor an error elsewhere matters: the pair repeats on the second operand, and a malformed cell in an unreferenced group leaves the count intact. This is the rule `GroupFilled` obeys, so the count and the scalar predicate agree about an erroneous group.
- The rule concerns undecided presence, not one error channel: a group whose repeatable descendant exceeds its capacity carries a structural over-limit finding rather than a cell finding, and still counts when its content is admitted (measured against an at-capacity control).
- A starred member's rows are structural: an instantiated row counts whatever it holds, a malformed cell inside a starred row leaves that row counted and adds no unavailability, and over-limit rows remain in the complete structural topology but never increase the value.
- A fixed group below a starred level: a malformed-only instance makes the whole count UNKNOWN, beside a filled instance too, while an instance holding admitted content beside a malformed value counts. A starred repeatable operand beside it counts its rows as above. Measured on two reopened levels, one malformed Number cause, a `Seal` holding a String and a Number, two different ancestor-starred scopes in one list, over-limit rows below the starred level, and a rule placed on or below it.
- The bound group counts the error field's own row. With a filled `Box`, `NumberOfFilledGroups(Rows, Box)` is `2` at a filled `Rows` row and `1` when `Box` is empty; a fixed child of the bound group contributes its own row's instance beside a star, so `NumberOfFilledGroups(Rows/Fix, Items*)` counts `2` at the row whose `Fix` is filled beside one `Items` row and at most `1` at a row whose `Fix` is empty.
- **Coverage.** On every dimension but coverage the count reads operands as the tally does. Under partial validation it is stricter: the count needs complete relevant coverage of its operand groups' instances as [§12 §5.6](10-validation-and-polarity.md#56-group-presence-and-group-counts) walks them, where the tally's predicates decide from the content they can see. The two projections must not be collapsed.

**Computation arm.**

- **Group presence never poisons.** A fixed operand counts when any descendant cell is present, as a value or as a formally invalid stored value, or a repeatable descendant holds an instantiated row. A seeded Number target computed from `NumberOfFilledGroups(Alpha, Beta)`, where `Alpha` holds only a formally invalid cell, takes `2`, the same value as when both groups are clean and filled, while two empty groups yield `0`. The same holds for a nested invalid cell: a shell whose only field lies two levels down and holds a non-numeric value counts, the cell appears in `formalErrorsInOperands`, and the target is neither cleared nor errored; emptying the cell drops the count by one. It holds per instance below a star: a `Seal` holding only a malformed `Code` counts one.
- **A descendant made invalid by a failed computed dependency is not content.** A computed descendant that cleared or was poisoned supplies no content, so the group does not count from it; a malformed stored sibling still fills the group.
- A value-reading computation over the same malformed cell in the same run produces no value; that abort and its target clearing are owned by [§11](09-computations.md#32-an-invalidity-clear-poisons).
- A starred operand counts its in-capacity instantiated rows: no rows `0`, one wholly empty row `1`, three empty rows `3`, so the value is neither a presence bit nor a filled-row tally. Over-limit rows are excluded: a group declared `max 5` holding five, six or seven rows counts `5`, and a starred `Sum` over the same rows stops at the same five, against a four-row control. The contribution never reads a cell, so a row holding only formally invalid content counts and a repeatable descendant does not multiply it: one row holding only a malformed Number counts `1`, and one row holding three rows of a repeatable descendant counts `1`.
- A fixed group below a starred level counts one per in-capacity instance holding a value, a formally invalid value, or an instantiated repeatable-descendant row, so an instance holding only a malformed cell counts, and the third batch of an over-limit document adds nothing. With two reopened levels, `Batches*/Boxes*/BSeal` counts one per in-capacity box whose `BSeal` holds a value or a formally invalid value, excluding a box beyond its own maximum. Measured on two reopened levels and a repeatable-descendant row under one.
- Mixed and repeated positions add independently: `NumberOfFilledGroups(Fixed, G*)` is the fixed operand's zero or one plus the row count, so emptying the fixed group's only field drops the total by exactly one; three rows in one starred group beside two in another count `5`, three beside none `3`, and the same starred group named twice counts `6` over three rows.
- Scope of the invalid-counts-as-content rule: measured for cell findings in fixed operands; structural and call-local group errors and repeatable operands are unmeasured on this arm.

**Arms compared** (value-reading consumers are in [B.2](#b2-the-three-cell-states--the-third-one-is-not-empty)):

| Operand state | Validation | Computation |
|---|---|---|
| fixed, admitted content beside a malformed cell | counts 1 | counts 1 |
| fixed, malformed-only content | whole count UNKNOWN | counts 1 |
| fixed, content only from a failed computed dependency | — | counts 0 |
| starred, malformed cell in a row | row counts | row counts |
| below a star, malformed-only instance | whole count UNKNOWN | instance counts |

**Extent and polarity.** The extent is one per fixed operand plus, per starred operand, the product of the declared capacities it ranges over; two starred scopes add theirs. A starred repeatable member's capacity is its own row maximum and is not multiplied by a repeatable descendant: a starred member owning a further repeatable group counts identically to one that does not, and three rows in a `max 3` group beside one fixed member reach an extent of `1 + 3`. This is the opposite of `NumberOfFilledFields`, whose slot capacity multiplies through repeatable descendants. A fixed group below two reopened levels has the product of both maxima as its extent. The count can still grow exactly while its value is below the extent, so a `count == n` rule fires OMISSION below it and VALUE at it ([§12](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing)). One admitted descendant makes a half-filled fixed group count as given, so a two-group comparison has fixed movement once both group entities are given. Two rows in a capacity-two group exhaust the extent and make the count fixed, while one row or no rows leave it grow-only.

Sources: [unavailability checkpoint](../docs/sources/group-list-and-capacity-probes.md#src-group-count-unavailability), [ancestor-starred computation checkpoint](../docs/sources/group-list-and-capacity-probes.md#src-ancestor-starred-group-count-computation), [K22 join-count checkpoint](../docs/sources/group-count-topology.md#src-k22-join-count-membership), [nested-descendant runtime checkpoint](../docs/sources/group-and-iteration-probes.md#src-nested-descendant-group-count-runtime), [repeatable-descendant checkpoint](../docs/sources/group-and-iteration-probes.md#src-repeatable-descendant-group-count), [deep repeatable-descendant checkpoint](../docs/sources/group-and-iteration-probes.md#src-deep-repeatable-descendant-group-count), [row-domain checkpoint](../docs/sources/group-and-iteration-probes.md#src-group-count-row-domains), [starred computation checkpoint](../docs/sources/group-and-iteration-probes.md#src-starred-group-count-computation), [nested invalid checkpoint](../docs/sources/group-and-iteration-probes.md#src-nested-descendant-group-count-invalid), [group-presence computation checkpoint](../docs/sources/computation-scheduling-probes.md#src-group-presence-computation-guards), [inbound 2026-09-24](../docs/sources/inbound-handbacks.md#inbound-2026-09-24-ancestor-starred-group-count), [inbound 2026-09-24b](../docs/sources/inbound-handbacks.md#inbound-2026-09-24b-kf463-validation), [inbound 2026-10-27](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-27).

#### A.4.9 Static admission of group and field-slot operands

Admission is decided per carrier. Each carrier below has a condition table and the gate order known for it; an order not listed is unmeasured. The error field's locus is a parameter of several gates: an unstarred repeatable group is fixed when the error field's row binds its level, and draws the walk's class `MVK_NO_WILDCARD` otherwise, unless the error field's position selects another class ([§9](07-repetition-and-iteration.md#4-where-a-star-binds--the-anchor-rules-)). The locus tables are measured for one repeatable level; nested repeatable binding is unmeasured except where a row says otherwise.

**`FieldFilled` / `FieldNotFilled` operand slot.** The slot reads one field. Gates apply in this order; the first that fails decides:

| Order | Condition | Class |
|---|---|---|
| 1 | a second operand | `MVK_PARAMSIZE_INVALID1` |
| 2 | a segment's own defect, such as `Claims.*` | `MVK_POINT_IN_A12_MODEL` |
| 2 | a segment's own defect, such as `Claims/Amount*/..`, or a star on any other level that does not repeat | `MVK_INVALID_WILDCARD` |
| 2 | a starred leading up-step | `MVK_INVALID_WILDCARD_REL` |
| 3 | the walk: an unstarred repeatable group whose level the error field does not bind | the walk's class (see above) |
| 4 | the slot names a root group the walk passes | `MVK_ROOT_GROUP_REFERENCED` |
| 4 | the slot names any other group, a starred one included | `MVK_NO_GROUPS_ALLOWED` |
| 5 | a star on a field's level | `MVK_NO_WILDCARDS_ALLOWED` |

The order-2 rows answer ahead of the walk, measured on the unbound segment itself and on a later one: both examples draw their class although `Claims` is unbound. Row 4's root class is measured on a fixed root spelled `..` from the group below it, on the repeatable root a rule sits in, and on a starred repeatable root read from another root. Row 5 is measured on relative spellings from the rule group and behind an up-step, and holds inside a `Having` body too, where the unstarred spelling is admitted.

**Group-list quantifiers and `NumberOfFilledGroups`.** Columns: the multi-operand trio `AllGroupsFilled`, `NotAllGroupsFilled`, `GroupsNotCollectivelyFilled`; the singleton-admitting pair `NoGroupFilled`, `AtLeastOneGroupFilled`; scalar `GroupFilled`; and the count. "—" means the chapter states no class.

| Condition | Trio | Pair | `GroupFilled` | `NumberOfFilledGroups` |
|---|---|---|---|---|
| group path does not resolve | class of the segment that missed: `MVK_INVALID_ROOT_GROUP` for an absolute path whose first segment names no root group; `MVK_TOO_MANY_PARENT_GROUPS` for a walk above the root; `MVK_INVALID_ENTITY` for any other miss, relative paths included | same | — | same |
| a field operand | admitted | admitted | — | `MVK_NO_FIELDS_ALLOWED` |
| an operand naming a group with no field in its subtree, in any position | the empty class: `MVK_GROUP_IS_EMPTY`, or `MVK_ROOT_GROUP_IS_EMPTY` for a root ([§10](08-paths-and-references.md)) | the empty class | the empty class | the empty class, ahead of the list gates |
| fewer than two operands, the sole one ordinary | `MVK_PARAMSIZE_INVALID2` | admitted | — | `MVK_PARAMSIZE_INVALIDGN` for a lone fixed operand holding a field, a root included; a lone empty group or root draws its empty class (`MVK_GROUP_IS_EMPTY`, `MVK_ROOT_GROUP_IS_EMPTY`) instead |
| a sole root | `MVK_ROOT_GROUP_REFERENCED` | admitted | — | as the row above |
| a root beside a disjoint operand | rejected; `MVK_ROOT_GROUP_REFERENCED` measured for a starred root in either position | `MVK_ROOT_GROUP_WITH_OTHER_PARAMETERS` | — | `MVK_ROOT_GROUP_WITH_OTHER_PARAMETERS`, in either order and whichever side is starred; an empty root draws `MVK_ROOT_GROUP_IS_EMPTY`; a non-root group beside another root's star is admitted |
| the same unstarred path twice | `MVK_DUPLICATE_PARAM1` | `MVK_DUPLICATE_PARAM1` | — | `MVK_DUPLICATE_PARAM1`, also for one group named once starred and once unstarred, in either order: only two starred operands escape duplicate checking |
| strict containment between two operands, a root beside its own descendant included | `MVK_DUPLICATE_PARAM2` | `MVK_DUPLICATE_PARAM2` | — | `MVK_DUPLICATE_PARAM2`, also for a fixed group beside a star strictly inside it and a star beside a star strictly inside it, in either order |
| the same starred path twice | (star refused) | admitted: duplicate checking skips wildcarded operands, so each is an authored occurrence | — | admitted, counted once per position |
| a starred repeatable operand | `MVK_NO_WILDCARDS_G_ALLOWED` | admitted | `MVK_NO_WILDCARDS_ALLOWED` | admitted in rules and computations, alone or in a mixed list such as `(G*, Fixed)` |
| a star on a non-repeatable group, such as an ordinary root | — | — | — | `MVK_INVALID_WILDCARD` |
| an unstarred repeatable group whose level the error field does not bind | the walk's class | the walk's class | the walk's class | the walk's class, ahead of arity when alone, a repeatable root included |
| a fixed operand whose fields lie only in nested descendants | — | — | — | admitted in either position and at arity three; depth does not bound it (content three levels down, or a repeatable descendant only) |
| longer lists | — | — | — | fixed lists of four and five and mixed lists of three and four admitted; the same starred group twice, two distinct starred groups, and a fixed group beside two starred groups admitted |

Known gate orders:

- **Containment before rootness**, on every carrier: a root beside its own descendant draws `MVK_DUPLICATE_PARAM2`, so an author is told to resolve the overlap rather than to remove the root.
- **Root before arity** on the trio (a sole root draws `MVK_ROOT_GROUP_REFERENCED`), and **root before the star gate** on the trio: a starred root draws `MVK_ROOT_GROUP_REFERENCED` rather than `MVK_NO_WILDCARDS_G_ALLOWED`, alone and in either position beside another operand. Whether the star gate also follows the containment gate is unmeasured.
- On the count, the **empty class** and the **walk's class** both answer ahead of arity for a lone operand.

**Locus table: an unstarred repeatable group `R` as operand (one repeatable level).** The same holds when the rule group itself is `R`.

| Error field | Form | Class |
|---|---|---|
| outside `R` | a sole operand or a pair | `MVK_NO_WILDCARD` |
| inside `R` | `AllGroupsFilled(R, fixed)` | admitted |
| inside `R` | a singleton-admitting positive quantifier, such as `AtLeastOneGroupFilled(R)` | admitted |
| inside `R` | sole `NoGroupFilled(R)`, unguarded | `MVK_NEG_CONDITION_IN_ITERATION`; admitted behind a `GroupFilled` guard |
| inside `R` | sole `NumberOfFilledGroups(R)` | `MVK_PARAMSIZE_INVALIDGN` |
| inside `R` | `NumberOfFilledGroups(R, other)`, unguarded | `MVK_NEG_CONDITION_IN_ITERATION`; admitted behind a positive guard, measured from a rule declared in `R` and from one declared at the root |

The iteration gate and its positive-guard lift are owned by [§9 §1.8](07-repetition-and-iteration.md#negative-condition-guard).

**A repeatable root is walked like any group.** Read from another root it draws `MVK_NO_WILDCARD` alone on every measured carrier. From a rule inside it the walk passes and each carrier meets its root classes: `AllGroupsFilled` draws `MVK_ROOT_GROUP_REFERENCED`, a sole `AtLeastOneGroupFilled` or `GroupFilled` is admitted, another root beside it draws `MVK_ROOT_GROUP_WITH_OTHER_PARAMETERS`, and a sole count draws `MVK_PARAMSIZE_INVALIDGN`.

**A sole bound `NumberOfFilledGroups(R)`: the class follows the error field.**

| Error field | Class |
|---|---|
| in `R` or in a fixed or repeatable child of it, and inside the rule's own group | `MVK_PARAMSIZE_INVALIDGN`, whichever such group declares the rule: `R`, the child, the root, a fixed group between them, or a repeatable group enclosing it; measured at the second repeatable level, on a repeatable root, and on a group holding fixed and repeatable subgroups |
| outside `R`, above it or beside it | `MVK_NO_WILDCARD` |
| outside the rule's group, even inside `R` | `MVK_ERROR_FIELD_NOT_IN_RULEGROUP`, the error locus's own class, which the same rule raises with no count at all |

**A star on any level exempts a lone count operand from arity.** A lone operand whose path carries a star, its own or an ancestor's, is exempt from arity, and its other gates still apply: a fixed group below a starred ancestor, such as `Batches*/Seal`, is admitted alone on both arms, and beside a fixed group. A group that is itself repeatable follows the ordinary wildcard rule with nothing nesting-specific: `MVK_NO_WILDCARD` unstarred, admitted starred.

| Form | Arm | Result |
|---|---|---|
| `Batches*/Seal` twice | computation | admitted, counted once per position |
| `Batches*/Seal` beside a disjoint star | computation | admitted |
| `Batches/Seal`, alone or beside a fixed group | computation | `MVK_NO_WILDCARD` |
| `Batches*/Boxes*/BSeal` with either level unstarred, alone | computation | `MVK_NO_WILDCARD` |
| `Batches/Seal` (outer level unstarred) with the error field in `Batches`, rule declared there or at the root | rule | admitted |
| `Batches/Seal` with the error field at the root | rule | `MVK_NO_WILDCARD` |
| inner level unstarred, error field in `Batches` or at the root | rule | `MVK_NO_WILDCARD` |

**Arms.** The count's duplicate, root, wildcard and arity rows and their order are measured on both the rule and the computation arm, except the empty-group gate, which is measured on the rule arm only. The nested-descendant row is measured on the computation arm; the locus tables are measured on the rule arm; the ancestor-starred rows carry their arm in the table above.

Sources: [group-operand walk inbound](../docs/sources/inbound-handbacks.md#inbound-2026-09-24c-group-operand-walk), [field-slot inbound](../docs/sources/inbound-handbacks.md#inbound-2026-09-24c-field-slot), [path-walk inbound](../docs/sources/inbound-handbacks.md#inbound-2026-09-24c-path-walk), [both-arms static-gate checkpoint](../docs/sources/group-list-and-capacity-probes.md#src-group-count-static-gates-both-arms), [entity-list operand reads inbound](../docs/sources/inbound-handbacks.md#inbound-2026-09-23b-entity-list-operand-reads), [ancestor-starred inbound](../docs/sources/inbound-handbacks.md#inbound-2026-09-24-ancestor-starred-group-count), [ancestor-starred computation checkpoint](../docs/sources/group-list-and-capacity-probes.md#src-ancestor-starred-group-count-computation), [computation star-binding checkpoint](../docs/sources/group-list-and-capacity-probes.md#src-computation-star-binding-gate), [count-star inbound](../docs/sources/inbound-handbacks.md#inbound-2026-09-26j-count-star), [count placement grid](../docs/sources/group-list-and-capacity-probes.md#src-count-placement-overlap-list-grid), [count placement by error field](../docs/sources/group-list-and-capacity-probes.md#src-count-placement-by-error-field), [nested-descendant admission checkpoint](../docs/sources/group-and-iteration-probes.md#src-nested-descendant-group-count-admission), [nested-descendant runtime checkpoint](../docs/sources/group-and-iteration-probes.md#src-nested-descendant-group-count-runtime), [starred computation checkpoint](../docs/sources/group-and-iteration-probes.md#src-starred-group-count-computation), [K22 static classes](../docs/sources/group-count-topology.md#src-k22-static-classes).

---

## Part B — §3 Formal errors and the "unknown" state

### B.1 What a formal error is

**Rule.** A field value that violates its data-type configuration produces a **formal error**. While it stands, built-in validation reads observe the field as UNKNOWN and cannot consume it as a checked operand. Formal errors:

- carry no rule-authored message: their text is built in, or for a String pattern, Enumeration value or requiredness check it is the field declaration's own template ([§13](11-messages-and-custom.md#part-a--13-error-message-interpolation)); rule errors, in contrast, are authored and can be error, warning or info; a registered custom field validator is the explicit exception, carrying its project code and optional validator-provided message ([§7](06-strings-and-enumerations.md#a3-custom-field-type-validation));
- are attributed internally to a sentinel rule path, `formalePruefung`, so from the author's rule's viewpoint the rule simply produces nothing;
- block the field from participating in built-in predicates, comparisons and aggregates. Author rules never create this state; only the producers of [B.3](#b3-what-puts-a-cell-in-the-third-state) do.

**A built-in finding reports only its own node.** A formal finding (a custom field type's and an over-repetition finding included) and the generated `mandatoryField` and `uniqueIndex` checks of [§4](03-empty-and-required.md) each produce one message at the finding's node address (a field, row or group instance) whose `referenced` holds exactly that address. A formal finding and `uniqueIndex` are VALUE with an empty `fillToFix`; `mandatoryField` is OMISSION, and its `fillToFix` holds the same address. Validation messages and computation's formal-operand channel have the same shape.

**`CustomCondition` is the host-SPI exception to the read boundary** ([§14](11-messages-and-custom.md#part-b--14-customcondition--the-escape-hatch)). The Kernel cannot infer the callback's hidden field dependencies from the rule, so a reached callback receives the document plus the complete formal-invalid set and decides for itself whether one of its necessary fields prevents evaluation. The callback contract requires `false` in that case, but the runtime does not pre-suppress the invocation.

**A would-be tautology is not one.** If `F` has a formal error:

```
FieldFilled(F) Or FieldNotFilled(F)     -- does NOT hold: F is unknown, so neither branch is satisfied
```

**Nor is a contradiction refused.** Admission does not decide satisfiability: `FieldFilled(Src) And FieldNotFilled(Src)` and `[Src] > 5 And [Src] < 3` on a non-repeatable Number are admitted with no static diagnostic, so whether a rule can ever fire is an analysis question, not an admission one.

Sources: [K21 consumer-readiness checkpoint](../docs/sources/consumer-readiness-probes.md#src-consumer-readiness-k21) (`builtin-channels`, `candidates`).

### B.2 The three cell states — the third one is *not* "empty"

**Rule.** A cell is in one of three states: **empty**, **filled**, or **not-check-relevant**. A cell is not-check-relevant while it carries a formal finding from one of the producers in [B.3](#b3-what-puts-a-cell-in-the-third-state); it need not hold a value, since requiredness annotates an empty cell and over-repetition stamps written cells whatever they hold. Two refinements:

- The required checkbox's finding is validation-scoped: computation reads a required-and-empty cell as plain empty. The index field's generated mandatory finding is not (B.3).
- Non-relevance under partial validation is not a cell state. The field-fill tally counts a non-relevant cell with the unavailable ones ([A.4.4](#a44-validation-the-unfiltered-field-fill-tally)); [§12 §5.3](10-validation-and-polarity.md#53-reading-a-cell-under-a-relevant-set) owns how each other consumer treats it.

The empty-value substitutions of [§2](03-empty-and-required.md) apply to the empty state only. A third-state cell answers UNKNOWN in validation and poison in computation, and each consumer class lands it differently:

| Consumer class | empty cell | not-check-relevant cell |
|---|---|---|
| `scalar read`: a built-in predicate or operator reading the value | per-kind substitution or the operator's own override ([§2 A.2](03-empty-and-required.md#a2-where-an-operator-overrides-its-kinds-default), assigned in [column N](14-operator-reference.md#empty-read)) | UNKNOWN — the branch cannot decide ([B.4](#b4-suppression-is-branch-scoped-and-reaches-presence-checks)) |
| `presence/fill`: a field presence predicate or field-fill quantifier | a definite FALSE / TRUE (counts as empty) | UNKNOWN — counted neither filled nor empty, so `NoFieldFilled` does not fire over it ([A.4.3](#a43-classifying-a-slot)) |
| `all-cells`: a combiner that accounts for every selected cell | dropped or substituted per operator | the operand is UNKNOWN wherever in the selection the cell sits |
| `stop-at-first`: a combiner that stops at its first filled cell | skipped | UNKNOWN only when reached: an invalid cell in the first-filled position makes it UNKNOWN; one after the first filled row is never reached |
| `skip-invalid`: a predicate that compares only the values it collects | skipped | skipped exactly like an empty cell (below) |
| `group presence`: a read of group content | no content | blocks only the negative answer: admitted content elsewhere in the group still decides it filled ([A.4.7](#a47-group-list-quantifiers), [A.4.8](#a48-numberoffilledgroups)) |
| any read in a computation | the per-kind compute behaviour ([§11](09-computations.md)) | `poisons`: a field-cell read, value or presence, aborts the computing instance; `never poisons`: a group presence read ([B.6](#b6-validation-excludes-computation-poisons)) |

An UNKNOWN operand does not by itself suppress the rule: the strong-Kleene connectives decide how far it reaches ([B.4](#b4-suppression-is-branch-scoped-and-reaches-presence-checks)). The class is per operator and is not inferable from family resemblance: [the operator reference](14-operator-reference.md#unavailable-read-in-validation) assigns each operator its validation class and [its computation class](14-operator-reference.md#unavailable-read-in-computation). Measured members: `presence/fill` — `FieldFilled`, `FieldNotFilled` and the field-fill quantifiers; `all-cells` — `Sum`, `MinValue`, `MaxValue`, `NumberOfDifferentValues` and `NumberOfFilledFields`; `stop-at-first` — `FirstFilledValue`; `skip-invalid` — `FieldValuesNotUnique`; `group presence` — `GroupFilled`, `GroupNotFilled`, the group-list quantifiers and `NumberOfFilledGroups`. Another operator's behaviour is stated in its own clause.

The distinction *empty ≠ invalid* is why a two-state value domain cannot model the language: `NoFieldFilled` fires over empties but not over invalids, and an all-cells aggregate drops or substitutes empties but goes UNKNOWN on one invalid cell.

**What separates the classes is each operator's own accumulation rule**, not the relevance gate it consults: all of these operators consult the same three-valued gate, so a rule keyed on the gate predicts the same answer for `Sum` and for `FirstFilledValue`. An all-cells combiner must account for every selected cell, so it propagates the UNKNOWN. A stop-at-first combiner never reaches a later cell, which is why `FirstFilledValue` fires when the malformed cell follows the first filled row and is UNKNOWN when the malformed cell occupies the first-filled position.

**`FieldValuesNotUnique` skips.** A third-state member is removed from the comparison exactly as an empty member is: it contributes no comparable value, and it never makes the predicate UNKNOWN. A duplicate among the other members still fires, and two equal invalid values are not a duplicate because neither enters the comparison ([§9](07-repetition-and-iteration.md)). The predicate has no early return on an invalid cell; its own return is at the first duplicate. Skipping and UNKNOWN propagation agree on every selection on which skipping does not fire, because a non-fired and an UNKNOWN leaf compose identically ([A.1](#a1-connectives-are-two-valued-parentheses-are-mandatory)). The separating case is an invalid member beside a duplicate among the other members: skipping fires, propagation would be silent.

**Position does not change an all-cells verdict.** For the all-rows aggregates the malformed cell's authored position does not change the verdict, measured with that cell at head and at tail. That is a claim about the verdict alone: the cell's own formal error names the row it sits in, so validation output is not position-blind. Whether the aggregate reaches UNKNOWN by stopping at the first such cell or by surveying the whole selection is not observable, and an implementation may do either. Under partial validation the same combiner can answer non-relevant for a whole repetition without reading a cell, which is why an all-rows aggregate stays UNKNOWN in partial validation even when every concrete row is enumerated ([§12](10-validation-and-polarity.md#5-full-vs-partial-validation)).

Sources: [checked String ingestion checkpoint](../docs/sources/domain-ingestion-probes.md#src-checked-string-ingestion-k13) (`domain-composition`: invalid values make a distinct count UNKNOWN and are skipped by uniqueness).

### B.3 What puts a cell in the third state

**Rule.** The same checked-cell mechanism, with the same eventual UNKNOWN and the same suppression for authored validation rules, receives findings from several stages, not only from a type-format mismatch:

| Producer | Finding |
|---|---|
| **a malformed value** | the base case, preceded on a stored or input value by [three cross-kind baseline checks](06-strings-and-enumerations.md#stored-value-checking-and-normalization) run in this order before any type-format check: a technical length limit, the model's [legal charset](06-strings-and-enumerations.md#a2-legal-charset-definitions-and-atomic-matching), and no leading or trailing blanks |
| **a declared-constraint violation** | range, length, pattern, digit counts, enumeration domain: a parseable but out-of-bounds value is exactly as invalid as an unparseable one |
| **a registered custom field-validator rejection** | one project-coded formal observation reused by every consumer of that relevant concrete-valued cell ([§7](06-strings-and-enumerations.md#a3-custom-field-type-validation), which also owns the reserved report that admits its value) |
| **the required checkbox on an empty field** ([§4](03-empty-and-required.md)) | after the generated mandatory rule has fired and its hit and message are retained, the empty target is annotated with a validation-scoped required finding; authored validation rules then see UNKNOWN, while computation sees plain empty ([§11](09-computations.md)) |
| **an empty index field** ([§4](03-empty-and-required.md#b4-the-index-fields-auto-generated-checks--mandatory-and-unique)) | after the generated index mandatory check draws `mandatoryField`, the empty cell is annotated as the required checkbox annotates its target, but the finding is not validation-scoped: a computation reading the cell poisons |
| **a duplicate index value** | a later model/instance check marks every participating cell, field-locally |
| **an over-repetition row** | the address-formal check below |

During computation, a target marked invalid by an aborted computation reads the same way for its dependents ([B.6](#b6-validation-excludes-computation-poisons)).

**First failure wins.** A value violating several checks reports only the first in the engine's fixed precedence. The order is owned per kind: String and Enumeration in [§7](06-strings-and-enumerations.md#stored-value-checking-and-normalization), Number in [§5](04-numbers-and-decimals.md#4-other-numeric-constraints), Date in [§6](05-dates-and-time.md#4-the-gregorian-floor). For other kinds the order is unspecified here.

**The requiredness order matters.** The generated `mandatoryField` rule is evaluated against the base cells and its hit retained before the required annotation is applied. Annotating first would make the mandatory rule's own `FieldNotFilled` read UNKNOWN and suppress the message that creates the annotation.

#### Over-repetition

**Rule.** The address-formal check detects a coordinate beyond the group's declared `repeatability` before scalar conversion. It supplies the structural finding in place of any would-be scalar finding and suppresses the ordinary checks of that row and of everything the document writes beneath it, while the row's physical content is retained. In the instance `/Order[1]/Lines[3]/Qty`, the complete formal channel is exactly `zuGrosseZeile@/Order[1]/Lines` and `zuGrosseKontextnummer@/Order[1]/Lines[3]/Qty`, with no Number, Boolean/Confirm, String-length or other scalar-format finding for that row.

**One finding per written node, all attributed to the outermost violation.** The outermost over-limit row in a subtree draws exactly one finding on its own address plus one for every instantiated descendant row, every written non-repeatable group instance and every present cell the document writes under it, at any depth, a cell declared directly in the violated group included, whose coordinate vector is exactly as long as the row's. A present cell written as JSON `null` or as an empty string counts; an absent one does not; a non-repeatable group instance counts even when it holds nothing. The set is read off the written document, not off the model: the same row written as an empty row object draws the row code alone although descendants are declared beneath it, and a cell holding a value stamps exactly as an empty one, with its ordinary format check suppressed.

**The mechanism is one index check per written entity against its own repeatable ancestry**, not containment in the violated row's coordinates: a node of a sibling group whose coordinates merely share the violated row's prefix draws nothing.

**The code is decided by the offending coordinate's position in the reporting address's own index vector.** A vector holds one entry per container level on the entity's path, and a field's vector carries one further entry for its own row cap.

| Offending position | Code |
|---|---|
| 0 | `zuGrosseLfdNummer` |
| last | `zuGrosseZeile` |
| any position between | `zuGrosseKontextnummer` |

A violated group is the last position of its own address and an interior position of every deeper one, which yields the familiar `zuGrosseZeile` / `zuGrosseKontextnummer` pair. At container depth one that position is also position 0, so an over-instantiated repeatable **root group** draws `zuGrosseLfdNummer` on the row and on every node beneath it, with no row or context code anywhere (measured on both codegen strategies against an in-capacity control).

**Nested violations are absorbed.** An over-limit row nested inside the subtree contributes its nodes to the count but draws no `zuGrosseZeile` of its own, and no message names its group, so its violation is invisible until the outer one is fixed; the formal channel is not monotone in the document. Absorption is transitive: three nested violated levels draw one row code, and all fourteen findings name the outermost group. Suppression reaches the same distance: a malformed cell two levels below an over-limit row reports nothing, while the identical value in an in-capacity sibling row reports normally. Over-limit rows in disjoint subtrees stay independent and each names its own group.

**Message content.** Every context-number message carries the outermost violated group's declaration path and its offending index, whatever the stamped node's depth; `referenced` holds exactly the stamped address and `fillToFix` is empty. The Kernel channel spells an address by eliding a repetition-one coordinate at every level and indexing the violated row, so a finding reads `A[3]/B/C/Value` with `B` and `C` at row 1.

**Partial validation does not narrow the set.** The check runs before relevance is consulted, so any nonempty relevant selection (the root, an unrelated root field, an unrelated repeatable field) reports the full set, while an empty selection ends the call and reports nothing. This is the exception to the coverage gate that [§12 §5.3](10-validation-and-polarity.md#53-reading-a-cell-under-a-relevant-set) applies to the rest of the formal channel.

Sources: [occurrence scope](../docs/sources/over-repetition-probes.md#src-over-repetition-occurrence-scope), [position classes](../docs/sources/over-repetition-probes.md#src-address-index-position-classes), [multiplicity](../docs/sources/over-repetition-probes.md#src-over-limit-finding-multiplicity), [attribution](../docs/sources/over-repetition-probes.md#src-nested-over-limit-attribution), [absorption depth](../docs/sources/over-repetition-probes.md#src-over-limit-absorption-depth), [runtime open-cells probe](../docs/sources/model-structure-and-declaration-probes.md#src-runtime-open-cells).

#### String ingestion boundary

**String checking's ingestion boundary** — the CRLF normalization of a checked-and-valid String, the String format check's clause order and the separate message-display path — is [§7](06-strings-and-enumerations.md#stored-value-checking-and-normalization)'s.

**A raw String is not a producer.** A String field declared with `noValueValidation` does not enter the third state. Its stored content remains ordinary content for presence predicates, while model validation closes every operation that would expose its value; the sole admitted `Length` declaration is eliminated into metadata rather than evaluated as a runtime rule ([§7](06-strings-and-enumerations.md#a1-raw-type-strings-novaluevalidation)).

Sources: a12-dmkits [`NvvRawTypeDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/NvvRawTypeDiffTest.kt) (IF125).

> **Non-normative implementation note.** Keep one checked-cell representation, but do not route every producer through the base formal check from field policy and raw cell to checked cell. The base check handles ordinary local findings such as malformed data and declared constraints, including String normalization after the raw-text line-break gate. Decide over-repetition first and construct the same checked-cell shape without running the scalar checker. Generated preliminary findings then annotate admitted base cells, in the requiredness order above. The phase read maps applicable findings to validation UNKNOWN and computation poison, ignoring the required finding during computation. Reject value-reading windows onto raw-type Strings during elaboration rather than at the read. Do not scatter invalidity handling across operators, and do not perform per-kind empty substitution inside the read.

### B.4 Suppression is branch-scoped, and reaches presence checks

**Rule.** For built-in predicates and operators, a formal error does not remove the whole rule; it makes the reading operand UNKNOWN, and the strong-Kleene `And`/`Or` decide the rest:

```
healthyValueTrue Or  [broken] > 0     -- still FIRES  (the VALUE-fired branch decides the verdict)
healthyTrue      And [broken] > 0     -- SUPPRESSED   (unknown absorbs the And)
```

- A single-branch rule is the case where branch-scoped and rule-scoped suppression look identical.
- The UNKNOWN reaches built-in operators that read no value: `FieldFilled(malformed)` decides nothing (UNKNOWN, not FALSE).
- The suppression is silent from the author's viewpoint: the engine emits its own formal-error code on the sentinel path while the author's rule yields nothing. In a report, the discriminator is the sentinel path versus the rule's own path.
- A fired branch decides an `Or` against an UNKNOWN sibling, and the message type follows `Or`'s value-wins rule, so an OMISSION-fired branch may still be upgraded to VALUE by a VALUE-fired sibling.
- A reached `CustomCondition` is different: it receives the formal-invalid set, returns its own Boolean leaf result, and only then participates in the surrounding `And`/`Or`.

The tables fix the verdict despite an UNKNOWN sibling; they do not by themselves fix whether validation physically reads an operand whose result is already decided. [§9](07-repetition-and-iteration.md#3-the-filter-having-the--correlation-and-aggregation) records validation leaves that can raise, where left-to-right short-circuiting is observable.

### B.5 The strong-Kleene tables (the exact algebra)

**Rule.** Propagation follows strong three-valued Kleene logic, the third value written `U`:

| `And` | T | F | U |   | `Or` | T | F | U |
|---|---|---|---|---|---|---|---|---|
| **T** | T | F | U |   | **T** | T | T | T |
| **F** | F | F | F |   | **F** | T | F | U |
| **U** | U | F | U |   | **U** | T | U | U |

The absorbing cases make suppression branch-scoped: `F And U = F`, `T Or U = T`. There is no negation row; the language provides none, so `¬U` is never needed.

**Information order.** Order the values by `U ⊑ T`, `U ⊑ F` and reflexivity, with `T` and `F` incomparable. `And` and `Or` are monotone in each argument under this order: refining an UNKNOWN input may resolve the result to either truth value, while a result that is already definite is stable under further refinement. A blanket claim that "not fired can only move toward fired" is false, because UNKNOWN may refine to FALSE as well as TRUE.

> **Non-normative implementation note.**
> ```lean
> inductive K where | tru | fls | unknown
> def K.and : K → K → K
>   | .fls, _ => .fls | _, .fls => .fls
>   | .tru, .tru => .tru | _, _ => .unknown
> def K.or : K → K → K
>   | .tru, _ => .tru | _, .tru => .tru
>   | .fls, .fls => .fls | _, _ => .unknown
> ```
> A predicate that reads a cell produces `K`, not `Bool`: reading a not-check-relevant cell yields `.unknown`; reading an empty or filled cell yields a definite value per the operator's rules. The monotonicity statement above is the useful regression theorem.

### B.6 Validation *excludes*; computation *poisons*

**Rule.** The two operations treat the third state with opposite temperament, which matters wherever computed fields chain:

- **Validation excludes.** A third-state cell stays where it is read and settles nothing: a tally counts it in neither bucket ([A.4.3](#a43-classifying-a-slot)), an all-cells aggregate over it is UNKNOWN, a skip-invalid predicate skips it, and a referencing branch is UNKNOWN ([B.2](#b2-the-three-cell-states--the-third-one-is-not-empty)). Nothing propagates beyond the rules that reference it.
- **Computation poisons.** During `compute`, a read of a third-state field cell, whether a value read or a presence read such as `FieldFilled` or a field-fill scan, throws: the reading computation instance aborts, produces no value, is itself marked invalid, and that mark poisons its dependents' reads in turn. The cascade is **order-dependent**, because only cells an evaluation actually reaches can poison it.
- **Group presence is not a field-cell read.** A group presence read never poisons in computation; [the operator reference](14-operator-reference.md#unavailable-read-in-computation) names the operators whose reads are group presence. A formally invalid stored descendant counts as group content; a descendant invalid only because its computed dependency failed supplies no content ([A.4.8](#a48-numberoffilledgroups)).

The compute side is owned by [§11](09-computations.md#32-an-invalidity-clear-poisons): the same third state that validation handles by exclusion, computation handles by an order-sensitive abort.

Sources: [group-presence computation checkpoint](../docs/sources/computation-scheduling-probes.md#src-group-presence-computation-guards).

---

## Checklist for a faithful reimplementation of §1 + §3

- [ ] The cell domain has **three** states (`empty` / `filled` / `notCheckRelevant`), resolved once at the read; partial-validation non-relevance reads as UNKNOWN too.
- [ ] `And`/`Or` are strong-Kleene over `{T, F, U}`; there is **no** negation combinator; validation polarity is OMISSION-wins under `And` and VALUE-wins under `Or`.
- [ ] The parser **rejects** unbracketed `And`/`Or` mixes.
- [ ] Negative predicates are individual constructors, **not** `Not p`; the non-complementary pairs behave as specified.
- [ ] Boolean has three field states; `== True` ≠ `FieldFilled`; Confirm-empty = `False` while Boolean-empty = not evaluated; stored tokens are case-folded by the reader, then checked case-sensitively.
- [ ] Group operands expand recursively; fill quantifiers distinguish the **declared** and **instantiated** ranges and use the canonical field-major / repetition-major stream; filters apply to the predicate's own range.
- [ ] Validation counts an unavailable cell in neither bucket and keeps it in the list; computation poisons on a reached third-state slot and leaves every suffix after the full predicate's final decision unread.
- [ ] Each value consumer's treatment of a third-state cell follows its own accumulation rule: all-cells → UNKNOWN; stop-at-first → UNKNOWN only when reached; skip-invalid → skipped like empty; each operator's class is the one [the operator reference](14-operator-reference.md#unavailable-read-in-validation) assigns.
- [ ] Group-list quantifiers use one definitely-filled / definitely-empty / neither tally over field and group operands; a starred repeatable operand contributes one filled item per instantiated in-capacity row; a non-repeatable terminal below stars contributes its group product per selected in-capacity environment.
- [ ] `NumberOfFilledGroups` folds over authored positions; a fixed operand's content is read over its whole subtree (an admitted cell **or** an instantiated repeatable-descendant row); validation leaves the count UNKNOWN only where an operand's presence is undecided, computation counts formally invalid stored content and never poisons; a starred operand contributes its in-capacity row count on both arms; extent is per-operand capacity, not multiplied by repeatable descendants.
- [ ] Static admission of group and field-slot operands follows the per-carrier tables and gate orders of A.4.9.
- [ ] Every producer of B.3 enters the same checked-cell boundary; a custom-validator rejection preserves its project code and optional message; over-repetition findings are one per written node, attributed to the outermost violation, and are not narrowed by partial validation.
- [ ] Suppression is **branch-scoped** and reaches presence predicates (`FieldFilled(invalid)` = UNKNOWN).
- [ ] The strong-Kleene information order is explicit; `And`/`Or` are monotone under it, and definite results are stable under refinement.
