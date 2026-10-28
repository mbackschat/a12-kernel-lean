# 08 — Paths and references (§10)

How a condition names a field or a group, and how that name selects a cell. A path is resolved relative to the current repetition context ([`01-data-model.md §2.1`](01-data-model.md#21-repetition-contexts-the-iteration-environment)); this chapter says how a path string selects a cell in it. Two mechanisms carry most of the weight for a faithful reimplementation: the **two-tier bare-name resolution order** (declaring group, then a flag-gated model-wide unique field short name, §2) and the fact that **rows are addressed by semantic key, never by position** (§4).

This chapter owns the path forms and their legality (§1), reference resolution (§2), where a star may stand and the gates a bracketed field-value read asks (§3), and the semantic index (§4). Where a star binds and what it reopens is [§9 §4](07-repetition-and-iteration.md#4-where-a-star-binds--the-anchor-rules-); filters and the `$` correlation are [§9 §3](07-repetition-and-iteration.md#3-the-filter-having-the--correlation-and-aggregation); the order in which a text's classes are raised is [concrete syntax §3.1](12-concrete-syntax.md#31-which-class-a-refused-text-draws); which operators admit a keyed or category operand is column K of [the operator reference](14-operator-reference.md#keyed-and-category-operands).

---

## 1. Absolute, relative, and short-name references

**A path is absolute or relative, and its segments name groups and, last, the entity read.** An absolute path starts at a root group with `/` (`/Order/Quantity`). A relative path starts at the declaring group of §2 and may open with a run of up-steps `..` (`../Other`); relative paths within a rule's group are shorter and survive the group being moved. A bare short name such as `[Quantity]` is a one-segment relative path, resolved by §2.

**A segment named like a keyword is single-quoted in a path.** A field or group named like a keyword (`And`, `Date`, `Today`, …) is written `'Date'`: `FieldFilled(Order/'Date')`.

**An up-step stands only in a relative path's leading run.** Up-steps chain only through `/`: `.. / .. / Code` is admitted, while `.. ..`, `.. .. / Code` and `..../Code` draw `MVK_UNEXPECTED_TOKEN`, a second `..` after a closed one being a stray token. A name written directly after the last up-step is the run's named turning point (§2). An up-step anywhere else, a misplaced named turning point such as `Claims/..Policy/Holder` included, is refused `MVK_UNEXPECTED_TOKEN` — but only once the path before it has passed the walk, if it is walked at all. What decides whether anything is resolved first is what precedes the misplaced step, not the segment beside it:

| What precedes the misplaced up-step | What happens | Witnesses |
|---|---|---|
| no starred named segment, and no leading up-run | nothing before it is resolved | `Claims/Nope/..`: `MVK_UNEXPECTED_TOKEN` |
| a starred named segment, or a leading up-run | the whole prefix is walked first, each segment with its own gates; only a prefix that clears its gates reaches the token refusal | `Claims*/Nope/..` and `../Nope/..`: `MVK_INVALID_ENTITY`; `/Nope/Claims*/..`: `MVK_INVALID_ROOT_GROUP`; `Claims/Amount*/..`: the star-on-a-field class `MVK_INVALID_WILDCARD` (§3.1) |

These are the same triggers that walk a path stopping at a separator, where a `$` mark is a third; [concrete syntax §3.1](12-concrete-syntax.md#31-which-class-a-refused-text-draws) owns that walk and when each step's class is raised. Across a condition the first defect in text order answers, a misplaced up-step taking its turn like any other reference. **A message parameter never walks the prefix:** there every misplaced up-step draws `MVK_UNEXPECTED_TOKEN`, so `$../Nope/..$` does where the same text in a condition draws the entity class.

**A path of up-steps alone names an ancestor group** and draws what a group in that slot draws: from a nested rule `..` is the root, which a field-fill operand refuses as a root and a group operand takes.

**A `*` may not stand on an up-step.** `..*/Budget`, which tries to reopen the ancestor step itself, is refused `MVK_INVALID_WILDCARD_REL` and must be written absolute, `/Project/Milestones*/Budget`. A named segment reached after walking upward may still be starred, so `../Items*/Count` is legal. A starred leading step that stays inside the model answers `MVK_INVALID_WILDCARD_REL` at its own segment, ahead of a later climb out of the model or a later `.*` suffix.

**`RuleGroup` names the rule's own containing group as an entity.** `GroupFilled(RuleGroup)` validates and counts as referencing the error field ([§9 §1.4](07-repetition-and-iteration.md#14-the-reference-set)). In every operand gate measured — a field-list, an aggregate, a value-function and a presence operand — `RuleGroup` draws the class the same condition draws with the group's path written out. Only the unquoted keyword is the group: beside a field named `RuleGroup`, `FieldFilled('RuleGroup')` reads that field.

- **`RuleGroup For "key"`** uses the ordinary semantic-index suffix of §4 rather than another addressing mechanism: `GroupFilled(RuleGroup For "SKU-1")` is admitted for an indexed `/Order/Items` rule group, while the same suffix on the unindexed `/Order` draws `MVK_NO_INDEX_FIELD`.
- **`RuleGroup*` is refused.** In an entity slot the star is the rule-context group's repetition star, and `NumberOfFilledGroups(RuleGroup*)` draws `MVK_INVALID_WILDCARD_FOR_RULEGROUP`.

**A group may be declared empty, and then it may not be named.** A group carrying no field anywhere in its subtree is legal in a model, and the model check reports the model valid. Every operand naming such a group is refused `MVK_GROUP_IS_EMPTY`, or `MVK_ROOT_GROUP_IS_EMPTY` when the group is a root:

- The gate is over the whole subtree, not the direct children, so a group populated only through a descendant subgroup is admitted.
- It applies to both repetition shapes, a starred count over an empty repeatable group included. A fixed root's presence and a starred repeatable root's count draw the root class. `RuleGroup` read in a rule declared in an empty group draws `MVK_GROUP_IS_EMPTY` on every group carrier measured, `GroupFilled` and `GroupNotFilled` included.
- It holds once the operand's star is right, because the read answers first: an empty repeatable group or root written without its star at a reference that does not iterate it draws the walk's `MVK_NO_WILDCARD`, and a star on an empty fixed group draws `MVK_INVALID_WILDCARD`.
- In an entity list it answers ahead of every list gate ([§9 §3.5](07-repetition-and-iteration.md#entity-list-operand-reads)).

Measured scope of the empty-group gate: static admission only, on an empty subgroup, an empty root and an empty repeatable group under `GroupFilled`, `FieldsNotCollectivelyFilled` and `NumberOfFilledGroups`, and on the group carriers of the later static batch; what an empty group does at runtime is unmeasured. `RepetitionNotUnique` refuses an empty reference group for its own reason ([§9 §6](07-repetition-and-iteration.md#6-repetitionnotunique-precisely-)).

Sources: [parser static-legality sweep](../docs/sources/diagnostic-class-vocabulary-and-sweeps.md#src-parser-static-legality-sweep) (row `R70`), [inbound 2026-10-26a](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-26a), [walked path](../docs/sources/inbound-handbacks.md#inbound-2026-09-26p-walked-path), [completed steps](../docs/sources/inbound-handbacks.md#inbound-2026-09-27-completed-steps), [production close](../docs/sources/inbound-handbacks.md#inbound-2026-09-26o-production-close), [path walk](../docs/sources/inbound-handbacks.md#inbound-2026-09-24c-path-walk), [K22 static batch 4](../docs/sources/group-count-topology.md#src-k22-static-s4), [empty star](../docs/sources/inbound-handbacks.md#inbound-2026-09-26k-empty-star), [empty declared group](../docs/sources/group-and-iteration-probes.md#src-empty-declared-group), [`RuleGroup` semantic index](../docs/sources/inbound-group-operand-batches.md#src-pr2-rulegroup-semantic-index).

---

## 2. Bare-name resolution order ⚠

**A relative path's first segment resolves in exactly two tiers — declaring group first, then a flag-gated model-wide unique field short-name lookup:**

1. Look **directly under the declaring group**: a rule's group, or a computation's declaring group rather than the group of the field it writes. This lookup is always attempted.
2. Only on a miss, **and** only for a relative reference while the model flag `fieldRefByShortNameAllowed` ([data model §1.1](01-data-model.md#11-the-two-special-model-level-configurations)) is on — its Kernel default is off — run a **model-wide unique short-name lookup over fields only**:
   - more than one match draws `MVK_FIELDNAME_NOT_UNIQUE` (**never a silent pick**);
   - zero matches fall through to `MVK_INVALID_ENTITY`.

   The serialized condition **retains** the short name; resolution is not rewritten into a path.

**The fallback answers only the first segment of a relative path that opens with no up-step**, starred or not, whatever follows it, and never a later segment; a path behind an up-step is unmeasured.

- An ambiguous first segment draws `MVK_FIELDNAME_NOT_UNIQUE` where a positional reading of the whole path would name a miss: `Remark/Nope`, `Remark*/Nope` and `Remark/Claims*` from a group declaring no `Remark`.
- A unique first segment binds its field, so the segment below it misses with `MVK_INVALID_ENTITY`, and a star on it is a star on a field, `MVK_INVALID_WILDCARD`.
- A first segment naming a group of the declaring group takes no fallback, so `Insured/Holder` misses although `Holder` is a unique short name.
- **A bare name naming a group of the declaring group takes none either:** the first tier finds the group, so from `/Grid` with a fixed group `Ledger`, `[Ledger] > 0` and `FieldFilled(Ledger)` draw `MVK_NO_GROUPS_ALLOWED` whether one field elsewhere is named `Ledger` or two.
- A message parameter's first segment reaches the same fallback, in that surface's own vocabulary ([§13 A.5](11-messages-and-custom.md#a5-entity-lookup-and-the-shared-root-gate)).

**There is no implicit ancestor walk.** A field in an ancestor group is reachable only through explicit `../` navigation or, when its short name is model-wide unique, through the flag-gated fallback. From `/Subscription/Addons`, `[Tier]` naming a field of `/Subscription` is refused `MVK_INVALID_ENTITY` with the flag off; with the flag on, the fallback binds it.

**A named turning point validates, it does not navigate.** In a `..Name/rest` path the up-count comes **only** from the `..` tokens; the trailing `Name` names, and validates, the ancestor landed on, and a matching `..Name/rest` resolves exactly like `../rest`. A turning point naming another group than the one the up-steps reach draws `MVK_INVALID_ENTITY` (unmeasured in a condition; a message parameter's turning point draws its `INVALID_ENTITY`, [§13 A.5](11-messages-and-custom.md#a5-entity-lookup-and-the-shared-root-gate)).

> **Non-normative implementation note.** Implement resolution as one scoped lookup, `resolve : Path → DeclaringGroup → Model → Except ResolveError FieldRef`, with the not-unique case as its own error rather than a first match. Add no ancestor tier, and compute a relative target from the `..` count alone, checking the turning point's name only as a guard.

Sources: [field-value read predictions](../docs/sources/field-value-read-probes.md#src-field-value-read-predictions), [path walk](../docs/sources/inbound-handbacks.md#inbound-2026-09-24c-path-walk), [field-value read remaining sites](../docs/sources/field-value-read-probes.md#src-field-value-read-remaining-sites), [short-name flag](../docs/sources/group-and-iteration-probes.md#src-short-name-flag-gates-the-model-wide-tier); a12-dmkits [`ShortNameRefDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/ShortNameRefDiffTest.kt) and [`PathLawsTest`](../../a12-rulekit/src/test/java/io/github/mbackschat/a12/dm/rulekit/validate/laws/PathLawsTest.java) (IF119) lock the two tiers under both flag settings.

---

## 3. The asterisk and `$`

This section is about the path syntax and the gates a read asks; how a star *binds* the enclosing indices — the anchor rules — is [§9 §4](07-repetition-and-iteration.md#4-where-a-star-binds--the-anchor-rules-).

### 3.1 Where a star may stand

**The asterisk `*` flattens a repeatable group into the list of its rows, and every repeatable level below a starred one must be starred too.** An outer level cannot be flattened while an inner one is pinned.

**A star may land only on a repeatable group.** On a fixed group, the root or a field it is refused `MVK_INVALID_WILDCARD`. The up-step's own star is §1's `MVK_INVALID_WILDCARD_REL`.

- **It answers ahead of the slot's own wildcard gate and ahead of a later segment that names nothing**, so a starred fixed group followed by an unknown leaf draws it.
- **It answers alone.** Where the same reference leaves a repeatable level unstarred, and the twin with the star moved onto that level draws the position's own class, the misplaced star draws `MVK_INVALID_WILDCARD` and nothing else; so does a star on the field beside a star on every level. The positions measured, with the class each twin draws: containment; `MVK_NO_WILDCARD`; `MVK_NO_WILDCARDS_ALLOWED` in a date slot or a scalar value-list subject; `MVK_DIFFERENT_GROUPS` in a `SumOfProducts` pair. A star on the field and a star on a fixed group are both measured at every one of these positions. A fixed group's star also answers alone against an unreferenced error field, and whether the twin without that star is admitted, as in the date slot and the scalar value-list subject, or draws a class of its own.
- **Alone holds per defect, not per condition.** Of a misplaced star and an unstarred repeatable level in one condition, whichever the text reads first answers, within one call's operand list and across two calls alike.

Measured scope: the segment order is measured on four carriers, `Sum`, `MaxValue`, `FirstFilledValue` and `FieldValuesNotUnique`, each giving one answer per path; the "answers alone" positions are the four listed above.

Sources: [misplaced star](../docs/sources/inbound-handbacks.md#inbound-2026-09-24e-misplaced-star), [fixed-group star](../docs/sources/inbound-handbacks.md#inbound-2026-09-25-fixed-group-star), [starred-path segment order](../docs/sources/path-resolution-class-probes.md#src-starred-path-segment-order).

### 3.2 The field-value read `[…]`

**The field-value read `[…]` asks its gates of the entity it names as its bracket closes, wherever it stands.** The gates run in this order, the first failing one answering:

| Order | Gate | Refused entity | Class |
|---|---|---|---|
| 1 | the reader's own classes | an unstarred repeatable level the reading scope does not bind; a misplaced star (§3.1); a name that resolves to nothing | `MVK_NO_WILDCARD`; `MVK_INVALID_WILDCARD`; `MVK_INVALID_ENTITY` |
| 1 | containment | a read the error field's containment refuses | containment's class ([§9 §1.5](07-repetition-and-iteration.md#15-error-field-admission)) |
| 2 | the group gate | a group, a starred group, the root, the ancestor a bare up-step `[..]` reaches; in a filter's body the level the filter iterates and a repeatable group it does not iterate included | `MVK_NO_GROUPS_ALLOWED` |
| 3 | the star gate | a starred path | `MVK_NO_WILDCARDS_ALLOWED` |
| 3 | the value gates | a String declared with `noValueValidation` (a raw String, [§7 A.1](06-strings-and-enumerations.md#a1-raw-type-strings-novaluevalidation)); a partially known Date ([§6 §6.2](05-dates-and-time.md#62-partially-known-dates)) | `MVK_INVALID_RAW_TYPE`; `MVK_INVALID_DATE_TYPE` |

The star gate asks the spelling, not the binding, so a star on the level the rule iterates is refused too. A starred group draws the group class, so the group gate stands ahead of the star gate. The star gate and the value gates share rank 3 because their order against each other is unmeasured.

**Because each bracket is checked as it closes, a read's class answers ahead of the construct around it.**

- Of two reads in one comparison the left one's class is named.
- A failing read answers ahead of a comparison's kind classes, ahead of an arithmetic operator's `MVK_NO_NUMBER_FOR_CALC`, ahead of a filter chain's `MVK_NO_ITERATION_FOR_WILDCARD`, and ahead of a scalar value list's own gates ([§8 B.4](06-strings-and-enumerations.md#b4-scalar-membership-is-a-singleton-specialization-not-boolean-negation-)).
- A pattern comparison's field is a read, so its group, raw and partial-Date classes answer ahead of the comparison's own `MVK_INVALID_TYPE_FOR_PATTERN_COMPARISON`; a DateRange comparison's sides are reads too.
- On a computation into a nonrepeatable Enumeration target a starred source draws `MVK_NO_WILDCARDS_ALLOWED` ahead of the target's source gate, read stored or through a declared category, while a category the Enumeration does not declare draws `MVK_CATEGORY_UNKOWN` ahead of the star.
- A field form's entity slot (`AbsValue`, `RoundDownValue`, `RoundUpValue`, `RoundAccountingValue`, [§5 §2](04-numbers-and-decimals.md#2-rounding)) is read the same way before its group gate: in a rule iterating nothing `RoundUpValue(Items, 2)` draws `MVK_NO_WILDCARD` for the unbound repeatable group, and `RoundUpValue(Notes/Pages, 2)` below two keyed groups draws `MVK_MULTIPLE_INDEX_FIELDS` (§4), each ahead of `MVK_NO_GROUPS_ALLOWED`.

**An operator argument typed as an entity is not a field-value read** and meets its operator's own gates, so `[Total] == Sum(Lines*/Qty)` is admitted. Which slots are `value` slots, bracketed, and which are `entity` slots, bare, is column S of [the operator reference](14-operator-reference.md#argument-slots).

Measured scope: the group and star gates are measured on a comparison side, an arithmetic operand, a scalar value list's members, a filter's body and a computation's operation; the raw and partial-Date gates on the same carriers except a filter's body. On a computation's operation the group and raw gates are measured writing a String, an Enumeration, a Time and a Number target, the partial-Date gate writing a Number and a Date, and the star gate one Number target, while an unstarred repeatable group there draws the reader's `MVK_NO_WILDCARD` on a Number and a String target. A DateRange comparison is measured with a group on either side and a raw String on the right. Other carriers follow the general rule unmeasured.

Sources: [inbound 2026-09-25f field-value read](../docs/sources/inbound-handbacks.md#inbound-2026-09-25f-field-value-read), [field-value read grid](../docs/sources/field-value-read-probes.md#src-field-value-read-grid), [K22 static batch 2](../docs/sources/group-count-topology.md#src-k22-static-s2), [inbound 2026-09-25g field-value read](../docs/sources/inbound-handbacks.md#inbound-2026-09-25g-field-value-read), [field-value read carriers](../docs/sources/field-value-read-probes.md#src-field-value-read-carriers), [field-value read remaining sites](../docs/sources/field-value-read-probes.md#src-field-value-read-remaining-sites), [inbound 2026-09-25i enum source](../docs/sources/inbound-handbacks.md#inbound-2026-09-25i-enum-source), [inbound 2026-10-23](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-23) (KF599, KF602).

### 3.3 A field named as an operator's parameter

**A field an operator names as a parameter asks the reader's classes and the group gate, but not the read's value gates; past them each operator asks its own gates.** So a raw String or a partially known Date meets the operator's own kind gate, not `MVK_INVALID_RAW_TYPE` or `MVK_INVALID_DATE_TYPE` by default. The measured outcomes:

| Parameter | Fixed group | Unstarred repeatable group | Raw String | Partially known Date |
|---|---|---|---|---|
| `Length` | `MVK_NO_GROUPS_ALLOWED` | `MVK_NO_WILDCARD` | `MVK_INVALID_LENGTH_OF_RAW_TYPE` | `MVK_NO_STRING`, as a full Date and a Number draw |
| `RangeAsNumber` | `MVK_NO_GROUPS_ALLOWED` | not stated | `MVK_INVALID_RAW_TYPE` | `MVK_INVALID_TYPE` |
| `FieldValueAsNumber` | `MVK_NO_GROUPS_ALLOWED` | `MVK_NO_WILDCARD` | `MVK_NO_CONVERT_IN_NUMBER` | `MVK_NO_CONVERT_IN_NUMBER` |
| `FieldValueAsString` | `MVK_NO_GROUPS_ALLOWED`, measured into a computation target only | `MVK_NO_WILDCARD` | `MVK_NO_NUMBER` | not stated |
| a DateRange endpoint's date component | `MVK_NO_GROUPS_ALLOWED` | not stated | not stated | not stated |

An unstarred repeatable group also draws `MVK_NO_WILDCARD` ahead of the substring operators' own gates. A name resolving to nothing draws `MVK_INVALID_ENTITY`, as `Length(NoSuch)` does. Column W of [the operator reference](14-operator-reference.md#raw-string-operand) carries each operator's raw-String class.

Measured scope: the group class on the rule side and into a nonrepeatable and a repeatable computation target, `FieldValueAsString` on the two targets alone; no row reads an unstarred repeatable group inside `RangeAsNumber` or a DateRange endpoint.

Sources: [field-value read predictions](../docs/sources/field-value-read-probes.md#src-field-value-read-predictions) (with the peer's KF395 and KF405 chains).

### 3.4 Category reads and category operands

**A category read `[F -> C]` reads the Enumeration field `F` through its category `C`** ([§8 B.2](06-strings-and-enumerations.md#b2-categories-via--)), and it is a read: the reader's classes and the group gate run first. An unstarred repeatable level meets the walk first, `MVK_NO_WILDCARD`, whether the category reads a group or a field.

- **`G` naming a group draws `MVK_NO_GROUPS_ALLOWED`**, as a comparison side, a scalar value list's member or subject and a computation's operation, and as an entity-list operand. In an entity list this is measured in `NumberOfFilledGroups`, `AtLeastOneGroupFilled`, `AllGroupsFilled`, `GroupFilled`, `GroupNotFilled`, `AllFieldsFilled` and `RepetitionNotUnique`, and it answers ahead of a repeated operand in `AtLeastOneGroupFilled`.
- **`F` declaring no Enumeration draws `MVK_NO_ENUMERATION`**, ahead of the read's raw and partial-Date gates and of `MVK_CATEGORY_UNKOWN`, over a raw String, a String, a partially known Date and a full Date alike. Measured carriers: a comparison side; a scalar value list's member or subject; a value-list quantifier's field, starred or not; a computation's copied source into a nonrepeatable or a repeatable target; an entity list's member inside `Sum`, `NumberOfFilledFields`, `DateRangesOverlap`, `AtLeastOneDateRangeOverlaps` and `FieldValuesNotUnique`.
- **An entity list whose carrier refuses a category draws `MVK_CATEGORY_NOT_ALLOWED` for an Enumeration's category.** The category is part of the operand's identity for the list's repeat gate, so `AllFieldsFilled(Tier -> Level, Tier)` draws the category class rather than a repeat.

How an operator treats an Enumeration category written as its entity operand is the second class of its cell in column K of [the operator reference](14-operator-reference.md#keyed-and-category-operands):

| Class | Meaning |
|---|---|
| `projected` | admitted; the operand reads through the category projection |
| `category refused, before repeat` | `MVK_CATEGORY_NOT_ALLOWED`, asked ahead of the list's repeated-operand gate, so it answers beside a repeated operand |
| `category refused, after repeat` | `MVK_CATEGORY_NOT_ALLOWED`, asked behind the repeated-operand gate, so beside a repeated operand `MVK_DUPLICATE_PARAM1` answers |
| `category refused` | `MVK_CATEGORY_NOT_ALLOWED`; its place against the repeat gate is unmeasured or does not arise |

On `GroupFilled` and `GroupNotFilled` the category class answers ahead of the field class `MVK_NO_FIELDS_ALLOWED` a category-free field draws, and on `RepetitionNotUnique` ahead of the class a root rule draws.

Measured scope: one Enumeration `Tier` with a category `Level`, every rule at the root of `/Order`; the refusing carriers are the nine field-fill predicates, `DateRangesOverlap`, `FieldValuesNotUnique`, the three counts `NumberOfFilledFields`, `NumberOfFilledGroups` and `NumberOfDifferentValues`, the five group-list quantifiers, `GroupFilled`, `GroupNotFilled` and `RepetitionNotUnique`; the place against the repeat is measured on the three counts (before) and on `AllFieldsFilled`, `FieldValuesNotUnique`, `AtLeastOneGroupFilled` and `RepetitionNotUnique` (after). `projected` rests on [§9 §3.5](07-repetition-and-iteration.md#35-entity-list-operand-admission)'s `FirstFilledValue` clause.

Sources: [inbound 2026-09-26b entity-list category](../docs/sources/inbound-handbacks.md#inbound-2026-09-26b-entity-list-category), [field-value read predictions](../docs/sources/field-value-read-probes.md#src-field-value-read-predictions).

### 3.5 Reads from a repeatable or parallel host

**A repeatable or parallel computation target, and a rule declared in a repeatable group, read as a nonrepeatable target and a root rule do.** The walk starts from the target's scope, so the target's own group passes the walk and draws `MVK_NO_GROUPS_ALLOWED`.

- Into a repeatable Number, Enumeration or String target a fixed group draws `MVK_NO_GROUPS_ALLOWED` and a raw String `MVK_INVALID_RAW_TYPE`, and into a Number or an Enumeration target a partially known Date draws `MVK_INVALID_DATE_TYPE`.
- A parallel iteration's operand reads the same way, a fixed group inside the keyed operand group and that group itself drawing `MVK_NO_GROUPS_ALLOWED`.
- A rule declared in a repeatable group draws the group and raw classes on an arithmetic operand and the group class on `Length`'s parameter.

Measured scope: a rule declared in a repeatable group is measured with `Length` alone among the parameters, and no row reads such a rule's own group.

Sources: [field-value read predictions](../docs/sources/field-value-read-probes.md#src-field-value-read-predictions).

### 3.6 The `$` marker

**A `$`-marked path is read from the complete captured outer repetition environment instead of the candidate environment**, and it may be written only inside a filter condition. The marked reference's resolved level selects its own coordinate from that environment, so parent and nested-descendant `$` references may resolve through different row coordinates, and `CurrentRepetition` over those paths may yield different indices. [§9 §3.1](07-repetition-and-iteration.md#31-the-filter-condition-and-its-static-gates) and [§9 §3.2](07-repetition-and-iteration.md#32-correlation--and-currentrepetition) own the marker's legality, the requirement that some filter reference stay unmarked, and how a marked read is judged statically.

Sources: [inbound 2026-09-26d marked read](../docs/sources/inbound-handbacks.md#inbound-2026-09-26d-marked-read).

---

## 4. Rows are addressed by semantic key, never by position ⚠

**The language has no positional row addressing** — no `[Field At n]`, no neighbour offset. A row is selected only by the value of its group's index field, through the semantic index; `CurrentRepetition` reads a coordinate as a number but selects nothing.

**`CurrentRepetition(G)`** yields a numeric index for comparison, arithmetic or `$` correlation ([§9 §3.2](07-repetition-and-iteration.md#32-correlation--and-currentrepetition)); it does not select a row. For a repeatable group it yields the bound row coordinate; for a non-repeatable group it yields the constant `1`, so its semantic domain is a resolved group level, not only a repeatable level. `CurrentRepetition(G) == n` **cannot stand alone**; it must be combined with a condition ensuring the repetition is filled. **Its operand is refused by a first-hit cascade**, in this order:

| Operand | Class |
|---|---|
| a name that resolves to nothing | `MVK_INVALID_ENTITY` |
| a star on a fixed group | `MVK_INVALID_WILDCARD` |
| outside a filter, an unstarred repeatable level | `MVK_NO_WILDCARD` |
| a field, starred or not | `MVK_NO_FIELDS_ALLOWED` |
| a starred repeatable group | `MVK_NO_WILDCARDS_ALLOWED` |
| inside the filter, an unstarred fixed group | `MVK_NO_ITERATION_FOR_WILDCARD` |

The other unstarred groups are admitted: outside a filter an unstarred fixed group, and inside the filter the filtered repeatable group itself.

Measured from a root rule reporting on a root field, on a missing, a fixed and a repeatable group, each plain and starred, as the group and as a field in it, in an ordinary comparison and in a `Sum(Repeating*/Amount Having …)` body.

**The semantic index `[Field For key]` is the only row-selection form**, equivalently `Group For "value"` for a group: it addresses a row by an **index-field value** ([§4 B.4](03-empty-and-required.md#b4-the-index-fields-auto-generated-checks--mandatory-and-unique)). A key is a quoted literal or a path to a keying field. **A key written without quotes is no literal:** a digit sequence is a path, as a bare `1` is in a `Date` component, so on a Number index `For 1` resolves as a name and draws `MVK_INVALID_ENTITY` where no entity carries it, while `For "1"` selects the row keyed `1`. The same holds over a String, an Enumeration and a Number index alike, a leading zero included, while an unquoted decimal does not parse and draws `MVK_UNEXPECTED_TOKEN`.

#### The key and the index group

**A key addresses the level of its index group, and only that level.** The index group is the nearest repeatable group on the keyed entity's chain declaring an index field. A chain on which no group declares an index field draws `MVK_NO_INDEX_FIELD`. An index declared on the root or on a fixed group addresses no repetition, but it keeps the read from that class: from the root, `Sum(Cover/Items/Amount For "X") > 0`, with `Cover` fixed and `Items` repeatable and unindexed, draws `MVK_NO_INDEX_FIELD` with no index on the chain and the unbound `Items` level's `MVK_NO_WILDCARD` when the root or `Cover` declares one. Where that gate leaves the read legal the key is admitted as well: from the root, `[Cover/Amount For "X"] > 0`, `FieldFilled(Cover/Note For "X")` and the starred `Sum(Cover/Items*/Amount For "X") > 0`, and from a rule declared in `Items`, `[Amount For "X"] > 0`, each with the index on the root or on `Cover`. At runtime such a key selects the one instance of its index group: a stored index equal to the key reads the operand as the unkeyed read does, and a different stored index reads it empty, so `FieldNotFilled(Cover/Amount For "X")` fires and the starred `Sum` is `0`. With the index field empty neither the condition nor its negation fires, and the index field draws `mandatoryField`. Several index fields on the keyed path draw `MVK_MULTIPLE_INDEX_FIELDS`.

- **A sound key addresses its read.** Each operand gate measured, probed on an operand it refuses, answers with its own class, as for a read of a level the rule iterates, where the same read unkeyed from the root draws `MVK_NO_WILDCARD`.
- **Several repetition layers are not refused as such.** An unindexed repetition above the index group still needs the rule's own iteration. So from the root `Riders/Legs/Amount For "X"` over an unindexed `Riders` draws `MVK_NO_WILDCARD`, and from a rule declared inside `Riders` it reaches `Sum`'s arity class.
- **A star draws the class of where it stands against the index group:** at the index group's own level `MVK_SEMANTIC_INDEX_AND_WILDCARD`, on a level above it `MVK_SEMANTIC_INDEX_BELOW_WILDCARD`, inside the key `MVK_SEMANTIC_INDEX_WITH_WILDCARD`, and below it none: a star below the index group is admitted and expands inside the selected row (§4.1).
- **A field-valued key read from inside the indexed group itself** is refused `MVK_SEMANTIC_INDEX_CONTAINED_IN_INDEX`, so a rule iterating that group cannot key the lookup by its current row's own field. The same lookup keyed by a field outside the group, or by a literal, is admitted from that iterating locus.
- **A semantic index inside a filter body** follows [§9 §3.1](07-repetition-and-iteration.md#31-the-filter-condition-and-its-static-gates), which refuses it on an unmarked reference and gives a marked keyed read classes of its own.

#### A defective key answers before the operand's gate

| Defect | Class |
|---|---|
| no index field declared on the chain; an index on the root or a fixed group lets the operand's own gate answer (above) | `MVK_NO_INDEX_FIELD` |
| a field-valued key whose kind does not pair with the index field's (table below) | `MVK_INDEX_TYPE_INCONSISTENT` |
| a literal key the index field refuses (the shape table below) | `MVK_INDEX_VALUE_INVALID`, over an Enumeration index ahead of the operand's own filter too |
| a key that itself crosses an unbound repetition, outside a filter body | `MVK_SEMANTIC_INDEX_INVALID_ITER`; inside a filter body the filter's own classes answer |
| a key field declared without value validation | `MVK_INVALID_RAW_TYPE` |

`MVK_SEMANTIC_INDEX_INVALID_ITER` belongs to the key: the keyed value crossing an unbound repetition draws `MVK_NO_WILDCARD`, so the class says whether the refused read stood inside the key, not whether it carried one. The raw-key class holds in every selection carrier measured: field presence and absence, group presence, a bracketed read and a field-fill list. Of two reads, the one first in the text answers.

**A field-valued key pairs with the index field by base kind**, as a parallel iteration's two index fields pair with each other on the pairs measured ([§9 §2.2](07-repetition-and-iteration.md#22-static-gates)):

| Kind family | Members, each pairing with every other member |
|---|---|
| text | String, Custom |
| Number | Number at any scale |
| Enumeration | Enumeration over any values |
| temporal | Date of any format, DateTime, Time, date fragment |
| date range | date range only |
| Boolean | Boolean only |
| Confirm | Confirm only |

Kinds of different families draw `MVK_INDEX_TYPE_INCONSISTENT`: pairing is by base type, so a Boolean key beside a non-Boolean index field, a Confirm one included, is inconsistent, and a Boolean key beside a Boolean index field pairs. Measured in both directions on rules and computations; the measured splits include a date-range key beside a Date index field and the reverse, and a Number key beside a String index field; the measured pairs include a Date index with a Date and a DateTime key, and a date-range index with a date-range key.

#### The literal key's shape, one rule per kind

**A `For` literal is format-checked against the index field's declaration during code generation and refused `MVK_INDEX_VALUE_INVALID` when it does not fit.** The check is a shape, one rule per kind, and lookup normalization (below) does not widen it: a field with `minFractionalDigits = 2` rejects `For "250"` even though an admitted `For "250.00"` and a stored numeric `250` would normalize to the same lookup key. **Its digits are ASCII on every index kind:** an Arabic-Indic or fullwidth `5` against a Number index, and such digits anywhere in a Date or DateRange key, draw that class, although the document reader converts a stored Arabic-Indic Number.

| Index field kind | A literal key fits when |
|---|---|
| Number | it is an optional minus, ASCII digits, and a fraction after `.` or `,` whose digit count lies within the declared fraction bounds; no fraction counts as none, and a field declaring no fraction admits none. The integer digits and a leading zero are not asked, so `05` and `12345` pass where `+5` does not |
| temporal | it matches the declared format one digit per component letter, so `2020-13-45` passes `yyyy-MM-dd` |
| date range | it is two such dates around the declared separator |
| Boolean | it is exactly `true` or `false`, whatever stored values the Boolean declares: a Boolean declaring the custom values `J` and `N` refuses the keys `J` and `N` |
| Confirm | it is `true` only |
| String | it is nonempty, meets the declared length bounds and matches the declared pattern over the whole key, either failing refusing it |
| Enumeration | it is one of the stored tokens exactly, case-sensitively, and never a label |
| Custom | it meets only the field's own authored positive minimum and maximum lengths, absent or zero bounds being inactive; the registered runtime validator is not invoked, and no String pattern or line-break policy is inherited |

The String rule in detail:

- **The pattern is matched over code points**, so `😀` is one character to `[^0-9]{2}` and fails it where the key `😀a` passes, both beside the repertoire refusal.
- **The pattern is Java's, matched against the whole key.** Its dialect is confirmed on case-insensitive flags, escaped code points, class union, intersection and complement, and property classes, and on intersections with an empty or doubled operand, whitespace, range, Latin-1 and case-folded left operands, a raw `]` and `}`, and an escaped class delimiter; captured backreferences are unmeasured.
- **Line terminators reach both checks normalized in exactly one non-overlapping pass:** a CRLF becomes LF and a lone CR is kept, so authored `A\r\r\nB` fits as `A\r\nB`, four UTF-16 units, and authored `A\r\nB` as `A\nB`, three. Static fit must not normalize the already-decoded key again. Measured on literal keys written in the condition, which does not separate the key's own normalization from the condition text's: against the pattern `a\n` the keys `a` + LF and `a` + CRLF pass and `a` + CR fails, against `a\r` only `a` + CR passes, `a\r\n` passes none, a maximum length 2 admits all three and a minimum length 3 none.

A stored Custom index cell still undergoes its separate registered validation before it contributes a lookup key.

#### Key identity at lookup

**Index-key identity belongs to the declared index field.** For a **Number** index field, each admitted stored key and the requested literal or field-valued key are normalized numerically before lookup, so `5` and `5.00` select the same row. For every non-Number index field, lookup uses the exact internally stored text; a String key that resembles a Number is not numerically normalized.

**A field-valued String key and the stored index cells meet after the same one-pass ingestion normalization.** A CRLF spelling and an LF spelling are one key across lookup, the generated uniqueness check, a parallel join and the selected message pointer, while a lone CR stays distinct from LF and equal lone-CR keys still match. Measured on ordinary evaluated String keys, both runtime strategies agreeing.

#### Keyed operand admission

**Whether an operator admits a semantic-index operand is a property of the operator.** No verdict of column K, for a keyed or a category operand (§3.4), transfers to an operator whose cell does not state it; [§9 §3.5](07-repetition-and-iteration.md#35-entity-list-operand-admission) owns the group and entity-list carrier clauses. The first class of an operator's cell in column K of [the operator reference](14-operator-reference.md#keyed-and-category-operands):

| Class | Meaning |
|---|---|
| `selected` | admitted; the operand reads the selected row (§4.1) |
| `index refused` | refused `MVK_SEMANTIC_INDEX_NOT_ALLOWED` |

- Which group and entity-list carriers admit an indexed field or group, and that `NumberOfFilledGroups` and `RepetitionNotUnique` refuse one, is stated with those carriers in [§9 §3.5](07-repetition-and-iteration.md#35-entity-list-operand-admission).
- **`NumberOfFilledGroups` asks the index before the field kind:** a keyed lower-star field draws `MVK_SEMANTIC_INDEX_NOT_ALLOWED` beside a sound group operand in either order, and a keyed scalar field draws it before one, where the unkeyed field draws `MVK_NO_FIELDS_ALLOWED`.
- **A keyed group and a keyed field of it repeat only under one key:** `Sum(Claims For "X", Claims/Amount For "X")` draws `MVK_DUPLICATE_PARAM2`, and with the field keyed `"Y"` nothing repeats and `Sum` draws its number class.
- **A keyed field list whose star stands below the index group keeps its list role.** With the key on `Packages` and the star on its repeatable `Parcels`, `NumberOfFilledFields`, `NumberOfDifferentValues`, `NoFieldFilled`, `AllFieldsFilled`, `AtLeastOneFieldFilled`, `FieldValuesNotUnique`, `AtLeastOneFieldValueIncludedInValueList` against a literal or a field, `Sum`, `MinValue` and `MaxValue` over one or two such lists, and `SumOfProducts` are admitted under a string key, and `NumberOfFilledFields` and `NumberOfDifferentValues` under a field-valued key too. The same list with a `Having` draws `MVK_SEMANTIC_INDEX_NOT_ALLOWED`, and a `$`-marked list or a `$`-marked key from a root rule draws `MVK_INVALID_OUTER_ITERATION`.

#### A filter after a key

**A `Having` written after a field-valued key is the key's own filter.** The key is an entity specification, which takes a filter, while a string key is a literal and takes none; how the key's filter is walked is [§9 §3.1](07-repetition-and-iteration.md#31-the-filter-condition-and-its-static-gates)'s.

- After a field-valued key: in `Sum(Claims*/Amount For Reference Having [Claims/ClaimRef] == "X") > 0` the filtered entity is the unstarred key `Reference`, and the filter's `MVK_WILDCARDS_REQUIRED` answers where the same operand unfiltered draws the index's `MVK_SEMANTIC_INDEX_AND_WILDCARD`. The same class answers with the operand unstarred and on a starred group operand carrying the index. A group key draws `MVK_NO_GROUPS_ALLOWED`, and a starred key `MVK_SEMANTIC_INDEX_WITH_WILDCARD`, as it does unfiltered.
- After a string key the `Having` is the operand's. Starred, the index's `MVK_SEMANTIC_INDEX_AND_WILDCARD` answers, with a bad name in the body too. Unstarred, the filter's `MVK_WILDCARDS_REQUIRED` answers where the same operand unfiltered reaches the aggregate's `MVK_PARAMSIZE_INVALIDN`, while an unstarred group operand draws `MVK_NO_GROUPS_ALLOWED`.

Sources: [inbound 2026-09-27a current repetition](../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-current-repetition), [keyed message membership](../docs/sources/message-parameter-rendering-probes.md#src-keyed-message-membership-k15) (rows `f00`–`f03`, `f11`), [inbound 2026-10-09 extensions](../docs/sources/inbound-handbacks.md#inbound-2026-10-09-extensions) (KF532), [inbound 2026-09-25i key addressing](../docs/sources/inbound-handbacks.md#inbound-2026-09-25i-key-addressing), [K22 static batch 4](../docs/sources/group-count-topology.md#src-k22-static-s4), [handback rows 2026-10-23](../docs/sources/model-structure-and-declaration-probes.md#src-handback-rows-2026-10-23) (`raw-key`), [inbound 2026-10-23](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-23) (KF605), [inbound 2026-09-25b index type table](../docs/sources/inbound-handbacks.md#inbound-2026-09-25b-index-type-table), [K22 static batch 6](../docs/sources/group-count-topology.md#src-k22-static-s6), [inbound 2026-09-26 index key shape](../docs/sources/inbound-handbacks.md#inbound-2026-09-26-index-key-shape), [inbound 2026-09-26m index key pattern](../docs/sources/inbound-handbacks.md#inbound-2026-09-26m-index-key-pattern), [index text normalization](../docs/sources/message-cache-probes.md#src-index-text-normalization), [inbound 2026-09-30a regex operands](../docs/sources/inbound-handbacks.md#inbound-2026-09-30a-regex-operands), [inbound 2026-09-27a index key dialect](../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-index-key-dialect), [inbound 2026-09-25i literal key](../docs/sources/inbound-handbacks.md#inbound-2026-09-25i-literal-key), [index-key literal fitting](../docs/sources/path-resolution-class-probes.md#src-index-key-literal-fitting), [inbound 2026-09-25i keyed duplicate](../docs/sources/inbound-handbacks.md#inbound-2026-09-25i-keyed-duplicate), [inbound 2026-09-27a keyed lower lists](../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-keyed-lower-lists), [inbound 2026-09-25c key filter](../docs/sources/inbound-handbacks.md#inbound-2026-09-25c-key-filter); a12-dmkits [KF479](../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf479) and [KF351](../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf351), [inbound 2026-10-27](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-27), [unknown-scale and root-index batch](../docs/sources/static-admission-and-class-probes.md#src-unknown-scale-and-root-index), [runtime open-cells probe](../docs/sources/model-structure-and-declaration-probes.md#src-runtime-open-cells).

### 4.1 What a semantic-index read yields

**The index column a lookup reads belongs to the enclosing parent instance bound by the current evaluation**, not to every instance of the index-field declaration in the document. For an indexed group below an unindexed repeatable parent, the column holds the index cells of that parent's rows only. Equal keys in different parents do not collide, a duplicate or invalid cell affects reads within its own parent binding only, and selection replaces only the indexed coordinate, preserving the enclosing bindings. A row beyond its group's declared capacity contributes nothing to the column (unmeasured for the semantic index; the parallel join's measured rule, [§9 §2.3](07-repetition-and-iteration.md#23-join-construction)).

**A repeatable level below the index group that the rule iterates is read at the rule's own row.** Selection replaces the index group's coordinate only. From a rule iterating `Slots` below a repeatable `Bins` indexed by `BinCode`, `[Qty For "b"]` reads bin `b`'s slot at the firing slot's row, a rule iterating `Cells` below `Slots` reads bin `b`'s cell at its own slot and cell rows, and a star below the key reopens its level. A row the selected group lacks reads empty, as a clean no-match does, so `FieldNotFilled(Qty For "b")` fires on it; this is measured on a Number field, and other kinds are unmeasured. A keyed read crossing a repeatable level below the key that the rule does not bind draws `MVK_NO_WILDCARD`, as the unkeyed read would. Measured in full validation, both strategies agreeing, on Number reads, their fill and a starred `Sum`; computation and partial validation below the key are admitted statically but unmeasured at runtime.

**A column is compromised when any of its in-capacity index cells is empty, duplicated or formally invalid.** A duplicated value marks every participant `uniqueIndex` ([§4 B.4](03-empty-and-required.md#b4-the-index-fields-auto-generated-checks--mandatory-and-unique)). Such a cell is never a selectable entry, and a duplicated value is unavailable rather than resolved by row order. A column with none of these is clean, or formally available. Under partial validation, which index cells the column takes and when a no-match decides are [§12 §5.5](10-validation-and-polarity.md#55-a-selection-that-resolves-to-no-row)'s.

**A validation read yields, by what the key selects** (a computation read is §4.2's):

| Selection | Validation read |
|---|---|
| a matched filled cell | its value |
| a matched empty cell | the kind's empty value |
| no row carries the key, over a clean column | the kind's empty value |
| no row carries the key, over a compromised column (a duplicated key included) | UNKNOWN |
| a matched formally invalid cell | UNKNOWN, reporting only its own class |
| a field-valued key that is malformed or formally invalid | UNKNOWN |

- **The kind's empty value** is that of [§2 A.1](03-empty-and-required.md#a1-the-per-kind-default): a Number reads the fillable `0`, so `[X For "k"] == 0` fires and types OMISSION, and a String or a Date reads NOT-GIVEN. **A clean no-match is empty, never UNKNOWN.**
- **As a presence operand, an absent row is judged like an empty cell (FALSE):** `FieldNotFilled(X For "k")` fires when no row carries the key. A duplicated key is separated from a no-match by exactly this: the presence operand fires on the no-match and stays silent on the duplicate.
- **A malformed field-valued key is not a key that matches no row.** It makes every keyed consumer unusable. In validation it reads UNKNOWN under group presence and its negation, a multi-operand group quantifier, field presence of either polarity, a value comparison, and `FirstFilledValue` over the keyed group alike, so none of them fires, while a key matching no row fires the negative-presence consumers and a zero comparison over `FirstFilledValue`. In computation the same read poisons the precondition or operation holding it, so the table aborts rather than falling through to a later alternative. Measured for a Number index field keyed by a Number field holding malformed text.

**A keyed group operand reads the selected row's cells, a repeatable level below the key included.** `NumberOfFilledFields(Packages For "P1")` counts every filled row of a repeatable `Items` below the key, where collapsing that level to its first row counts fewer, and `AllFieldsFilled` reads that level's declared rows. A key no row carries reads every cell empty, and a key two rows carry is undecided while a deciding sibling operand still fires. A malformed cell in the selected row keeps `NumberOfFilledFields` and `NoFieldFilled` silent in validation; in computation `NoFieldFilled` over it poisons its alternative while `AtLeastOneFieldFilled` stops at the filled key. Statically, `Sum(Packages/Items For "P1")` over a repeatable group below the key draws `MVK_NO_WILDCARD`, and starred it meets `Sum`'s number gate. Measured on one model, both Kernel strategies agreeing.

**A star below a keyed parent expands inside the selected row.** With `P1` holding two `Items` weighing 2 and 5 and `P2` holding only its key:

- `Sum`, `NumberOfFilledFields`, `MaxValue` and `MinValue` of `Packages/Items*/Weight For "P1"` read 7, 2, 5 and 2.
- `NoGroupFilled(Packages/Items* For …)` is false for `P1` and true for `P2` and for an absent key.
- A duplicated `P1` leaves `NoFieldFilled` over the keyed star silent, and `NotAllFieldsFilled` silent over a keyed star or a keyed fixed group alike, since an undecided selection has no declared slot left to count as missing; beside it only an empty sibling operand fires it. An absent key fires `NotAllFieldsFilled` with OMISSION.
- `FirstFilledValue` falls through `P2`'s empty list to its next operand.
- The collection consumers read the same selected list: with `P1`'s items carrying `Sku` `S1` and `S2`, `AtLeastOneFieldValueIncludedInValueList(Packages/Items*/Sku For "P1" In "S1")` fires, `FieldValuesNotUnique` stays silent where `S1`/`S1` fires it, and `SumOfProducts` pairs two such lists by position ([§9 §3.8](07-repetition-and-iteration.md#38-sumofproducts)).

Measured on both runtime strategies.

**An absent selected lower list retains omission provenance.** For Number and String field or starred-group lists below a String index, a missing or empty key leaves the list empty and omission-bearing. `NoFieldValueIncludedInValueList` on either side and values-side `NotAllFieldValuesIncludedInValueList` therefore fire as OMISSION when their other operands permit a decision. This holds in full validation and, once the separate coverage requirements are satisfied, in partial validation.

**The same absence keeps a starred aggregate fillable.** A key that selects no row — no row carries it, it differs from every row's key, or it is empty — leaves `Sum` over a starred list below the key at the all-empty identity, able to grow and shrink ([§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing)), so a fired comparison over it is OMISSION. A computation's generated mismatch `[T] != Sum(Rows/Items*/N For Key)` shows it where the selected row's exhausted `Items` types VALUE. Measured for `Sum` in full validation; `MinValue`, `MaxValue` and `NumberOfDifferentValues` read the same selected list, and partial validation reaches it once the aggregate coverage gate admits the call, neither of which is measured.

Sources: [index group resolution](../docs/sources/model-structure-and-declaration-probes.md#src-index-group-resolution), [below-key selection](../docs/sources/model-structure-and-declaration-probes.md#src-below-key-selection), [semantic-index reads](../docs/sources/model-structure-and-declaration-probes.md#src-semantic-index-reads), [inbound 2026-09-25g keyed group](../docs/sources/inbound-handbacks.md#inbound-2026-09-25g-keyed-group), [inbound 2026-09-27a keyed parent stars](../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-keyed-parent-stars), [inbound 2026-09-30a keyed products](../docs/sources/inbound-handbacks.md#inbound-2026-09-30a-keyed-products), [selected-list declared extent](../docs/sources/group-list-and-capacity-probes.md#src-selected-list-declared-extent), [generated self-validation](../docs/sources/model-structure-and-declaration-probes.md#src-generated-self-validation-k14), [inbound 2026-09-23d malformed key](../docs/sources/inbound-handbacks.md#inbound-2026-09-23d-grandparent-fill-and-malformed-key).

### 4.2 Per-lookup (validation) vs per-column (compute)

**Validation and computation read the same parent-scoped column (§4.1) with different strictness.**

- **Validation judges per lookup.** A compromised cell *elsewhere* in the column does **not** suppress a clean match; the compromise matters only to an unresolved no-match, which then reads UNKNOWN and suppresses by the branch-scoped rule of [§3 B.4](02-logic-and-formal-errors.md#b4-suppression-is-branch-scoped-and-reaches-presence-checks).
- **Computation is stricter and judges per column.** Any compromised cell — malformed, duplicated or empty — poisons every computation read of that column, even one whose key matches a clean row, so every reading computation is cleared ([§11 §5.4](09-computations.md#54-parallel-joins), [§11 §3.2](09-computations.md#32-an-invalidity-clear-poisons)). Over a clean column a matched filled cell, a matched empty cell and a no-match read as §4.1's table gives for validation, while a matched formally invalid cell and a malformed or formally invalid field-valued key poison where validation reads UNKNOWN.

> **Non-normative implementation note.** Make indexed lookup phase-aware and return a `CellObservation`, with a clean no-match returning `empty`, never `unknown` or `poison`: this is the load-bearing difference from "missing ⇒ invalid", and it is why `[X For "k"] == 0` and `FieldNotFilled(X For "k")` fire on absence. Keep the two strictnesses as one explicit lookup policy over one resolved column. Keep `CurrentRepetition` a value-producing operand over a resolved group level, reading the named level's coordinate from the selected environment after `$` has chosen the captured one, give the AST no positional-select constructor, and fail closed on a missing or ambiguous repeatable binding.

### 4.3 Selected references in validation messages

**When the error field is referenced under one unique semantic-index key at a level the rule does not ordinarily or parallel-iterate, a fired rule replaces that level of its error address with the index cache's association for the key.** That level would otherwise be pinned to coordinate `1` ([§9 §1.1](07-repetition-and-iteration.md#11-iteration-scope)). The other error-address coordinates remain unchanged, and the replaced coordinate preserves its enclosing parent. The eligibility rule:

- **An ordinary message reference to the repeated error field**, directly or through a containing group operand, keeps physical iteration authoritative.
- Otherwise only semantic references targeting the repeated error field, or an ancestor group containing it, count. **Target identity is the authored syntax, not the runtime key:** repeated occurrences of one authored key do not compete; one exact authored key target carries its selected repetition, or `-5` on a clean no-match, using the deepest error-containing selector whatever the operand order (source reading, unmeasured); while two distinct key expressions — distinct literal keys or distinct key fields — retain ordinary error-row iteration, even when they normalize to one Number key or currently select one row.
- Sibling payload references add no pointer target.
- A target below the indexed group inherits its nearest indexed ancestor: the key selects that outer row, authored target-group coordinates remain independently iterated, and lower levels default to row `1` for message attachment.
- On the computation path, the current cascade overlay supplies both a field-valued query key and the selected scalar or group payload below an indexed ancestor.
- **A runtime failure's message is not reanchored:** it keeps the iterator's first error address ([§12 §3.1](10-validation-and-polarity.md#31-truth-testing-and-message-classification)). Source reading, unmeasured.

**The lookup is structural.** An independently firing branch can reanchor the error even when the selected payload is unavailable. A missing or empty key, or a key with no association, yields the unknown selected coordinate (`-5` in the observed external paths), and a duplicated key's coordinate is the cache association below. A field-valued key is read as a checked value, so a formally invalid key, or one outside a partial call's relevant set, selects no row even when its text equals a stored index. Unknown pointer coordinates do not change the no-match value semantics of §4.1. Source-derived; full and partial controls on invalid and duplicate keys corroborate the emitted-address distinction.

**A fired message's reference collection is structural too.** A selected operand contributes its payload field or expanded group descendants, the selected group's index field, and the key field when the key is field-valued; a literal key contributes no key-field pointer. These references remain present when another branch determines the outcome or the selected payload is invalid; reference membership is not an evaluation trace. A star below the selected level remains wildcard (`0`) on each expanded payload pointer, and the index-field pointer stops at the selected level. Below the selected level, a repeatable level the rule's own iteration binds names the firing row: a rule iterating `Slots` that reads `[Qty For "b"]` over a repeatable `Bins` index references the selected bin at the firing slot's row, and a rule iterating `Bays` below a root or fixed-group index references the firing bay. A level the read's own star reopens stays wildcard even where the rule iterates it. A rule binding some levels below the key reads the rest through its star, as `Sum(Cells*/Q For "b")` from `Slots` references `Cells[0]` at the firing slot; an unstarred lower level the rule does not bind is refused `MVK_NO_WILDCARD` (§4.1).

#### Duplicate keys and the index-association cache

**Pointer resolution reads the index cache independently of duplicate-invalid value evaluation**, so a duplicate key can leave a concrete selected pointer in a message fired by an independent branch. The association is an overwrite lookup over the admitted normalized index insertions (source reading); the retained duplicate controls rule out both first-physical-row and last-physical-row selection as the rule.

- **The winner depends on the whole cache population.** The order depends on every admitted entry in the temporary cache, unrelated fields and repeatable-group placeholders included: an unrelated valid field or an empty repeatable group can change the winning duplicate coordinate, while an empty or formally invalid field contributes nothing in the measured controls. Adding an empty outer parent can change a duplicate address within another parent, although the association itself is parent-local.
- **The host's bucket ordering is part of the semantics.** Physical-row order and an index-column-only fold are insufficient; the measured changes agree with the OpenJDK 21 bucket-capacity transitions. Collision-heavy caches can make the selected duplicate coordinate host-dependent: repeating identical model and document inputs under either runtime strategy has produced both row 1 and row 2. So model and document bytes alone do not determine every duplicate message address; the actual cache order or association must remain an explicit input for such observations. Neither an arbitrary stable tie-breaker nor a claim that every duplicate is ambiguous follows.
- **Uncertainty is local to the queried association.** A collision-sensitive key can coexist with separately determined selected-reference and parallel error coordinates, on full and partial calls, and an absent key still yields an unknown coordinate. Resolving one query must retain every admitted entry for its capacity and collision effects; it may disregard their unrelated associations, not their population contribution.
- **Defaults join after the original population.** An empty declared S-value supplies no default. Full validation appends eligible singleton Enumeration defaults to the cache **after** ordering the original admitted population, so a late default neither enlarges that population nor changes its duplicate winner, while the same token physically present from the start can cross a capacity threshold. Cache eligibility is distinct from authored readability: a formally invalid singleton index contributes no admitted original association, so its declared default can supply a message pointer while its original formal error remains and authored reads stay UNKNOWN. Partial validation adds no such association. Explicit requiredness, multiple rows and admitted explicit keys prevent default insertion.
- **Model-wide internal field names affect the order.** Colliding short names anywhere in the model receive suffixes in full-path order, authored suffix-shaped names being reserved, so renaming an index to collide with another field, or reserving a suffix with an unrelated field, can change a duplicate message pointer without changing its key values or physical rows.
- **Partial validation filters the population by caller relevance** before host ordering and overwrite. Relevant fields and their touched ancestor-group placeholders contribute; an unrelated field excluded by relevance can change a duplicate message coordinate even while the query and the duplicate rows stay relevant, and a concrete index-row selection excludes the other row's association. A concrete selector beyond a descendant's declared capacity can still make its in-capacity ancestors relevant: preserve the selector through ancestor projection, then exclude over-capacity physical groups and cells at admission, since dropping the whole selector first can change a duplicate pointer even when the selected excess cell does not exist. Partial default handling and rule-firing gates remain [§12 §5](10-validation-and-polarity.md#5-full-vs-partial-validation)'s, independently of this structural projection.

Measured scope: full validation covers String keys, Number payloads, selected groups and lower stars; the partial population matrix covers String keys, Number payloads and selected field, group and lower-star references. Other host profiles require their own calibration.

**The OpenJDK 21 full-validation profile.** Document traversal inserts index entries for a group and parent in ascending physical-row order; list-bin insertion prepends entries, and non-tree resizing preserves their relative order. So among duplicate candidates in the greatest occupied bucket, a bin that never treeified selects the smallest physical row. A currently small bin does not establish that premise, since it may have split from a tree, and collision-driven early growth can leave capacity 32 or 64 depending on unrelated insertion timing. A document-only reduction is justified only when every remaining capacity possibility yields the same association and the bin-order premise is established. Measured on a no-filler control, which confirms the list-bin winner; other capacities and tree histories are unmeasured.

Sources: [selected error reanchoring](../docs/sources/message-cache-probes.md#src-selected-error-reanchoring), [selected message reference resolution](../docs/sources/message-and-pointer-probes.md#src-selected-message-reference-resolution), [inbound 2026-10-13](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-13), [cache population order](../docs/sources/message-and-pointer-probes.md#src-message-cache-population-order), [cache collision](../docs/sources/message-and-pointer-probes.md#src-message-cache-collision), [query isolation](../docs/sources/message-cache-probes.md#src-message-cache-query-isolation), [defaults and names](../docs/sources/message-cache-probes.md#src-message-cache-default-and-names), [partial population](../docs/sources/message-cache-probes.md#src-message-cache-partial-population), [partial topology](../docs/sources/message-cache-probes.md#src-message-cache-partial-topology), [inbound 2026-10-28](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-28), [below-key selection](../docs/sources/model-structure-and-declaration-probes.md#src-below-key-selection).

---

## Checklist for §10

- [ ] Keyword-named segments are quoted; `RuleGroup` is the rule's group and counts as an error-field reference; its semantic-index suffix needs an index group, and `RuleGroup*` is refused.
- [ ] An up-step stands only in the leading run and chains only through `/`; a misplaced one is `MVK_UNEXPECTED_TOKEN` once any walked prefix has cleared its gates; a message parameter never walks the prefix.
- [ ] A star on a `..` step is `MVK_INVALID_WILDCARD_REL`, so that ancestor repetition needs an absolute path; a later named segment after `../` may be starred.
- [ ] An empty group is legal to declare and refused when named, once its star is right.
- [ ] Bare-name resolution: declaring group, then the flag-gated model-wide unique field lookup on a relative path's first segment only (distinct not-unique error, never a silent pick); no implicit ancestor walk; a `..Name` turning point is a guard, not a hop.
- [ ] A star stands only on a repeatable group, every lower repeatable level starred too; a misplaced star is `MVK_INVALID_WILDCARD`, answering alone per defect.
- [ ] A bracketed read asks the reader's classes, then the group, star and value gates, as its bracket closes; an operator parameter asks the reader's classes and the group gate, then its operator's own gates.
- [ ] A category read of a non-Enumeration is `MVK_NO_ENUMERATION`; an Enumeration category in an entity operand follows column K's category class.
- [ ] **No positional row addressing**; `CurrentRepetition` produces a number and selects nothing; the semantic index `[Field For key]` is the sole row selector, addressing the nearest repeatable index group's level.
- [ ] A literal key is shape-checked per kind in ASCII digits; lookup identity is numeric for a Number index and exact stored text otherwise; a keyed operand is admitted per column K.
- [ ] Semantic-index no-match over a clean column is **empty** (not UNKNOWN), and presence on absence is FALSE, so `FieldNotFilled(X For "k")` fires; over a compromised column it is UNKNOWN in validation and poison in computation; a malformed matched cell or key is UNKNOWN or poison.
- [ ] Validation reads **per lookup**; computation reads **per column** (stricter).
- [ ] A unique authored key on the error field reanchors that error-address level from the index cache's association; duplicate-key addresses depend on the cache population and host order, which stay an explicit input.
