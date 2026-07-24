# 07 — Repetition, iteration, and cross-array evaluation (§9)

This is the kernel's most distinctive semantics, and the largest single reimplementation risk. A flat rule fires zero or one time; a rule over *repeatable* data fires **per row**, and several constructs turn it into what is effectively a small **query language over arrays** — joins, correlated subqueries, aggregates, uniqueness.

The mental model to hold: **iteration produces a set of repetition contexts** (the `Env` of [`01-data-model.md §2.1`](01-data-model.md#21-repetition-contexts-the-iteration-environment)), the rule is evaluated once per context, and each construct is *about how the environment is built and extended*.

---

## 1. When a rule iterates, and where its error lands

A rule **iterates when its condition contains an iteration-bearing repeatable reference.** Its **iteration scope is derived from the condition's references — never from the rule node's placement or from the error entity by itself.** An ordinary unstarred reference contributes its repeatable path. A starred operand contributes only the already-bound repeatable prefix strictly above its first `*`; the starred level and every level below it are reopened by that operand rather than added to the surrounding rule iteration. Candidate-local references inside `Having` likewise belong to the operand-local traversal rather than to the surrounding rule scope.

- The rule is evaluated **once per actual repetition present in the document**, preserving full parent coordinates and document order; an iterating scope with no actual row produces no evaluation, and each emitted message attaches to **that specific row**.
- Compatible nested references select the deepest ordinary nonparallel path. Incompatible sibling/cross-branch paths require the separate parallel-iteration construction; they are not merged positionally.
- The **error field must inhabit a scope compatible with** the derived iteration — a genuine cross-cardinality split is rejected (`MVK_ERROR_FIELD_NOT_IN_RULEGROUP`).
- The **error field must be *referenced* by the condition** — directly, or indirectly (an enclosing `GroupFilled(Group)` counts) — or the model is rejected (`MVK_ERROR_FIELD_NOT_REFERENCED`). This is an admission and error-targeting constraint, not another source of iteration levels.

Example: a rule with error field `Round` inside a repeatable `Poker` group, condition `FieldFilled(Poker/Round) And [Poker/Win_Loss] >= 0`, evaluates once per existing round and reports on the offending round.

Two boundary rules sharpen this:

- **The error entity alone is not an anchor.** A rule whose error field sits *deeper-repeatable* than its condition references keeps the *references'* scope (the error field does not deepen iteration on its own).
- **A rule with no repeatable (non-starred) reference evaluates exactly once**, anchored at its error entity, regardless of its declaring container's instance content. The declaring group matters only for resolving relative references.

> **Lean modelling note.** `iterationScope : Rule → Except ScopeError (Option (List RepeatableLevel))` is computed from the checked condition references. Compatible scopes merge by prefix and retain the deepest path; sibling paths fail into the separately specified parallel boundary. Rule assembly then proves that the checked error declaration is compatible with the derived scope and is referenced by the condition. `evalRule` enumerates the actual instantiated contexts (`Env`s) that assign a row to each level in scope, preserving complete parent coordinates and document order. Do **not** derive scope from where the rule node or error entity is declared. A rule with empty scope evaluates once at the root `Env`.

---

## 2. Parallel iteration — joining two repeatable groups by key

When a rule references **two repeatable groups where neither is nested in the other**, they are iterated **jointly, keyed by an Index Field** that must exist on each group and **share the same name and type**. This is an **outer join** over the index values:

```
FieldsNotCollectivelyFilled(Demand/Units, Capacity/Units)   -- iterated per shared Warehouse index value
```

**Constraints:** at most **one** index field on the error field's path and on each parallel-iterated group; parallel iteration is **not allowed over rules using `RepetitionNotUnique`**; and **negative conditions are not allowed in a parallel iteration** except alongside a positive condition.

**Mechanics (verified):**

- The iteration value-set is the **union** of the joined groups' index values.
- An **unmatched side reads "not specified"**, its pointer carrying the fixed sentinel repetition index **`-5`** (`IIdentifier.UNKNOWN`).
- An **invalid** index value (duplicated or empty) marks that group's index invalid for the parent, so references into it read three-valued **UNKNOWN** for unmatched values — which *suppresses* a negative operator like `FieldsNotCollectivelyFilled`.
- Non-repeatable intermediate groups are **transparent** to the join; a repeatable **non-indexed frame** is legal above exactly one joined group.

> **Lean modelling note.** This is a genuine outer join. Model it as: collect each group's `Map IndexValue Row`; the iteration keys are `keysOf(a) ∪ keysOf(b)`; for each key build an `Env` where a present side binds its row and an absent side binds the `-5` sentinel (read as "not specified"). Keep the sentinel explicit — several downstream reads (a negative predicate going UNKNOWN on the unmatched side) *depend* on distinguishing "absent" from "empty".

---

## 3. The filter `Having`, the `$` correlation, and aggregation

`Having` filters a repetition list (a `*`-path) down to the rows where a condition holds, **before an aggregate consumes it**:

```
Sum(Products*/Quantity Having [Products/ProductName] == "N33") > 100
```

The keep rule is exact: retain a candidate only when the filter condition is **known true**. A false or three-valued unknown result drops that row **before the aggregate or quantifier reads the selected consumer cell**. The filter otherwise uses the ordinary condition tables, so a dominating true `Or` may still decide despite an unknown sibling. In a standalone comparison, an invalid row-local operand drops only that candidate; an invalid captured-outer operand makes that comparison unknown for every candidate that reads it, so each such standalone filter drops.

Computation uses the same condition tree but not validation's unknown-as-drop projection: a formally invalid filter operand actually reached during computation poisons the reading computation. Filter and target reads are interleaved by one **kept-successor lookahead**. After a candidate is kept, the iterator searches through later false candidates until it finds the next kept candidate or exhausts the stream before the consumer reads the current candidate's target. A poison encountered during that search therefore wins over a filled current target. Once one successor has been kept, a terminal current target leaves every filter after that successor unread. This is neither eager filtering of the complete selection nor target-first row evaluation, and an earlier terminal authored operand still hides every later operand and its filter.

The **`$` operator** — usable **only inside a filter condition** — switches a reference from the candidate environment to the **complete captured outer repetition environment** of the iterating rule, turning the filter into a **correlated subquery** (e.g. "holidays whose date equals the current stop's ETA"). The reference's resolved repeatable level then selects its own coordinate from that environment: a parent-level `$` reference and a nested-descendant `$` reference may denote different repetition indices in the same rule instance. At least one unmarked reference must reach a repeatable level reopened by the filtered operand; an all-`$` filter or one whose unmarked references are confined to bound ancestor levels does not establish the filtered iteration and is rejected. Every other unmarked reference must be available from the candidate environment, while every `$` reference must be available from the captured rule environment. `$` is **not** optional sugar: a filter may only iterate the repetition levels the *filtered field* stars, so `$` is the **sole** way a filter references an out-of-scope (outer) field.

A same-group starred candidate set includes the current outer coordinate unless explicitly excluded; correlation does **not** imply self-exclusion. `CurrentRepetition(G) != CurrentRepetition($G)` compares the resolved repetition coordinate at level `G`, not an opaque physical-row identity. In a multi-star `A*/B*` candidate set, comparing only `B` can therefore exclude every candidate that shares the outer row's `B` leaf index across different `A` rows.

**Aggregation consumes an ordered resolved stream, not a mathematical set.** Authored entity-list entries retain their authored order, a group entry expands its fields in stable model order, and repetition coordinates advance in ascending order with the lowest nested repeat level changing fastest. `Having` selection occurs before the selected target is read, as above; the first selected formally unavailable or non-relevant target makes the aggregate unavailable immediately, so the suffix is not read. The internal kept-successor order still determines which reached filter or target failure occurs first, but the public computation result erases that source identity; a draining aggregate that reaches the same failure set therefore cannot expose filter-versus-target precedence, while a prefix consumer such as `FirstFilledValue` can expose which suffix was never reached. `Sum` performs no arithmetic step for an unspecified cell—the same numeric contribution as zero—but records that cell's own declaration for polarity. `MaxValue` / `MinValue` ignore unspecified fields; a Number list with none specified yields `0`, while a Date list yields no value ([§2](03-empty-and-required.md)). `Sum`'s per-step arithmetic is specified in [§5](04-numbers-and-decimals.md#5-internal-precision--the-constants-that-must-match-exactly).

The direct plain-field form of `Sum` / `MaxValue` / `MinValue` / `FirstFilledValue` / `NumberOfDifferentValues` requires at least two distinct resolved field references. A single group or flattened (`*`) operand is legal through the separate expansion route because it denotes a field scope rather than a singleton direct list. In an ordinary document model, duplicate checking rejects repeated direct non-wildcard references and indirect group/field overlap, but deliberately skips every wildcarded reference: the same flattened or filtered-star operand may therefore appear more than once and is consumed again at each authored position. Evaluation preserves that stream; it never silently deduplicates it. HModel wildcard checking is a separate profile.

`NumberOfDifferentValues` accepts one homogeneous value-comparable family: Number; String together with ordinary stored Enumeration; or mutually comparable date-like declarations. The Number overload identifies filled values by the same scale-19 equality as ordinary Number comparison and uniqueness. The String/Enumeration overload compares the evaluated String value or ordinary stored Enumeration token exactly after declaration-owned checking; String and stored-Enumeration fields may mix, the same token from either kind counts once, and category projection is not admitted. Every overload has integral result scale 0. Empty cells and declared-but-uninstantiated rows do not enter the set but leave its size growable; a reached filter makes the available count both-directionally fillable because later filling can alter membership; the first reached formally unavailable or non-relevant selected cell makes the aggregate unavailable. Repeating a wildcard slot still consumes its stream again, but equal repeated values do not increase the distinct count.

`SumOfProducts(A*, B*)` is a specialized pair aggregate rather than an ordinary flattened entity list. It accepts exactly two Number fields from the same repeatable group and model-instance/root-sequence coordinate; each path must contain a repeatable level, only its lowest repeatable level may carry an unrestricted `*`, and `Having` is rejected. The result scale is the sum of the two field scales. Evaluation constructs one common row environment stream and, in canonical row order, multiplies the two values from each environment and adds that product to the running total; every multiplication and addition uses the precision-50 boundary. An empty cell supplies numeric zero with its own declaration's directional missingness, while the first reached formal failure makes validation unavailable and computation poison. An omitted row at either path makes a successful validation result both-directionally fillable. Partial validation requires wildcard or ancestor all-rows coverage for both fields; enumerating every current concrete row or covering only one field is insufficient.

**The filter condition may not contain**: `CustomCondition`, `RepetitionNotUnique`, a semantic index, a parallel iteration, or a nested filter.

> **Lean modelling note.** A filtered star is `filter (fun candidateEnv => evalFilter cond candidateEnv outerEnv doc) candidates` — where `evalFilter` resolves a `$`-marked reference against the complete captured `outerEnv` and an unmarked reference against `candidateEnv`. Each resolved reference still names the repeatable level whose coordinate it reads. That two-environment split *is* correlation; collapsing `outerEnv` to one scalar “outer row” is incorrect. The filter-content restrictions are a well-formedness check on the AST.

---

## 4. Where a star binds — the anchor rules ⚠

This is the subtlest part. A `*` in an operand path controls which enclosing indices are *fixed* (inherited from the current row) versus *re-opened* (iterated over).

- A starred operand read from an iterating row binds the enclosing indices **only for the repeatable levels strictly above the (first) `*`** — the starred level itself **always iterates its full extent**. So a **same-group star spans *all* rows, not the current one** (only `$` correlates; a bare star never does). A multi-star operand `A*/B*/F` binds at the levels **above `A`**.
- Declared-tail completeness follows that same first-star boundary **hierarchically**. For `A*/B*/C*/F`, missing declared capacity at `A`, beneath any actual in-scope `A` row at `B`, or beneath any actual in-scope `A/B` row at `C` leaves an open tail; so does an instantiated selected leaf whose `F` cell is empty. The unfiltered star is structurally complete only when every reopened repeatable level is exhausted under every actual parent and no selected leaf is empty. A reopened level with no finite `repeatability` is always open. A repeatable level strictly above the first star remains bound, so unused capacity outside that bound row does not taint the operand. Comparing the flattened leaf-row count only with the deepest cap is invalid: a dense branch can numerically hide a missing outer or middle branch.
- A **cross-subtree** star binds only along the **shared named ancestry** — an enclosing row's index is never applied *positionally* to an unrelated chain, so a cross-subtree count or presence reads **identically from every iterating row**.
- A bare (unstarred) reference to an **index-keyed** repeatable group in a group-scope quantifier is an **iteration anchor of its own** — ancestor-or-self, per row, judging the *current* row's cells; a non-indexed repeatable group needs the `*`.

> **Lean modelling note.** Encode the rule literally: given the current `Env` and an operand path, keep the `Env` bindings for levels **strictly above the first starred segment**, and *re-open* (iterate all rows of) the starred level and everything below it. "Same-group star spans all rows" is then not a special case — it is what "re-open the starred level" *means* when the star is at the current level. The cross-subtree rule = only shared-ancestry prefixes carry a binding; unrelated chains start from a fresh iteration. Define tail completeness recursively over that reopened repetition tree: compare each actual parent's child coordinates with that level's finite cap, recurse through actual children, treat an absent cap as unbounded/open, and inspect selected leaf emptiness. Do not materialize the declared Cartesian product, and do not replace the recursive predicate with one flattened count. Property-test the environment and completeness functions against hand-computed small cases (1–2 rows, 1–2 levels).

---

## 5. `GroupFilled` and the other repetition rules

Validation presence for one concrete group instance is a product of three independent dimensions: `content` records formally admitted content, `erroneous` records whether a formally rejected descendant marked the group erroneous, and `relevance` is `NONE`, `PARTIAL`, or `FULL`. Do not collapse that state to one Boolean.

- Formally admitted content comes from a formally valid valued descendant, a duplicate index value admitted before uniqueness reports its error, or an instantiated repeatable descendant row. A created-but-empty repeat row is therefore content for itself and its ancestors. An over-limit row still supplies that structural content even though it receives `zuGrosseZeile` / `zuGrosseKontextnummer` and its ordinary row checks are suppressed.
- A malformed, custom-invalid, or constraint-invalid value rejected by formal conversion is not content. It independently marks every ancestor group erroneous.
- For a **repeatable** `G`, an instantiated row itself establishes content. For a **non-repeatable** `G`, the group's own structural node is not content; only the admitted descendant sources above count.

Under full relevance, the scalar predicates are exactly:

| admitted content | erroneous | `GroupFilled` | `GroupNotFilled` |
|---|---|---|---|
| no | no | false | true |
| no | yes | false | unknown/non-firing |
| yes | no | true | false |
| yes | yes | true | unknown/non-firing |

`GroupNotFilled` is therefore not Boolean negation of `GroupFilled`. Group-list tally and plain numeric group-count consumption are specified in [§1](02-logic-and-formal-errors.md#a4-fill-quantifiers-group-scopes-and-the-two-iteration-ranges).

Under partial validation, any relevant descendant gives each ancestor group at least `PARTIAL` relevance. Admitted content observed in that relevant slice is enough to establish `GroupFilled`; absence requires `FULL` relevance plus no content and no error. `FULL` relevance comes from an explicitly relevant group or ancestor, or complete relevant coverage of all declared descendant fields across deeper repeatable axes. One relevant empty descendant cannot prove absence.

- **Negative conditions** (those that hold when nothing is specified) are **not permitted** in combination with repeatable groups — the parser rejects them (`MVK_NEG_CONDITION_IN_ITERATION`) unless guarded, e.g. `GroupFilled(K) And AtLeastOneFieldFilled(K/F)`.
- **List predicates over a repeatable group with `*` consider all *possible* repetitions**, including unspecified ones, not only those holding data (the "declared range" of [§1](02-logic-and-formal-errors.md#a4-fill-quantifiers-group-scopes-and-the-two-iteration-ranges)).
- An instance **beyond the group's declared `repeatability`** draws the structural errors `zuGrosseZeile` / `zuGrosseKontextnummer` (**VALUE**) at the address-formal gate before scalar conversion, and the over-limit rows' ordinary checks are **suppressed** ([§3](02-logic-and-formal-errors.md)); creating that row still supplies structural content to its non-repeatable ancestors.
- **"At least N rows"** is expressible via the starred single-group count: `NumberOfFilledGroups(G*)` counts one repeatable group's instantiated rows *including zero*, so `NumberOfFilledGroups(Items*) < N` fires at 0…N−1 rows (the aggregate-consumed star does **not** put the rule into per-row iteration). **"At most N"** stays structural (`repeatability`).
- **`FieldValuesNotUnique(f1, f2, …)`** — or the starred `FieldValuesNotUnique(G*/f)` over a repetition's rows — fires when two of the operands' **present** values are equal: empties are skipped (two empties are not a duplicate), equality is the **typed** comparison (a scale-0 `5` equals a scale-2 `5.00`), and a formally-invalid operand **suppresses**.

---

## 6. `RepetitionNotUnique`, precisely ⚠

`RepetitionNotUnique(… @From Group)` checks uniqueness within a chosen reference group; the `@From` directive selects the scope (unique per order vs. unique across all orders). The verified mechanics:

- **Fires per row whose (composite) key duplicates another row's** within the scope — a composite key compares as the **tuple**. An **all-empty** key row is **skipped**, but among participants (≥ 1 key field filled) **empties match empties**. Polarity: all-filled duplicates are **VALUE**; a duplicate with an empty (fillable) key component is **OMISSION**.
- It is an ordinary per-row **3VL predicate leaf** in every model-legal `And`/`Or` tree. The duplicate relation is built over the full selected scope independently of every surrounding branch, then its per-row result composes through the ordinary verdict/polarity tables of [§12](10-validation-and-polarity.md#3-every-fired-message-is-typed--value-vs-omission-). A guard-false duplicate does not fire yet still makes its partner a duplicate; an RNU OMISSION under `Or` with a false sibling remains OMISSION, while an independently firing VALUE sibling wins. A negative-presence sibling that would let the iterating rule fire on a not-filled repetition is not model-legal (`MVK_NEG_CONDITION_IN_ITERATION`).
- A **formally-invalid key cell drops its row from the duplicate relation**, per key cell: malformed, duplicate-index, over-repetition, and **required-empty** cells all count as unknown — the distinguishing property is **requiredness, not emptiness** (an *optional*-empty cell is a valid null participant). A formal error on a **non-key** field of the same row does *not* drop it.
- Under **partial validation**, a row participates in duplicate construction only when every instance of every composite-key field in that row is relevant. If any key component is nonrelevant, that row is excluded; a duplicate cluster therefore exists only among rows whose complete keys are relevant. An independently decisive relevant branch in the surrounding Boolean tree may still fire.
- When RNU supplies the firing, `referenced` contains every key field in the current row and every duplicate peer row. A VALUE RNU firing has no `fillToFix` pointers; an OMISSION RNU firing projects that same complete duplicate-cluster key set into `fillToFix`. References owned by independent composed branches remain resolved at the current evaluated row rather than expanding over the duplicate peers. These are pointer sets, not ordered sequences.
- The **default reference group** (no `@From`) is the **first repeatable group below the rule group** on the key path, and uniqueness is checked per that group's **parent row** — a key two repeatable levels deep is checked across all inner rows of the whole outer scope, not per intermediate group. `@From` overrides.

The key list contains one or more direct plain field references. Groups, categories, wildcards, semantic-index accesses, and String fields configured without value validation are rejected, but there is no Number/String-only kind gate: every otherwise value-validating field kind is admitted. Runtime equality has exactly two branches. Number keys compare as the normalized numeric values of [§5](04-numbers-and-decimals.md); every non-Number key compares the exact internally stored text. A direct Enumeration key therefore uses its stored token—not display text or a category projection—and temporal keys do not acquire instant-based comparison merely because ordinary temporal comparisons do.

A model-legal condition contains at most one `RepetitionNotUnique` leaf. A second occurrence is rejected during consistency checking with `MVK_INVALID_COMBINATION_OF_REPETITON_NOT_UNIQUE`. This is an operator-specific model-legality constraint, not an evaluation rule and not an EBNF restriction.

> **Lean modelling note.** Two-phase, and the phases must be separate: **(1)** derive the duplicate multiset over the whole scope from eligible rows (under partial validation require every key component to be relevant; drop rows with any invalid/required-empty key cell; skip all-empty-key rows), computing which keys occur ≥ 2× and retaining their complete peer clusters; **(2)** expose the per-row RNU verdict as an ordinary leaf inside the complete Boolean tree, then project peer pointers only when that leaf contributes to the firing. The trap is folding a surrounding guard into phase (1) — the duplicate relation is branch-independent, so a guarded-away row still makes its partner a duplicate. Composite key = tuple with "empty matches empty" among participants; equality is the typed comparison of [§5](04-numbers-and-decimals.md)/[§8](06-strings-and-enumerations.md).

---

## Checklist for §9

- [ ] Ordinary iteration scope = compatible iteration-bearing condition references, **not** rule placement or the error entity alone; the error field must be referenced and scope-compatible; an empty derived scope evaluates once, while an iterating scope with zero actual rows evaluates zero times.
- [ ] Error field must be referenced by the condition and share its scope.
- [ ] Parallel iteration = outer join over the **union** of shared-index values; unmatched side = sentinel `-5` "not specified"; invalid index ⇒ UNKNOWN ⇒ suppresses negatives.
- [ ] `Having` keeps only known-true candidates before consuming their selected cells; false/unknown rows drop; `$` switches to the **complete captured outer environment**, and the resolved level selects its coordinate; same-group correlation includes self unless explicitly excluded; filter-content restrictions enforced.
- [ ] Aggregates consume entity/model/repetition encounter order; `Having` runs before the target read; the first selected unavailable target stops the scan; Number `Sum` retains each missing contributor's declaration for polarity.
- [ ] Star binding: fix levels **strictly above** the first star, re-open the starred level and below; same-group star spans all rows; cross-subtree binds only on shared ancestry. Tail completeness recurses per actual parent at every reopened finite level; unbounded reopened levels stay open; flattened leaf counts are insufficient.
- [ ] Group presence is admitted content × error × `NONE`/`PARTIAL`/`FULL` relevance, with distinct definitely-filled and definitely-empty projections. Rejected malformed-only content does not fill; duplicate-index values and instantiated repeat rows do; over-limit rows still fill ancestors structurally.
- [ ] Over-repetition rows ⇒ `zuGrosseZeile` (VALUE) + suppressed; negative-in-iteration rejected unless guarded.
- [ ] `NumberOfFilledGroups(G*)` counts rows incl. zero without per-row iteration; `SumOfProducts` uses one same-group lowest-star row stream, staged products/sum, summed scale, both-field relevance, and empty/formal/tail polarity; `FieldValuesNotUnique` uses typed equality, skips empties, and suppresses on invalid.
- [ ] `RepetitionNotUnique`: direct value-validating key fields only; Number equality versus exact stored-text equality for every non-Number; at most one leaf per model-legal condition (`MVK_INVALID_COMBINATION_OF_REPETITON_NOT_UNIQUE` on a second); branch-independent duplicate relation then ordinary legal `And`/`Or` composition; required-empty/invalid key cells drop the row; partial validation requires every composite-key cell relevant; peer-exact `referenced`/`fillToFix` projection; default `@From` = first repeatable below the rule group, per parent row.
