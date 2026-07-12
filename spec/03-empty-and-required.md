# 03 — Empty values and the "required" property (§2 + §4)

Two joined topics:

- **§2** — how an *unspecified* operand behaves. This is the **single most common source of real-world rule bugs**, because a document spends most of its life half-empty, and the same comparison shape silently changes meaning with the operand's type.
- **§4** — the "required" property, which is not a runtime flag but *expands into a generated rule* and *manifests as a formal error* — so it is really a §2/§3 topic wearing an editor hat.

The third cell state (formally-invalid) is [§3](02-logic-and-formal-errors.md)'s subject; here "empty" always means *unspecified*, never *invalid*.

---

## Part A — §2 Non-specified (empty) values

### A.1 The per-kind default

How an unspecified field affects a comparison depends on its **type**:

| Field type | Unspecified value in a comparison |
|---|---|
| **number** | a default of **`0`** is substituted |
| **confirm** | treated as **`False`** |
| **string, date, boolean, enumeration, custom** | the comparison is **not evaluated** (no error, no fire) |

```
[Amount] < 100          -- number: FIRES on an empty Amount, because 0 < 100
[Date] > "01.01.2022"   -- date: does NOT fire on an empty Date (not evaluated)
```

⚠ This is the trap. To avoid flagging an empty number, guard it:

```
FieldFilled(Amount) And [Amount] < 100
```

Two immediate riders:

- The `0` substitution does **not** apply to minimum/maximum *aggregate* calculations — there, unspecified fields are *ignored* (see A.3–A.4; note the operand-list `Min`/`Max` are a *different* family that *does* substitute).
- **There are no empty strings.** `[F] == ""` is never satisfied, even when `F` is unfilled — and neither is `!= ""`: a string comparison with an empty operand on *either* side (a literal `""`, or an empty coercion result) is **not evaluated**, for both `==` and `!=`. Use `FieldNotFilled(F)` to test absence.

> **Lean modelling note.** Resolve an operand read to a small sum that carries *both* the kind's substitution and the "was it actually given" bit polarity needs later ([§12](10-validation-and-polarity.md)):
> ```lean
> inductive Operand where
>   | value (v : Value) (given : Bool)   -- given=false ⇒ a substituted default (0 / False)
>   | notEvaluated                       -- string/date/bool/enum empty ⇒ the comparison yields notFired
> ```
> Then a comparison over any `notEvaluated` operand short-circuits to *not-fired*, a number-empty reads `value (num 0) (given:=false)`, a confirm-empty reads `value (bool false) (given:=false)`. The `given` bit is what makes a fired comparison OMISSION vs VALUE downstream.

### A.2 Where an operator overrides its kind's default

The per-kind table is only the *default*. Several operators route an empty operand through a different door, so the *same* empty field gets the free pass in one position and is evaluated in the next:

| position | an empty operand… |
|---|---|
| a string in a `+` **concatenation** | concatenates as `""`, so the enclosing comparison **is** evaluated — `[Full] != [First] + " " + [Last]` mis-fires on empty parts unless guarded |
| **`Length(F)`** | reads as length **`0`**, evaluated — the string family's own empty-as-`0` backdoor; needs a `FieldFilled` guard like a number |
| **`PatternMatched` / `PatternViolated`** | **not evaluated** — an empty string violates no pattern; test absence with `FieldNotFilled` |
| the date/time **extractors** (`DayFromDate`, …) and date **differences** | read as the fillable **`0`** — the enclosing comparison is evaluated and can fire |
| **value-list membership** | an empty subject makes membership **UNKNOWN** (neither the "included" nor the "not-included" form fires); an empty numeric list *entry* never matches (the `0` substitution does not apply to entries) |
| the **count family** (`NumberOfFilledFields`, `NumberOfValueInFields`, …) | an empty cell is **never counted** (`NumberOfValueInFields(0 In …)` does *not* count an empty number as a match for `0`), but the count stays *growable* — a fired comparison types **OMISSION** |
| operand-list **`Min([A],[B])` / `Max(…)`** | an empty **NUMBER** operand is substituted `0` and **competes in the fold** (the `0` can win); an empty **DATE** operand is **skipped** (the date-bearing side wins) |
| the field-list / starred aggregates **`Sum` / `MaxValue` / `MinValue`** | the empty cell is **dropped from the fold** — `MaxValue(-5, empty)` is `-5` (no `0` folded in); `Sum` reads it as `0`, which for a sum is the same thing |

The last two rows are one design split seen from both sides, and they resolve the "min/max ignore empties" rider above: the **aggregates** `MaxValue`/`MinValue` drop empties; the **operand-list** `Min`/`Max` substitute. `0` is `Sum`'s neutral element but not min/max's, which is *why* the aggregates must drop empties where `Sum` may fold them.

### A.3 What an all-empty selection folds to (the aggregate identities)

"One operand empty" (A.2) and "the *whole* selection empty" are different questions. Each aggregate has a defined identity for the all-empty case:

- **NUMBER aggregates fold to the fillable `0`**, not "undefined": `MaxValue(A,B) == 0` fires with both empty; `MinValue(Items*/Count) == 0` fires on a group with *no rows at all*. `Sum` over an all-empty list is likewise `0`.
- **DATE `Min`/`Max` fold to *no value*:** a comparison against an all-empty date aggregate never fires; a *computation* of it CLEARS its target.
- **`FirstFilledValue` follows its operand *kind*:** an all-empty selection yields the fillable `0` for a NUMBER operand, but *no value* (NOT-GIVEN) for a DATE or STRING operand.

⚠ This identity is treacherous because it hides under most thresholds: `0` and "not evaluated" produce the *same* non-fire for `MaxValue(…) > 3`, so a wrong mental model survives every such rule and only surfaces where `0` itself satisfies the comparison — `MinValue(…) < 10` is the shape that finally distinguishes them.

### A.4 The row gate — where the substitutions stop

All of the above happens **inside a content-bearing row.** Under full validation, an entirely empty instance is evaluated only when the condition is one that *can* fire on emptiness — a *structural* property of the condition, true of the negative-presence family (`NoFieldFilled`, `FieldNotFilled`, `NotAllFieldsFilled`, …) and composing through `And`/`Or`. A plain comparison **never** fires on a truly blank instance, so the empty-as-`0` rows above presuppose some sibling content.

One wrinkle in "what counts as content": an **instantiated repeatable row is itself content** — a created-but-blank repeat row *is* evaluated, so per-row empty-as-`0` fires on every such row — whereas a non-repeatable group's bare structural presence is *not* content. Partial validation overrides the gate entirely: a *relevant* instance is always evaluated, even empty or phantom ([§12](10-validation-and-polarity.md)).

> **Lean modelling note.** The row gate is easy to miss and produces "fires on a blank document" bugs. Model it as a predicate `canFireOnEmpty : Ast → Bool` (structurally: true for the negative-presence predicates, closed under `And`/`Or`), and gate a row's evaluation on `hasContent(row) ∨ canFireOnEmpty(cond)`. Treat an instantiated repeatable row as `hasContent := true` by construction.

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

The **"Only if the Parent Group is filled"** option changes *which* group is referenced — and for a nested field the referenced group differs between the two modes:

| Field (location) | Parent-filled = **no** | Parent-filled = **yes** |
|---|---|---|
| `F1` (in group `A`) | `FieldNotFilled(F1)` | `GroupFilled(A) And FieldNotFilled(F1)` |
| `F5` (in group `C`, nested under `K`) | `GroupFilled(C) And FieldNotFilled(F5)` | `GroupFilled(K) And FieldNotFilled(F5)` |

"The parent is filled" uses the *same* content notion as `GroupFilled` ([§9](07-repetition-and-iteration.md)): a **repeatable** parent counts a created-but-empty row (so a conditionally-required field can flag a row the user added but left blank); a **non-repeatable** parent counts a filled descendant — *including an instantiated repeatable descendant row*, not only a valued field.

### B.2 Required manifests as a *formal error*

A required-by-checkbox, unfilled field eventually produces a **formal error** — so the field becomes "unknown" to authored validation rules ([§3](02-logic-and-formal-errors.md)). That is *stronger* than the equivalent author-written `FieldNotFilled(F)`, which leaves the field evaluable. The required-and-empty "unknown" is branch-scoped like any formal error: `[ReqNum] < 100` is suppressed, but `[ReqNum] < 100 Or <VALUE-true>` still fires.

The generated rule and the formal finding cannot be installed as one eager check. Start with the base checked cells, where `formalCheck` has applied only ordinary local checks. Evaluate the generated mandatory condition against that base view and retain its `mandatoryField` hit/message. Only on a hit, and only after retaining the message, annotate the empty target cell with the validation-scoped `.required` finding used by subsequent authored rules. If the annotation came first, the generated rule's own `FieldNotFilled(F)` would read UNKNOWN, suppress itself, and never produce the mandatory message: requiredness would be defined by a circular self-suppression.

⚠ **The compute/validate asymmetry.** For *validation*, a required-and-empty cell is UNKNOWN (a formal error). For *computation*, the same cell reads as **plainly empty** (a number reads `0`) — compute does not treat "required" as invalidity. This asymmetry is load-bearing in [§11](09-computations.md).

### B.3 The "mandatory" star is a heuristic, not ground truth

Some UIs show a star for mandatory fields, computed by a fixed "star method" that inspects a fixed set of constructs. **Starred fields are always mandatory, but not every mandatory field is starred** — deciding mandatoriness in general is not effectively decidable. A missing star therefore does **not** imply optional. (This is a UI concern; a reimplementation of *evaluation* can ignore the star entirely — only the generated rule matters.)

### B.4 The index field's auto-generated checks — mandatory *and* unique

A repeatable group can declare an **`indexFieldName`**. That single declaration arms **two** automatic checks, with no authored rule:

- the index field is **auto-required** (parent-filled semantics), drawing `mandatoryField` on an empty index cell;
- its values are auto-checked for **uniqueness**: the engine emits `uniqueIndex` on **every** row whose non-empty index value duplicates another's (*not* all-but-first), scoped **per parent row**, as a **VALUE** error. An empty index value is *excluded* from the uniqueness check and draws `mandatoryField` instead.

A duplicate-flagged cell enters the third state ([§3](02-logic-and-formal-errors.md)) **field-locally**: rules reading *that* field on those rows are suppressed (branch-scoped), while a sibling field's rules on the same rows still fire; and an aggregate or count over a starred index column carrying any duplicated-or-mandatory-empty cell is non-evaluable.

Because the engine generates both checks, a model must **not** also author the equivalent rules — they would double up. (The index field is also the join key for parallel iteration and the semantic index; [§9](07-repetition-and-iteration.md).)

> **Lean modelling note.** Treat "required" and "index field" as *desugaring passes* over the model that emit ordinary generated rules **plus** staged checked-cell annotations from [§3.B.3](02-logic-and-formal-errors.md#b3-what-puts-a-cell-in-the-third-state). Concretely, a `required` flag emits a `mandatoryField` rule with the ancestor-decided condition. Validation evaluates that rule on the base `formalCheck` result, retains any hit/message, and only on a hit adds `.required` to the empty target for authored-rule observation; computation ignores this validation-scoped annotation. An `indexFieldName` emits the mandatory rule, the per-parent-row uniqueness check (marking *all* duplicate participants `notCheckRelevant`), and registers the join key. Doing this as desugaring keeps the evaluator's core small and mirrors how the real engine treats these as generated, not special-cased.

---

## Checklist for §2 + §4

- [ ] Operand reads carry the per-kind substitution **and** a `given` bit; `notEvaluated` short-circuits comparisons.
- [ ] The per-operator overrides (concat, `Length`, patterns, extractors, value-list, counts, operand-list `Min`/`Max`, aggregates) each behave per A.2.
- [ ] All-empty aggregate **identities** per kind (NUMBER→`0`, DATE min/max→no value, `FirstFilledValue`→by kind).
- [ ] The **row gate**: substitutions only inside content-bearing instances; instantiated repeatable rows *are* content.
- [ ] `required` desugars to the ancestor-decided generated rule; validation evaluates and retains that rule's message on base checked cells before adding the target's validation-scoped `.required` finding, and computation reads the cell empty.
- [ ] `indexFieldName` desugars to mandatory + per-parent-row uniqueness (every duplicate flagged), and registers the join key.
