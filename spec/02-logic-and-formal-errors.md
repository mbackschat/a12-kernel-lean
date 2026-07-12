# 02 — Logic, truth values, and the "unknown" state (§1 + §3)

This is the core of the evaluation model, and the place a reimplementation most often goes wrong. Two ideas interlock:

- **§1** — the logic is two-valued (`And`/`Or` and the predicates are satisfied or not), there is *no* generic negation, and connectives need explicit parentheses.
- **§3** — but the *data* has a **third state** (present-but-formally-invalid = "unknown"), and when an operand reads it, the operand becomes UNKNOWN and ordinary Kleene `And`/`Or` decides how far that reaches.

The punchline: **only the data is three-valued; the logic stays two-valued and simply propagates the unknown.** Get the third state into your value domain from day one — a two-state `Option`-style value cannot express this language.

---

## Part A — §1 Truth values and logical evaluation

### A.1 Connectives are two-valued; parentheses are mandatory

`And` and `Or` are ordinary two-valued connectives. There is **no implicit precedence** between them — mixing them without brackets is a *parse* error (`MVK_BRACKET_MISSING`), not a default grouping:

```
( FieldFilled(A) And [A] <= 0 ) Or FieldNotFilled(B)      -- ok
FieldFilled(A) And [A] <= 0 Or FieldNotFilled(B)          -- rejected at parse time
```

The two bracketings mean different things, so the language refuses to choose. A reimplementation's parser should reject the un-bracketed mix rather than pick a precedence.

### A.2 There is no `Not`

The language has **no generic negation operator**. Every negative check is a *dedicated predicate* with its own evaluation logic. This is deliberate: it avoids ever having to define negation over the "unknown" state.

The consequence that bites: **positive/negative predicate pairs are not always logical complements.** You cannot assume `NotP ≡ ¬P`.

- `AllFieldsFilled(L)` vs `NotAllFieldsFilled(L)` — `NotAllFieldsFilled` holds when **at least one** field is unspecified, *including when none are filled*.
- `FieldsNotCollectivelyFilled(L)` holds when at least one **but not all** are filled — it *excludes* the all-empty case (so it is not the negation of "all filled").
- `NotExactlyOneFieldFilled(A,B,C)` holds for **0 filled and for 2+ filled**.

```
NotExactlyOneFieldFilled(A, B, C)   -- satisfied at 0 filled AND at 2+ filled
```

> **Lean modelling note.** Do **not** model predicates as `p` and `Not p`. Model each predicate as its own constructor in the AST with its own evaluation clause. There is no `K.not` combinator (§B below), and you will never need one — which is a feature, because Kleene negation would otherwise force awkward choices on the unknown value. Treat the non-complementary pairs as *distinct predicates that happen to read related*.

### A.3 Boolean is a three-state field *type* (distinct from three-valued logic)

Careful — two different "threes". The **logic** carries an unknown value (§B). Separately, the **Boolean field type** has three *states*: not-filled, `True`, `False`.

```
[Flag] == True       -- holds iff Flag is filled AND its value is True
[Flag] == False      -- holds iff Flag is filled AND its value is False
FieldFilled(Flag)    -- holds iff Flag has any value (True or False)
```

So `[Flag] == True` is **not** `FieldFilled(Flag)`, and an unset boolean satisfies *neither* `== True` nor `== False`. To say "not confirmed" for a Confirm field, write `[Confirm] != True`.

**Confirm vs Boolean** differ on the empty case: an unspecified **Confirm** reads `False` in a comparison; an unspecified **Boolean** leaves the comparison *not evaluated* (see [§2](03-empty-and-required.md)). At the storage tier: a boolean token is lowercase `true`/`false` (any other token is a formal error); a confirm accepts only `true` or unspecified — a stored `false` on a confirm is itself a formal error, consistent with "a checkbox whose only value is True".

### A.4 Fill quantifiers: group scopes and the two iteration ranges

The fill quantifiers (`AllFieldsFilled`, `NoFieldFilled`, `AtLeastOneFieldFilled`, `MoreThanOneFieldFilled`, `NotExactlyOneFieldFilled`, `NotAllFieldsFilled`, `FieldsNotCollectivelyFilled`) and the group quantifiers (`AllGroupsFilled`, `NoGroupFilled`, …) have subtle counting rules:

- **A group operand means "every field inside it, recursively."** A field-fill quantifier over a group expands to the quantifier over every descendant field, through nested subgroups; a repeatable group in the operand carries its `*` onto each descendant; a mixed group+field operand list is legal. Value aggregates (`Sum`, `MinValue`, `MaxValue`, `NumberOfDifferentValues`) over a starred group expand the same way.
- **Two iteration ranges over a starred scope.** `AllFieldsFilled` / `NotAllFieldsFilled` walk the **full declared range** — up to `repeatability`, an un-instantiated repetition reading *empty* — so `AllFieldsFilled(G*)` holds only when every *declared* row is filled. `AtLeastOneFieldFilled`, `NoFieldFilled`, `MoreThanOneFieldFilled`, `NotExactlyOneFieldFilled` clamp to the **instantiated** rows. `FieldsNotCollectivelyFilled` mixes them (≥1 filled over instantiated rows AND ≥1 empty over the declared range). On a non-repeatable scope the two ranges coincide.
- **Group quantifiers admit a starred single group only for the count-zero / count-≥1 members.** `NoGroupFilled(G*)` and `AtLeastOneGroupFilled(G*)` count *instantiated* rows — and a **created-but-empty row counts as a filled group** (a row is content; [§9](07-repetition-and-iteration.md)). The `AllGroupsFilled` / `NotAllGroupsFilled` / `GroupsNotCollectivelyFilled` family **rejects** the asterisk.
- **A formally-invalid cell counts in neither bucket.** A present-but-invalid cell (§B) is *neither* filled nor empty in a fill tally, and any invalid element makes a value aggregate non-evaluable.

> **Lean modelling note.** "Declared range vs instantiated range" is a real semantic fork, not an optimisation — encode both. A clean approach: give a repeatable group both its `repeatability` (declared) and its actual row count, and let each quantifier state which range it folds over. `AllFieldsFilled` folds over `0 .. repeatability-1` (missing rows = empty); `AtLeastOneFieldFilled` folds over `0 .. rowCount-1`.

---

## Part B — §3 Formal errors and the "unknown" state

### B.1 What a formal error is

A field whose value violates its **data-type configuration** produces a **formal error**. While it stands, the field is **"unknown"** to the kernel and **cannot be evaluated in any validation rule**. Formal errors:

- use a **fixed, non-authorable** message (contrast rule errors, which are authored and can be error/warning/info),
- are attributed internally to a sentinel rule path (`formalePruefung`) — so from the *author's* rule's viewpoint the rule simply produces nothing,
- **block the field from participating in any rule** (author rules never do this — only formal errors do).

**A would-be tautology is not one.** If `F` has a formal error:

```
FieldFilled(F) Or FieldNotFilled(F)     -- does NOT hold: F is unknown, so neither branch is satisfied
```

### B.2 The three cell states — the third one is *not* "empty"

A cell has three states: **empty**, **filled**, and **not-check-relevant** (present but formally invalid). The empty-value substitutions of [§2](03-empty-and-required.md) are the *empty* column only; an invalid cell answers "unknown" and lands differently everywhere:

| What reads the cell | empty cell | **not-check-relevant** (filled-but-invalid) cell |
|---|---|---|
| a comparison reading its value | per-kind substitution ([§2](03-empty-and-required.md)) | **UNKNOWN** — the branch cannot decide |
| `FieldFilled` / `FieldNotFilled` / fill quantifiers | a definite FALSE / TRUE (counts as empty) | **UNKNOWN** — counted as *neither* filled nor empty (so `NoFieldFilled` does **not** fire over it) |
| a value aggregate or count over a selection containing it | the empty cell is dropped or substituted | the **whole aggregate is non-evaluable** — the enclosing rule is suppressed |
| a computation reading it | the per-kind compute behaviour ([§11](09-computations.md)) | the read **aborts the computing instance** — compute's *poison* ([§11](09-computations.md)) |

The distinction *empty ≠ invalid* is the reason a two-state value domain cannot model the language: `NoFieldFilled` fires over empties but not over invalids; an aggregate substitutes/drops empties but goes non-evaluable on one invalid.

### B.3 What puts a cell in the third state

More than a type-format mismatch. The *same* mechanism (same "unknown", same suppression) is triggered by all of:

- **a malformed value** — the base case, *plus* two cross-kind baseline checks that run before any type-format check: legal charset (the model's `supportedCharacters`, else the full BMP `U+0000..U+FFFF`), and no leading/trailing blanks;
- **a declared-constraint violation** — range, length, pattern, digit counts, enum domain: a parseable-but-out-of-bounds value is *exactly as invalid* as an unparseable one. A value violating several checks reports the **first** in the engine's fixed precedence;
- **the "required" checkbox on an empty field** ([§4](03-empty-and-required.md)) — for *validation* this required-and-empty cell is unknown like any other formal error; for *computation* it reads as plainly empty (an important asymmetry, [§11](09-computations.md));
- **a duplicate index value** — the auto uniqueness check marks *every* participating cell, field-locally;
- **an over-repetition row** — a row beyond the group's declared `repeatability`, which also suppresses that row's ordinary checks.

> **Lean modelling note.** These are five *sources* of one state. Model a single `formalCheck : Model → Field → RawValue → CellState` that returns `filled v` or `notCheckRelevant`, and route *all* five sources through it, so downstream evaluation only ever sees the resolved three-state cell. Do not scatter invalidity handling across the operators — resolve it once, at the read.

### B.4 Suppression is branch-scoped, and reaches presence checks

A formal error does **not** remove the whole rule; it makes the reading operand UNKNOWN and Kleene `And`/`Or` decides the rest:

```
healthyTrue Or  [broken] > 0     -- still FIRES  (healthy branch decides)
healthyTrue And [broken] > 0     -- SUPPRESSED   (unknown absorbs the And)
```

A single-branch rule is just the case where branch-scoped and rule-scoped suppression look identical. The unknown reaches **even operators that read no value**: `FieldFilled(malformed)` decides nothing (it is UNKNOWN, not FALSE). And the suppression is **silent** from the author's viewpoint — the engine emits its own formal-error code on the sentinel path while the author's rule yields nothing; in a report the discriminator is the sentinel path vs the rule's own path.

### B.5 The strong-Kleene tables (the exact algebra)

The propagation follows strong three-valued Kleene logic (the third value is written `U`):

| `And` | T | F | U |   | `Or` | T | F | U |
|---|---|---|---|---|---|---|---|---|
| **T** | T | F | U |   | **T** | T | T | T |
| **F** | F | F | F |   | **F** | T | F | U |
| **U** | U | F | U |   | **U** | T | U | U |

Note the absorbing cases that make suppression branch-scoped: `F And U = F`, `T Or U = T`. There is **no** negation row — the language provides none, so you never need to define `¬U`.

> **Lean modelling note.**
> ```lean
> inductive K where | tru | fls | unknown
> def K.and : K → K → K
>   | .fls, _ => .fls | _, .fls => .fls
>   | .tru, .tru => .tru | _, _ => .unknown
> def K.or : K → K → K
>   | .tru, _ => .tru | _, .tru => .tru
>   | .fls, .fls => .fls | _, _ => .unknown
> ```
> A predicate that reads a cell produces `K` (not `Bool`): reading a `notCheckRelevant` cell yields `.unknown`; reading `empty`/`filled` yields a definite `.tru`/`.fls` per the operator's rules. A worthwhile property to prove: **monotonicity** — turning any `U` operand into a definite value can only move the rule from *not-fired* toward *fired* or leave it (no non-monotone flips). This is the formal statement of "suppression only ever hides errors, never invents them", and it is a strong regression guard.

### B.6 Validation *excludes*; computation *poisons*

The two operations treat the third state with opposite temperament — a difference that matters wherever computed fields chain:

- **Validation excludes.** An invalid cell drops out: tallies count it in neither bucket, aggregates over it go non-evaluable, referencing branches go UNKNOWN. Nothing propagates beyond the rules that reference it.
- **Computation poisons.** During `compute`, invalid cells are set up so that any *read* of one throws; the reading computation instance aborts, produces no value, is itself marked invalid, and that mark cascades to its dependents' reads in turn — **order-dependently**, because only cells an evaluation actually reads can poison it.

The compute side is the subject of [§11](09-computations.md); the key is that the *same* third state you handle by exclusion in validation, you must handle by an (order-sensitive) abort in computation.

---

## Checklist for a faithful reimplementation of §1 + §3

- [ ] Value domain has **three** states (`empty` / `filled` / `notCheckRelevant`), resolved once at the read.
- [ ] `And`/`Or` are strong-Kleene over `K = {T,F,U}`; **no** negation combinator.
- [ ] Parser **rejects** un-bracketed `And`/`Or` mixes.
- [ ] Negative predicates are individual constructors, **not** `Not p`; the non-complementary pairs behave as specified.
- [ ] Boolean has three field-states; `== True` ≠ `FieldFilled`; Confirm-empty = `False` while Boolean-empty = not-evaluated.
- [ ] Fill quantifiers distinguish the **declared** vs **instantiated** iteration ranges, and count an invalid cell as neither filled nor empty.
- [ ] Suppression is **branch-scoped** and reaches presence predicates (`FieldFilled(invalid)` = UNKNOWN).
- [ ] Monotonicity property holds (locking test).
