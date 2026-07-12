# 13 — The Lean encoding guide (the consolidated plan)

This gathers the per-file `Lean modelling note` callouts into one actionable head-start for a Lean 4 formalization. It is opinionated: it recommends a **type design**, names the **encoding traps** that break naive attempts, proposes a **staged build order**, and lists the **properties worth proving/testing**. Read the deep-dive files for the *why* behind each; this is the *how to start*.

The stance is *semantics-first*: the goal is a faithful **executable specification** (`#eval`-able, property-testable) whose behaviour matches the engine — proofs about it are a later, optional layer that this design tries not to obstruct.

---

## 1. The core types

Six types carry the language. Get these right and the rest is filling in operator clauses.

```lean
/-- (a) A number's scale is a STATIC field property, not a runtime datum. -/
structure NumField where
  scale       : Nat        -- max fractional digits (always bounded; missing ⇒ 0)
  signed      : Bool       -- `positivesOnly = false`; drives fillability, NOT minValue

/-- (b) The three cell states — empty ≠ invalid. This is non-negotiable. -/
inductive CellState where
  | empty
  | filled (v : Value)
  | notCheckRelevant        -- present but formally invalid ⇒ "unknown"

/-- (c) The value domain (sketch — expand per kind). -/
inductive Value where
  | num  (d : Rat)          -- exact; rescale explicitly at the §5 points
  | str  (s : String)
  | bool (b : Bool)
  | conf (b : Bool)         -- Confirm: empty reads False
  | date (d : CalDate)      -- with precision; an unreal date is a *non-value*, see below
  | enum (stored : String)  -- compared by stored token
  -- date-time, time, fragment, range, custom …

/-- (d) Kleene truth. No negation combinator exists. -/
inductive K where | tru | fls | unknown

/-- (e) The firing outcome = truth × polarity, folded into one 3-way lattice. -/
inductive Outcome where | firedValue | firedOmission | notFired

/-- (f) The iteration environment: a binding of each enclosing repeatable level to a row. -/
abbrev Env := List (RepeatableLevel × Nat)
```

And the two top-level functions the whole set builds toward:

```lean
def eval    : Ast → Env → Document → EvalResult          -- EvalResult ≈ { truth : K, pol : Polarity, fill : Fillability }
def compute : Model → Document → (Path → Env → ComputeOutcome)  -- VALUE / CLEARED / ERRORED, with an order-dependent poison effect
```

Keep `compute` **outcome-producing**, not document-mutating; make `apply : Document → outcomes → Document` and `validate` separate, so the compute→apply→validate flow ([`01-data-model.md`](01-data-model.md)) is explicit and the poison stays contained in `compute`.

---

## 2. The ten encoding traps

Each has burned a real reimplementation; each is a place a "reasonable" design silently diverges.

1. **Two-state value domain.** Using `Option Value` cannot express *empty ≠ invalid*. Use the three-state `CellState`, resolved once at the read via a single `formalCheck`. ([§3](02-logic-and-formal-errors.md))
2. **Per-kind empty.** An empty operand's meaning depends on the field kind *and* the operator position (number→`0`, confirm→`False`, string/date→not-evaluated; overridden by concat/`Length`/counts/aggregates). Carry a `given : Bool` bit alongside the substituted value. ([§2](03-empty-and-required.md))
3. **Scale as a runtime datum.** Scale is *static*; it gates `==`/`!=` at *parse time* via a `scaleOf` derivation (`+`→max, `*`→sum, `/`,`^`→unknown). Don't attach it to the runtime decimal. ([§5](04-numbers-and-decimals.md))
4. **Forgetting the second lattice (polarity).** VALUE/OMISSION is computed from *directional fillability* propagated through the whole expression — a second interpreter pass parallel to truth. Budget for it up front; retrofitting is painful. ([§12](10-validation-and-polarity.md))
5. **Eager operand evaluation in `compute`.** Poison is *read-driven*: `And`/`Or` short-circuit and scans stop early, so an unread invalid cell must **not** poison. Thread reads through `Except Poison` with genuinely short-circuiting connectives — never evaluate-all-then-combine. ([§11](09-computations.md))
6. **Conflating the two "no values" in compute.** A precondition-clear cascades as EMPTY (implemented by *pre-stripping* computed inputs); an invalidity-clear POISONS (throw-on-read). Both mechanisms must exist and be distinct. ([§11](09-computations.md))
7. **Iteration scope from placement.** Scope = the *referenced* repeatable fields, never the node's tree position; empty scope ⇒ evaluate once. ([§9](07-repetition-and-iteration.md))
8. **Star binding.** Fix `Env` levels *strictly above* the first `*`; re-open the starred level and below. Same-group star spans *all* rows (only `$` correlates). This one function is ~half of §9. ([§9](07-repetition-and-iteration.md))
9. **Semantic-index no-match = unknown.** A no-match reads **empty** (fillable `0` / NOT-GIVEN), *not* UNKNOWN — so `[X For "k"] == 0` and `FieldNotFilled(X For "k")` fire on absence. ([§10](08-paths-and-references.md))
10. **The row gate & declared-vs-instantiated ranges.** Substitutions only inside content-bearing instances; `AllFieldsFilled` folds the *declared* range while `AtLeastOneFieldFilled` folds the *instantiated* rows. ([§2](03-empty-and-required.md)/[§1](02-logic-and-formal-errors.md))

---

## 3. A staged build order

Build the executable spec bottom-up; each stage is testable against the engine before the next.

1. **Scalars & literals.** `Value`, the number model with explicit rescale (constants **19 / HALF_UP / 50-digit**), the calendar (`AddMonths`/`AddYears` conventions, epoch sub-day, Gregorian floor), the string/date literal typer. Lock the rounding table and the `RoundDown([q]/3*3,0)==[q]` pre-round example. ([§5](04-numbers-and-decimals.md), [§6](05-dates-and-time.md), [§7](06-strings-and-enumerations.md))
2. **`CellState` + `formalCheck`.** Route all five invalidity sources ([§3](02-logic-and-formal-errors.md)) through one function; get *empty ≠ invalid* into the type.
3. **Kleene evaluation of flat conditions.** `K.and`/`K.or` (no negation), comparisons over the per-kind empty substitution, the individual negative predicates, the fill quantifiers (both ranges). Prove **monotonicity**. ([§1](02-logic-and-formal-errors.md), [§2](03-empty-and-required.md))
4. **Required & index desugaring.** Emit the generated `mandatoryField`/uniqueness rules + their (validation-scoped) formal-check sources. ([§4](03-empty-and-required.md))
5. **The iteration environment.** `iterationScope`, context enumeration, star binding, `Having`/`$` correlation, parallel-iteration outer join, `RepetitionNotUnique`'s two-phase cache. Property-test star binding on tiny models. ([§9](07-repetition-and-iteration.md))
6. **Paths.** Three-tier bare-name resolution, `..`/named-ancestor, semantic index (no-match = empty), the `..`+`*` rejection. ([§10](08-paths-and-references.md))
7. **Polarity.** Add the `Fillability` pass (`canGrow`/`canShrink`, sign-aware seeds; propagation through arithmetic/functions/aggregates/counts/dates/concat/`Having`); fold into `Outcome` with omission-wins-And / value-wins-Or. ([§12](10-validation-and-polarity.md))
8. **Computation.** The three outcomes, the empty-cascade (pre-strip) vs poison (throw-on-read, short-circuit), the stored form (render + reduced formal check), the delta reporting, the implicit-validation-rule desugaring. ([§11](09-computations.md))
9. **Partial validation.** Relevant-set gating, out-of-set = UNKNOWN, global auto-add, starred-aggregate-only-when-wildcarded, phantom rows. ([§12](10-validation-and-polarity.md))
10. **Interpolation & CustomCondition.** Pure `render` step; oracle-parameterized `custom`. ([§13/§14](11-messages-and-custom.md))

---

## 4. What to lock with property tests

The engine is the oracle; if a real instance is available, differential-test against it. Regardless, these internal properties are strong regression guards:

- **Monotonicity** — replacing a `U` (invalid/UNKNOWN) operand with any definite value never turns a *fired* result into *not-fired* against the fire direction (formalizes "suppression only hides errors"). ([§3](02-logic-and-formal-errors.md))
- **Determinism given a clock** — `eval`/`compute` are pure functions of `(model, document, injected clock, label provider, custom oracles)`; no hidden global reads. ([§6](05-dates-and-time.md), [§14](11-messages-and-custom.md))
- **Compute delta** — reporting `= project(computeAll, changedOrClearedOrErrored)`; unchanged cells are not reported. ([§11](09-computations.md))
- **Poison order-dependence is *intended*** — a test that an invalid cell beyond a short-circuit/scan-stop does **not** poison (a naive eager engine fails this). ([§11](09-computations.md))
- **`No` vs `NotAll`** — the value-list quantifiers are not duals; property-test their poison asymmetry on shared inputs. ([§8](06-strings-and-enumerations.md))
- **Star binding small cases** — hand-computed 1–2 row / 1–2 level expectations for same-group vs cross-subtree stars. ([§9](07-repetition-and-iteration.md))
- **Rescale order** — `RoundDown([q]/3*3, 0) == [q]` fires at `q=1`; the scale-19 pre-round is present. ([§5](04-numbers-and-decimals.md))
- **`Valid`/`Invalid` are not complements** — under a malformed part both are UNKNOWN; under an empty part `Invalid` fires OMISSION. ([§6](05-dates-and-time.md))

---

## 5. The clean-room boundary (if you port from a real engine)

The original engine is licensed such that a runtime *linking/shipping/calling* it, or a *line-by-line transliteration of its source*, is a derivative work. This specification is a description of **observable behaviour**, which is free to reimplement. So:

- **Do** read this set (and, if you have it, probe a real engine) to learn exact behaviour, then write **original** Lean and lock it against that behaviour with the property/differential tests above.
- **Don't** transcribe engine source expressions into Lean, and **don't** call the engine from the reimplementation. Copy the *mechanism*, never the *expression*.

This is exactly how the specification behind this document set was itself built — behaviour observed and re-expressed, never source ported.

---

## 6. One-paragraph summary

A faithful A12 evaluator is a pair of pure functions over a **three-state** value domain and an explicit **iteration environment**: `eval` produces a **truth (Kleene) and a polarity (VALUE/OMISSION)** together, and `compute` produces a **per-cell outcome (VALUE/CLEARED/ERRORED)** with an **order-dependent, read-driven poison** kept inside it. The genuinely hard parts — and the ones to build and test first — are the third cell state (empty ≠ invalid), the polarity second-lattice, the star-binding environment, and the compute poison. Everything else is careful but mechanical per-operator work.
