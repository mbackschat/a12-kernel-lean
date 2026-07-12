# a12-kernel-lean — encoding architecture & decisions

The *how* and *why* of the Lean encoding, layered on the language-neutral semantics in [`../spec/`](../spec/). The spec (start at [`../spec/SEMANTICS-MAP.md`](../spec/SEMANTICS-MAP.md), plan in [`../spec/13-lean-encoding-guide.md`](../spec/13-lean-encoding-guide.md)) stays the canonical semantics distillation; this file records the concrete Lean design decisions that operationalize it, and what was adopted / adapted / rejected.

## Goal & role (decided 2026-07-12)

**A proved reference oracle, executable-first, with proofs added where they pay** — not a replacement for the ecosystem's shipped interpreter.

- Build the executable **reference evaluator** first — `#eval`-able, property-tested, differentially tested against [`../../a12-kernel`](../../a12-kernel) (the engine oracle) and by replaying [`../../a12-rulekit/corpus`](../../a12-rulekit/corpus) (portable, engine-verified conformance cases).
- Add declarative `Prop`-judgment + refinement proofs **incrementally**, only where a proof earns its keep: the verdict-algebra laws, monotonicity, and the one-sided soundness properties for partial validation and message polarity (below).
- Lean here is the ecosystem's **formal semantics-of-record and oracle**. The shipped clean-room evaluator already exists in Kotlin (`../../a12-rulekit`'s `:interpreter`, native-image + JS); this project does not aim to replace it.

The honest theorem chain (no overclaiming equivalence to an external binary):

```text
prose + source findings + differential corpus
        │
        ▼   human review + empirical conformance
   chosen formal semantics  (namespace A12Kernel.V30_8_1)
        │
        ▼   machine-checked proof (added incrementally)
   Lean reference interpreter
        │
        ▼   machine-checked refinement (later)
   optimized Lean interpreter
```

Finite differential observations do **not** establish universal equivalence to kernel 30.8.1; they establish *adequacy evidence*. Behaviour is pinned to an observed version, so the semantics will live under `namespace A12Kernel.V30_8_1` once a second version is in view, so observed behaviour never silently becomes the timeless definition of "A12 semantics". (Tracked by [`A12Kernel/Basic.lean`](../A12Kernel/Basic.lean)'s `kernelVersion` until then.)

## Sources & authority

Authority runs [`../../a12-kernel`](../../a12-kernel) (the engine — source of truth) → [`../spec/`](../spec/) → [`../../a12-rulekit`](../../a12-rulekit); every decision below is anchored there. An external PL-semantics spike (2026-07-12) served **only as a source of ideas** — it is *not* authoritative. Its relevant content has been extracted into this doc and the core modules, and it is no longer a live reference. Where it converged with `../spec/` it added confidence; where it conflicted (an intrinsically-typed AST, a `{coefficient, scale}` decimal) the spec/kernel won.

## Core encoding decisions

### Extrinsic (untyped) AST, not an intrinsically-typed one

The AST is indexed only by nothing — a closed inductive with an exhaustive evaluator (per [`../spec/13`](../spec/13-lean-encoding-guide.md)). We **rejected** an intrinsically-typed `Expr (σ : Schema) : Ty → Type`: A12's type system does not encode cheaply into indices (scale goes `unknown` after `/`/`^`; `TypeDefinition` legality is only known post-expansion; enum comparability is config-dependent; `Custom` delegates), and the hard semantic content lives in the *value domain and cell observations*, not in type indices — where intrinsic typing would make proofs fight `Eq.mpr`/transport. Static type/scale/scope checking is done by an elaboration pass that *produces* a well-formed core; intrinsic typing stays available as a later hardening only if a proof goal demands it. Derived scale is modelled as `ScaleInfo (exact | unknown)` plain data ([`A12Kernel/Core.lean`](../A12Kernel/Core.lean)).

### `Value.num` is `Rat` + a separate rendered stored-form — not a `{coefficient, scale}` decimal

The value domain carries exact `Rat` for numeric value. A plain `Rat` loses the *representation* A12 needs (`7` vs `7.00` is a reportable compute delta; `minFractionalDigits` rendering). We resolve that by keeping the **numeric value** as `Rat` and modelling the **stored form** as a separately-rendered string (which is literally what A12 stores — a value in the target's declared format), so representation-equality is stored-form string equality while numeric comparison is on `Rat`. Faithfulness to the engine's `BigDecimal` requires applying explicit rounding at the arithmetic points — scale-19 `HALF_UP` for comparisons, `MathContext(50)` for intermediates — which the number stage will implement as named operations. This keeps the value domain simple and reversible; switching to an explicit `{coefficient, scale}` decimal remains an option if the rendered-string split proves awkward.

### Unified `Verdict`, not a bare fired/notFired outcome

A condition evaluates to `Verdict = notFired | fired (p : Polarity) | unknown` with explicit `conj`/`disj` tables (strong-Kleene on truth; omission-wins-`And`, value-wins-`Or`), merging truth and the spec's `Polarity` into one type. It fixes a real gap: `spec/13`'s `Outcome` (`firedValue | firedOmission | notFired`) cannot represent an `unknown` rule result, which is essential — a formal error can leave a whole condition `unknown`. `K` (Kleene truth) is retained for expression/predicate-level truth and as the object of the monotonicity proof. The `conj`/`disj` tables are locked by `example … := rfl` guards ([`A12Kernel/Core.lean`](../A12Kernel/Core.lean)).

### Two-level cell model: `CheckedCell` → `observeCell(Phase)` → `CellObservation`

`spec/13`'s three-state `CellState` (empty ≠ invalid) is refined into an invariant `CheckedCell {rawPresent, parsed, findings}` and a **phase-indexed read** producing a `CellObservation` (`empty | value | unknown cause | poison cause`), where formal invalidity surfaces as `unknown` in validation but `poison` in computation ([`A12Kernel/Cell.lean`](../A12Kernel/Cell.lean)). The `FormalCause` enum names the five+ invalidity sources routed through one `formalCheck`. **Empty-substitution never happens in the read** — the consuming operator decides what an empty operand means (number→`0` in `<`, skipped by `Max`/`Min`; string→`""` in concat, ignored by `==`). This is the single most important defence against the most common reimplementation bug.

### `Document` = instantiated rows independent of cell values

`Document {instantiatedRows : List RowAddr, rawCells : CellAddr → Option String}` ([`A12Kernel/Document.lean`](../A12Kernel/Document.lean)). Row existence is tracked separately from cell content because a blank-but-instantiated repeat row is observable — inferring rows from non-empty cells breaks `GroupFilled`, requiredness, the row-gate, and repeatable-group quantifiers. We use `List`, **not `Finset`**, because order is observable (`FirstFilledValue`, computation scheduling, poison reads) — and `Finset` would pull Mathlib and hurt `#eval`.

### Injected `World`, custom hooks as pure/total oracles

`Today`/`Now`/custom conditions/label lookups read from an explicit `World`, never `IO`, so `eval`/`compute` are deterministic given a clock ([`A12Kernel/Document.lean`](../A12Kernel/Document.lean)). Custom conditions and field-type validators are external oracles required to be pure and total; a host exception becomes an explicit infrastructure failure, never a silent "did not fire". **Open:** timezone/DST semantics (spring-gap, autumn-fold, pinned tz-rule version) — the review flagged this as "not mathematically closed", and it is the exact still-open divergence in the Kotlin interpreter (`../../a12-rulekit`, IG62).

### Polarity and partial validation are one-sided-sound abstract interpretations — verify, don't assume the `iff`

Partial validation (relevant cells concrete, non-relevant → `unknown`, `true Or unknown` fires while `true And unknown` is suppressed) is a definite-truth abstract interpretation with a one-directional guarantee. Message polarity (VALUE/OMISSION) is likewise an approximation of how the expression could vary under future fills — and because `Having` escalates to OMISSION conservatively, the intended reading is **VALUE = proven-not-repairable-by-fill; OMISSION = possibly-repairable**, a one-sided soundness property, *not* an exact classification. We formalize the exact kernel algorithm, then *test/prove the one-sided property* rather than assuming the prose is an equivalence. Target theorems: `partial_condition_sound`, `value_not_repairable_by_fill`, and monotonicity (replacing an `unknown` operand with any definite value never flips a fired result to not-fired against the fire direction).

## Proof discipline

- Trusted core: terminating `def`s, structural recursion over the AST/finite lists; no `partial`, no `unsafe`; `IO` stays out of the semantics.
- Guard the root theorems in CI with `#print axioms` (report transitive axiom dependencies); keep `native_decide` **out** of the trusted root chain (it adds compiler trust) — it is fine for separate large conformance runs.
- Pinned toolchain: `leanprover/lean4:v4.31.0` ([`../lean-toolchain`](../lean-toolchain)); no external dependencies.

## Module layout (current + intended)

Current ([`../A12Kernel.lean`](../A12Kernel.lean) is the root):

- `A12Kernel/Core.lean` — `K` + strong-Kleene, `Polarity`, `Verdict` + `conj`/`disj`, `ScaleInfo`, `NumField`, `Value`.
- `A12Kernel/Cell.lean` — `FormalCause`, `Phase`, `CheckedCell`, `CellObservation`.
- `A12Kernel/Document.lean` — `GroupId`/`FieldId`, `RowAddr`/`CellAddr`, `Document`, `Env`, `Instant`, `World`.
- `A12Kernel/Basic.lean` — smoke + `kernelVersion`.

Intended growth (bottom-up per [`../spec/13`](../spec/13-lean-encoding-guide.md) §3): a `Semantics/` group (`FormalCheck`, `Observation`/`observeCell`, `Values`, `Iteration`, `Validation`, `Computation`), an `Interpreter/` group (`Reference` then `CompiledModel`/`Fast`), a `Proofs/` group, and a `Conformance/` group. The `Iteration` module is expected to elaborate string paths into explicit access / iteration plans rather than resolving them during evaluation.

## First conformance targets

The thin-but-deep first slice (from the review's §12, each hitting a distinct trap); source the inputs from `../../a12-rulekit/corpus` where a matching engine-verified case exists (it has `compute`, `comparison`, `partial`, `clock`, `fuzz` families):

1. Empty number in a comparison, with sibling-row content, behaves as `0`.
2. Empty Boolean compared with `False` stays non-evaluable.
3. Empty Confirm compared with `True` behaves as `False`.
4. `healthy`-fired `Or` malformed is fired.
5. `healthy`-fired `And` malformed is unknown.
6. `MaxValue(-5, empty) = -5`, while an all-empty numeric aggregate is `0`.
7. A created blank repeat row is content.
8. Required-empty number computes as `0` but suppresses validation reads.
9. Malformed input poisons a dependent computation.
10. A poisoned cell after `FirstFilledValue`'s first filled element is not read.
