# a12-kernel-lean — encoding architecture & decisions

The *how* and *why* of the Lean encoding, layered on the language-neutral semantics in [`../spec/`](../spec/). The spec (start at [`../spec/SEMANTICS-MAP.md`](../spec/SEMANTICS-MAP.md), plan in [`../spec/13-lean-encoding-guide.md`](../spec/13-lean-encoding-guide.md)) stays the canonical semantics distillation; this file records the concrete Lean design decisions that operationalize it, and what was adopted / adapted / rejected.

## Goal & role (decided 2026-07-12)

**A versioned mechanized theory, executable-first, with a required proof spine and additional proofs selected by payoff** — not a replacement for the ecosystem's shipped interpreter.

- Build small semantic capsules around an executable **reference evaluator** — `#eval`-able, internally guarded, checked by replaying [`../../a12-rulekit/corpus`](../../a12-rulekit/corpus), and compared with focused kernel observations exported through the external [`../../a12-rulekit/adapter`](../../a12-rulekit/adapter) harness.
- Establish the required semantic theory incrementally: exact theorem vocabulary and supported fragments, algebra and checked non-laws, elaboration/desugaring preservation, evaluator/judgment bridges where an independent judgment adds value, read noninterference, and the one-sided partial-validation and polarity results.
- Lean here is the ecosystem's **formal semantics-of-record for the chosen account of observed behaviour**. The shipped clean-room evaluator already exists in Kotlin (`../../a12-rulekit`'s `:interpreter`, native-image + JS); this project does not aim to replace it.

[`PROJECT-DESIGN.md`](PROJECT-DESIGN.md) owns the project charter. [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md) owns the three claim classes, case studies, theorem opportunities, trust boundaries, and working discipline. This file owns the concrete Lean representation decisions.

The honest theorem chain (no overclaiming equivalence to an external binary):

```text
prose + source findings + differential corpus
        │
        ▼   human review + empirical adequacy
   chosen Lean semantics for 30.8.1
        ├──────────────► named laws + checked counterexamples
        │                         (machine-checked)
        ▼
   reference evaluator ◄────► declarative / trace semantics where useful
        │                         (soundness + completeness)
        ▼   machine-checked refinement (later, only if needed)
   optimized Lean evaluator
```

Finite differential observations do **not** establish universal equivalence to kernel 30.8.1; they establish *adequacy evidence*. Every semantic clause, theorem, and conformance case is conceptually versioned from the outset. [`A12Kernel/Basic.lean`](../A12Kernel/Basic.lean)'s `kernelVersion` records the current single-version surface; migrate the public semantic namespace to `A12Kernel.V30_8_1` before a second version or a stable external API makes an unversioned meaning ambiguous.

## Sources & authority

Authority runs [`../../a12-kernel`](../../a12-kernel) (the engine — source of truth) → [`../spec/`](../spec/) → [`../../a12-rulekit`](../../a12-rulekit); every decision below is anchored there. An external PL-semantics spike (2026-07-12) served **only as a source of ideas** — it is *not* authoritative. Its relevant content has been extracted into this doc and the core modules, and it is no longer a live reference. Where it converged with `../spec/` it added confidence; where it conflicted (an intrinsically-typed AST, a `{coefficient, scale}` decimal) the spec/kernel won.

The differential path assigns distinct roles rather than treating all executable sources as interchangeable. The kernel is the authoritative behavior. The a12-rulekit [`adapter`](../../a12-rulekit/adapter) is the external harness and result-export boundary for focused kernel probes, never a dependency of the Lean theory. The a12-rulekit [`corpus`](../../a12-rulekit/corpus) is the portable replay boundary consumed by this repository. The a12-rulekit [`interpreter`](../../a12-rulekit/interpreter) is a secondary clean-room implementation useful for triangulation, fuzzing ideas, and detecting disagreements; it is not an oracle, and kernel evidence resolves any conflict. This preserves the clean-room boundary: kernel execution and result normalization happen externally, while committed Lean inputs contain only portable own-domain evidence.

## Core encoding decisions

### Extrinsic (untyped) AST, not an intrinsically-typed one

The AST is indexed only by nothing — a closed inductive with an exhaustive evaluator (per [`../spec/13`](../spec/13-lean-encoding-guide.md)). We **rejected** an intrinsically-typed `Expr (σ : Schema) : Ty → Type`: A12's type system does not encode cheaply into indices (scale goes `unknown` after `/`/`^`; `TypeDefinition` legality is only known post-expansion; enum comparability is config-dependent; `Custom` delegates), and the hard semantic content lives in the *value domain and cell observations*, not in type indices — where intrinsic typing would make proofs fight `Eq.mpr`/transport. Static type/scale/scope checking is done by an elaboration pass that produces a core rule with an explicit `WellFormed` boundary; elaboration soundness and the absence of impossible evaluator failures for accepted core rules are proof obligations. Intrinsic typing stays available as a later hardening only if a concrete proof goal demands it. Derived scale is modelled as `ScaleInfo (exact | unknown)` plain data ([`A12Kernel/Core.lean`](../A12Kernel/Core.lean)).

### Checked elaboration resolves names and owns field-policy coherence

[`A12Kernel/Elaboration/Flat.lean`](../A12Kernel/Elaboration/Flat.lean) follows the parser–elaborator–core split used by Lean/Lean4Lean and the explicit surface-to-core boundary exemplified by `do` Unchained. Its input is structured and parser-independent; its output is a `CheckedFlatCondition` carrying proofs that the expanded model validated and every core field matches one unique non-repeatable declaration. The supported path subset is intentionally narrow: absolute paths, parent-relative paths without named turning-point labels, and bare lookup in the kernel order local → nearest ancestor → flag-gated model-wide unique. Ambiguity, invalid models, repeatable references, unsupported operators, kind mismatches, and illegal Confirm literals fail closed.

The same `FlatModel` compiles raw cells into the runtime `FlatContext`, so successful surface evaluation cannot pair a resolved numeric field with a caller-invented Boolean policy. Trusted theorems connect every admitted field to its unique matching declaration and prove that context construction applies exactly that declaration’s `formalCheck` policy; missing or ambiguous IDs become malformed/unknown. The low-level `FlatCondition.evalFull` remains available for isolated semantic laws and can still receive an arbitrary `FlatContext`, so policy coherence is claimed only for the checked surface route.

This slice does not implement the complete §10 path language. Quoted concrete syntax, named-ancestor labels, `RuleGroup`, stars, `$`, semantic indices, repeatable evaluation, and parser/renderer preservation are outside the current structure. [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) owns the live assurance and external-evidence status.

### `Value.num` is `Rat` + a separate rendered stored-form — not a `{coefficient, scale}` decimal

The value domain carries exact `Rat` for numeric value. A plain `Rat` loses the *representation* A12 needs (`7` vs `7.00` is a reportable compute delta; `minFractionalDigits` rendering). We resolve that by keeping the **numeric value** as `Rat` and modelling the **stored form** as a separately-rendered string (which is literally what A12 stores — a value in the target's declared format), so representation-equality is stored-form string equality while numeric comparison is on `Rat`. Faithfulness to the engine's `BigDecimal` requires applying explicit rounding at the arithmetic points — scale-19 `HALF_UP` for comparisons, `MathContext(50)` for intermediates — which the number stage will implement as named operations. This keeps the value domain simple and reversible; switching to an explicit `{coefficient, scale}` decimal remains an option if the rendered-string split proves awkward.

### Unified `Verdict`, not a bare fired/notFired outcome

A condition evaluates to `Verdict = notFired | fired (p : Polarity) | unknown` with explicit `conj`/`disj` tables (strong-Kleene on truth; omission-wins-`And`, value-wins-`Or`), merging truth and the spec's `Polarity` into one type. A bare `firedValue | firedOmission | notFired` outcome cannot represent an `unknown` rule result, which is essential because a formal error can leave a whole condition unknown. `K` is retained for expression/predicate-level truth and for stating the exact information-order laws: unknown lies below both definite values, which are incomparable; `And`/`Or` are monotone under that order, so unknown may refine to true or false while an already definite result is stable. The `conj`/`disj` tables have executable `example … := rfl` guards; the algebraic theory still requires quantified proofs ([`A12Kernel/Core.lean`](../A12Kernel/Core.lean)).

### Two-level cell model: `CheckedCell` → `observeCell(Phase)` → `CellObservation`

The earlier three-state sketch (empty ≠ invalid) is refined into an invariant `CheckedCell {rawPresent, parsed, findings}` and a **phase-indexed read** producing a `CellObservation` (`empty | value | unknown cause | poison cause`) ([`A12Kernel/Cell.lean`](../A12Kernel/Cell.lean)). Base `formalCheck` handles ordinary local findings such as malformed values and declared constraints; generated and structural passes annotate the same checked-cell representation later. Requiredness is deliberately staged: evaluate the generated mandatory rule against base checked cells, retain its hit/message, and only on a hit add `.required` to the empty target for authored validation rules. Installing `.required` first would make the mandatory rule's own `FieldNotFilled` read unknown and suppress itself. Ordinary findings surface as `unknown` in validation and `poison` in computation, while `.required` is validation-scoped and observes as ordinary empty during computation. **Empty-substitution never happens in the read** — the consuming operator decides what an empty operand means (number→`0` in `<`, skipped by `Max`/`Min`; string→`""` in concat, ignored by `==`). This is the single most important defence against the most common reimplementation bug.

### `Document` = instantiated rows independent of cell values

`Document {instantiatedRows : List RowAddr, rawCells : CellAddr → Option String}` ([`A12Kernel/Document.lean`](../A12Kernel/Document.lean)). Row existence is tracked separately from cell content because a blank-but-instantiated repeat row is observable — inferring rows from non-empty cells breaks `GroupFilled`, requiredness, the row-gate, and repeatable-group quantifiers. We use `List`, **not `Finset`**, because order is observable (`FirstFilledValue`, computation scheduling, poison reads) — and `Finset` would pull Mathlib and hurt `#eval`.

### Injected `World`, custom hooks as pure/total oracles

`Today`/`Now`/custom conditions/label lookups read from an explicit `World`, never `IO`, so `eval`/`compute` are reproducible given their explicit inputs ([`A12Kernel/Document.lean`](../A12Kernel/Document.lean)). Custom conditions and field-type validators are external oracles required to be pure and total; a host exception becomes an explicit infrastructure failure, never a silent "did not fire". Purity and totality do **not** imply locality, fill-monotonicity, or stability under partial validation, so theorems needing those properties either exclude custom oracles or quantify over an explicit oracle contract with a read footprint and the required laws. **Open:** timezone/DST semantics (spring-gap, autumn-fold, pinned tz-rule version) — the review flagged this as "not mathematically closed", and it is the exact still-open divergence in the Kotlin interpreter (`../../a12-rulekit`, IG62).

### Polarity and partial validation are one-sided-sound abstract interpretations — verify, don't assume the `iff`

Partial validation (relevant cells concrete, non-relevant → `unknown`, `true Or unknown` fires while `true And unknown` is suppressed) is a definite-truth abstract interpretation with a one-directional guarantee. Message polarity (VALUE/OMISSION) is likewise an approximation of how the expression could vary under future fills — and because `Having` escalates to OMISSION conservatively, the intended reading is **VALUE = proven-not-repairable-by-fill; OMISSION = possibly-repairable**, a one-sided soundness property, *not* an exact classification. Formalize the exact kernel algorithm, then prove the one-sided property only after `InformationRefines`, `FillExtends`, `AgreesOn`, row/world stability, and supported-fragment assumptions are explicit. The canonical theorem ladder and known exclusions live in [`LEAN-FORMALIZATION.md`](LEAN-FORMALIZATION.md).

## Proof discipline

- Trusted core: pure definitions accepted as total by Lean's kernel; prefer structural recursion, but use well-founded recursion or pure local `do`/mutation when clearer. No `partial`, `unsafe`, or `IO` in the trusted semantics.
- Maintain one trusted theorem root that imports every trusted proof module. Generate and review its transitive axiom report in CI, and mechanically reject active `sorry`, unclassified project axioms, `unsafe`, `partial`, and `native_decide` in the trusted closure. `native_decide` remains acceptable only for separate conformance work because it adds compiler trust.
- A root theorem's review surface includes its exact statement, hypotheses, direction, result domain, supported fragment, counterexamples just outside the fragment, and axiom report. Theorem counts and `0 sorry` are not assurance metrics by themselves.
- Keep the executable core dependency-free while cheap. If serious proof work needs mature finite-map, permutation, order, rational, or calendar theory, prefer a separate Mathlib-backed proof target over reimplementing a theorem library or burdening `#eval`.
- Current executable target: pinned `leanprover/lean4:v4.31.0` ([`../lean-toolchain`](../lean-toolchain)) with no external dependencies. A future separate proof or documentation target may add version-pinned dependencies without changing that core contract.

## Current module layout

Current ([`../A12Kernel.lean`](../A12Kernel.lean) is the root):

- `A12Kernel/Core.lean` — `K` + strong-Kleene, `Polarity`, `Verdict` + `conj`/`disj`, `ScaleInfo`, `NumField`, `Value`.
- `A12Kernel/Cell.lean` — `FormalCause`, `Phase`, `CheckedCell`, `CellObservation`.
- `A12Kernel/Document.lean` — `GroupId`/`FieldId`, `RowAddr`/`CellAddr`, `Document`, `Env`, `Instant`, `World`.
- `A12Kernel/Semantics/Observation.lean` — normalized scalar input, the closed base-finding subset, `formalCheck`, staged annotations, and phase observation.
- `A12Kernel/Semantics/FlatValidation.lean` — the typed one-field equality/presence fragment, row gate, scale-19 comparison rescaling, and verdict evaluator.
- `A12Kernel/Semantics/Required.lean` — the two-pass absolute/non-repeatable required-field fragment.
- `A12Kernel/Elaboration/Flat.lean` — checked structured-surface lowering, normalized non-repeatable path lookup, field legality, and model-derived raw-cell checking.
- `A12Kernel/Proofs.lean` — trusted theorem root; algebra, information order, checked-cell invariants, phase laws, required-staging preservation, and elaboration/context coherence.
- `A12Kernel/Conformance.lean` — executable semantic and elaboration locks for the supported fragment.
- `A12Kernel/Basic.lean` — smoke + `kernelVersion`.

Planned sequencing and open work belong in [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md), durable treatment decisions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and live coverage/evidence state in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md). This file changes when the actual module or representation structure changes; it does not carry a parallel roadmap or status table.
