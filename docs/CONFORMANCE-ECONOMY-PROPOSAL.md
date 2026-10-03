# Conformance economy proposal

**Status: adopted 2026-10-02.** The owner adopted every recommendation in [§4](#4-decisions) and authorized broader assessment, fixes and improvements wherever they reach conformance faster or more economically, with the plan adapted as phases teach. It changes how this project reaches Kernel 30.8.1 conformance, not what conformance means. [`PLAN.md`](PLAN.md) carries the phase sequence.

## 1. Where conformance stands

[`CONFORMANCE-COVERAGE.md`](CONFORMANCE-COVERAGE.md) owns the figures. Its [construct axis](CONFORMANCE-COVERAGE.md#axis-0--kernel-constructs-by-arm) classifies all 110 constructs of the a12-dmkits operator catalog on both arms, and its headline gives the share the Kernel admits that Lean represents broadly. Two readings matter for the plan.

- **The computation arm lags the validation arm.** Guard composition and temporal expressions remain major closing routes. The [computation-condition owner](implementation/computations.md#cap-computation-conditions) states the implemented leaves and their limits; the construct axis owns the current counts.
- **"Calibrated" overstates runtime evidence.** Many calibrated cells rest on static admission rows only, not on replayed runtime values.

## 2. Why the current method does not converge

Each point was measured on 2026-10-02 at `c3d40ed2`.

- **Fixtures cost more than semantics.** Since 2026-09-01, 34 826 lines were added under `Conformance/` against 27 048 under `Semantics/` and `Elaboration/`. With about 113 000 nonblank lines, `Conformance/` is the largest Lean tree.
- **Every Kernel observation is transcribed by hand.** Lean reads neither a DM-JSON model nor DSL text, so each probe grid becomes a hand-built Lean fixture. 228 of the 263 retained capture directories hold a model that a reader could replay unchanged.
- **The representation grows by shape, not by composition.** A validation comparison is a leaf per shape: field against literal, field against field, field against `Today`, and so on. Many constructs have one carrier per value kind and route: 34 `FirstFilled` modules and 52 `Addressed*` modules. The DSL composes freely, so each new nesting needs a new carrier, and the cost grows with the product of constructs, kinds and contexts.
- **The peer measured the same failure.** a12-dmkits' [conformance plan](../../a12-rulekit/docs/CONFORMANCE-PLAN.md) found that hand-driven fixing "had no finite target". It replaced that method with one generated population checked against the Kernel, with divergences kept as a clustered ledger.

## 3. Feasible conformance, made finite

Conformance is reached when three conditions hold together:

1. every catalog construct is **broad on every arm the Kernel admits**;
2. **no tier-1 divergence** remains between Lean and the Kernel over a declared, versioned population of models and documents;
3. everything outside that is a **named host boundary** with its reason.

Universal correspondence stays unprovable. The population and the catalog are the finite denominators.

**Host boundaries.** These stay outside the denominator, each declared rather than modelled:

- regular-expression execution beyond the built-in compiler, which needs a host-supplied compiler;
- `CustomCondition` and custom-field validator callbacks;
- rendered message prose, since this project names keys and parameters only;
- diagnostics that only Groovy code generation or the metamodel raises;
- legacy H-model and multi-form constructs.

<a id="closing-routes"></a>
### Closing routes

Each open cell in the construct table names the route that would close it. The counts are live in the report.

| route | the mechanism | closes |
|---|---|---|
| `guard` | the validation condition tree as the computation guard, under computation's ordered poison and short-circuit account | every predicate and comparison absent from guards |
| `temporal-expr` | one typed temporal value expression: shifts over a stored Date, `Today` and `Now` operands, extractors at numeric positions, temporal extrema and constructors as computation results | the per-route temporal carriers and their missing nestings |
| `rule-leaf` | condition-tree leaves for forms that exist only as standalone capsules: the field-fill quantifiers, `Valid`/`Invalid`, `Date`/`Time`/`DateTime` construction, `DateFromDateTime` and `TimeFromDateTime` comparisons, and `FirstFilledValue` beyond tokens | rules that combine those forms with any other condition |
| `having` | the ordinary condition production as a `Having` body, with all six comparison operators | filter bodies that are refused today |
| `string-expr` | `StringExpr` as a validation operand | String functions in rule conditions |
| `rounding-spelling`, `banded-rounding` | the `*Value` field-only spellings, and banded rounding beside a tolerance | small closures on existing nodes |
| `semantic-index` | keyed leaves and keyed group operands in the condition spine | the remaining keyed forms |
| `calibration-only` | a Kernel observation for a represented cell | evidence, not semantics |

## 4. Decisions

Each decision states its recommendation and the reason for it.

### D1 — read models and DSL text in Lean

Options:
- **(a)** a Lean-native, clean-room reader for DM-JSON models and bilingual condition and operation text, lowering into the existing surface;
- **(b)** import a12-dmkits' parsed form through an upstream export;
- **(c)** keep transcribing by hand.

**Recommendation: (a).** The model importer is small, because `Reference/StrictJson.lean` already parses JSON. A Lean-native text reader keeps the theory usable on its own by every consumer it serves. It also lets Lean meet the static-legality oracle directly: `dmtool rule check` accept or refuse, and the MVK class, against Lean's. That addresses the uncovered checker codes without a hand grid per code. As built, the reader parses with `Lean.Data.Json` rather than `StrictJson`, whose number rendering drops a written fraction's trailing zeros, so the [document reader](../A12Kernel/Reference/Dm/Document.lean) refuses such a number instead of guessing its scale.

Under (b), every Lean surface change would wait on a peer schema. The parser stays outside the proof boundary that [`PROJECT-DESIGN.md`](PROJECT-DESIGN.md#scope-boundary) already draws. It is differentially tested, never proved, and written from `spec/` and the peer's grammar classification, never by transcribing the Kernel grammar. This decision changes that scope table's "initially outside" parser row.

### D2 — one population differential instead of per-capsule grids

The runner is one Lean executable. It reads a `kernelProbe` request (a model plus named documents) and prints the same row projection the probe artifact yields. One script compares the two and clusters divergences into a committed ledger with the peer's tiers (as built, the replay executable compares and classifies each instance itself, and the coverage report only counts its lines):

- **tier 1** — a different value or verdict;
- **tier 2** — Lean refuses or cannot represent what the Kernel answers.

**Recommendation: two populations, in this order.**
1. **P1, replay:** every retained capture, because it is already paid for.
2. **P2, generated:** obtained by an upstream request for a12-dmkits' seed and near-miss populations as a portable export, rather than a second generator here.

Run P2 through the existing `kernelProbe` route.

<a id="d3--build-the-closing-routes-as-keystones-in-cluster-order"></a>
### D3 — close families through shared mechanisms

**Adopted priority correction, 2026-10-03:** select a route by the unfinished construct/arm cells and compositions it can close, reuse of existing semantics, and total delivery cost. Population clusters locate defects and provide regression controls; their frequency alone cannot prioritize constructs the population does not exercise. Guard composition and temporal expressions precede isolated residual rows. The permanent [conformance-convergence rule](../CLAUDE.md#permanent-conformance-convergence-rule) governs model inference, separating observations and family closure in every session.

`temporal-expr` needs the gap records' restriction against a general temporal expression tree lifted. Their own rule asks for a second completed user before generalizing, and the per-route carriers are many such users.

### D4 — retire a hand fixture once the population carries its claim

**Recommendation: adopt the peer's test-base policy.** A fixture retires only against an equivalent population assertion of the same claim kind, listed in the landing that deletes it, and executed one family at a time. Deleting a fixture needs this approval even when it is redundant.

### D5 — calibrate by population, not by grid

**Recommendation:** a new `kernelProbe` grid is built only for a discriminator the population lacks, such as a calendar discontinuity or a poison-timing separator. Everything else is calibrated by adding its shape to the population.

### D6 — prove at the mechanism

**Recommendation:** keep the required proof spine. A new law is admitted only at a shared mechanism with a named consumer, never as a per-carrier restatement. This is already rule 4 of the simplification rule, now applied as a hard gate.

## 5. Sequence

| phase | work | ends when |
|---|---|---|
| 0 | denominator and this proposal | the owner decides §4 |
| 1 | D1 importer and reader, D2 runner, P1 replay ledger | every retained capture replays, and its tier-1 and tier-2 clusters are committed |
| 2 | D3 family mechanisms in coverage/payoff order, D4 retirements per family | the named construct/arm partitions close end to end, with their population clusters resolved and no regression |
| 3 | orchestration keystones: result application ([SG16](gaps/keystone.md#gap-sg16)), messages ([SG10](gaps/strings-and-messages.md#gap-sg10)) and mandatory information ([SG14](gaps/targets-and-derivation.md#gap-sg14)) | each is replayed over P1 and P2 |
| 4 | P2 at full size, static legality through `rule check` | no tier-1 cluster over the declared population |

## 6. Scope

- **Required:** D1 to D3, the P1 replay ledger, and the construct axis kept current.
- **Optional:** P2 at full size before phase 3; D4 retirements beyond the families a keystone touches.
- **Excluded:** proving the reader correct; a regular-expression engine; message prose; a second population generator in this repository.
