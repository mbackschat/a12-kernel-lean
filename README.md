# a12-kernel-lean

A clean-room **Lean 4 mechanized theory and executable specification** of the [A12 Kernel](../a12-kernel)'s validation & computation semantics.

> **Not an official A12 artifact.** A personal exploration, not affiliated with or endorsed by mgm, built with LLM assistance. This is a **clean-room** formal spec: it ships no kernel code and never links, calls, or transcribes the kernel (see [`AGENTS.md`](AGENTS.md)).

The A12 Kernel is mgm technology partners' model-and-DSL engine for complex business forms: analysts declare validation rules (each phrased as the *error* condition) and computations (derived fields), which the engine evaluates against form documents. This project preserves that observed **evaluation semantics** as a versioned [mechanized theory](docs/LEAN-FORMALIZATION.md): executable as a reference oracle, empirically anchored to kernel 30.8.1, and equipped with a required proof spine plus selectively proved higher-level properties.

## Why Lean

Lean makes every captured semantic clause explicit and executable, then lets selected consequences be stated with exact hypotheses and proved for all modeled inputs. It can also preserve checked counterexamples, prove elaborations and optimizations semantics-preserving, and eventually verify real rule models against independently stated business invariants. It does **not** make a chosen clause correct merely by typechecking it or prove the real kernel universally equivalent; corpus and differential evidence remain the empirical bridge. The project charter is [`docs/PROJECT-DESIGN.md`](docs/PROJECT-DESIGN.md), and the case studies, potential, proof boundaries, and working practices are in [`docs/LEAN-FORMALIZATION.md`](docs/LEAN-FORMALIZATION.md).

## How knowledge travels to other software

Think of this repository as a **semantics factory**. It centralizes reusable A12 research, retains relevant kernel observations, states the chosen account precisely in Lean, checks useful laws and counterexamples, and packages the result as a small versioned **semantic shipment**. A downstream **consumer** receives that shipment instead of repeating the semantic archaeology.

During development, the first outward step is usually a bounded **consumer probe**: apply current semantic material to one concrete interpreter, importer, refactoring, analysis, synthesis, explanation, or other task and see what is usable or missing. A probe may reveal a new use case and may later motivate a shipment or product, but it creates no support, qualification, infrastructure, or roadmap commitment by itself.

```text
kernel observations and source knowledge
                    ↓
       Lean semantics, proofs, and limits
                    ↓
            bounded consumer probe
                    ↓ if valuable and research-closed
       purpose-specific semantic shipment
                    ↓
       cold-qualified independent consumer
                    ↓
             optional adopted product

gaps and newly discovered potential return to the Lean semantics
```

A shipment contains only the closed capability a consumer needs: its identity and exclusions, language-neutral types and rules or relations, normalized examples, evidence limits, and appropriate qualification tools. The normative semantics stay fixed when an evaluator moves from Rust to Python, while the implementation profile must still resolve relevant host boundaries such as exact numbers, Unicode, resource limits, and process behavior. Changing the job—from evaluation to import or refactoring—changes the task contract itself.

The proposal defines ten general task categories:

> **Execute · Translate · Transform · Compile · Analyze · Verify · Synthesize · Qualify · Explain · Govern**

[`PRODUCT-PROPOSAL.md`](docs/PRODUCT-PROPOSAL.md#general-consumer-task-categories) owns this taxonomy. The user-facing [`use-case guide`](docs/USE-CASES.md) gives every category a first consumer probe, explains what it could later produce, shows how Lean helps, and keeps proof, retained evidence, certificates, and finite testing distinct. A completed historical Rust experiment was a particularly strong **Execute/Qualify** probe that reached finite qualification for one retired evaluator capability; it is not current or general interpreter support. The [post-simplification probe records](docs/USE-CASES.md#completed-probe-record-generated-computation-alternatives) show the present balance: current semantics already expose unsafe refactorings and useful solver-free analyses without infrastructure, while the [cross-level follow-up](docs/USE-CASES.md#completed-probe-record-whole-rule-messages-and-cross-level-capture) identifies one genuine missing semantic bridge before captured selection can produce a repeatable whole-rule message. The paired [field-fill readbacks](docs/USE-CASES.md#completed-probe-record-validation-field-fill-quantifiers) independently recover the extensional validation table and the separate ordered computation scans, including their unsafe phase-reuse and rewrite boundaries, without producing a shipment. The durable model and gates are in [`docs/PROJECT-DESIGN.md`](docs/PROJECT-DESIGN.md), and the detailed probe, shipment, and qualification contract is in [`docs/IMPLEMENTER-GUIDE.md`](docs/IMPLEMENTER-GUIDE.md).

## Status

This is a development formal semantics and compatibility-kit experiment, not a complete A12 interpreter or qualified production release.

| Surface | Current boundary |
|---|---|
| Lean theory | Executable and proof-bearing fragments cover a signed-or-unknown numeric scale summary with constant expandability and the unsuppressed exact-comparison gate; a distinct authored numeric tree retaining literal scale and braces; the exact plain division-region/direct-left-power authoring rule and order-sensitive one-pass division rewrite; a checked same-group, nonrepeatable validation consumer over two numeric expressions and all six ordinary comparison operators; a checked resolved whole-rule boundary that emits an error code, severity, an explicit nonrepeatable error address with an empty repetition path, verdict-derived VALUE/OMISSION type, and opaque already-resolved text; a structured one-pass renderer over already-resolved message display inputs; a checked two-alternative literal-Number desugaring that keeps first-match computation separate from all-alternatives generated validation; a numeric computation-expression result plus ordinary fit-path stored-decimal conversion, target classification, change-delta projection, exact one-address final application, and clean-empty/value/poison dependency observation; a post-parse full-Date boundary separating decoded parts, Gregorian reality, the 1583-10-16 value floor, and strict chronology; a selected whole-second UTC local-DateTime-to-instant bridge with proved calendar successor, civil-coordinate monotonicity, and UTC order preservation, plus a whole-hour instant-shift core, resolved sub-day instant differences, and a fixed 2024 Berlin autumn-overlap discriminator; phase-aware flat validation; the narrower direct Number field-to-literal route; pure two-operand fixed-threshold tolerance; a first nonrepeatable partial-validation rule gate; exactly-once evaluated-String CRLF normalization; staged requiredness; one-group iteration, checked one-group captured-outer `$` correlation, and an internal source-grounded two-level captured-environment separator; ordered computation-presence conditions, common-precondition expansion, and first-match alternatives; narrow one-target String computation capsules; and one resolved guarded String table that selects once and never resumes after the selected operation produces no value, target rejection, or poison |
| Public reference | The current normalized process advertises reference semantics 0.3.0 through [`supported-fragment-v2.json`](reference/supported-fragment-v2.json), exposes a checked flat operation and one named single-group correlation operation, and fails closed outside that boundary; the general numeric expression/scale/tolerance, String/Length, and String-computation capsules are not exposed |
| Empirical and formal assurance | Compact retained observations cover flat validation, paths, requiredness, directional Number/String operators, one-group iteration/correlation, clean String computation, and direct String cascade. External a12-dmkits kernel probes also ground scale-zero empty Number/String interpolation, one filled message value, positive and reverse-fraction DateTime differences, fresh-standard parsing, the Berlin overlap separator, and selected calendar-day stepping, but this repository retains no portable message, Date, or DateTime observation and its wider display cascade, CRLF message path, and second temporal shift equality are source-derived. The retained observations do not cover the two-level diagonal/off-diagonal correlation separator, checked whole-rule assembly, generated two-alternative rule, resolved String alternative terminality, full-Date or general UTC DateTime boundaries, code/severity behavior, complete message rendering, or the hidden not-fired/unknown distinction; those and the wider numeric expression/authoring/scale/tolerance/target/dependency clauses remain explicitly external-evidence pending. The theorem root establishes selected evaluator, terminal selected-String-operation and suffix-irrelevance, captured-environment routing, checked-boundary, rule-emission, resolved-message rendering, civil/full-Date admission and chronology, civil successor and coordinate/UTC order preservation, whole-second time admission, resolved sub-day difference order/truncation, finite Berlin profile resolution and calendar-day sign laws, instant-shift algebra, authoring-gate, region, one-pass lowering, stored-decimal, target/delta/dependency, algebraic, and structural laws—not universal kernel equivalence |
| Evidence replay | The shared [`ObservationBundle`](A12Kernel/Evidence/ObservationBundle.lean) reader and typed projections pin three compact bundles. [`ValidationProjection`](A12Kernel/Evidence/ValidationProjection.lean) replays 24 private records from the compact [validation bundle](evidence/kernel-30.8.1/captures/validation-core-v1/semantic-observations.json), while the candidate process binds each of its 25 public flat/correlation records to the exact normalized request and externally supported response projection. `lake test` also replays 22 root-String and five direct-cascade cases. Complete removed raw estates remain recoverable through the [validation](docs/archived/VALIDATION-RAW-EVIDENCE.md), [root-String](docs/archived/STRING-COMPUTATION-RAW-EVIDENCE.md), and [direct-cascade](docs/archived/STRING-DIRECT-CASCADE-RAW-EVIDENCE.md) records |
| Consumer handover | Current 0.3.0/V2 flat and correlation development kits and suites exist; the completed 0.2.0/V1 Rust exercise remains a [historical result](docs/archived/REFERENCE-SEMANTICS-0.2.0-AND-RUST-EXPERIMENT.md), not current qualification |

The internal theory also captures the resolved Number/canonical-token value-list operators `AtLeastOne`, `No`, and `NotAll`, including their deliberately different UNKNOWN and omission-polarity rules. It starts after expansion, comparability checking, and `Having` filtering and is not yet part of the public reference process; [`LF44`](docs/LEAN-FINDINGS.md#lf44--no-and-notall-value-list-quantifiers-are-not-duals) gives the short rationale and [`IMPLEMENTATION-MAP.md`](docs/IMPLEMENTATION-MAP.md) owns the exact boundary.

The internal Number theory also captures one resolved-operand `FirstFilledValue`: invalidity before selection suppresses validation and poisons computation, invalidity after selection is never read, an empty prefix changes only validation polarity, and a correctly marked all-empty selection yields the fillable zero. It begins after ordered expansion, filtering, and partial-relevance classification, excludes multiple authored operand slots and every other value kind, and is not exposed by the public process; [`LF48`](docs/LEAN-FINDINGS.md#lf48--firstfilledvalue-is-a-prefix-sensitive-scan-not-a-list-fold) explains why this needs a dedicated scan.

The internal computation theory now also captures all seven field-fill predicates over one caller-supplied, already-expanded ordered slot stream. It preserves the declared-versus-instantiated range split, exact internal first-reached poison, operator-specific stops, and the two staged composite decisions; a malformed suffix after the full predicate's final decision is never read. It does not yet expand authored fields, groups, stars, filters, or paths or integrate the leaf into the public computation AST. [`LF50`](docs/LEAN-FINDINGS.md#lf50--computation-field-fill-quantifiers-are-ordered-phase-specific-scans) owns the exact boundary.

The internal validation companion captures the same seven names over one caller-supplied unfiltered tally, not the computation scan. It keeps filled, empty, formally unavailable, and declared-but-uninstantiated counts distinct and returns only fired VALUE/OMISSION or the kernel-visible collapsed `FALSE_OR_UNKNOWN`. This makes validation permutation-insensitive at the resolved tally boundary while computation remains order-sensitive in the presence of poison. Authored expansion, `Having`, empty-row eligibility, partial validation, connective integration, and public protocol support remain open; [`LF51`](docs/LEAN-FINDINGS.md#lf51--validation-field-fill-quantifiers-are-extensional-and-observably-collapsed) owns the exact boundary.

The resolved Number theory now carries the kernel's complete conservative power-direction table alongside the staged power value. It distinguishes fixedness, parity, base regions around `−1`, `0`, and `1`, and reciprocal-first negative exponents; invalid powers remain unavailable before polarity is considered. Thus `0 ^ emptyUnsigned` and `0 ^ emptySigned` both currently equal `1` but produce different directions and make the same true `> 0` comparison OMISSION- versus VALUE-typed. This pure capsule is not yet admitted by checked authored validation or computation, the public process, or retained project-local evidence; [`LF52`](docs/LEAN-FINDINGS.md#lf52--power-fillability-is-a-conservative-branch-table-not-parity-inference) owns the boundary.

The internal resolved-runtime theory now also contains one resolved nonempty literal-key semantic-index read over a canonical-token key column: a Number value consumer plus kind-independent validation/computation presence and field-fill-operand projections. A clean no-match and a matched empty target both read empty, so indexed `FieldNotFilled` holds on either and contributes an empty quantifier operand; an unavailable key column is validation-unknown only after no match but becomes an ordered computation poison slot before any match is read. This makes a clean validation match survive an unrelated bad key even though the same reached computation operand aborts; an invalid target matters only when its row is selected, and a deciding earlier quantifier operand can leave a later poison unread. Path syntax, literal checking, key normalization, field-keyed indices, nested repetitions, and portable local evidence remain outside this capsule; [`LF53`](docs/LEAN-FINDINGS.md#lf53--semantic-index-lookup-has-match-first-validation-and-column-first-computation) owns the exact distinction.

The internal Enumeration theory now separates runtime projection from static direct-field comparability. Runtime comparison uses the stored token or one positional many-to-one category token; empty is not evaluated, formal unavailability stays UNKNOWN, and every firing is VALUE. The static gate treats absent labels and identity labels alike, rejects String versus a genuinely remapped display enum, and checks two display-bearing enums as a common-locale partial bijection rather than requiring identical declarations. It begins after legal ordinary closed declarations and direct equality/inequality field shape; table/dynamic enums, partial or duplicate-display declarations, literals, category-field admission, paths, protocol support, and project-local portable evidence remain outside. [`LF54`](docs/LEAN-FINDINGS.md#lf54--enumeration-categories-are-positional-runtime-projections-not-display-lookups) owns runtime projection and [`LF55`](docs/LEAN-FINDINGS.md#lf55--enumeration-field-comparability-depends-on-effective-remapping-not-label-presence) owns the static gate.

The internal Date theory also has a resolved Date-range overlap family: endpoint equality is a valid one-day range, overlap uses closed intervals, inversion never overlaps, and duplicate occurrences remain distinct. A separate ordered operand layer implements both authored shapes and their different polarity scans: any-pair overlap remembers a reached kept occurrence from a filtered operand, while scalar-versus-list uses only the first matching list operand and cannot be rescued by list-internal overlap after a skipped scalar. The boundary begins after formal checking and actual filter selection; paths/stars, cell classification, and checked authoring remain outside it. [`LF49`](docs/LEAN-FINDINGS.md#lf49--date-range-overlap-is-closed-occurrence-based-and-shape-sensitive) owns the exact distinction.

The internal Date theory now also captures the reason-and-verdict boundary of three-part `Date(day, month, year)` construction and the first direct numeric consumer of that result. Real constructions expose the selected day, month, or year as a fixed Number; incomplete and calendar-rejected constructions both expose amount `0`, but incomplete zero remains symmetrically not-given and makes every true fixed-literal comparison OMISSION-typed, while unreal zero is fixed and VALUE-typed. Formal unavailability stays UNKNOWN without an invented cause. This starts after component checking and a separately supplied calendar decision; exact model-zone/cutover resolution, DateTime composition, differences, authoring, and protocol remain open. [`LF46`](docs/LEAN-FINDINGS.md#lf46--constructed-date-validity-needs-a-reason-bearing-non-value) explains the distinction and [`IMPLEMENTATION-MAP.md`](docs/IMPLEMENTATION-MAP.md#resolved-three-part-date-construction) owns the exact boundary.

[`IMPLEMENTATION-MAP.md`](docs/IMPLEMENTATION-MAP.md) owns exact semantic/proof/evidence status, [`EVIDENCE.md`](docs/EVIDENCE.md) owns the retained observation inventory and claim boundary, the [flat](docs/IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) and [correlation](docs/IMPLEMENTER-KIT-CORRELATION.md) kits own capability-specific handover state, and [`PLAN.md`](docs/PLAN.md) owns only the immediate continuation.

The evidence approach is intentionally simpler going forward: semantic and theorem work lands first with an honest evidence status, and related clauses are calibrated in batches. Existing a12-dmkits corpus/differential facilities are used when their observations fit; otherwise a concrete family may justify one minimal upstream handback. Lean retains and reads only the compact typed observations it needs, while historical raw packets remain recoverable for audit. No generic capture framework or its filesystem, receipt, runner, capability, and qualification mechanics is recreated per family.

The public wire shape remains protocol 1 while the current executable advertises reference semantics 0.3.0 with the V2 manifest and suites. The separating request is [`empty-unsigned-number-not-equal-negative.request.json`](examples/reference-cli/empty-unsigned-number-not-equal-negative.request.json): historical 0.2.0 source revision `9fa50276f5fb70dcd879b0a9712c8d69c0868967` produced OMISSION, while the corrected current process produces VALUE. The retired 0.2.0/V1 artifacts, Rust qualification, exact digests, and Git recovery points live only in the [archived experiment record](docs/archived/REFERENCE-SEMANTICS-0.2.0-AND-RUST-EXPERIMENT.md); current gates do not rehash or replay them.

## Build

Needs **Lean 4.31.0** (via [`elan`](https://github.com/leanprover/elan); pinned in [`lean-toolchain`](lean-toolchain)). There are no external Lake package dependencies; native executables still include pinned Lean toolchain/runtime components, whose release implications are tracked in [`docs/PRODUCTION-RELEASE.md`](docs/PRODUCTION-RELEASE.md).

```sh
lake build
lake test
lake exe checkReferenceProcess
lake exe checkBoundedProcess
./scripts/check-lean-trust.sh
```

Contributor, artifact-drift, and independent-candidate commands are maintained in [`TESTING.md`](docs/TESTING.md#tier-gates).

## Try the reference CLI

The committed files under [`examples/reference-cli/`](examples/reference-cli/) are runnable sample data and regression fixtures. This example demonstrates the kernel's comparison-local empty-Number substitution: omitting the declared Number cell makes the equality with zero fire with omission polarity.

```sh
lake exe a12-kernel-reference < examples/reference-cli/empty-number-equals-zero.request.json
```

Direction matters after substitution. An empty unsigned Number can grow but cannot shrink, so the already accepted flat request `empty unsigned Number != -1` fires with VALUE polarity rather than the blanket OMISSION produced by the earlier one-bit account:

```sh
lake exe a12-kernel-reference < examples/reference-cli/empty-unsigned-number-not-equal-negative.request.json
```

This correction is why the current executable advertises reference semantics 0.3.0. It does not relabel the retired 0.2.0/V1 Rust result as V2, and it does not expose the internal String/Length or String-computation capsules. A request carries protocol and kernel-behavior versions but no reference-semantics selector; detect the executable account from that exact binary's `--manifest` output and pin the binary or release digest. Do not infer it from response shape alone.

Inspect the exact supported boundary with:

```sh
lake exe a12-kernel-reference --manifest
```

See [`docs/PROTOCOL.md`](docs/PROTOCOL.md) for the request/response contract, exit behavior, representative sample scenarios, and deliberate exclusions; the machine-readable suites own their complete finite case inventories.

The captured-outer sample returns firing rows 2 and 3:

```sh
lake exe a12-kernel-reference < examples/reference-cli/correlation-direction.request.json
```

See [`docs/IMPLEMENTER-KIT-CORRELATION.md`](docs/IMPLEMENTER-KIT-CORRELATION.md) for the exact language-neutral model, algorithm, worked traces, evidence/law/non-law map, Rust playbook, and candidate tools.

## Where to go next

- Explore bounded consumer probes, possible later products, and how Lean helps in the [`use-case guide`](docs/USE-CASES.md).
- Understand which repository trees are authoritative, generated, retained, or transient in the [`artifact lifecycle guide`](docs/ARTIFACTS.md).
- Integrate with the reference executable through the [`normalized protocol`](docs/PROTOCOL.md).
- Build an independent evaluator with the [`implementer guide`](docs/IMPLEMENTER-GUIDE.md) and an implemented [flat](docs/IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) or [correlation](docs/IMPLEMENTER-KIT-CORRELATION.md) kit.
- Design a future importer or rule-transformation shipment from the guide's [`task profiles`](docs/IMPLEMENTER-GUIDE.md#task-profiles) and [`use cases`](docs/USE-CASES.md); no such shipment is implemented yet.
- Study Lean's role, limits, case studies, and proof practices in [`LEAN-FORMALIZATION.md`](docs/LEAN-FORMALIZATION.md).
- Review the durable charter in [`PROJECT-DESIGN.md`](docs/PROJECT-DESIGN.md) and the proposed product boundary in [`PRODUCT-PROPOSAL.md`](docs/PRODUCT-PROPOSAL.md).
- Use [`docs/README.md`](docs/README.md) for every other route and the canonical document-ownership registry.

The project-owned [`spec/`](spec/) is the distilled language-neutral semantic bridge, while [`../a12-kernel`](../a12-kernel) remains the behavioural source of truth and [a12-dmkits (local `a12-rulekit/` checkout)](../a12-rulekit) is the peer clean-room knowledge, corpus, interpreter, and kernel-differential project as well as the historical producer of the retained direct-cascade evidence. [`SOURCES.md`](docs/SOURCES.md) provides the provenance and drill map; [`A12-DMKITS-SPEC-SYNC-LEDGER.md`](docs/A12-DMKITS-SPEC-SYNC-LEDGER.md) queues spec changes for reconciliation into a12-dmkits. This repository never links, calls, or transcribes the kernel; [`AGENTS.md`](AGENTS.md) defines the full clean-room, source-authority, dependency, and worktree rules.

## License

MIT © 2026 Martin Backschat — see [`LICENSE`](LICENSE). This project's source ships no kernel code, so it carries no copyleft entanglement (the same basis as [a12-dmkits](../a12-rulekit)' MIT source).
