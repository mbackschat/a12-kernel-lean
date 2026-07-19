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

[`PRODUCT-PROPOSAL.md`](docs/PRODUCT-PROPOSAL.md#general-consumer-task-categories) owns this taxonomy. The user-facing [`use-case guide`](docs/USE-CASES.md) gives every category a first consumer probe, explains what it could later produce, shows how Lean helps, and keeps proof, retained evidence, certificates, and finite testing distinct. A completed historical Rust experiment was a particularly strong **Execute/Qualify** probe that reached finite qualification for one retired evaluator capability; it is not current or general interpreter support. The [post-simplification probe records](docs/USE-CASES.md#current-probe-record-generated-computation-alternatives) show the present balance: current semantics already expose unsafe refactorings and useful solver-free analyses without infrastructure, while the [cross-level follow-up](docs/USE-CASES.md#current-probe-record-whole-rule-messages-and-cross-level-capture) identifies one genuine missing semantic bridge before captured selection can produce a repeatable whole-rule message. Neither probe is a shipment. The durable model and gates are in [`docs/PROJECT-DESIGN.md`](docs/PROJECT-DESIGN.md), and the detailed probe, shipment, and qualification contract is in [`docs/IMPLEMENTER-GUIDE.md`](docs/IMPLEMENTER-GUIDE.md).

## Status

This is a development formal semantics and compatibility-kit experiment, not a complete A12 interpreter or qualified production release.

| Surface | Current boundary |
|---|---|
| Lean theory | Executable and proof-bearing fragments cover a signed-or-unknown numeric scale summary with constant expandability and the unsuppressed exact-comparison gate; a distinct authored numeric tree retaining literal scale and braces; the exact plain division-region/direct-left-power authoring rule and order-sensitive one-pass division rewrite; a checked same-group, nonrepeatable validation consumer over two numeric expressions and all six ordinary comparison operators; a checked resolved whole-rule boundary that emits an error code, severity, an explicit nonrepeatable error address with an empty repetition path, verdict-derived VALUE/OMISSION type, and opaque already-resolved text; a checked two-alternative literal-Number desugaring that keeps first-match computation separate from all-alternatives generated validation; a numeric computation-expression result plus ordinary fit-path stored-decimal conversion, target classification, change-delta projection, exact one-address final application, and clean-empty/value/poison dependency observation; a post-parse full-Date boundary separating decoded parts, Gregorian reality, the 1583-10-16 value floor, and strict chronology; phase-aware flat validation; the narrower direct Number field-to-literal route; pure two-operand fixed-threshold tolerance; a first nonrepeatable partial-validation rule gate; exactly-once evaluated-String CRLF normalization; staged requiredness; one-group iteration, checked one-group captured-outer `$` correlation, and an internal source-grounded two-level captured-environment separator; ordered computation-presence conditions and first-match alternatives; and narrow one-target String computation capsules |
| Public reference | The current normalized process advertises reference semantics 0.3.0 through [`supported-fragment-v2.json`](reference/supported-fragment-v2.json), exposes a checked flat operation and one named single-group correlation operation, and fails closed outside that boundary; the general numeric expression/scale/tolerance, String/Length, and String-computation capsules are not exposed |
| Empirical and formal assurance | Compact retained observations cover flat validation, paths, requiredness, directional Number/String operators, one-group iteration/correlation, clean String computation, and direct String cascade. They anchor component polarity and selected pointers, but not the two-level diagonal/off-diagonal correlation separator, checked whole-rule assembly, generated two-alternative rule, full-Date boundary, code/severity behavior, resolved text, or the hidden not-fired/unknown distinction; those and the wider numeric expression/authoring/scale/tolerance/target/dependency clauses remain explicitly external-evidence pending. The theorem root establishes selected evaluator, captured-environment routing, checked-boundary, rule-emission, civil/full-Date admission and chronology, authoring-gate, region, one-pass lowering, stored-decimal, target/delta/dependency, algebraic, and structural laws—not universal kernel equivalence |
| Evidence replay | The shared [`ObservationBundle`](A12Kernel/Evidence/ObservationBundle.lean) reader and typed projections pin three compact bundles. [`ValidationProjection`](A12Kernel/Evidence/ValidationProjection.lean) replays 24 private records from the compact [validation bundle](evidence/kernel-30.8.1/captures/validation-core-v1/semantic-observations.json), while the candidate process binds each of its 25 public flat/correlation records to the exact normalized request and externally supported response projection. `lake test` also replays 22 root-String and five direct-cascade cases. Complete removed raw estates remain recoverable through the [validation](docs/archived/VALIDATION-RAW-EVIDENCE.md), [root-String](docs/archived/STRING-COMPUTATION-RAW-EVIDENCE.md), and [direct-cascade](docs/archived/STRING-DIRECT-CASCADE-RAW-EVIDENCE.md) records |
| Consumer handover | Current 0.3.0/V2 flat and correlation development kits and suites exist; the completed 0.2.0/V1 Rust exercise remains a [historical result](docs/archived/REFERENCE-SEMANTICS-0.2.0-AND-RUST-EXPERIMENT.md), not current qualification |

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

The project-owned [`spec/`](spec/) is the distilled language-neutral semantic bridge, while [`../a12-kernel`](../a12-kernel) remains the behavioural source of truth and [a12-dmkits (local `a12-rulekit/` checkout)](../a12-rulekit) is the peer clean-room knowledge, corpus, interpreter, and kernel-differential project as well as the historical producer of the retained direct-cascade evidence. [`SOURCES.md`](docs/SOURCES.md) provides the provenance and drill map; [`A12-DMKITS-SPEC-SYNC.md`](docs/A12-DMKITS-SPEC-SYNC.md) queues spec changes for reconciliation into a12-dmkits. This repository never links, calls, or transcribes the kernel; [`AGENTS.md`](AGENTS.md) defines the full clean-room, source-authority, dependency, and worktree rules.

## License

MIT © 2026 Martin Backschat — see [`LICENSE`](LICENSE). This project's source ships no kernel code, so it carries no copyleft entanglement (the same basis as [a12-dmkits](../a12-rulekit)' MIT source).
