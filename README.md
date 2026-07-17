# a12-kernel-lean

A clean-room **Lean 4 mechanized theory and executable specification** of the [A12 Kernel](../a12-kernel)'s validation & computation semantics.

> **Not an official A12 artifact.** A personal exploration, not affiliated with or endorsed by mgm, built with LLM assistance. This is a **clean-room** formal spec: it ships no kernel code and never links, calls, or transcribes the kernel (see [`AGENTS.md`](AGENTS.md)).

The A12 Kernel is mgm technology partners' model-and-DSL engine for complex business forms: analysts declare validation rules (each phrased as the *error* condition) and computations (derived fields), which the engine evaluates against form documents. This project preserves that observed **evaluation semantics** as a versioned [mechanized theory](docs/LEAN-FORMALIZATION.md): executable as a reference oracle, empirically anchored to kernel 30.8.1, and equipped with a required proof spine plus selectively proved higher-level properties.

## Why Lean

Lean makes every captured semantic clause explicit and executable, then lets selected consequences be stated with exact hypotheses and proved for all modeled inputs. It can also preserve checked counterexamples, prove elaborations and optimizations semantics-preserving, and eventually verify real rule models against independently stated business invariants. It does **not** make a chosen clause correct merely by typechecking it or prove the real kernel universally equivalent; corpus and differential evidence remain the empirical bridge. The project charter is [`docs/PROJECT-DESIGN.md`](docs/PROJECT-DESIGN.md), and the case studies, potential, proof boundaries, and working practices are in [`docs/LEAN-FORMALIZATION.md`](docs/LEAN-FORMALIZATION.md).

## How knowledge travels to other software

Think of this repository as a **semantics factory**. It centralizes reusable A12 research, retains relevant kernel observations, states the chosen account precisely in Lean, checks useful laws and counterexamples, and packages the result as a small versioned **semantic shipment**. A downstream **consumer** receives that shipment instead of repeating the semantic archaeology.

```text
kernel observations and source knowledge
                    ↓
       Lean semantics, proofs, and limits
                    ↓
       purpose-specific semantic shipment
                    ↓
 evaluator, importer, refactoring tool, or other consumer
                    ↓
 qualification results and newly discovered gaps return here
```

A shipment contains only the closed capability a consumer needs: its identity and exclusions, language-neutral types and rules or relations, normalized examples, evidence limits, and appropriate qualification tools. The normative semantics stay fixed when an evaluator moves from Rust to Python, while the implementation profile must still resolve relevant host boundaries such as exact numbers, Unicode, resource limits, and process behavior. Changing the job—from evaluation to import or refactoring—changes the task contract itself.

The proposal defines ten general task categories:

> **Execute · Translate · Transform · Compile · Analyze · Verify · Synthesize · Qualify · Explain · Govern**

[`PRODUCT-PROPOSAL.md`](docs/PRODUCT-PROPOSAL.md#general-consumer-task-categories) owns this taxonomy. The user-facing [`use-case guide`](docs/USE-CASES.md) explains what each category can produce, how Lean helps concretely, and where proof, retained evidence, certificates, or finite testing still differ. The current Rust experiment exercises **Execute** and **Qualify** for one finite evaluator capability; importer, refactoring, compilation, analysis, and the other categories remain future potential rather than current support claims. The durable model and gates are in [`docs/PROJECT-DESIGN.md`](docs/PROJECT-DESIGN.md), and the detailed shipment contract is in [`docs/IMPLEMENTER-GUIDE.md`](docs/IMPLEMENTER-GUIDE.md).

## Status

This is a development formal semantics and compatibility-kit experiment, not a complete A12 interpreter or qualified production release.

| Surface | Current boundary |
|---|---|
| Lean theory | Executable and proof-bearing fragments cover phase-aware flat validation, directional numeric polarity, exactly-once evaluated-String CRLF normalization shared by comparison, UTF-16 `Length`, and computation reads, the direct-String-versus-`Length` empty distinction, staged requiredness, one-group iteration, one checked captured-outer `$` correlation shape, and narrow one-target String computation capsules separating expression evaluation, root storage, target minimum/maximum checking, payloadful error, application view, and change-only delta reporting |
| Public reference | The current normalized process advertises reference semantics 0.3.0 through [`supported-fragment-v2.json`](reference/supported-fragment-v2.json), exposes a checked flat operation and one named single-group correlation operation, and fails closed outside that boundary; the internal String/Length and String-computation capsules are not exposed |
| Empirical and formal assurance | Retained kernel observations include focused operator-sensitive Number/String, clean String-computation, and String target-validation packets, while the theorem root establishes selected evaluator, store, target-check, delta, algebraic, and structural laws—not universal kernel equivalence |
| Evidence transport | a12-dmkits provides the maintained, frozen-V1 portable capture/qualification boundary; the accepted retained [`string-direct-cascade-v1` answer](evidence/kernel-30.8.1/captures/string-direct-cascade-v1/README.md) is now closed by a typed Lean binder and agrees with the existing cascade evaluator on all five qualified public observations, while hidden dependency state, scheduling, and exact empty application state remain outside the claim |
| Consumer handover | Flat and correlation development shipments exist; one isolated Rust exercise implemented the flat shipment, completed its checker-accepted seven-mutation qualification, and agreed with the pinned Lean reference on all 52 post-cold generated cases |

[`IMPLEMENTATION-MAP.md`](docs/IMPLEMENTATION-MAP.md) owns exact semantic/proof/evidence status, [`EVIDENCE.md`](docs/EVIDENCE.md) owns the retained observation inventory and claim boundary, the [flat](docs/IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) and [correlation](docs/IMPLEMENTER-KIT-CORRELATION.md) kits own capability-specific handover state, and [`PLAN.md`](docs/PLAN.md) owns only the immediate continuation.

The public wire shape remains protocol 1, but the executable semantics now has an explicit lineage. Reference semantics 0.2.0 and its v1 manifest, suites, Rust qualification, and generated-differential receipt are frozen historical artifacts; the current executable advertises reference semantics 0.3.0 with v2 manifest and suites. The separating request is [`empty-unsigned-number-not-equal-negative.request.json`](examples/reference-cli/empty-unsigned-number-not-equal-negative.request.json): replaying historical source revision `9fa50276f5fb70dcd879b0a9712c8d69c0868967` produces OMISSION, while the corrected current process produces VALUE. [`reference-semantics-lineage-v1.json`](reference/reference-semantics-lineage-v1.json) records that distinction, and the referenced [`0.2.0 artifact lock`](reference/reference-semantics-0.2.0.lock.json) lets the process gate rehash its selected 152-entry historical evidence/example/principal-artifact inventory. Human handover documents are outside that lock, while the post-revision separating request and replay receipt are bound separately by the lineage.

## Build

Needs **Lean 4.31.0** (via [`elan`](https://github.com/leanprover/elan); pinned in [`lean-toolchain`](lean-toolchain)). There are no external Lake package dependencies; native executables still include pinned Lean toolchain/runtime components, whose release implications are tracked in [`docs/PRODUCTION-RELEASE.md`](docs/PRODUCTION-RELEASE.md).

```sh
lake build
lake test
lake exe checkReferenceProcess
lake exe checkBoundedProcess
lake exe checkGeneratedDifferential --self-test
# The next two gates deliberately validate the frozen 0.2.0 Rust campaign.
lake exe checkGeneratedDifferential --check-profile reference/flat-validation-empty-logic-v1.generated-differential-v1.json
lake exe checkGeneratedDifferential --check-result reference/flat-validation-empty-logic-v1.generated-differential-v1.json qualification/flat-validation-empty-logic-v1-rust-v1/generated-differential-v1.RESULT.json
./scripts/check-lean-trust.sh
```

Contributor, artifact-drift, and independent-candidate commands are maintained in [`TESTING.md`](docs/TESTING.md#final-gate).

## Try the reference CLI

The committed files under [`examples/reference-cli/`](examples/reference-cli/) are runnable sample data and regression fixtures. This example demonstrates the kernel's comparison-local empty-Number substitution: omitting the declared Number cell makes the equality with zero fire with omission polarity.

```sh
lake exe a12-kernel-reference < examples/reference-cli/empty-number-equals-zero.request.json
```

Direction matters after substitution. An empty unsigned Number can grow but cannot shrink, so the already accepted flat request `empty unsigned Number != -1` fires with VALUE polarity rather than the blanket OMISSION produced by the earlier one-bit account:

```sh
lake exe a12-kernel-reference < examples/reference-cli/empty-unsigned-number-not-equal-negative.request.json
```

This correction is why the current executable advertises reference semantics 0.3.0. It does not expand or relabel the frozen 0.2.0 Rust capability, which excludes this request, and it does not expose the internal String/Length or String-computation capsules. A request carries protocol and kernel-behavior versions but no reference-semantics selector; detect the executable account from that exact binary's `--manifest` output and pin the binary or release digest. Do not infer it from response shape alone.

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

- Explore possible products and ways Lean helps in the [`use-case guide`](docs/USE-CASES.md).
- Understand which repository trees are authoritative, generated, retained, or transient in the [`artifact lifecycle guide`](docs/ARTIFACTS.md).
- Integrate with the reference executable through the [`normalized protocol`](docs/PROTOCOL.md).
- Build an independent evaluator with the [`implementer guide`](docs/IMPLEMENTER-GUIDE.md) and an implemented [flat](docs/IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) or [correlation](docs/IMPLEMENTER-KIT-CORRELATION.md) kit.
- Design a future importer or rule-transformation shipment from the guide's [`task profiles`](docs/IMPLEMENTER-GUIDE.md#task-profiles) and [`use cases`](docs/USE-CASES.md); no such shipment is implemented yet.
- Study Lean's role, limits, case studies, and proof practices in [`LEAN-FORMALIZATION.md`](docs/LEAN-FORMALIZATION.md).
- Review the durable charter in [`PROJECT-DESIGN.md`](docs/PROJECT-DESIGN.md) and the proposed product boundary in [`PRODUCT-PROPOSAL.md`](docs/PRODUCT-PROPOSAL.md).
- Use [`docs/README.md`](docs/README.md) for every other route and the canonical document-ownership registry.

The read-only [`spec/`](spec/) is the distilled language-neutral baseline, while [`../a12-kernel`](../a12-kernel) remains the behavioural source of truth and [a12-dmkits (local `a12-rulekit/` checkout)](../a12-rulekit) is the peer clean-room knowledge and evidence-transport project. [`SOURCES.md`](docs/SOURCES.md) provides the writable drill map. This repository never links, calls, or transcribes the kernel; [`AGENTS.md`](AGENTS.md) defines the full clean-room, source-authority, dependency, and worktree rules.

## License

MIT © 2026 Martin Backschat — see [`LICENSE`](LICENSE). This project's source ships no kernel code, so it carries no copyleft entanglement (the same basis as [a12-dmkits](../a12-rulekit)' MIT source).
