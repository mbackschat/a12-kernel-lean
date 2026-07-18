# Archived reference semantics 0.2.0 and Rust experiment

> **Status:** immutable historical record. Reference semantics 0.2.0/V1 was removed from the current worktree after its behavior was superseded by 0.3.0/V2 and no maintained consumer required the old runnable estate. This document records recovery and the completed knowledge-transport experiment; it is not a current capability, command, or release claim.

## Historical compatibility identity

| Item | Value |
|---|---|
| Reference semantics | `0.2.0` |
| Protocol | `1` |
| Manifest schema | `2` |
| Kernel behavior | `30.8.1` |
| Flat suite | `flat-validation-empty-logic-v1` |
| Correlation suite | `single-group-correlation-v1` |
| Historical reference source | `9fa50276f5fb70dcd879b0a9712c8d69c0868967` |
| Complete pre-retirement worktree | `07d21272956ec49890267d0fc99deb70e4fd709c` |
| Retired implementation snapshot | `03186c1` |

The historical account differs from current reference semantics 0.3.0 on the separating request `examples/reference-cli/empty-unsigned-number-not-equal-negative.request.json`: the old account returned `Fired(Omission)`, while the corrected current account returns `Fired(Value)`. Requests and responses carry protocol and kernel versions but no reference-semantics selector, so the old result is recoverable only from the pinned historical source rather than from the current executable.

## Deleted artifact identities

The complete files remain available at pre-retirement revision `07d21272956ec49890267d0fc99deb70e4fd709c`.

| Historical path | SHA-256 |
|---|---|
| `reference/supported-fragment-v1.json` | `89e47bda4ee54ac1f80f3bba004e85c27b0cb31c5d97fda1869727cf358e3f17` |
| `reference/flat-validation-empty-logic-v1.capability.json` | `52708f38e3d72e6d0939c00438baf1abdd3b34df31fbb23f8dea0bac86fef3c1` |
| `reference/flat-validation-empty-logic-v1.conformance.json` | `a71b70dfd832ed607c171a4d9139d76663ebb224c63f41059cfbd5ea272f3c8c` |
| `reference/flat-validation-empty-logic-v1.generated-differential-v1.json` | `897dca670bf9fcb6d0cff7cbcb6ce01fd6feb1c41187712928d9f0edcdbe6f87` |
| `reference/flat-validation-empty-logic-v1.mutation-plan.json` | `5489f223e2cf5362d718ca94935533cf2982beadd5c944b9c78e11cd54e89381` |
| `reference/single-group-correlation-v1.conformance.json` | `7e1b8f52ee08c8b3aed8e414df27573ebc9f8ffe27c4103aa8f954fe7277ec2d` |
| `reference/reference-semantics-0.2.0-separating-replay.json` | `bd0148e39019c8773f57e7904c01e10c19b33b9cbcae7f498e9eacc50a6d060a` |
| `reference/reference-semantics-0.2.0.lock.json` | `75636af6d8bca17aa0ab4f1528597c5105d32eb0ecb23cc1f3426c7e33474473` |
| `reference/reference-semantics-lineage-v1.json` | `8319f62c25d43fe7fab0e39a30184b7e189aaab0e0d28d6506041db4c115a78c` |
| `qualification/flat-validation-empty-logic-v1-rust-v1/generated-differential-v1.RESULT.json` | `478ad0be4fefe2f0e7e0e5cddc6b81171c5f0ed6f7fc32abc1d2156106781f15` |

The historical artifact lock contains the selected 152-file dependency inventory for the 0.2.0 shipment. Its digest is recorded above; reproducing that inventory requires the pinned pre-retirement revision. Current gates intentionally do not traverse or rehash the retired tree.

## Cold Rust implementation

The first isolated consumer experiment tested whether a language-neutral semantic handover could carry a nontrivial A12 decision procedure without requiring the implementer to research the kernel.

The handover originated at source revision `fb0a50d8715aaef07431692811ed89ac69a764c5`. The implementer produced natural Rust revision `7606fd5b881a8bdb8c94daf409ff4c495e572b29`, the initial report at `c39be53cb5031e60a8244d5feadda4c851846288`, the corrected inventory/report state at `91044000c7f71d98e1e67691be035b627e6f7508`, and the feedback report at `9e308bf405ddc7c029a5d1297386ecb2415e5c4c`.

The source-side mutation packet was exported at `e408c9bd87ab8de576c900f2e42e0f13e868da76`; its packet SHA-256 was `28b1e0e074a53dc3abb7fe69f4ae97286f4fdf1e81a1d80e92e8a29709a8ab16`. The isolated consumer committed the accepted seven-mutation result and its 138 raw logs at Rust revision `d213005b3972c2acd8f67e87f523a923d69f6a54`. Every predicted mutation fired, every restoration gate passed, and no unresolved semantic question remained.

The later generated differential used Lean source revision `2cdc37746737d83241f91cd89fa0b56c99c2d47a` and the same Rust candidate revision. It executed 52 generated cases through both processes and recorded 52 agreements, zero disagreements, and the same verdict distribution on both sides:

| Verdict | Count |
|---|---:|
| `notFired` | 14 |
| `fired.value` | 11 |
| `fired.omission` | 13 |
| `unknown` | 14 |

The canonical result SHA-256 is `478ad0be4fefe2f0e7e0e5cddc6b81171c5f0ed6f7fc32abc1d2156106781f15`. Downstream revision `6a4df4ebaf15efd5620d60caf6cf9ac9834b668e` mirrored that result and documented the outcome without changing the executed candidate identity.

## What the experiment established

Under its recorded isolation boundary, the language-neutral state model, staged algorithm, complete verdict tables, worked traces, separating cases, explicit exclusions, and evidence classifications were sufficient for one independent Rust implementation to recover the named finite evaluator without consulting Lean source, the kernel, a12-dmkits, or undocumented conversation context. The seven source mutations and 52-case post-cold differential showed that the transported mechanism generalized beyond dispatch on the eight visible fixtures.

This establishes knowledge transport only for the historical finite profile. It does not transfer Lean proofs, establish universal Rust correctness, add kernel evidence, close general flat validation, authenticate the attested external command history, or qualify a production release. The current [implementer guide](../IMPLEMENTER-GUIDE.md) retains the reusable playbook; the current [flat kit](../IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) and [correlation kit](../IMPLEMENTER-KIT-CORRELATION.md) target reference semantics 0.3.0/V2.

## Historical correlation documentation audit

An isolated documentation audit also consumed the historical 16-case correlation kit, protocol, manifest, examples, evidence projections, and ordinary build commands without reading the Lean implementation, `spec/`, sibling repositories, or kernel material. It recovered the raw and resolved types, seven-stage evaluator, asymmetric `Inner`/`Outer` routing, filter-before-consumer footprint, process contract, and evidence limits. The audit found and triggered corrections for two material documentation contradictions: a model may declare sibling repeatable groups even though one rule selects exactly one, and the public all-inner result is `unsupported/uncorrelatedHaving`, not the internal `missingOuter` constructor. It did not implement or execute an independent candidate, so it established documentation sufficiency to start the named spike rather than executable conformance.

## Recovery

Use a detached checkout or worktree at `07d21272956ec49890267d0fc99deb70e4fd709c` to inspect every deleted V1 artifact and its non-writing integrity gate. Use `03186c1` when the retired mutation and generated-differential implementations themselves are required. Do not restore those files or commands to current `main` merely to reproduce history.
