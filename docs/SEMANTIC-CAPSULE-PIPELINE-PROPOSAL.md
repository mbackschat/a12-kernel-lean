# Compact semantic-evidence pipeline

> Status: accepted consolidation plan, 2026-07-17. This document owns the migration from packet-specific Lean re-auditing to a settled a12-dmkits transporter and compact Lean semantic projections. Current implementation state remains in [`PLAN.md`](PLAN.md), [`ARCHITECTURE.md`](ARCHITECTURE.md), [`EVIDENCE.md`](EVIDENCE.md), and [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md).

## Decision

The project will keep kernel differential evidence but stop reproducing the complete capture system inside Lean. a12-dmkits owns kernel execution, runner fidelity, request and consumed-document binding, capabilities, legality, qualification, closure identity, receipts, deterministic recapture, and raw-packet verification. a12-kernel-lean retains that complete certified raw unit for audit, treats it as opaque during normal replay, and consumes one compact producer-certified semantic-observation bundle through an operation-neutral reader plus a small typed family projection.

This is an explicit trust boundary, not a claim that transport no longer matters. The real kernel remains the behavioral oracle. a12-dmkits becomes the trusted transporter from kernel execution to the compact observation bundle, while its interpreter remains triangulation rather than an oracle. Lean checks the bundle's closed semantic projection against its executable account and proves internal laws; it no longer re-implements the transporter's receipt, filesystem, runner, capability, qualification, or closure audit for every capsule.

## Why this changes

The first full capture proved that a maintained external boundary can produce reproducible, qualified evidence. It also showed that downstream re-auditing does not scale with the semantic body:

| Current surface | Physical lines | Nonblank lines |
|---|---:|---:|
| `A12Kernel/Evidence/` | about 8,200 | — |
| Direct-cascade semantics, proofs, and conformance | about 405 | — |
| Direct-cascade schema, replay, binder, and tests | 2,183 | 1,936 |
| Complete replaceable direct-cascade stack including capture-receipt code and tests | 2,458 | 2,179 |
| Three packet-specific String binders | 2,733 | 2,493 |

The problem is not the once-in-a-lifetime upstream capture implementation. The problem is making each new Lean semantic capsule understand packet inventories, capability bytes, qualification reports, consumed-document identities, runner fidelity, closure identities, and process receipts. Those are producer assurance concerns, not A12 semantic clauses.

The completed Rust experiment, retained direct-cascade packet, trusted proof root, pure semantic capsules, and small older projection replays have all proved useful. The packet-specific Lean binder pattern has proved too expensive to repeat. The project therefore consolidates around the parts that paid for themselves and removes the duplicated boundary.

## Ownership after consolidation

| Concern | Owner | Lean treatment |
|---|---|---|
| Kernel execution and engine closure | a12-dmkits | Named provenance only |
| Request legality and consumed-input identity | a12-dmkits | Trusted producer assertion |
| Runner route integrity and fidelity | a12-dmkits | Trusted producer assertion |
| Qualification, receipts, deterministic recapture, and mutation qualification | a12-dmkits | Raw artifacts retained, opaque to ordinary replay |
| Compact bundle production from the certified observation | a12-dmkits | Producer-certified interface |
| Bundle schema, identity, bounded decoding, and case separation | a12-kernel-lean owns the canonical consumer contract; a12-dmkits explicitly accepts and implements its producer side | Checked once by an operation-neutral Lean reader; a12-kernel-lean mints an incompatible schema version only through an accepted cross-project proposal |
| Family input and observable result meaning | a12-kernel-lean | Closed typed family projection |
| Executable semantics, laws, and non-laws | a12-kernel-lean | Trusted semantic and proof roots |
| Interpreter comparison | a12-dmkits plus project review | Triangulation only |

The raw packet remains immutable and inspectable. “Opaque to Lean” means ordinary `lake test` does not recursively verify or reinterpret it; it does not mean the packet is deleted or unauditable.

## Three assurance tiers

### Tier 1 — semantic development

The default unit is the small vertical Lean capsule: source study, exact executable clause, red/green conformance, useful theorem, nearest non-law, assumptions, and implementation-map update. A missing external observation is recorded as `external evidence pending`; it does not block independent semantic and proof work when the clause is sufficiently grounded to model narrowly.

Tier 1 must remain the dominant day-to-day work. It must not require a capture schema change, packet binder, qualification report, filesystem inventory, or release artifact.

### Tier 2 — family calibration

Related primitive choices receive a focused external matrix through the maintained a12-dmkits boundary. The producer returns a compact semantic-observation bundle plus references to the retained raw certified unit. Lean decodes the compact bundle, projects one named family into typed inputs and observations, executes the real semantic definitions, and rejects mismatches.

Tier 2 establishes empirical correspondence only for the retained observations. It does not prove universal kernel equivalence.

### Tier 3 — shipment and release qualification

Full candidate differentials, mutation qualification, production packaging, protocol compatibility, and downstream release claims run only for a real shipment or consumer. Existing Rust qualification remains useful history, but these process lanes are not mandatory scaffolding for every new semantic clause.

## Compact bundle contract

The generic envelope deliberately knows almost nothing about A12 operations:

```lean
structure SourceIdentity where
  producer : String
  revision : String
  rawCapture : FileDigest
  qualification : Option QualificationIdentity

structure ObservationCase where
  id : String
  input : Json
  observed : Json

structure Family where
  id : String
  projectionId : String
  projectionVersion : Nat
  source : SourceIdentity
  cases : List ObservationCase

structure Bundle where
  schemaVersion : Nat
  kernelVersion : String
  families : List Family
```

The generic reader enforces closed members, the supported schema and kernel version, valid nonempty identities, positive versions, portable source paths and digest syntax, unique compound `(family id, projection id, projection version)` identities, nonempty unique case IDs within each family record, bounded input size, and exact preservation of the opaque `input` and `observed` JSON values. This permits multiple projection records for one semantic family and reuse of one projection contract across families without making an exact consumer identity ambiguous.

Separating `input` from `observed` is mandatory. A family decoder must not hide an expected result inside the replay input, and a semantic mutation must still disagree with the observation half.

The generic reader must not contain operation, model, computation, validation-message, runner, channel, legality, capability, packet-envelope, or qualification-report vocabulary. It must not walk, parse, hash, or relationally validate the retained raw packet. The source identities are provenance anchors asserted by the producer-certified bundle.

Each family owns a small typed decoder for its exact inputs and observables. It preserves multiplicity and every semantically claimed distinction, but deliberately omits producer-only transport detail. A family may project away a stronger raw distinction only when the exclusion is explicit—for example, the first direct-cascade account projects exact absent versus present-empty application state to a value-only result.

## What leaves ordinary Lean replay

After the compact direct-cascade bundle is accepted, remove its packet-specific:

- capture-receipt decoder and role inventory;
- recursive packet-tree hashing and receipt sidecar checks;
- capabilities byte parsing;
- packet, legality, model, request, placement, and consumed-document relation checks;
- raw route/channel/fidelity decoders;
- qualification profile/report and closure parsing;
- recapture-diff and scenario-mutation receipt checks;
- interpreter-fidelity reconstruction.

The complete raw packet, qualification sidecars, recapture diff, and mutation receipt remain under `evidence/` unchanged. Their upstream checks and Git provenance remain available for an audit. Lean's durable statement becomes:

> Lean decodes and replays an upstream-certified compact typed projection anchored to named retained raw receipt identities; the raw unit remains available for upstream verification and human audit but is opaque to ordinary Lean replay.

## Measurable limits

The first migration has hard budgets measured as nonblank production lines, excluding module comments and JSON data:

- generic envelope and loader: at most 180;
- direct-cascade typed family decoder, evaluator projection, and checker: at most 360;
- steady-state target for a later ordinary family: at most 250;
- family tests plus relocated generic process locks: at most 110;
- `EvidenceMain` glue: at most 20;
- complete first replacement: at most 670;
- required net reduction from the current direct-cascade stack: at least 1,500.

Across future migrated families, common compact evidence infrastructure should settle around 800–1,000 nonblank lines, not grow in proportion to packet complexity. A new family must not add receipt, filesystem, digest, capability, qualification, or closure code.

If the generic reader exceeds its limit, stop and remove leaked producer responsibilities. If a family exceeds 360 lines, stop and identify whether it is really multiple semantic families. Do not solve a budget miss with compressed unreadable code or generic untyped maps.

The local pre-producer measurement is now concrete: generic reader 157 nonblank lines, its tests 99, direct-cascade family 226, family tests 128, relocated artifact-tree tests 23, and three lines of `EvidenceMain` glue, for 636 raw nonblank lines. This leaves 34 under the complete 670-line cap. Applying the stated exclusion for module comments and inline JSON fixture data leaves 89 lines of family executable test logic plus 19 lines of generic guard logic, totaling 108 under the 110-line tests-plus-guards allowance.

## First migration: direct String cascade

The direct-cascade family is the proof case because its current raw binder is the most expensive and its five semantic observations are already understood.

The compact family carries:

- `source`, prior `Mid`, and prior `Out` as typed case input;
- typed clean, changed, errored, cleared, and value-only applied observations;
- closed Mid/Out targets and a closed target-error cause;
- the exact five case IDs and input matrix;
- explicit exclusions for hidden dependency representation, scheduling, raw runner fidelity, typed/rendered dual values, exact absent-versus-present-empty state, and interpreter-only differences.

The checker compares typed observations directly rather than canonical signature strings. It is parameterized over the replay function so a test mutation can deliberately evaluate the consumer against the original context instead of the producer overlay. The required mismatch set is the three cases with a pre-filled `Mid`: `source-abc-mid-old`, `source-absent-mid-old`, and `source-abcd-mid-old`; the equal and initially absent controls must remain equal. A separate observed-payload mutation changes the target error cause and must also fail.

The old and new lanes may coexist only during the migration gate. Once the producer-certified compact bundle is ferried and both lanes agree, delete the old direct-cascade binder, schema, replay, and tests in the same delivery sequence. Do not leave permanent dual paths.

`A12Kernel/Process/Artifact.lean` and `ArtifactTree.lean` remain because downstream mutation qualification still uses them. Their unique global path-order and symlink guards now live in the 23-nonblank-line process-owned `ArtifactTreeTest.lean`, so deleting the capture receipt tests will not discard generic filesystem coverage.

## Producer-side consolidation and frozen a12-dmkits capture-contract V1

Frozen a12-dmkits capture-contract V1 identities and retained artifacts must never be mutated, but current-main implementation code does not have to live forever merely because an immutable artifact exists. This is unrelated to this repository's separate frozen reference-semantics v1 manifests, suites, and Rust shipment, which are not candidates for deletion here. When a successor capture/export path arrives, a12-dmkits should avoid maintaining complete parallel capture-contract V1 and successor stacks indefinitely.

The future upstream proposal must inventory three categories:

1. **Immutable history:** capture-contract V1 capabilities bytes, packet/receipt identities, accepted raw packets, source revisions, and acceptance record remain untouched.
2. **Minimal compatibility duty:** keep only the smallest fixture or verifier needed by an actual supported consumer, or explicitly pin the historical verifier to its tagged source revision.
3. **Retirable implementation:** duplicate capture-contract V1 runner, mapper, command, schema, and mutation machinery may be removed from current main after the successor reproduces the required semantic bundle, all named external consumers accept it, the frozen packet remains auditable through a documented historical reproduction route, immutable bytes are proven unchanged, a clean successor capture passes, and the owner approves the sunset.

“V2 exists” alone is not a deletion condition. The sunset gate requires a consumer inventory, byte-preservation proof for immutable artifacts, a documented historical reproduction route, a clean successor capture, explicit owner approval, and removal rather than indefinite dual maintenance. If no live external consumer needs current-main capture-contract V1 execution, Git history or a tagged release may own historical reproducibility instead of a permanent compatibility subsystem. Retained raw bytes and this repository's frozen reference-semantics v1 shipment remain immutable regardless of the upstream implementation decision.

## Sequencing

1. Finish the internally proved String-ingestion capsule and leave its external observation pending. Completed in commit `41ddc9d`.
2. Implement the generic bundle reader and direct-cascade family decoder against red/green local contract tests. Local fixtures are schema tests, not kernel evidence.
3. Measure the implementation. If it misses the limits, simplify locally before asking upstream to implement the producer.
4. Completed: [`A12-DMKITS-COMPACT-EVIDENCE-PROPOSAL.md`](A12-DMKITS-COMPACT-EVIDENCE-PROPOSAL.md) defines the one post-capture direct-cascade exporter, exact source identities and acceptance bytes, handback, and the separate capture-contract V1 sunset inventory. Validation-message capture remains outlook only. The user ferries the proposal; this project never edits the sibling.
5. Receive and verify the producer-certified compact bundle, retain it beside the opaque raw unit, and prove old-versus-new semantic agreement during the migration gate.
6. Switch `lake test` to the compact family, retain the already relocated generic artifact-tree guards, and delete the replaced direct-cascade stack.
7. Rerun the real and semantic-mutation gates, measure the net deletion, and update current-state owners.
8. Only if the measured pattern meets the limits, consider migrating the two historical String binders. Do not rewrite them merely for uniformity.
9. Request a new external operation only when a real semantic family needs an observation the settled exporter cannot represent. Do not front-load a universal capture protocol.

## Upstream engagement rule

Simple, isolated upstream changes receive a paste-ready prompt. The compact exporter plus capture-contract V1 sunset is a cross-project compatibility change with architecture and lifecycle consequences, so it receives a proposal document under this repository's `docs/` until accepted. That proposal must name the audited a12-dmkits revision, exact source mechanism, required versioned bytes, producer/consumer responsibility, compatibility and retirement effects, separating tests, mutation predictions, acceptance gates, and handback format.

After acceptance, durable producer facts move into a12-dmkits' live spec and this project's evidence/current-state owners. The temporary cross-project proposal is then archived or deleted according to [`DOC-DISCIPLINE.md`](DOC-DISCIPLINE.md); it must not remain a second live upstream specification.

## Stop conditions

Stop and redesign if:

- a new semantic case requires new Lean packet plumbing rather than data;
- the generic reader learns an operation-specific concept;
- family code revalidates producer receipts or runner fidelity;
- raw packets become the input to normal Lean replay again;
- compact observations lose polarity, poison/unknown, multiplicity, order, applied-state, or other distinctions the family actually claims;
- a semantic mutation does not fail;
- old and new evidence lanes remain after the migration gate;
- a12-dmkits capture-contract V1 and its successor become permanent duplicated implementations without a supported-consumer reason;
- external evidence blocks unrelated internal semantic/proof progress;
- evidence infrastructure resumes growing faster than executable semantics and proofs.

The practical goal is one settled evidence bridge and many small semantic capsules. Once that bridge is proven, most project effort returns to semantics, theorems, counterexamples, and useful consumer-facing knowledge.
