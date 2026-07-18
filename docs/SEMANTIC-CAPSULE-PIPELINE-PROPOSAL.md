# Compact semantic-evidence pipeline

> Status: implemented and measured, 2026-07-18. This document owns the settled boundary and scaling constraints that replaced packet-specific Lean re-auditing with the a12-dmkits transporter and compact Lean semantic projections. Current implementation state remains in [`PLAN.md`](PLAN.md), [`ARCHITECTURE.md`](ARCHITECTURE.md), [`EVIDENCE.md`](EVIDENCE.md), and [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md).

## Decision

The project will keep kernel differential evidence but stop reproducing the complete capture system inside Lean. a12-dmkits owns kernel execution, runner fidelity, request and consumed-document binding, capabilities, legality, qualification, closure identity, receipts, deterministic recapture, and raw-packet verification. a12-kernel-lean retains that complete certified raw unit for audit, treats it as opaque during normal replay, and consumes one compact producer-certified semantic-observation bundle through an operation-neutral reader plus a small typed family projection.

This is an explicit trust boundary, not a claim that transport no longer matters. The real kernel remains the behavioral oracle. a12-dmkits becomes the trusted transporter from kernel execution to the compact observation bundle, while its interpreter remains triangulation rather than an oracle. Lean checks the bundle's closed semantic projection against its executable account and proves internal laws; it no longer re-implements the transporter's receipt, filesystem, runner, capability, qualification, or closure audit for every capsule.

## Why this changes

The first full capture proved that a maintained external boundary can produce reproducible, qualified evidence. It also showed that downstream re-auditing does not scale with the semantic body:

| Baseline before migration | Physical lines | Nonblank lines |
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

The completed compact direct-cascade migration removed its packet-specific:

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

The first migration used the following stop-and-inspect budgets measured as nonblank production lines, excluding module comments and JSON data:

- generic envelope and loader: at most 180;
- direct-cascade typed family decoder, evaluator projection, and checker: at most 360;
- steady-state target for a later ordinary family: at most 250;
- family tests plus relocated generic process locks: at most 110;
- `EvidenceMain` glue: at most 20;
- complete first replacement: at most 670;
- required net reduction from the current direct-cascade stack: at least 1,500.

These scoped migration thresholds forced producer responsibilities out of the first replacement; they are not permanent component-size promises after an all-in consolidation moves a live shared guard into the reader while deleting the larger generic mechanism that owned it. Across future migrated families, common compact evidence infrastructure must remain below a 1,000-line ceiling rather than grow in proportion to packet complexity. A new family must not add receipt, filesystem, digest, capability, qualification, or closure code.

During the first migration, exceeding a scoped limit required stopping to remove leaked producer responsibilities or split an oversized family. After consolidation, any proposed reader growth still requires a demonstrated live cross-family need and an all-in recount below the ceiling. Do not solve a budget miss with compressed unreadable code or generic untyped maps.

The first migration checkpoint measured 666 raw nonblank lines against a 2,179-line packet-specific baseline, a scoped reduction of 1,513. That checkpoint deliberately excluded 359 nonblank lines of shared `Artifact` and `ArtifactTree` production support, so it must not be reported as the final all-in cost. The subsequent consolidation deleted all 382 nonblank lines of generic artifact, tree, and tree-test machinery, moved the live path/digest/file guards into the compact reader, and removed one glue line. The settled all-in lane is 753 nonblank lines: reader 211, reader tests 156, direct-cascade family 249, family tests 130, and seven `EvidenceMain` import/check lines. This is 272 fewer than the honest 1,025-line all-in checkpoint and remains below the 1,000-line common-infrastructure ceiling. The reader's 211 lines supersede the scoped 180-line checkpoint because they absorb only the live guards while removing 359 lines of generic production support; the narrower 670-line first-replacement cap served its migration audit and is not reused to hide formerly shared support.

## First migration: direct String cascade

The direct-cascade family is the proof case because its current raw binder is the most expensive and its five semantic observations are already understood.

The compact family carries:

- `source`, prior `Mid`, and prior `Out` as typed case input;
- typed clean, changed, errored, cleared, and value-only applied observations;
- closed Mid/Out targets and a closed target-error cause;
- the exact five case IDs and input matrix;
- explicit exclusions for hidden dependency representation, scheduling, raw runner fidelity, typed/rendered dual values, exact absent-versus-present-empty state, and interpreter-only differences.

The checker compares typed observations directly rather than canonical signature strings. It is parameterized over the replay function so a test mutation can deliberately evaluate the consumer against the original context instead of the producer overlay. The required mismatch set is the three cases with a pre-filled `Mid`: `source-abc-mid-old`, `source-absent-mid-old`, and `source-abcd-mid-old`; the equal and initially absent controls must remain equal. A separate observed-payload mutation changes the target error cause and must also fail.

The old and new lanes coexisted for one migration gate, agreed on all five cases, and the old direct-cascade binder, schema, replay, receipt decoder, and tests were then deleted. No permanent dual path remains.

The compact [`ObservationBundle`](../A12Kernel/Evidence/ObservationBundle.lean) now owns directly the closed portable-path, digest, bounded-file, and regular non-symlink behavior needed by the live reader. No generic artifact-tree helper remains. The completed Rust mutation campaign is not a reason to retain broader packet-oriented APIs or tests; their historical implementation remains available at Git revision `03186c1`.

## Producer-side consolidation and frozen a12-dmkits capture-contract V1

Frozen a12-dmkits capture-contract V1 identities and retained artifacts must never be mutated, but current-main implementation code does not have to live forever merely because an immutable artifact exists. The owner has confirmed that no known maintained external consumer needs current-main execution and that Git history plus the retained raw and compact artifacts may own historical reproducibility. The current [retirement handoff](A12-DMKITS-CAPTURE-V1-RETIREMENT-PROPOSAL.md) therefore directs a12-dmkits to remove the complete portable capture-V1 implementation and every live documentation trace without minting a successor; only archived documentation retains the exact history.

This decision is separate from this repository's reference-semantics 0.2.0/V1 lineage. That local compatibility estate is now independently audited for migration to current 0.3.0/V2 in the [reference and evidence simplification proposal](REFERENCE-AND-EVIDENCE-SIMPLIFICATION-PROPOSAL.md); immutable historical Rust claims are archived rather than relabeled.

The durable distinction is:

1. **Immutable historical evidence:** accepted raw and compact bytes, packet and qualification identities, and source revisions remain recoverable and are never rewritten.
2. **Current-main producer code:** the unused capture source set, schemas, commands, exporter, qualification machinery, mutations, tests, and live documentation are removed rather than maintained or duplicated.
3. **Future producer capability:** a new operation is demand-driven by a concrete semantic family and designed from its observation needs; it is not a compatibility successor created merely to preserve V1 structure.

## Sequencing

1. Finish the internally proved String-ingestion capsule and leave its external observation pending. Completed in commit `41ddc9d`.
2. Completed: implement the generic bundle reader and direct-cascade family decoder against red/green local contract tests. Local fixtures remain schema tests, not kernel evidence.
3. Completed: measure and simplify the local implementation before requesting the producer.
4. Completed: the temporary cross-project proposal produced the one closed post-capture exporter recorded historically in a12-dmkits' capture-contract V1 estate. The accepted bytes are retained here; the unused upstream implementation is now subject to the owner-directed [retirement handoff](A12-DMKITS-CAPTURE-V1-RETIREMENT-PROPOSAL.md). Validation-message capture remains outlook only.
5. Completed: verify and retain the producer-certified compact bundle beside the opaque raw unit and prove old-versus-new semantic agreement during the sole migration gate.
6. Completed: switch `lake test` to the compact family, retain only its closed reader guards, and delete the replaced direct-cascade stack.
7. Completed: the real overlay-bypass semantic mutation failed, the natural gate recovered, and the first scoped migration measured a 1,513-line reduction. The subsequent all-in audit removed the remaining generic artifact-tree machinery and settled the complete live lane at 753 nonblank lines.
8. Only if the measured pattern meets the limits, consider migrating the two historical String binders. Do not rewrite them merely for uniformity.
9. Request a new external operation only when a real semantic family needs an observation the settled exporter cannot represent. Do not front-load a universal capture protocol.

## Upstream engagement rule

Simple, isolated upstream changes receive a paste-ready prompt. A cross-project capability or retirement with architecture and lifecycle consequences receives a temporary proposal document under this repository's `docs/` until accepted. It must name the audited a12-dmkits revision, exact source mechanism, required versioned bytes, producer/consumer responsibility, compatibility and retirement effects, separating tests where relevant, acceptance gates, and handback format.

After acceptance, durable producer facts move into a12-dmkits' live owners when the capability remains current, or into its archived documentation when the capability is retired; this project's evidence/current-state owners retain only their local consequences. The temporary cross-project proposal is then archived or deleted according to [`DOC-DISCIPLINE.md`](DOC-DISCIPLINE.md); it must not remain a second live upstream specification.

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
