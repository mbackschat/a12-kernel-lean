# Compact semantic-evidence pipeline

> Status: implemented and measured, last consolidated 2026-07-19. This document owns the settled compact Lean consumer boundary, the completed retirement of its one-time upstream producer estate, and the scaling constraints for future demand-driven calibration. Current implementation state remains in [`PLAN.md`](PLAN.md), [`ARCHITECTURE.md`](ARCHITECTURE.md), [`EVIDENCE.md`](EVIDENCE.md), and [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md).

## Decision

The project keeps kernel differential evidence without reproducing a complete producer system inside Lean. Historical a12-dmkits capture-contract V1 established kernel execution, runner fidelity, request and consumed-document binding, capabilities, legality, qualification, closure identity, receipts, deterministic recapture, raw-packet verification, and the compact export for the accepted direct-cascade unit. a12-kernel-lean retains that unit for audit, treats it as opaque during normal replay, and consumes its compact semantic-observation bundle through an operation-neutral reader plus a small typed family projection. a12-dmkits has since retired the producer implementation from current `main`.

This is an explicit historical trust boundary, not a claim that transport no longer matters. The real kernel remains the behavioral oracle. For the accepted unit, the pinned a12-dmkits revisions are the producer and its interpreter is triangulation rather than an oracle. Lean checks the bundle's closed semantic projection against its executable account and proves internal laws; it does not re-implement receipt, filesystem, runner, capability, qualification, or closure audits. For a future family, current corpus/differential facilities are used only when their natural observation fits; otherwise the family remains `external evidence pending` until a concrete minimal upstream capability and its assurance contract are accepted.

## Why this changed

The first full capture proved that a maintained external boundary can produce reproducible, qualified evidence. It also showed that downstream re-auditing does not scale with the semantic body:

| Baseline before migration | Physical lines | Nonblank lines |
|---|---:|---:|
| `A12Kernel/Evidence/` | about 8,200 | — |
| Direct-cascade semantics, proofs, and conformance | about 405 | — |
| Direct-cascade schema, replay, binder, and tests | 2,183 | 1,936 |
| Complete replaceable direct-cascade stack including capture-receipt code and tests | 2,458 | 2,179 |
| Three packet-specific String binders | 2,733 | 2,493 |

The problem is not the once-in-a-lifetime upstream capture implementation. The problem is making each new Lean semantic capsule understand packet inventories, capability bytes, qualification reports, consumed-document identities, runner fidelity, closure identities, and process receipts. Those are producer assurance concerns, not A12 semantic clauses.

The completed Rust experiment, retained direct-cascade packet, trusted proof root, pure semantic capsules, and small older projection replays have all proved useful. The packet-specific Lean binder pattern proved too expensive to repeat. The project therefore consolidated around the parts that paid for themselves and removed the duplicated boundary.

## Ownership after consolidation

| Concern | Owner | Lean treatment |
|---|---|---|
| Accepted direct-cascade execution, input binding, runner fidelity, qualification, receipts, recapture, and compact production | Historical a12-dmkits revisions and the project-local recovery record | Raw artifacts remain immutable in Git history; the checked-out compact artifact and its pinned producer assertions drive ordinary Lean replay |
| Current ordinary corpus capture/replay and kernel differentials | Current a12-dmkits facilities under their live owners | Used only when their existing own-domain observation naturally closes the requested family |
| Missing future observation capability | a12-kernel-lean specifies the concrete semantic need; a12-dmkits implements only an accepted upstream request | No V1 packet shape, qualification graph, exporter, or universal successor is presumed |
| Bundle schema, identity, bounded decoding, and case separation | a12-kernel-lean | Checked once by an operation-neutral Lean reader; reuse or evolution requires a concrete accepted consumer need |
| Family input and observable result meaning | a12-kernel-lean | Closed typed family projection |
| Executable semantics, laws, and non-laws | a12-kernel-lean | Trusted semantic and proof roots |
| Interpreter comparison | a12-dmkits plus project review | Triangulation only |

The raw packet remains immutable and inspectable at its named Git revision. “Opaque to Lean” means ordinary `lake test` does not recursively verify or reinterpret it; deleting it from `HEAD` does not delete its audit history.

## Three assurance tiers

### Tier 1 — semantic development

The default unit is the small vertical Lean capsule: source study, exact executable clause, red/green conformance, useful theorem, nearest non-law, assumptions, and implementation-map update. A missing external observation is recorded as `external evidence pending`; it does not block independent semantic and proof work when the clause is sufficiently grounded to model narrowly.

Tier 1 must remain the dominant day-to-day work. It must not require a capture schema change, packet binder, qualification report, filesystem inventory, or release artifact.

### Tier 2 — family calibration

Related primitive choices receive a focused external matrix. First use an existing maintained a12-dmkits corpus or differential route if its natural observation shape is sufficient. Otherwise request the smallest purpose-specific producer capability and define its assurance and retention boundary from the concrete need. An accepted handback supplies a compact semantic account and the provenance or supporting material required by that contract; it does not automatically reproduce the retired V1 packet structure. Lean decodes the compact account, projects one named family into typed inputs and observations, executes the real semantic definitions, and rejects mismatches.

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

The generic reader must not contain operation, model, computation, validation-message, runner, channel, legality, capability, packet-envelope, or qualification-report vocabulary. It must not walk, parse, hash, or relationally validate retained raw material. Source identities are provenance anchors asserted by the direct producer or by the reviewed migration that created the compact bundle; each family must state which assurance route it uses.

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

The complete historical raw packet, qualification sidecars, recapture diff, mutation receipt, and expectation-free scenario have moved out of `HEAD`. Their exact project revision, Git tree objects, principal SHA-256 identities, producer revisions, and claim limits are recorded in the [archived evidence record](archived/STRING-DIRECT-CASCADE-RAW-EVIDENCE.md). Lean's durable statement is:

> Lean decodes and replays a historically producer-certified compact typed projection anchored to named retained raw receipt identities; the raw unit remains available through pinned Git history and human audit but is opaque to ordinary Lean replay.

## Measurable limits

The first migration used the following stop-and-inspect budgets measured as nonblank production lines, excluding module comments and JSON data:

- generic envelope and loader: at most 180;
- direct-cascade typed family decoder, evaluator projection, and checker: at most 360;
- steady-state target for a later ordinary family: at most 250;
- family tests plus relocated generic process locks: at most 110;
- `EvidenceMain` glue: at most 20;
- complete first replacement: at most 670;
- required net reduction from the then-current direct-cascade stack: at least 1,500.

These scoped migration thresholds forced producer responsibilities out of the first replacement; they are not permanent component-size promises after an all-in consolidation moves a live shared guard into the reader while deleting the larger generic mechanism that owned it. Across future migrated families, common compact evidence infrastructure must remain below a 1,000-line ceiling rather than grow in proportion to packet complexity. A new family must not add receipt, filesystem, digest, capability, qualification, or closure code.

During the first migration, exceeding a scoped limit required stopping to remove leaked producer responsibilities or split an oversized family. After consolidation, any proposed reader growth still requires a demonstrated live cross-family need and an all-in recount below the ceiling. Do not solve a budget miss with compressed unreadable code or generic untyped maps.

The first migration checkpoint measured 666 raw nonblank lines against a 2,179-line packet-specific baseline, a scoped reduction of 1,513. That checkpoint deliberately excluded 359 nonblank lines of shared `Artifact` and `ArtifactTree` production support, so it must not be reported as the final all-in cost. The subsequent consolidation deleted all 382 nonblank lines of generic artifact, tree, and tree-test machinery, moved the live path/digest/file guards into the compact reader, and removed one glue line. The settled all-in lane is 753 nonblank lines: reader 211, reader tests 156, direct-cascade family 249, family tests 130, and seven `EvidenceMain` import/check lines. This is 272 fewer than the honest 1,025-line all-in checkpoint and remains below the 1,000-line common-infrastructure ceiling. The reader's 211 lines supersede the scoped 180-line checkpoint because they absorb only the live guards while removing 359 lines of generic production support; the narrower 670-line first-replacement cap served its migration audit and is not reused to hide formerly shared support.

## Historical first migration: direct String cascade

The direct-cascade family was selected as the first proof case because its then-current raw binder was the most expensive and its five semantic observations were already understood.

The compact family carries:

- `source`, prior `Mid`, and prior `Out` as typed case input;
- typed clean, changed, errored, cleared, and value-only applied observations;
- closed Mid/Out targets and a closed target-error cause;
- the exact five case IDs and input matrix;
- explicit exclusions for hidden dependency representation, scheduling, raw runner fidelity, typed/rendered dual values, exact absent-versus-present-empty state, and interpreter-only differences.

The checker compares typed observations directly rather than canonical signature strings. It is parameterized over the replay function so a test mutation can deliberately evaluate the consumer against the original context instead of the producer overlay. The required mismatch set is the three cases with a pre-filled `Mid`: `source-abc-mid-old`, `source-absent-mid-old`, and `source-abcd-mid-old`; the equal and initially absent controls must remain equal. A separate observed-payload mutation changes the target error cause and must also fail.

The old and new lanes coexisted for one migration gate, agreed on all five cases, and the old direct-cascade binder, schema, replay, receipt decoder, and tests were then deleted. No permanent dual path remains.

The compact [`ObservationBundle`](../A12Kernel/Evidence/ObservationBundle.lean) now owns directly the closed portable-path, digest, bounded-file, and regular non-symlink behavior needed by the live reader. No generic artifact-tree helper remains. The completed Rust mutation campaign is not a reason to retain broader packet-oriented APIs or tests; their historical implementation remains available at Git revision `03186c1`.

## Second migration: root-String computation and target validation

The two older root-String stacks now use one compact typed lane with two ordered source records rather than falsely merging two independent captures. The unconstrained record preserves 13 delta-only cases; it does not promote exact application into external evidence. The target-validation record preserves nine checked outcomes, deltas, and exact absent/present-empty/present-value application states. Both records remain project-reviewed projections of historically route-agreed kernel observations, not producer-certified compact exports.

Commit `19733d9` is the one-time dual-path agreement checkpoint. At that revision, the complete old binders checked receipts, models, case shapes, route agreement, and triangulation; a temporary typed comparator required exact ordered equality with all 22 compact inputs and observations; and focused semantic mutations failed on their predicted sets. The old schemas, replays, binders, raw data, and comparator are subsequently removed. [`STRING-COMPUTATION-RAW-EVIDENCE.md`](archived/STRING-COMPUTATION-RAW-EVIDENCE.md) owns the recovery revisions, digests, claims, and exclusions.

The permanent family-specific addition is 271 nonblank production lines plus 65 test lines. It replaces 2,106 old permanent Lean lines and a 125-line migration-only checker. The 13,104-byte compact bundle replaces 80,490 bytes of raw captures, models, projections, and cases. The generic reader did not grow, and no packet, receipt, qualification, route, or generator concept entered ordinary replay.

## Third migration: validation, operators, iteration, and correlation

The final migration uses one compact validation bundle rather than four more readers or a duplicate correlation evaluator. Its 49 records preserve seven closed families: 25 public normalized evidence associations and 24 private path, required, operator-sensitive, and uncorrelated-iteration replays. There are 48 distinct external observations because the directional empty-Number witness intentionally appears in both halves.

The public half reuses the existing candidate/reference process gate. It binds the pinned bundle, kernel version, declared evidence case, exact normalized request, and fidelity-projected expected response; no second public replay driver or protocol bridge remains. The private half uses small adapters over the live reference evaluator, required staging, checked flat evaluator, and one-star iteration semantics. Static rejection code/class pairs are closed together, required-empty retains its modeled message code and pointer, external silence remains suppression rather than a claimed hidden verdict, and static acceptance remains acceptance rather than an external runtime-row claim.

Commit `a04d6d9f51227dbe47014a5181590507e1b269bd` is the one-time validation dual-path checkpoint. It ran all 48 validation cases through their complete legacy stack beside the 24-case compact private replay and passed both current public suites with strengthened request, response, and case-association mutations. The already-compact 22-case root-String and five-case cascade lanes also passed; their own archives record their earlier complete-binder comparisons. The subsequent deletion removes 85 raw files and 761,310 bytes, 12 legacy modules and 2,061 nonblank lines, and the legacy driver body. The permanent validation projection and focused tests occupy 428 nonblank lines; the final driver is a small dispatcher. Exact source digests, producer caveats, the one a12-dmkits iteration disagreement, and recovery revisions live in [`VALIDATION-RAW-EVIDENCE.md`](archived/VALIDATION-RAW-EVIDENCE.md).

At completion of the three migrations, the evidence source estate was 1,528 nonblank Lean lines and 82,628 bytes, while Evidence/Reference/Process support was 5,449 nonblank lines against 5,453 theory lines. This is a historical migration baseline, not the current theory count or a reusable support budget. The checked-out `evidence/` directory contained only the three compact bundles and totaled 135,047 bytes. Future ordinary work grows semantic capsules; any proposed support growth still needs a named current consumer, explicit approval under the repository rules, and a fresh ratio check.

## Producer-side consolidation and retired a12-dmkits capture-contract V1

Frozen a12-dmkits capture-contract V1 identities and retained artifacts remain immutable, while revision `45b264b2d6213dd7d4d261fa040034371b0c8fcd` removed the complete unused implementation from current upstream `main`: 96 tracked files, 634,739 bytes, and 11,637 nonblank lines of source, tests, fixtures, mutation machinery, commands, build wiring, and live documentation. The exact historical contract and detached-revision recovery route live only in a12-dmkits' [`archived capture proposal`](../../a12-rulekit/docs/archived/A12-DMKITS-CAPTURE-PROPOSAL.md). No successor was minted.

This decision is separate from this repository's reference-semantics identities. The local 0.2.0/V1 compatibility estate has been retired; current shipments use 0.3.0/V2 over unchanged wire protocol 1, and the exact historical Rust claims and recovery revisions live in the [archived record](archived/REFERENCE-SEMANTICS-0.2.0-AND-RUST-EXPERIMENT.md). The completed [reference and evidence simplification work program](archived/REFERENCE-AND-EVIDENCE-SIMPLIFICATION-PROPOSAL.md) records the measured deletion sequence and tradeoff.

The durable distinction is:

1. **Immutable historical evidence:** accepted raw and compact bytes, packet and qualification identities, and source revisions remain recoverable and are never rewritten.
2. **Current-main producer code:** the unused capture source set, schemas, commands, exporter, qualification machinery, mutations, tests, and live documentation have been removed rather than maintained or duplicated.
3. **Future producer capability:** a new operation is demand-driven by a concrete semantic family and designed from its observation needs; it is not a compatibility successor created merely to preserve V1 structure.

## Completed migration and continuing trigger

The archived [reference and evidence simplification work program](archived/REFERENCE-AND-EVIDENCE-SIMPLIFICATION-PROPOSAL.md) and the family-specific evidence archives own the completed migration checkpoints, measurements, recovery identities, and dual-path agreement records. They are history, not a live queue.

Request a new external operation only when a real semantic family needs an observation the current corpus/differential facilities cannot retain. The retired exporter is not a live extension point; design the smallest new producer from the concrete observation need and do not front-load a universal capture protocol.

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
- a deliberately selected mutation expected to cross a claimed semantic seam is not killed by its predicted separating case or cases;
- old and new evidence lanes remain after the migration gate;
- retired a12-dmkits capture-contract V1 is resurrected or a universal successor is built without a supported-consumer reason;
- external evidence blocks unrelated internal semantic/proof progress;
- evidence infrastructure resumes growing faster than executable semantics and proofs.

The practical goal is one settled evidence bridge and many small semantic capsules. Once that bridge is proven, most project effort returns to semantics, theorems, counterexamples, and useful consumer-facing knowledge.
