# a12-dmkits portable capture V1 retirement handoff

> **Status:** temporary cross-project handoff, ready for owner transfer. This document is deleted after an accepted a12-dmkits handback and migration of durable facts. It concerns only a12-dmkits' adapter-internal portable capture contract; it does not concern the kernel's deprecated document API or this repository's separate reference-semantics 0.2.0/0.3.0 lineage.

## Decision and rationale

Retire the frozen portable capture-contract V1 from current a12-dmkits `main` without minting a successor. Its only known maintained external client has retained the accepted raw unit and producer-certified compact semantic bundle in this repository and no longer invokes the live capture commands. Keeping executable V1 compatibility therefore makes every future kernel, Gradle, dependency, and adapter change carry an otherwise unused source set, schemas, verifier, commands, fixtures, mutation guards, and tests.

The audited estate is approximately 11,637 nonblank lines before documentation and build glue: about 5,890 production lines under [`adapter/src/capture/`](../../a12-rulekit/adapter/src/capture/), 3,032 test lines under the capture test package, 2,100 mutation-harness lines, and 615 fixture/example lines. The dedicated [`adapter/build.gradle`](../../a12-rulekit/adapter/build.gradle) wiring also owns a source set, configurations, purity gate, capture commands, one-off exporter, and capture-only dependency declaration. The current [kernel-upgrade proposal](../../a12-rulekit/docs/KERNEL-31-UPGRADE-PROPOSAL.md) demonstrates the ongoing cost by assigning this frozen estate its own API migration and compile gate.

Historical reproducibility moves to exact Git revisions and the existing archived capture document. If raw V1 reproduction is ever necessary, use a detached worktree at the final exporter revision. Do not retain current-main machinery or live-document compatibility traces solely to make that historical operation convenient.

## Boundaries

Delete the portable capture source set, its tests/resources/examples/mutations, its Gradle configurations and tasks, the hard-closed semantic-observation exporter, and every V1 reference from live documentation. Preserve the exact anchors below only in the existing archived capture document; no live spec, guide, README, plan, finding, command index, or compatibility note should retain capture-V1 support or history.

Do not delete or alter a12-dmkits' live `RuntimeLaws`, `CorpusCapture`, `CorpusGenerator`, `CorpusEngines`, corpus replay, or regular differential tests. Do not conflate portable capture V1 with the kernel's deprecated document API called V1. Do not touch a12-kernel-lean or reinterpret its unrelated reference-semantics v1/v2 identity.

## Historical anchors

| Role | Identity |
|---|---|
| Repaired frozen capture baseline | `3ebe756422e8f2dea447fbd62f9b26c2f774b7e5` |
| Accepted retained capture | `c992afd62e4fa6148733a5538a3248c30fce60bf` |
| Final compact exporter | `1b5f463b89adc6cfb81b41121cd6c97855e8cbe3` |
| Lean raw-unit landing | `70f296f` |
| Lean compact adoption | `210405c` |
| Capabilities SHA-256 | `b87d381e7f43446bc886292766e34beab72ca3ec179be5f0f614975e66d603ca` |
| Packet receipt SHA-256 | `7e38744283cf17f7f57fe0bce342084a8e2896fb99aa60c2a9f4fb52e185dc17` |
| Qualification receipt SHA-256 | `f581d82d7eb04929b38d4663bbb48a28f09c7399273cd5974cd59e739eca5d64` |
| Compact bundle SHA-256 | `1d8d253e553eba70fa990975666884833748bed9d9b2b6483f472767a9837c7a` |

## Copy-ready upstream prompt

```text
a12-dmkits: retire the frozen portable capture-contract V1 from current main; do not mint a successor

Work only in a12-dmkits. This is an owner-directed deletion and consolidation, not a capture V2 implementation. Snapshot the initial visible worktree and preserve every unrelated tracked or untracked path exactly. Do not write into ../a12-kernel-lean/.

Root decision

The only known maintained external client, a12-kernel-lean, has retained the accepted raw unit and producer-certified compact semantic bundle and no longer calls the live capture commands. The upstream audit found no remaining current-main consumer. Git history plus exact retained artifacts own historical reproducibility. Remove the completed portable capture-contract V1 estate rather than carrying it through future kernel/toolchain changes or building a parallel V2.

Do not conflate this contract with:

- the kernel's deprecated V1 document API;
- the live conformance corpus and RuntimeLaws/CorpusCapture/CorpusGenerator/CorpusEngines;
- a12-kernel-lean's separate reference-semantics protocol v1/v2.

Archived historical anchors

Append one concise completion/retirement section containing the following anchors to the existing archived capture proposal. Do not put this material into a live specification, README, guide, finding, or plan:

- frozen baseline 3ebe756422e8f2dea447fbd62f9b26c2f774b7e5
- accepted capture c992afd62e4fa6148733a5538a3248c30fce60bf
- final exporter 1b5f463b89adc6cfb81b41121cd6c97855e8cbe3
- a12-kernel-lean raw landing 70f296f and compact adoption 210405c
- capabilities b87d381e7f43446bc886292766e34beab72ca3ec179be5f0f614975e66d603ca
- packet receipt 7e38744283cf17f7f57fe0bce342084a8e2896fb99aa60c2a9f4fb52e185dc17
- qualification receipt f581d82d7eb04929b38d4663bbb48a28f09c7399273cd5974cd59e739eca5d64
- compact bundle 1d8d253e553eba70fa990975666884833748bed9d9b2b6483f472767a9837c7a

Delete at the root

- adapter/src/capture/**
- adapter/src/test/java/io/github/mbackschat/a12/dm/adapter/capture/**
- adapter/src/test/resources/capture/**
- adapter/capture-examples/**
- tracked adapter/capture-mutations/**
- all capture source-set/configuration, command tasks, exporter task, verifyCapturePurity wiring, capture-only dependency/test wiring, and capture.golden.fix forwarding in adapter/build.gradle

Documentation

- Delete the portable capture contract from live CONFORMANCE-CORPUS-SPEC §15–§15h, including the frozen-V1 record, policies, mutation map, acceptance record, and parked V2 design. Do not replace it with a live retirement section.
- Remove the portable-capture command section from corpus/README.md.
- Remove the capture guard row from TESTING-SPEC and the current capture source-set claim from ARCHITECTURE.
- Correct KERNEL-31-UPGRADE-PROPOSAL so it no longer plans to port or compile capture code; preserve its remaining RuntimeLaws and production document-API migration.
- Sweep API-GUIDE, API-FINDINGS, INTERPRETER-FINDINGS, KERNEL-FINDINGS, docs/README, plans, and every other live Markdown owner for capture-V1 references. Preserve unrelated durable semantic/API findings, but do not keep capture provenance in live findings.
- Keep the existing archived capture proposal as the sole documentation trace and append the completion/retirement anchors there. An archive index may continue to classify it as historical; no active route should point readers to it.

Root-cause acceptance

1. Prove that no source or published component outside the deleted internal estate imports capture classes or relies on its tasks.
2. Search for a second instance: no live command, source-set, task, guard, parked capture-V2 design, portable-capture V1 identifier, capture-V1 provenance, or current-main ownership claim may remain outside `docs/archived/`. Unrelated kernel document-API V1 terminology is out of scope and must remain correct.
3. Gradle exposes no capture source set, capture command, exportSemanticObservations, compileCaptureJava, or verifyCapturePurity task.
4. The live corpus capture/replay and RuntimeLaws differential estate is byte-preserved except for documentation references.
5. Run ./build.sh :interpreter:check :adapter:test :cli:test.
6. Run git diff --check, documentation-link checks, and verify the final visible status differs from the initial status only by this retirement.
7. Report deleted file and line counts, remaining current consumers and live references (both expected: none), the archived recovery record, tests, dependency/publication effects, and unresolved risks.
8. Commit locally with: refactor(capture): retire frozen v1 tooling

Stop rather than inventing a compatibility shim, V2 schema, adapter, generator, or new permanent guard. A future producer capability is demand-driven by a concrete consumer. Do not push.
```

## Expected handback

Return the final a12-dmkits revision, clean-worktree proof, deleted file/nonblank-line totals, proof that no live capture consumer or task remains, exact historical recovery route, full gate result, dependency/publication impact, and any deviation from the prompt. This repository will then remove or replace every current link and ownership claim that points to upstream `CONFORMANCE-CORPUS-SPEC` §15–§15h, including those in `CLAUDE.md`, `docs/README.md`, `docs/PROJECT-DESIGN.md`, `docs/TESTING.md`, `docs/EVIDENCE.md`, and the compact-pipeline contract; retain only the local historical evidence facts their readers still need; delete this temporary handoff; and independently decide its separate reference-semantics V1 retirement.
