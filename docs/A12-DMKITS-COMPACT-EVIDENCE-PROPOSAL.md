# a12-dmkits compact semantic-observation export

> Status: cross-project handoff proposal, pending a12-dmkits acceptance. Audited against clean a12-dmkits revision `979c9524745e06f0c84d980b1846ff5d251ef3e0` on 2026-07-17. This document is temporary: after the handback is accepted, durable results move into [`EVIDENCE.md`](EVIDENCE.md), [`ARCHITECTURE.md`](ARCHITECTURE.md), and the upstream [`CONFORMANCE-CORPUS-SPEC.md`](../../a12-rulekit/docs/CONFORMANCE-CORPUS-SPEC.md), then this proposal is deleted.

## Decision

Add one small adapter-internal, post-capture exporter for the already retained and qualified `string-direct-cascade-v1` packet. It must emit the exact compact bundle consumed by [`ObservationBundle.lean`](../A12Kernel/Evidence/ObservationBundle.lean) and [`StringCascadeProjection.lean`](../A12Kernel/Evidence/StringCascadeProjection.lean).

This is not a new capture system, not `a12-dmkits-capture-capabilities-v2`, and not a new operation payload. It reuses the settled V1 packet verifier and policy engine, projects one closed family, writes one canonical JSON file, and stops. It must not add a runner, capability registry, packet schema, report schema, receipt tree, plugin mechanism, family registry, validation-message implementation, or second mutation program.

The immediate exporter does not by itself replace the live capture harness: it projects an existing packet and cannot capture a future semantic question. Retirement of current-main V1 implementation code is therefore a separate owner-approved lifecycle decision, described below.

## Why this is the scalable boundary

The complete a12-dmkits capture estate is valuable once: it establishes runner identity, consumed input, legality, closure, capabilities, byte integrity, qualification, and deterministic capture. Rebuilding those assurances in Lean made the direct-cascade evidence path larger than the semantics it protects.

The settled split is:

1. a12-dmkits verifies the raw packet and qualification once.
2. a12-dmkits emits a producer-certified semantic projection whose source identities point back to the retained raw packet and qualification.
3. Lean validates only the small closed bundle, decodes its typed family, and compares it with the real Lean evaluator.
4. The raw packet remains immutable and available for audit, but ordinary Lean replay never parses its runner or receipt machinery again.

The local consumer is already executable under synthetic contract tests and measures 611 nonblank lines in total. Its replacement target is the existing 2,179-nonblank-line direct-cascade binder stack, with a required net deletion of at least 1,500 lines after the producer bytes arrive.

The upstream capture estate currently measures roughly 5,348 nonblank production lines, 2,422 capture-test lines, and 831 mutation-script lines. That investment should remain one settled transporter, not be duplicated into parallel full V1 and V2 stacks.

## Frozen inputs

The exporter accepts only the already retained direct-cascade evidence unit:

| Identity | Required value |
|---|---|
| Kernel behavior | `30.8.1` |
| Scenario set | `string-direct-cascade-v1`, version `1` |
| Request SHA-256 | `4c5d4911ecacde819618b3b921b0bd30aa34b514cb0bbf3f0d2b735f21a0fd43` |
| Model SHA-256 | `3d21add02d259a8d1ad2e14475582513aec2f4e60176f1c02c81d40de88a895d` |
| Frozen capability | `a12-dmkits-capture-capabilities-v1`, SHA-256 `b87d381e7f43446bc886292766e34beab72ca3ec179be5f0f614975e66d603ca` |
| Packet receipt | `7e38744283cf17f7f57fe0bce342084a8e2896fb99aa60c2a9f4fb52e185dc17` |
| Qualification policy | `kernel-route-confirmed-v1` |
| Qualification receipt | `f581d82d7eb04929b38d4663bbb48a28f09c7399273cd5974cd59e739eca5d64` |
| Accepted capture revision | `c992afd62e4fa6148733a5538a3248c30fce60bf` |

The complete bytes are retained under [`evidence/kernel-30.8.1/captures/string-direct-cascade-v1/`](../evidence/kernel-30.8.1/captures/string-direct-cascade-v1/). The exporter must consume them read-only and must never rewrite, copy over, or “upgrade” them.

## One command

Add a separate entry point such as `CompactObservationTool` and one Gradle task:

```sh
./build.sh :adapter:exportSemanticObservations \
  -PsemanticEvidence.packet=<packet-dir> \
  -PsemanticEvidence.packetReceiptSha256=7e38744283cf17f7f57fe0bce342084a8e2896fb99aa60c2a9f4fb52e185dc17 \
  -PsemanticEvidence.qualification=<qualification-dir> \
  -PsemanticEvidence.qualificationReceiptSha256=f581d82d7eb04929b38d4663bbb48a28f09c7399273cd5974cd59e739eca5d64 \
  -PsemanticEvidence.output=<new-or-empty-dir>
```

The exact task and class names may change if a12-dmkits has a clearer local convention, but the boundary may not change:

- the exporter is separate from `CaptureTool`;
- it is not advertised by or added to `a12-dmkits-capture-capabilities-v1`;
- it reuses the existing capture source set and established `VerifiedPacket`, `PolicyEngine`, strict/canonical JSON, digest, source-state, and output-safety mechanisms;
- prefer a new `capture.export` package and leave existing V1 decoder, runner, registry, mapper, policy, and CLI classes unchanged;
- it requires a clean committed exporter revision;
- it reuses `OutputDirs` to require a new or empty caller-owned directory, writes exactly `<output-dir>/semantic-observations.json` as UTF-8 with final newline and at most 256 KiB, and prints that file's SHA-256;
- two runs from the same clean revision and inputs are byte-identical;
- it creates no receipt directory or signature layer for this one file.

The output is named `semantic-observations.json` for the handback and is intended to land at the retained capture root beside `packet/` and `qualification/`. Therefore the source paths inside it are exactly `packet/RECEIPT.json` and `qualification/RECEIPT.json`, relative to its final retained location.

## Exact compact wire contract

The outer contract is closed and operation-neutral:

```json
{
  "schemaVersion": 1,
  "kernelVersion": "30.8.1",
  "families": [
    {
      "id": "string-direct-cascade-v1",
      "projectionId": "string-direct-cascade-semantic-v1",
      "projectionVersion": 1,
      "source": {
        "producer": "a12-dmkits",
        "revision": "<clean 40-character lowercase exporter revision>",
        "rawCapture": {
          "path": "packet/RECEIPT.json",
          "sha256": "7e38744283cf17f7f57fe0bce342084a8e2896fb99aa60c2a9f4fb52e185dc17"
        },
        "qualification": {
          "policyId": "kernel-route-confirmed-v1",
          "receipt": {
            "path": "qualification/RECEIPT.json",
            "sha256": "f581d82d7eb04929b38d4663bbb48a28f09c7399273cd5974cd59e739eca5d64"
          }
        }
      },
      "cases": [
        {
          "id": "source-abc-mid-old",
          "input": {
            "source": "ABC",
            "priorMid": "OLD",
            "priorOut": "STALE"
          },
          "observed": {
            "clean": [
              {
                "target": "mid",
                "value": "ABC"
              },
              {
                "target": "out",
                "value": "ABC-X"
              }
            ],
            "changed": [
              {
                "target": "mid",
                "value": "ABC"
              },
              {
                "target": "out",
                "value": "ABC-X"
              }
            ],
            "errors": [],
            "cleared": [],
            "applied": [
              {
                "target": "mid",
                "value": "ABC"
              },
              {
                "target": "out",
                "value": "ABC-X"
              }
            ]
          }
        }
      ]
    }
  ]
}
```

The example shows one case only; the real output contains exactly the five cases below in the shown order. Unknown members are forbidden at every level. JSON `null` is the only no-value encoding. Empty stored strings are forbidden. Observation arrays preserve multiplicity and use canonical semantic target order: producer `mid` before consumer `out`. Entries for the same target retain their original relative order.

`source.revision` is the clean a12-dmkits exporter commit, not the historical packet-producing revision. The two receipt identities separately anchor the historical raw capture and qualification.

## Exact family matrix

| Case, in order | Input `source / priorMid / priorOut` | `clean` | `changed` | `errors` | `cleared` | `applied mid / out` |
|---|---|---|---|---|---|---|
| `source-abc-mid-old` | `ABC / OLD / STALE` | `mid=ABC`, `out=ABC-X` | `mid=ABC`, `out=ABC-X` | none | none | `ABC / ABC-X` |
| `source-abc-mid-abc` | `ABC / ABC / STALE` | `mid=ABC`, `out=ABC-X` | `out=ABC-X` | none | none | `ABC / ABC-X` |
| `source-absent-mid-old` | `null / OLD / STALE` | `out=-X` | `out=-X` | none | `mid` | `null / -X` |
| `source-absent-mid-absent` | `null / null / STALE` | `out=-X` | `out=-X` | none | none | `null / -X` |
| `source-abcd-mid-old` | `ABCD / OLD / STALE` | none | none | `mid: attempted=ABCD, cause=tooLong` | `out` | `null / null` |

These values are acceptance expectations derived from the retained qualified packet; they are never inserted into a capture request or used to choose observations.

## Exact raw-to-compact mapping

The exporter derives input from these exact optional field placements, all with reps `[1, 1]`; absence means JSON `null`:

| Compact input | Request placement |
|---|---|
| `source` | `/Cascade/Source` |
| `priorMid` | `/Cascade/Mid` |
| `priorOut` | `/Cascade/Out` |

Raw target identity is closed:

| Compact target | Raw target or probe | Declared computation |
|---|---|---|
| `mid` | `/Cascade[1]/Mid` | `/Cascade/MidComputation` |
| `out` | `/Cascade[1]/Out` | `/Cascade/OutComputation` |

Each projected channel has one exact source and compact shape:

| Raw channel | Required granularity | Compact member and entry shape | Value rule |
|---|---|---|---|
| `withoutErrors` | `all-computed-clean` | `clean`: `{"target": <mid-or-out>, "value": <string>}` | typed value is available kind `STRING`; rendered value is available and equal |
| `changedSubset` | `delta-vs-input` | `changed`: `{"target": <mid-or-out>, "value": <string>}` | typed value is available kind `STRING`; rendered value is available and equal |
| `withErrors` | `errored-instances` | `errors`: `{"target": <mid-or-out>, "attempted": <string>, "cause": "tooLong"}` | attempted typed value is available kind `STRING` and equals rendered text; the complete retained cause tuple maps to `tooLong` |
| `cleared` | `input-filled-only` | `cleared`: `<mid-or-out>` | exact raw target and declared computation must agree with the target table |
| `formalErrorsInOperands` | `operand-formal-errors` | omitted from compact observation | raw channel must be available and empty |
| `appliedState` | `requested-probes` | `applied`: `{"target": <mid-or-out>, "value": <string-or-null>}` | `presentValue` uses the available typed `STRING`; `absent` and `presentEmpty` become `null` |

## Producer checks and projection

The production command must:

1. Load the packet through `VerifiedPacket.load` with the exact out-of-band packet receipt digest.
2. Rely on that verified exact packet identity for its already checked kernel, capability, closure, legality, and cross-artifact relations. Inspect the copied request only to require the exact scenario, model, case order, operation, placement, and probe shape needed by this family; do not build a second packet or capability validator.
3. Verify the qualification directory's receipt tree against the exact out-of-band qualification digest. Because this proposal pins one already retained qualification tree, do not build a general report-verification framework.
4. Reapply `kernel-route-confirmed-v1` through the existing `PolicyEngine` and require `satisfied`, with all five Groovy-versus-Java comparisons equal under `compute-projection-kernel-route-v1`.
5. Only after route agreement, use `kernel-groovy-dynamic` as the deterministic anchor observation.
6. Derive `input` from the packet's copied request placements. Do not hand-code input values in production.
7. Project `withoutErrors` to `clean`, `changedSubset` to `changed`, `withErrors` to `errors`, `cleared` to `cleared`, and `appliedState` to value-only `applied`.
8. Require every projected channel to be available with its exact V1 granularity. Require `formalErrorsInOperands` to be available and empty; this family omits it only because every retained case is empty.
9. Require target and computation paths to be the exact `Mid`/`Out` paths. Require typed `STRING` and rendered text to agree wherever both are available. Do not silently prefer one disagreement.
10. Map only the exact retained cause tuple `stringZuLang / VALUE_ERROR / /Cascade[1]/Mid` to `tooLong`; reject every other code, type, pointer, missing field, or unavailable cause.
11. Map applied `presentValue` to its nonempty String and both `absent` and `presentEmpty` to `null`. Reject unknown states and kinds. The stronger absent-versus-present-empty distinction remains in the immutable raw packet and is deliberately outside this value-only projection.
12. Normalize each observation list by stable target rank `mid`, then `out`; do not sort by value, deduplicate, convert to a map, or collapse repeated entries.

The a12-dmkits interpreter observation is not exported. It remains triangulation in the raw unit and never becomes the oracle.

## Minimal implementation and line budget

Reuse established code. Do not reimplement packet receipt checking, packet relations, source-state probing, policy evaluation, strict JSON, canonical JSON, hashing, or output safety.

For this delivery, excluding module comments and inline JSON fixture data:

- exporter production code: at most 300 nonblank lines;
- focused tests: at most 220 nonblank lines;
- Gradle/task glue: at most 30 nonblank lines;
- complete new implementation: at most 550 nonblank lines.

If the implementation misses a limit, stop and identify which settled producer responsibility was accidentally duplicated. Do not meet the limit through compressed unreadable code.

Do not create a generic family registry or projector SPI for one family. A second real family is the earliest point at which shared extraction may be justified.

No dependency, published module, interpreter API, dmtool-release surface, kernel version, or kernel-linkage change is part of this proposal. Report and stop if implementation unexpectedly requires one.

## Red/green and mutation sensitivity

Start with a failing exact-output test using an injected fixed exporter revision, then implement the minimum production path.

The focused committed guards are:

1. Exact canonical compact output for the five-case typed fixture.
2. Two runs with the same injected source identity produce identical bytes.
3. The frozen V1 capabilities golden remains SHA-256 `b87d381e7f43446bc886292766e34beab72ca3ec179be5f0f614975e66d603ca`.
4. A changed request placement or input matrix refuses.
5. A non-satisfied route comparison refuses before anchor projection.
6. Dropping or changing the attempted value or cause refuses or changes the exact golden as predicted.
7. Changing an applied state/value refuses or changes only the predicted case.
8. Reversing incidental raw Mid/Out order still emits canonical Mid-before-Out order.
9. Duplicating a raw observation preserves the duplicate and therefore changes the compact output; it must never disappear through a set or map.
10. Wrong packet or qualification receipt digests, dirty exporter state, a nonempty output directory, and output over 256 KiB refuse.

Use the smallest typed or JSON fixture that exercises the projector. Do not copy the complete retained packet into a12-dmkits merely to make a permanent integration fixture, and do not create another broad mutation receipt. The final handback run against the real retained packet is the end-to-end acceptance.

## Required handback

Return:

- clean a12-dmkits exporter revision and unchanged worktree status;
- the exact command used against the read-only retained packet and qualification;
- confirmation that `CaptureTool`, V1 schemas, V1 capabilities bytes, runners, policies, and frozen golden were unchanged;
- the output filename, byte count, SHA-256, and exact `semantic-observations.json` bytes;
- the second-run SHA-256 and byte-equality result;
- focused-test and full-master-gate outcomes;
- measured production/test/Gradle nonblank lines;
- explicit confirmation that no capture-capabilities, packet, observation, projection, policy, or operation V2 identity was minted;
- any remaining limitation or divergence, without broadening the exporter to solve it.

Write the handback only into an ignored a12-dmkits directory. Do not write into this repository; the user will ferry the bytes and report.

## Lean acceptance and deletion gate

After ferrying, a12-kernel-lean will:

1. independently hash the returned file, add the returned exporter revision as an exact `StringCascadeProjection` constant with a rejection test, and pin the returned file SHA-256 through the existing digest mechanism before decoding;
2. load it with the generic bounded reader;
3. decode all five cases with the typed direct-cascade family;
4. require zero mismatches from the real Lean evaluator;
5. run the old complete binder and new compact lane together once;
6. relocate the two generic artifact-tree guards;
7. switch `lake test` to the compact lane and delete the old cascade binder, schema, replay, receipt decoder, and replaced tests;
8. retain the raw packet and sidecars byte-for-byte;
9. require at least 1,500 net nonblank lines deleted and a real semantic mutation still caught.

Old and new lanes may coexist only for this migration gate.

## Capture-contract V1 lifecycle — later decision, not this delivery

The exporter implementation and handback must not edit upstream §15g, delete or dispatch V1 code, mint V2, or make a support-policy change. This section records the decision gate for a later, separately authorized delivery. That later delivery starts only after a fresh consumer inventory and explicit owner direction.

The compact exporter is not grounds for deleting live capture: it cannot answer a new kernel question. Current-main V1 retirement becomes valid only in one of two situations:

1. a real successor capture path exists and has completed a clean consumer-accepted capture; or
2. the owner explicitly chooses a demand-triggered model in which current main offers no live capture and historical V1 execution is performed from a pinned checkout.

Before either retirement:

- inventory every live V1 caller, CI job, script, fixture, and external consumer;
- migrate each live consumer or record why it still needs same-HEAD V1 execution;
- preserve the accepted raw and qualification bytes, receipt identities, frozen capability bytes, mutation receipts, freeze/acceptance record, exact toolchain, and reproduction commands;
- create or name a permanent historical revision or tag containing the runnable V1 implementation;
- rehash all immutable retained bytes unchanged;
- run a clean successor capture if a successor is the reason for retirement;
- obtain explicit owner approval.

If no supported consumer requires same-HEAD V1 service, the recommended lifecycle is:

> V1 remains historically reproducible at its pinned revision; current main serves the successor only.

That policy permits current-main deletion of the V1 runner, mapper, commands, schemas, compatibility dispatch, and mutation machinery. Keep only the smallest checksum or metadata guard justified by a real current consumer. Git history, a tag, the live upstream spec, and the retained external evidence preserve the immutable identity; “immutable” does not mean “all implementation code must remain on main forever.”

This requires an explicit correction to the current upstream [`§15g`](../../a12-rulekit/docs/CONFORMANCE-CORPUS-SPEC.md#15g-the-parked-v2-lane-a12-dmkits-capture-capabilities-v2--the-start-here-record) promise that V1 requests are served from current main forever. Do not silently delete code while leaving that support promise in force.

If a real consumer does require V1 and a successor from the same HEAD, retain version dispatch only for that named need and measure its maintenance cost. Do not assume this exceptional case in advance.

This lifecycle discussion concerns a12-dmkits capture-contract V1 only. It does not authorize deletion or rewriting of this repository's frozen reference-semantics v1 manifests, suites, Rust qualification history, or retained raw evidence.

## Later families

The next likely observation need is validation-message output, but it remains outlook only. Do not implement it or mint capture V2 in this delivery.

After direct-cascade migration proves the compact boundary, each later semantic family should add only:

- one expectation-free scenario question;
- one producer-side typed projection;
- one compact family record;
- one Lean typed decoder and replay;
- focused separating mutations.

If a later question requires a new runner channel or raw operation payload, that is the point to consider a capture successor. It is not a reason to predict and build every future kernel surface now.
