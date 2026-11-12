# Interpreter verification of a12-dmkits' interpreter over this repository's corpus

> **Status:** temporary upstream proposal, item IV-P4 of the [interpreter verification checklist](PLAN.md#interpreter-verification-checklist), carried to a12-dmkits by the owner under the [upstream engagement rule](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md#upstream-engagement-rule). Once a12-dmkits accepts it, its durable facts move into a12-dmkits' owners and this file is deleted.

## Request

The owner, as a12-dmkits' owner, asks a12-dmkits to compare its interpreter with kernel 31.3.1 over this repository's retained corpus, request by request and row by row, to fix the interpreter where it disagrees, and to dispose every remaining disagreement by name. A sample of 61 corpus requests at an earlier a12-dmkits revision found seven disagreeing; on the four Lean replayed, Lean matches the kernel on every line it compares ([checkpoint](sources/cross-layer-routes.md#src-interpreter-corpus-sample)).

The work starts from a12-dmkits `d2ac4c0397d5629c9934739e55159ff95d0fd152` on `feature/q2` or a successor. The code, the fixes and the roadmap are a12-dmkits'; this repository supplies the contract and checks the handback.

## The contract, by pointer

| Item | Owner of the statement |
|---|---|
| What is compared and which side decides | [IV-P1 `relation`](PLAN.md#interpreter-verification-checklist) |
| The outcome of a row and call | [IV-P1 `outcomes`](PLAN.md#interpreter-verification-checklist) |
| Where Lean agrees with the kernel | [IV-P1 `lean`](PLAN.md#interpreter-verification-checklist) |
| What each disagreement becomes | [IV-P1 `dispositions`](PLAN.md#interpreter-verification-checklist) |
| The corpus | [IV-P2 `corpus`](PLAN.md#interpreter-verification-checklist), `bindings` and `tracked` |
| The power control | [IV-P3](PLAN.md#interpreter-verification-checklist) |

In short: every request of the corpus runs through `:adapter:probeDifferential` or a route reading it the same way, every row and call ends `ok`, `DIFF`, `UNSUPPORTED`, `fault` or `refused`, and every `DIFF`, `UNSUPPORTED` and one-sided `fault` ends as `fixed`, `declined`, `host-limit`, `kernel-fault`, `instrument` or `kernel-finding`. The kernel decides each disagreement; on a replay-compared verdict Lean agrees with the kernel, so a disagreement there is an interpreter defect. The pointers decide where this summary is shorter.

## Responsibilities

- **The corpus**: a12-dmkits rebuilds it from a `git archive` of this repository at the revision the hand-off task pins, running `python3 scripts/recapture-kernel-evidence.py prepare --from 30.8.1 --to 31.3.1 --stamp 28.4.0:29.8.0` inside the extract and listing the 620 requests with `requests --to 31.3.1` there; this writes nothing outside the extract, runs no kernel, and warns once about the unstamped `noversion_DM.json`. The 50 tracked requests of IV-P2 `tracked` in the same extract and the two power-control requests in a12-dmkits' own evidence complete it.
- **The comparison**: `:adapter:probeDifferential` as [KERNEL-PROBE-SPEC §8](../../a12-rulekit/docs/KERNEL-PROBE-SPEC.md#8-comparing-the-interpreter-over-a-request) states it, with the changes IV-P1 `outcomes` requires: an outcome per row so that one raise does not abort a request, and messages compared with their multiplicity. A batch route is a12-dmkits' choice, since one Gradle call per request cost about 27 s on 2026-11-12; it reads a request as probeDifferential does at the same revision, with the same parser, consistency refusal, JVM setting and `DocumentDifferential`, and gives the same output on the 61 requests the checkpoint samples.
- **The fixes**: an interpreter defect is fixed red/green, its regression test naming the corpus request and row. The test data generator's gates keep passing; where a fix changes the interpreter, the gates' interpreter pin moves to the handed-back revision and the handback says how the pin was verified again.
- **This repository** checks the handback: for every disagreement on a replay-compared verdict it re-runs Lean's replay on that row, and it records the result as inbound provenance. It writes no a12-dmkits code.

## Public surface

The handback needs one command that runs gates 1 to 3 and writes the outcome table. Any further surface is a12-dmkits' choice.

## Versioned bytes of a result

Per request: its corpus path, and per row and call its outcome: `ok`, `DIFF` with the disagreeing channels, `UNSUPPORTED` with the declined rules, `fault` with the raising side and its locus, or `refused` with its reason. Per outcome needing a disposition: the disposition, and for `fixed` the regression test, for `declined` and `host-limit` the named refusal or limit, for `kernel-fault` both loci, for `kernel-finding` the measurement. The table names the a12-dmkits revision with its `git status --short` before and after the run, the kernel, and the contract revision the hand-off task pins. The byte layout is a12-dmkits'.

## Acceptance gates

1. **Coverage.** Every corpus request runs at one clean a12-dmkits revision with an outcome per row and call; a request binding custom conditions or field types or declaring only `de_DE` is compared by a route IV-P2 `bindings` admits or is `refused` with its reason; none is skipped silently.
2. **Disposition.** Every `DIFF`, `UNSUPPORTED` and one-sided `fault` carries one disposition.
3. **Power control.** Every row of both KF690 requests is `ok`.
4. **Regression.** The test data generator's [gates 1 to 4](../../a12-rulekit/docs/TEST-DATA-GENERATOR-SPEC.md#running-gates-14), [contradiction detection's gates 1 to 3](../../a12-rulekit/docs/TEST-DATA-GENERATOR-SPEC.md#contradiction-detection) and [field fillability's gates 1 to 3](../../a12-rulekit/docs/TEST-DATA-GENERATOR-SPEC.md#field-fillability) pass at the same revision, with user-installed Z3.

## Handback

The committed a12-dmkits revision, the one command that runs gates 1 to 3 and the commands of gate 4. The outcome table with its counts, the disposition of each outcome needing one, any moved interpreter pin, and any `kernel-finding` with its kernel measurement, which this repository records as inbound provenance rather than as another outbound entry.

## Excluded

Lean-proved laws as interpreter properties; the channels the comparison names as not compared; the kernel's generated-Java strategy; Lean's side of the power control, which this repository adds after the hand-off.
