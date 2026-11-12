# Interpreter verification of a12-dmkits' interpreter over this repository's corpus

> **Status:** temporary upstream proposal, item IV-P4 of the [interpreter verification checklist](PLAN.md#interpreter-verification-checklist), carried to a12-dmkits by the owner under the [upstream engagement rule](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md#upstream-engagement-rule). Once a12-dmkits accepts it, its durable facts move into a12-dmkits' owners and this file is deleted.

## Request

The owner, as a12-dmkits' owner, asks a12-dmkits to compare its interpreter with kernel 31.3.1 over this repository's retained corpus, request by request and row by row, to fix the interpreter where it disagrees, and to dispose every remaining disagreement by name. A sample of 61 corpus requests found seven disagreeing where Lean agrees with the kernel ([checkpoint](sources/cross-layer-routes.md#src-interpreter-corpus-sample)).

The work starts from a12-dmkits `d2ac4c0397d5629c9934739e55159ff95d0fd152` on `feature/q2` or a successor. The code, the fixes and the roadmap are a12-dmkits'; this repository supplies the contract and checks the handback.

## The contract, by pointer

| Item | Owner of the statement |
|---|---|
| What is compared and which side decides | [IV-P1 `relation`](PLAN.md#interpreter-verification-checklist) and its `lean` sub-bullet |
| What each disagreement becomes | [IV-P1 `dispositions`](PLAN.md#interpreter-verification-checklist) |
| The corpus | [IV-P2 `corpus`](PLAN.md#interpreter-verification-checklist) and its `bindings` sub-bullet |
| The power control | [IV-P3](PLAN.md#interpreter-verification-checklist) |

In short: every request of the corpus runs through `:adapter:probeDifferential` or a route reading it the same way, and every verdict that is not `ok` ends as `fixed`, `declined`, `host-limit`, `instrument` or `kernel-finding`. The kernel decides each disagreement; on the channels Lean's population replay compares, Lean agrees with the kernel, so a disagreement there is an interpreter defect. The pointers decide where this summary is shorter.

## Responsibilities

- **The corpus**: a12-dmkits rebuilds it from a `git archive` of this repository at the revision the hand-off task pins, running `python3 scripts/recapture-kernel-evidence.py prepare --from 30.8.1 --to 31.3.1 --stamp 28.4.0:29.8.0` inside the extract and listing the requests with `requests --to 31.3.1` there; this writes nothing outside the extract and runs no kernel. The 50 runtime requests under `evidence/kernel-31.3.1/captures/` of the same extract and the two power-control requests in a12-dmkits' own evidence complete it.
- **The comparison**: `:adapter:probeDifferential` as [KERNEL-PROBE-SPEC §8](../../a12-rulekit/docs/KERNEL-PROBE-SPEC.md#8-comparing-the-interpreter-over-a-request) states it. A batch route is a12-dmkits' choice, since one Gradle call per request cost about 27 s on 2026-11-12; it must read a request the same way, with the same parser, consistency refusal, JVM setting and `DocumentDifferential`, and give the same verdicts on the 61 sampled requests the checkpoint names.
- **The fixes**: an interpreter defect is fixed red/green, its regression test naming the corpus request and row. The test data generator's gates 1 to 4, Q2-P9's gates 1 to 3 and Q2-P10's gates 1 to 3 keep passing, since their replay runs on the interpreter.
- **This repository** checks the handback: for every disagreement on a replay-compared channel it re-runs Lean's replay on that row, and it records the result as inbound provenance. It writes no a12-dmkits code.

## Public surface

None is required. One command that runs the whole comparison and writes its verdict table is a12-dmkits' to offer.

## Versioned bytes of a result

Per request: its corpus path, and per row and call its verdict, `ok`, `DIFF` with the disagreeing channels, `UNSUPPORTED` with the declined rules, or a refusal before evaluation with its reason. Per verdict that is not `ok`: its disposition, and for `fixed` the regression test, for `declined` and `host-limit` the named refusal or limit, for `kernel-finding` the measurement. The table names the a12-dmkits revision, the kernel and the contract revision the hand-off task pins. The byte layout is a12-dmkits'.

## Acceptance gates

1. **Coverage.** Every corpus request runs at one clean a12-dmkits revision with a verdict per row and call. A request the comparison refuses before evaluation, such as one whose model the kernel's check refuses or one binding custom conditions or field types, is listed with its reason or compared by a route that binds the same on both sides; none is skipped silently.
2. **Disposition.** Every verdict that is not `ok` carries one disposition, and no disagreement stays open.
3. **Power control.** Both KF690 requests agree: the interpreter fails the rule where the kernel does, under full validation and both comparisons.
4. **Regression.** The test data generator's gates 1 to 4, Q2-P9's gates 1 to 3 and Q2-P10's gates 1 to 3 pass at the same revision.

## Handback

The committed a12-dmkits revision and the one command that runs gates 1 to 3, together with the commands of gate 4. The verdict table with its counts, the disposition of each verdict that is not `ok`, and any `kernel-finding` with its kernel measurement, which this repository records as inbound provenance rather than as another outbound entry.

## Excluded

Lean-proved laws as interpreter properties; the channels the comparison names as not compared; the kernel's generated-Java strategy; Lean's side of the power control, which this repository adds after the hand-off.
