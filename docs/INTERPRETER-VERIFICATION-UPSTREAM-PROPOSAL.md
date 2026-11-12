# Interpreter verification baseline over this repository's corpus

> **Status:** temporary upstream proposal, item IV-P4 of the [interpreter verification checklist](PLAN.md#interpreter-verification-checklist), carried to a12-dmkits by the owner under the [upstream engagement rule](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md#upstream-engagement-rule). Once a12-dmkits accepts it, its durable facts move into a12-dmkits' owners and this file is deleted.

## Request

The owner, as a12-dmkits' owner, asks a12-dmkits to record how its interpreter compares with kernel 31.3.1 on every request of this repository's retained corpus, row by row, without changing the interpreter. A sample of 61 corpus requests at an earlier a12-dmkits revision found seven disagreeing ([checkpoint](sources/cross-layer-routes.md#src-interpreter-corpus-sample)). This repository then classifies the disagreements against Lean (IV-P6), and a later request asks for the fixes (IV-P7).

The work starts from a12-dmkits `d2ac4c0397d5629c9934739e55159ff95d0fd152` on `feature/q2` or a successor whose interpreter sources equal it. The code and the table are a12-dmkits'; this repository supplies the contract and checks the handback.

## The contract, by pointer

| Item | Owner of the statement |
|---|---|
| What the comparison compares | [IV-P1 `relation`](PLAN.md#interpreter-verification-checklist) |
| The corpus | [IV-P2 `corpus`](PLAN.md#interpreter-verification-checklist) and [IV-P3](PLAN.md#interpreter-verification-checklist) |
| What this request asks | [IV-P4](PLAN.md#interpreter-verification-checklist) |

The pointers decide where this file is shorter.

## Responsibilities

- **The corpus**: a12-dmkits rebuilds it from a `git archive` of this repository at the revision the hand-off task pins, running `python3 scripts/recapture-kernel-evidence.py prepare --from 30.8.1 --to 31.3.1 --stamp 28.4.0:29.8.0` inside the extract and listing the 620 requests with `python3 scripts/recapture-kernel-evidence.py requests --to 31.3.1` there. This writes only under the extract's `evidence/kernel-31.3.1/local/`, runs no kernel, and warns once about the unstamped `noversion_DM.json`. The 50 tracked requests are every JSON object naming `model` and `rows` under the extract's `evidence/kernel-31.3.1/captures/`. The two IV-P3 requests are in a12-dmkits' own tree. At the pinned revision the corpus holds 672 requests.
- **The comparison**: `:adapter:probeDifferential`, unchanged in what it compares and in the kernel locale `en_US`, with two instrument changes. A raise while evaluating one row, on either side, is recorded for that row and call, and the request's other rows are still compared. Messages are compared with their multiplicity, where `ProbeRequestDifferential.channel` at `d2ac4c039` compares by set difference. Whether the run uses one Gradle call per request, which cost about 27 s on 2026-11-12, or a batch route reading each request the same way is a12-dmkits' choice.
- **The interpreter** stays as it is: `git diff d2ac4c039 <revision> -- interpreter/src shared-regex/src` is empty.
- **This repository** checks the handback and keeps no text from the table beyond codes, paths and outcomes, since a kernel-produced text may appear in it.

## The outcome table

One table for the whole corpus, in a byte layout a12-dmkits chooses, with a header naming the a12-dmkits revision, `git status --short` of the checkout before and after the run (both empty), the kernel version, the kernel locale and the contract revision the hand-off task pins.

One entry per request, naming its path relative to its root, `lean` for the extract and `dmkits` for a12-dmkits' tree. A request the comparison refuses before evaluating any row is `notRun`, with its reason: `bindings` for one binding `customConditions` or `customFieldTypes`, `modelRefused` for a model the comparison's consistency refusal stops, or otherwise the raising side and exception class. A model that does not declare `en_US` is not refused before evaluation; its rows end as the comparison meets them, a kernel raise among them. Every other request has, for each of its rows, one outcome for the call `full` and, when the row names `relevant`, one for the call `partial`:

| Outcome | Carries |
|---|---|
| `ok` | nothing more |
| `diff` | each disagreeing line as the comparison prints it, with its channel and side |
| `unsupported` | the rules the interpreter's support audit declines |
| `raise` | the raising side, `kernel`, `interpreter` or `both`, and each side's exception class, without its message |

## Acceptance gates

1. **Coverage.** Each of the 672 requests appears exactly once; a request that is not `notRun` has exactly one outcome per row for `full`, and one for `partial` exactly on the rows naming `relevant`.
2. **Instrument.** Each instrument change has a red/green regression test: a request with one raising row reports outcomes for its other rows, and a message reported twice by one side and once by the other is a `diff`.
3. **Unchanged interpreter.** The interpreter diff above is empty and the checkout is clean before and after the run.

## Handback

The committed a12-dmkits revision, the one command that writes the table and checks gates 1 and 3, the table bound by a SHA-256 manifest, its counts per outcome and per `notRun` reason, and the test names of gate 2. Any observation that looks like a semantic disagreement goes into the handback as an observation for IV-P6, not as a fix.

## Excluded

Interpreter fixes and dispositions, which IV-P7 asks for after IV-P6; comparing `notRun` requests by another route; the channels the comparison names as not compared; the kernel's generated-Java strategy; Lean-proved laws as interpreter properties.
