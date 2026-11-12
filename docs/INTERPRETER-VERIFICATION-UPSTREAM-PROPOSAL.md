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

- **The corpus**: a12-dmkits rebuilds it from a `git archive` of this repository at the revision the owner's hand-off message pins, extracted outside both checkouts, running `python3 scripts/recapture-kernel-evidence.py prepare --from 30.8.1 --to 31.3.1 --stamp 28.4.0:29.8.0` inside the extract and listing the 620 requests with `python3 scripts/recapture-kernel-evidence.py requests --to 31.3.1` there. This writes only under the extract's `evidence/kernel-31.3.1/local/`, runs no kernel, and warns once about the unstamped `noversion_DM.json`. The 50 tracked requests are every JSON object naming `model` and `rows` under the extract's `evidence/kernel-31.3.1/captures/`. The two IV-P3 requests are in a12-dmkits' own tree. The corpus holds 672 requests, counted at `3eaba59352d75c0739eb729dca9359351ff460b6`; the hand-off message restates the count if its pin changes either evidence tree.
- **The comparison**: `:adapter:probeDifferential`, unchanged in what it compares and in the kernel locale `en_US`, with two instrument changes to what it compares and prints, and the recording the outcome rules below need, all outside the interpreter sources. First, nothing raised while handling one side, call or row stops the request's other sides, calls or rows. Second, every list channel compares with multiplicity, each excess occurrence printing as one line: at `d2ac4c039` `ProbeRequestDifferential.channel` subtracts the other side's set, so a message both sides report, one of them more often, prints nothing. Computed outcomes stay a map. Whether the run uses one Gradle call per request, which cost about 27 s on 2026-11-12, or a batch route reading each request the same way, with the task's JVM settings of assertions off and `-Duser.timezone=UTC`, is a12-dmkits' choice.
- **The interpreter** stays as it is: `git diff d2ac4c039 <revision> -- interpreter/src interpreter/build.gradle shared-regex/src` is empty.
- **This repository** checks the handback and keeps no text from the table beyond codes, paths, outcomes and exception classes, since a kernel-produced text may appear in it.

## The outcome table

The command runs at a committed a12-dmkits revision R and writes the table and its SHA-256 manifest outside the checkout or under a path the checkout ignores; they may be committed afterwards, with `git add -f` for an ignored path, at a revision touching only their directory. The table's header, written last, names R, `git status --short` of the checkout before and after the run (both empty), the kernel version, the kernel locale and the contract revision the hand-off message pins. Its byte layout is a12-dmkits'.

One entry per request, naming its path relative to its root, `lean` for the extract and `dmkits` for a12-dmkits' tree. A request the comparison stops before handling any row is `notRun` with the reason it reaches first, in the comparison's order at `d2ac4c039`:

| Reason | When |
|---|---|
| `refusedRequest` | the probe's parser stops it |
| `bindings` | its `customConditions` or `customFieldTypes` is non-empty |
| `modelRefused` | the consistency oracle raises exactly `KernelRuntimeProbe.Refused` |
| `refusedKernel` | that oracle stops otherwise |
| `refusedInterpreter` | loading the model or the clock stops it |
| `noRows` | it has no rows |

A `refused…` reason carries the fully qualified class of the outermost throwable, or the token `Timeout` or `ProcessExit` when the time limit or a dying run process stopped that stage.

Every other request has, for each of its rows, one outcome for the call `full`, which covers `validateFull` and the computation together, and, when the row names `relevant`, an empty list included, one for the call `partial`. Both sides are run for every row and call whatever the other side does. The outcome is the first that applies:

| Outcome | When | Carries |
|---|---|---|
| `unsupported` | the support audit, `DmInterpreter.validate` on the row's document as at `d2ac4c039`, declines a rule; recorded on both calls of the row, whose kernel sides still run; no other unsupported list is read, and an assertion elsewhere that nothing is declined is a `raise` | the audit's declined rule paths |
| `raise` | a `Throwable` escapes a side's handling of the call; reading the row's document and the support audit belong to the interpreter side of both calls; a side exceeding a per-side time limit the handback states is `Timeout`, and a run process that dies is `ProcessExit` on the side, call and row it was running, the run then resuming in a fresh process at the next side, call or row | the side, `kernel`, `interpreter` or `both`, and for each raising side the fully qualified class of the outermost throwable or the token `Timeout` or `ProcessExit`, without a message |
| `diff` | a compared channel disagrees | each disagreeing line as the comparison prints it, with its channel and side |
| `ok` | otherwise | nothing more |

A rule failure the kernel reports as a message is a message and compares as one. A model that does not declare `en_US` is not stopped before its rows; they end as the rules above meet them.

## Acceptance gates

1. **Coverage.** Each of the 672 requests appears exactly once; a request that is not `notRun` has exactly one outcome per row for `full`, and one for `partial` exactly on the rows naming `relevant`.
2. **Instrument.** Each instrument change has a red/green regression test: a request whose one row raises on the interpreter side reports that row's kernel side and outcomes for its other rows, and a message both sides report, one of them twice, is a `diff`.
3. **Unchanged interpreter.** The interpreter diff above is empty at R and the checkout is clean before and after the run.

## Handback

R and any later revision committing the table, the one command that writes the table and checks gates 1 and 3, the table with its manifest, its counts of call entries per outcome and of requests per `notRun` reason, the time limit, and the test names of gate 2. Any observation that looks like a semantic disagreement goes into the handback as an observation for IV-P6, not as a fix.

## Excluded

Interpreter fixes and dispositions, which IV-P7 asks for after IV-P6; comparing `notRun` requests by another route; the channels the comparison names as not compared; the kernel's generated-Java strategy; Lean-proved laws as interpreter properties.
