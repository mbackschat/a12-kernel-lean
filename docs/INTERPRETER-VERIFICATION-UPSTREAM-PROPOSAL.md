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
- **The comparison**: `:adapter:probeDifferential`, unchanged in what it compares and in the kernel locale `en_US`, with two instrument changes to what it compares and prints, and the recording the outcome rules below need, all outside the interpreter sources. First, nothing that fails in one call stops the row's other call, the call's other side, or the request's other rows. Second, every list channel compares with multiplicity, each excess occurrence printing as one line: at `d2ac4c039` `ProbeRequestDifferential.channel` subtracts the other side's set, so a message both sides report, one of them more often, prints nothing. Computed outcomes stay a map. Whether the run uses one Gradle call per request, which cost about 27 s on 2026-11-12, or a batch route reading each request the same way, with the task's JVM settings of assertions off and `-Duser.timezone=UTC`, is a12-dmkits' choice.
- **The interpreter** stays as it is: `git diff d2ac4c039 <revision> -- interpreter/src interpreter/build.gradle shared-regex/src` is empty.
- **This repository** checks the handback and keeps no text from the table beyond codes, paths, outcomes and exception classes, since a kernel-produced text may appear in it.

## The outcome table

The command runs at a committed a12-dmkits revision R and writes the table and its SHA-256 manifest outside the checkout or under a path the checkout ignores; they may be committed afterwards, with `git add -f` for an ignored path, at a revision touching only their directory. The table's header, written last, names R, `git status --short` of the checkout before and after the run (both empty), the kernel version, the kernel locale and the contract revision the hand-off message pins. Its byte layout is a12-dmkits'.

One entry per request, naming its path relative to its root, `lean` for the extract and `dmkits` for a12-dmkits' tree. A request the comparison stops before handling any row is `notRun` with the first of these that applies, in this order: `bindings` when its `customConditions` or `customFieldTypes` is non-empty, `modelRefused` when the consistency oracle raises `KernelRuntimeProbe.Refused`, `refused` when any other stage before the rows stops it, with the stage, in tokens the handback lists, and the fully qualified class of the outermost throwable, and `noRows` when it has no rows.

Every other request has, for each of its rows, named by the row's `name`, one outcome for the call `full`, which covers `validateFull` and the computation together, and, when the row names `relevant`, an empty list included, one for the call `partial`:

| Outcome | When | Carries |
|---|---|---|
| `unsupported` | the support audit, `DmInterpreter.validate` on the row's document as at `d2ac4c039`, returns a non-empty `unsupported` list; no side of the row runs, as at `d2ac4c039`; `DocumentDifferential`'s own assertions that a call declines nothing stay, and their failure is an interpreter-side `raise` | each entry's `rulePath` |
| `raise` | a side's handling of the call, or the audit for the interpreter side, does not complete, or comparing the two results does not | each such side, `kernel`, `interpreter` or `comparison`, with the fully qualified class of the outermost throwable, or a token naming why the run could not record it |
| `diff` | a compared channel disagrees | each disagreeing line as the comparison prints it, with its channel and side |
| `ok` | otherwise | nothing more |

When the audit raises, every call of the row is `raise` with `interpreter` and the audit's throwable, the interpreter calls are not attempted, and each kernel side still runs and adds `kernel` if it raises. Each entry names its row and its call, `full` or `partial`. How the run bounds time and survives a failing or dying process is a12-dmkits' choice, stated in the handback with its tokens; it decides only which `raise` entries carry a token, never whether a row or call has an entry. A rule failure the kernel reports as a message is a message and compares as one. A model that does not declare `en_US` is not stopped before its rows.

## Acceptance gates

1. **Coverage.** Each of the 672 requests appears exactly once; a request that is not `notRun` has exactly one outcome per row for `full`, and one for `partial` exactly on the rows naming `relevant`.
2. **Instrument.** Each instrument change has a red/green regression test: a request whose one row raises only on the interpreter side of `full` records that call as `raise` on the interpreter side alone and has outcomes for its other rows, and a message both sides report, one of them twice, is a `diff`.
3. **Unchanged interpreter.** The interpreter diff above is empty at R and the checkout is clean before and after the run.

## Handback

R and any later revision committing the table, the one command that writes the table and checks gates 1 and 3, the table with its manifest, its counts of call entries per outcome and of requests per `notRun` reason, the run's time and process handling with its tokens, and the test names of gate 2. Any observation that looks like a semantic disagreement goes into the handback as an observation for IV-P6, not as a fix.

## Excluded

Interpreter fixes and dispositions, which IV-P7 asks for after IV-P6; comparing `notRun` requests by another route; the channels the comparison names as not compared; the kernel's generated-Java strategy; Lean-proved laws as interpreter properties.
