# a12-dmkits specification synchronization ledger

This is the live outbound reconciliation queue for changes to the project-owned language-neutral semantics under [`../spec/`](../spec/). It owns open `SPEC-` corrections and `EXP-` observation requests without becoming a second semantic specification. Terminal receipts leave this queue after their useful live facts are preserved in the canonical spec, source or gap owner.

The terminal receipts retired on 2026-10-10 remain in [the ledger at `e2bc04e5`](https://github.com/mbackschat/a12-kernel-lean/blob/e2bc04e5cefbcce7b380a1c8f0687b5c2cd4a730/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md), under their stable entry anchors. Earlier deleted receipts remain in [the historical ledger](https://github.com/mbackschat/a12-kernel-lean/blob/a050f1506bedaab7078d4121ad2b3378c2a43052/docs/archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md) and [the accepted receipts through 2026-09-24](https://github.com/mbackschat/a12-kernel-lean/blob/a050f1506bedaab7078d4121ad2b3378c2a43052/docs/archived/A12-DMKITS-SPEC-SYNC-LEDGER-ACCEPTED-THROUGH-2026-09-24.md) at `a050f150`. Recover any exact receipt with `git show <revision>:<path>` and find its stable ID; retired IDs are never reused.

## Ledger contract

Every commit that corrects, narrows, or extends kernel behavior in `spec/` and still needs a12-dmkits reconciliation must add or update an entry here in the same change. The spec clause owns the complete semantic account; an entry links to that clause and records only the transport facts needed by a12-dmkits.

An inbound correction whose exact source revision is already committed and reviewed in a12-dmkits does not create a new outbound entry. Record that revision and its evidence route in [`SOURCES.md`](SOURCES.md). If the inbound result answers an existing `pending` or `handed-off` entry, update that same entry instead.

Pure spelling, formatting, link, and non-semantic navigation edits do not enter the ledger. One entry may group several clauses only when they express one coherent behavioral correction with one upstream acceptance decision.

Each entry has a stable `SPEC-YYYY-MM-DD-NN` or `EXP-YYYY-MM-DD-NN` ID that is unique across the live queue and its retired Git history. IDs are never reused. An entry records its exact status, canonical clause or experiment question, concise delta, evidence basis and kernel version, expected reconciliation surfaces, acceptance condition, local introducing revision, and reviewed a12-dmkits revision and disposition when terminal. A later correction creates a new entry with `Supersedes`; it never rewrites a terminal receipt.

Statuses are exactly `pending`, `handed-off`, `accepted`, `answered`, `resolved`, `rejected`, or `superseded`. `accepted` requires review of an exact a12-dmkits revision against the entry's acceptance condition. `resolved` is only for an `EXP-` closed locally without an upstream observation. **`answered` is for an entry the peer engaged whose outcome is neither acceptance nor refutation**, and it exists because four entries reached exactly that state and the six-status list could not express any of them: an `EXP-` closed *by* an upstream observation rather than locally, and a `SPEC-` where the peer could not corroborate in the way its own acceptance condition anticipated, or found reconciliation unnecessary, or stated a free choice not to carry it. An `answered` entry owes nothing in either direction and carries a `disposition` or `answered` row saying which of those it was; do not relabel one as `accepted`, which asserts an acceptance review that never happened. An inconclusive handback remains `handed-off`. Contrary kernel evidence prevents acceptance and requires the local semantic account to be corrected before the entry is rejected or superseded.

The user transfers pending entries. Treat the entire `../a12-rulekit/` checkout as read-only. Reconciliation here means inspecting an exact committed a12-dmkits revision and recording the reviewed outcome in the existing entry. Do not create a second feedback ledger. A `dmtool-release` instrument defect goes to the a12-dmkits session directly, or to a dated feedback note under the user's exchange directory when no such session is reachable, as defined by [`TESTING.md`](TESTING.md#structured-dmtool-probes-and-feedback); neither belongs in this ledger.

The introducing revision cannot name itself inside the same commit. Until handoff, `introducing commit` means the first commit containing the stable entry ID; resolve it with:

```sh
git log --reverse -S 'SPEC-YYYY-MM-DD-NN' --format='%H' -- docs/A12-DMKITS-SPEC-SYNC-LEDGER.md | head -n 1
```

An exact a12-dmkits revision must resolve when its handback is reviewed. If later upstream history rewriting makes it unreachable, retain the historical citation, do not invent a replacement mapping, and re-discharge any reused claim against the maintained owner at the then-current reviewed revision. The measured boundary and claim limit are the older receipt file's `#receipt-continuity` section at that revision.

## Entry kinds and routing

- **`SPEC-…`** records a locally originated semantic correction that still needs a12-dmkits reconciliation. A locally measured static-legality finding is a `SPEC-`, not an experiment request.
- **`EXP-…`** requests one specific kernel-runtime observation only after the available local source, static-check, retained-evidence, and runtime-probe routes have been checked and shown unable to settle it. State the exact input, competing accounts, prediction under each account, negative result, and route limit. If no input distinguishes the accounts, the entry is not ready.
- **The user carries pending entries to a12-dmkits.** Prepare the stable ID and its checkpoint anchor in the same change. Do not send entries to peer sessions automatically; reconcile the exact committed handback when the user supplies it, following [the repository authority](../CLAUDE.md#%EF%B8%8F-hard-rule--request-a12-dmkits-improvements-upstream-never-patch-a-copied-harness).
- **The routing test is one question: is kernel behavior in question, or only this project's ability to observe it?** A `dmtool-release` command, schema, diagnostic, exit, or artifact defect is instrument feedback rather than kernel semantics: it goes to the a12-dmkits session directly or, when none is reachable, to a dated feedback note in the user's `~/Downloads` exchange directory per [`TESTING.md`](TESTING.md#structured-dmtool-probes-and-feedback), and **never to this ledger**, because a note has no acceptance condition or reviewed-revision receipt. A missing tool capability that blocks a measurement is such a note, while the semantic question it blocks is an entry. A cross-project capability or retirement request follows the [upstream engagement rule](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md#upstream-engagement-rule).

[`SOURCES.md`](SOURCES.md#engine-routing-rule--pick-the-layer-by-the-question-not-by-habit) owns the current observation-route inventory and [`TESTING.md`](TESTING.md#the-kernel-runtime-probe-route) owns its method. Every claim leaving this repository must also satisfy the discharge rule in [`../CLAUDE.md`](../CLAUDE.md#%EF%B8%8F-hard-rule--discharge-a-claim-before-stating-it-or-flag-it-and-surface-it).

## Current queue

<a id="spec-2026-10-24-11"></a>
### SPEC-2026-10-24-11 — A parallel rule reaching an unregistered custom condition keeps no earlier joined-row firing and ends

- `status`: pending
- `canonical`: [spec/11](../spec/11-messages-and-custom.md), the parallel-leaf and registration-lookup bullets.
- `delta`: Replaces the unmeasured note: a parallel rule that reaches an unregistered name keeps no message of a joined row that fired before the reaching row, evaluates no later joined row, and below a repeatable outer row no later outer row. Adds that an `Or` arm reading no joined field is refused beside the pair whatever it holds, while an arm pairing a joined read with the custom condition is admitted.
- `basis`: The [parallel reach checkpoint](sources/model-structure-and-declaration-probes.md#src-k22-parallel-custom-reach), seven documents and six static rows, measured locally 2026-10-24, Kernel 30.8.1, at the measurement pin `08b0d6499`, replayed by `lake exe a12-kernel-replay` and the rule-check projection.
- `acceptance`: Reconcile the `keep`, `reg2` and `mid` outcomes of `P4`, `P7`, `Q1` and `Q7` and the six static verdicts. The partial rows are retained uncompared; do not claim partial behavior from them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-24-10"></a>
### SPEC-2026-10-24-10 — Uniqueness, count and custom-condition leaves beside a joined group target, and joined declarations over different partner groups

- `status`: pending
- `canonical`: [spec/07](../spec/07-repetition-and-iteration.md), the group error-entity bullet; [spec/09](../spec/09-computations.md), the alternatives bullet.
- `delta`: Adds that beside a join a group target admits `FieldValuesNotUnique` over the pair, a starred partner group or two error-side fields, `NumberOfDifferentValues` over the pair and a custom condition, the uniqueness leaves firing at the line's first part where their field forms fire; that two joined declarations into one target over different partner groups concatenate; and that the ended scan holds for Date and Enumeration joined targets.
- `basis`: The [joined group-target checkpoint](sources/model-structure-and-declaration-probes.md#src-k22-joined-group-target-leaves), nine rules over four documents and ten computations over one, measured locally 2026-10-24, Kernel 30.8.1, at the measurement pin `08b0d6499`, replayed by `lake exe a12-kernel-replay`.
- `acceptance`: Reconcile the `k22g` firings except `g4` and `g5`, and the `k22z` outcomes. The runtime of a custom condition on a joined group target is unsettled; do not claim it.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-24-09"></a>
### SPEC-2026-10-24-09 — Separate declarations into a key-joined target, ordinary parallel leaves on an unmatched side, and partial calls over them

- `status`: pending
- `canonical`: [spec/09](../spec/09-computations.md), the alternatives bullet and the joined-precondition bullet; [spec/07](../spec/07-repetition-and-iteration.md), the unmatched-side bullet and the partial-validation note.
- `delta`: Adds that into a key-joined target a separate declaration reading no partner field ends the combined table's scan with the target cleared wherever it is reached, whatever its preconditions, leaving later alternatives unreached and poisoning no dependent, while one declaration mixing joined and ordinary alternatives and two joined declarations select normally; that `GroupFilled` of an enclosing group holds at a key-only target row without a partner; that `Length`, text comparison, value-list membership, a filled-field count and the side's own key read an unmatched side as empty, an unmatched error side firing at `-5` when its group has no free row; and that a partial call fires an ordinary parallel leaf only for joined rows it covers on both sides.
- `basis`: The [cross-declaration checkpoint](sources/model-structure-and-declaration-probes.md#src-k22-cross-declaration), two runs over eleven rows measured locally 2026-10-24, Kernel 30.8.1, at the measurement pin `08b0d6499`, replayed by `lake exe a12-kernel-replay` and the [partial leaf locks](../A12Kernel/Reference/Dm/ParallelLeafPartialLocks.lean).
- `acceptance`: Reconcile the `k22x` and `k22y` outcomes and the five partial scopes. The mechanism ending the scan and a partial call over a joined computation's generated rule are unmeasured; do not claim them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-24-08"></a>
### SPEC-2026-10-24-08 — Enumeration and invalid-row joined targets, atoms without a joined form, a guard-only join and Number keys in a joined computation

- `status`: pending
- `canonical`: [spec/09](../spec/09-computations.md), the String or Date joined-target bullet and the bullet after it.
- `delta`: Adds that a joined Enumeration target copies the partner's token; that String, Date and Enumeration targets clear every instance at a repeated or empty key and clear a target row beyond capacity alone; that a literal-keyed read, a filtered starred `Sum`, `DayFromDate(Today)` and a target-row `NumberOfFilledFields` keep their target-row value inside a joined operation beside an unmatched partner reading empty; that a precondition keyed by a partner field joins by itself; and that Number keys of differing maximum fractional digits join a computation numerically.
- `basis`: The [joined-computation checkpoint](sources/model-structure-and-declaration-probes.md#src-k22-joined-computations), ten computations over three documents measured locally 2026-10-24, Kernel 30.8.1, at the measurement pin `08b0d6499`, replayed by `lake exe a12-kernel-replay`.
- `acceptance`: Reconcile the 90 computation and generated-rule instances of the `k22j` run. A Number-keyed computation with differing minimum fractional digits, a Boolean or DateRange joined target and a guard keyed by a partner field beside a joined operation are unmeasured here; do not claim them.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

The four entries above are pending. The ten terminal receipts accepted at the [October 24a handback](sources/inbound-handbacks.md#src-inbound-2026-10-24a) remain in [the ledger at `255d971f`](https://github.com/mbackschat/a12-kernel-lean/blob/255d971f369efe847a4b39d5127b8a290e4f37ff/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md). The eight terminal receipts accepted at the [October 23 handback](sources/inbound-handbacks.md#src-inbound-2026-10-23) remain in [the ledger at `e48204df`](https://github.com/mbackschat/a12-kernel-lean/blob/e48204df08f6dd823c28011f520672cfefe0fd60/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md). The 16 terminal receipts closed at the [October 18 response](sources/inbound-handbacks.md#src-inbound-2026-10-18), fourteen `accepted` and two `answered`, remain in [the ledger at `bf2216b6`](https://github.com/mbackschat/a12-kernel-lean/blob/bf2216b69d5a3bbaefe182b76271ddf8d6b27ecf/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md). The 13 terminal receipts accepted on 2026-10-13 remain in [the ledger at `d502ca6b`](https://github.com/mbackschat/a12-kernel-lean/blob/d502ca6b4736cbfe0fcadbf5b8c12b96b45ad509/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md); [the October 13 provenance](sources/inbound-handbacks.md#src-inbound-2026-10-13) owns their reviewed revision and limits. The 24 receipts retired earlier on 2026-10-13 remain in [the preceding ledger](https://github.com/mbackschat/a12-kernel-lean/blob/cfffb2f1109796e0358e9f953e3fa6ee625797c1/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md).
