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

<a id="spec-2026-10-10-01"></a>
### SPEC-2026-10-10-01 — explicit narrower guards qualify target-derived operand scope

- `status`: pending
- `canonical`: [computation formal inputs](../spec/09-computations.md) and [filter cache scope](../spec/07-repetition-and-iteration.md#3-the-filter-having-the--correlation-and-aggregation) derive target subtrees from guard preprocessing, not an unconditional target expansion.
- `delta`: the implicit nearest-repeatable-group guard is omitted when an authored computation already has a conditional-group profile protecting that row or a narrower containing group. A narrower guard can exclude outer siblings from expanded operand scope; explicit row guards still include them. Computed fields stay excluded from formal inputs.
- `basis`: [three-model Kernel 30.8.1 matrix](sources/computation-scheduling-probes.md#src-computation-guard-operand-scope), 15 agreeing runtime rows, plus the source-owned common mechanism. Formal findings do not prevent the target computing. Cache consequences are source-derived, not newly runtime-measured.
- `acceptance`: reconcile KF538's blanket target-subtree account and operand/cache collection with implicit, explicit-row and narrower-containing-group controls. Preserve per-authored-computation preprocessing and distinguish scheduling dependencies from operands. Retain nested/sparse/partial-validation limits. Introducing revision is the first commit containing this ID; no reviewed peer response yet.


<a id="spec-2026-10-10-02"></a>
### SPEC-2026-10-10-02 — consumer-specific sparse filter traversal above 100 candidates

- `status`: pending
- `canonical`: [filter traversal](../spec/07-repetition-and-iteration.md#3-the-filter-having-the--correlation-and-aggregation).
- `delta`: Sparse-enabled consumers use phase-visible coordinate-prefix occupancy above 100 cache-bounded candidates. Initial/reset searches remain dense until a candidate is kept; rejection does not advance the kept cursor. Computation retains successor lookahead. First-filled, value counts and any-pair overlap remain dense; scalar-versus-list overlap opts into sparse traversal.
- `basis`: [Kernel 30.8.1 computation matrices and source account](sources/group-and-iteration-probes.md#src-sparse-filter-traversal), both strategies agreeing. Sum/filled count, threshold/reset/occupancy controls, Number/String/Boolean value counts and exact/yearless overlap policies are measured. Distinct/extrema extensions and full validation remain source-derived.
- `field-fill extension`: The five-row, seven-operator Kernel matrix now confirms these policies on computation and full validation: positive presence is sparse-enabled; negative presence, second-witness and declared-empty are dense. Both phases use kept-successor lookahead and can decide before a later filter failure. Composite guards restart with the appropriate policy. The full-validation adapter now consumes incrementally; an eager materialized filter selection is not equivalent. Wider carrier/profile calibration and other predicate/membership prefix adapters remain pending.
- `uniqueness extension`: [Uniqueness](../spec/07-repetition-and-iteration.md#5-groupfilled-and-the-other-repetition-rules) remains dense on both arms and preserves successor lookahead before deciding at a duplicate. Full validation compares incrementally, so a duplicate hides later filters and authored operands. The source route is settled; new large-domain and validation-prefix external calibration remains pending.
- `membership extension`: The [six-row membership matrix](sources/group-and-iteration-probes.md#src-sparse-filter-traversal) confirms sparse collection/search for AtLeastOne and dense passes for No/NotAll. The [membership clause](../spec/06-strings-and-enumerations.md#b3-the-value-list-quantifiers--per-cell-three-way-classification-) now preserves ordinary NotAll's presence short circuit before a failing filtered values side. Reconcile KF68's equivalence claim at the pure-member boundary; it does not authorize eager filtered collection. Number/String both-arm calibration is retained; optimized OL emission, wider carriers and partial validation remain bounded separately.
- `reconcile`: iteration prose and consumer-specific evaluator traversal. Preserve the distinction between candidate cache scope, occupancy, filter execution and payload consumption; do not replace it with physical-row filtering.
- `acceptance`: Review the canonical account against the retained matrix and source, reconcile the peer's supported surfaces, and state remaining predicate/prepass, partial-validation and external-calibration limits explicitly.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
- `reviewed a12-dmkits revision`: pending.
