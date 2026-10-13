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

Four corrections are `pending` below and have not been handed off. The 24 terminal receipts retired on 2026-10-13 remain in [the preceding ledger](https://github.com/mbackschat/a12-kernel-lean/blob/cfffb2f1109796e0358e9f953e3fa6ee625797c1/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md). [The consolidated provenance](sources/inbound-handbacks.md#src-inbound-2026-10-12) and [the profile clarification](sources/custom-field-probes.md#src-custom-legacy-profile) own their reviewed revisions, evidence routes and limits.

<a id="spec-2026-10-12-01"></a>
### SPEC-2026-10-12-01 — selected error addresses use the unique non-iterating key

- `status`: pending
- `canonical`: [selected validation-message references](../spec/08-paths-and-references.md#43-selected-references-in-validation-messages).
- `delta`: State the eligibility and address-replacement rule for a unique authored semantic-index key on the error field, separately from payload availability and ordinary iteration.
- `basis`: Kernel 30.8.1 at `cb66e51fa7ab90b650698f861bf670754e2e1e66`; [source checkpoint](sources/message-cache-probes.md#src-selected-error-reanchoring). The peer's selected-error controls at `17b3eb0840e2e5dccf76135eb91fef04512ef3e8` establish full/partial invalid-key and duplicate-key outcomes, not every eligibility contrast. No new Kernel capture is claimed.
- `acceptance`: Reconcile the canonical account and existing selected-error implementation with the source-owned unique-key/non-iterating gate. Check repeated same-key versus competing-key occurrences, ordinary iteration at the selected level, parent-local association, unavailable payload and absent association. Preserve the explicit duplicate-cache host-order boundary; do not adopt first-admitted row order as the Kernel oracle.
- `introducing revision`: `83008cf9`. Local K05 closure is recorded in [the plan](PLAN.md#active-unit); peer reconciliation remains pending.

<a id="spec-2026-10-13-01"></a>
### SPEC-2026-10-13-01 — Date first-filled targets render independently of source spelling

- `status`: pending
- `canonical`: [typed selection](../spec/09-computations.md#4-the-stored-form--a-computed-value-lands-as-a-string-in-the-targets-shape) and the Date target rule in the same clause.
- `delta`: Remove the false refusal of crossed ISO/dotted Date formats. First-filled sources retain the list's exact-profile gate; target compatibility uses the temporal comparison gate, and the target renders the selected Date, including component omission.
- `basis`: Kernel 30.8.1, [target-profile checkpoint](sources/repeatable-temporal-computation-probes.md#src-temporal-target-profiles-k11). Both strategies agree on fixed/repeated dotted-to-ISO, full-to-year and year-month-to-year results, fallback, reached poison and independent rows. The same checkpoint retains compact-format execution, yearless Base-Year completion, checked-source admission and source-rejection versus target-rejection controls. DateTime-to-Date refusals remain distinct.
- `acceptance`: Reconcile the canonical first-filled assignment account and any source/target profile-identity restriction. Preserve the exact-profile source-list gate, source-order short circuit, target-owned formatting and rejection, source-format partial completion, and year-presence/Base-Year comparison rule. Existing sufficient evidence can discharge the peer work; no duplicate capture is requested.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-13-02"></a>
### SPEC-2026-10-13-02 — full-input checking precedes registered validation and optional conversion

- `status`: pending
- `canonical`: [String input checks](../spec/06-strings-and-enumerations.md#a2-legal-charset-definitions-and-atomic-matching) and [custom conversion](../spec/06-strings-and-enumerations.md#a3-custom-field-type-validation).
- `delta`: State raw-String bypass and the technical-length → charset → ASCII-edge-space → basic-format sequence. The technical guard counts authored UTF-16 units before normalization, refuses above 99,999 with `wertZuLang` and is absent from computed-target checking. Replace unresolved custom length/charset/conversion ordering with the source-owned invocation contract, preserving the distinction between ordinary measured validation and opt-in codec source characterization.
- `basis`: [Ordered ingestion and domain checkpoint](sources/domain-ingestion-probes.md#src-checked-string-ingestion-k13), pinned Kernel 30.8.1 source and both-strategy artifacts. Registered repeated Custom and mixed Custom/String distinct/uniqueness use the once-normalized accepted value. The converter selects the two-argument result's converted text without consuming its optional error message. The [technical-length checkpoint](sources/domain-ingestion-probes.md#src-technical-length-k13) is source-grounded with no retained capture.
- `acceptance`: Reconcile the canonical input ordering and custom invocation contract. Preserve raw bypass, the technical guard's UTF-16 unit and authored-text measurement, single first input failure, original validator input, declared bounds in callback context, default conversion-off behavior, opt-in direction and normalized conversion input. Reuse sufficient existing tests; no arbitrary validator or codec implementation is requested.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-13-03"></a>
### SPEC-2026-10-13-03 — computation binding errors retain authored operand order

- `status`: pending
- `canonical`: [Computation membership admission](../spec/06-strings-and-enumerations.md#b5-computation-preconditions-preserve-reached-errors-and-traversal-order).
- `delta`: Check each operand's computation binding before reading the next operand, retaining that first read error through Number-to-token fallback. Whole-list duplicate and kind checks remain later.
- `basis`: [Thirteen retained static cases](sources/domain-ingestion-probes.md#src-membership-read-order-k13) with admitted Number/String controls, missing-name/unbound field and group twins, Custom operands, a competing duplicate and an isolated mixed-kind refusal. All actual-model Lean readbacks agree.
- `acceptance`: Reconcile operand-local binding with authored read order and fallback projection. An earlier unbound operand reports `MVK_NO_WILDCARD`; an earlier missing name reports `MVK_INVALID_ENTITY`. Preserve existing intra-operand gates and whole-list checks; no exhaustive diagnostic permutation is claimed.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-13-04"></a>
### SPEC-2026-10-13-04 — Enumeration declaration notifications are collected in six ordered blocks

- `status`: pending
- `canonical`: [Category declaration pairing](../spec/06-strings-and-enumerations.md#b2-categories-via--).
- `delta`: Add restricted-charset invalid-character notifications per rejected UTF-16 unit, the field-level codeless supplementary-plane notification, all shortfalls before all surpluses, value/category and value duplicates, the codeless repeated-value notification, supplementary-value skips and identical-notification collapse.
- `basis`: [Retained 37-row consistency capture](sources/model-structure-and-declaration-probes.md#src-enumeration-declaration-notifications), real Kernel 30.8.1 through structured authoring at clean a12-dmkits `a4091041fe4d0de02053517f11d12f480b5c2cbc`; Lean reader locks replay every row.
- `acceptance`: Reconcile declaration checking with the six-block order and per-unit/per-value multiplicity, keeping the two codeless classes distinct from coded ones. Do not claim an order inside the arity or category-duplicate blocks, supplementary scalars in category names or tokens, or table-backed Enumerations.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-13-05"></a>
### SPEC-2026-10-13-05 — over-repetition findings are per written entity, partial-insensitive and operand-inventory scoped

- `status`: pending
- `canonical`: [Over-repetition row](../spec/02-logic-and-formal-errors.md#b3-what-puts-a-cell-in-the-third-state) and [computation formal input scope](../spec/09-computations.md#33-what-compute-reports).
- `delta`: Count written nonrepeatable group instances and present null/empty cells; judge each entity on its own ancestry rather than by coordinate-prefix containment; report the full set for every nonempty partial selection and none for an empty one; scope the computation channel to uncomputed operand cells plus ancestor instances of operand and computed fields.
- `basis`: [Occurrence-scope capture](sources/over-repetition-probes.md#src-over-repetition-occurrence-scope), eleven rows on both Kernel 30.8.1 strategies at clean a12-dmkits `a4091041fe4d0de02053517f11d12f480b5c2cbc`; Kernel source `CheckCommand.formalePruefung`, `ValidationCommand.processPartlyValidation` and `CalculationCommand.getEntityFullNamesNotRemovedFromData`. The validation-side occurrence and partial results corroborate the peer's `OverRepetitionOccurrenceDiffTest`; the sibling-coordinate twin, operand-path nonrepeatable group and computed-target ancestry are new measurements.
- `acceptance`: Reconcile the structural emitter with per-entity own-ancestry checking, including nonrepeatable group instances, and the computation channel with the computed-target ancestry rule. Preserve position-selected codes, absorption and the empty-selection boundary; no emission order is claimed.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
