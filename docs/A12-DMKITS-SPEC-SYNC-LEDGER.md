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

Three corrections are `pending` below and have not been handed off. The 13 terminal receipts accepted on 2026-10-13 remain in [the ledger at `d502ca6b`](https://github.com/mbackschat/a12-kernel-lean/blob/d502ca6b4736cbfe0fcadbf5b8c12b96b45ad509/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md); [the October 13 provenance](sources/inbound-handbacks.md#src-inbound-2026-10-13) owns their reviewed revision and limits. The 24 receipts retired earlier on 2026-10-13 remain in [the preceding ledger](https://github.com/mbackschat/a12-kernel-lean/blob/cfffb2f1109796e0358e9f953e3fa6ee625797c1/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md).

<a id="spec-2026-10-13-13"></a>
### SPEC-2026-10-13-13 — quoted Number conversion, kept leading-zero text and the full formal cascade with its message keys

- `status`: pending
- `canonical`: [storage regimes](../spec/04-numbers-and-decimals.md#stored-decimal-identity-and-runtime-read-text-depend-on-the-storage-regime) and [other numeric constraints](../spec/04-numbers-and-decimals.md#4-other-numeric-constraints).
- `delta`: Quoted Number text converts by the host decimal grammar (sign, BMP decimal digits, fraction, exponent); unconvertible text and, on a `leadingZerosAllowed` field, text with an ASCII leading zero stay verbatim. A scale outside 32 bits keeps the text; an extreme in-range scale can fault validation. The cascade gains a leading plus first, signed zero, missing separator and leading zero at their positions, and a negative zero on an unsigned zero-forbidding amount field reports `zahlIstNull`. The lexical checks are reached by kept text, not only by display conversion, which this replaces. Message keys additionally read sign and plain fractional shape.
- `basis`: [ingress checkpoint](sources/domain-ingestion-probes.md#src-number-ingress-k16), four runtime requests over fourteen documents at a12-dmkits `a4091041`, Kernel 30.8.1, plus the retained `FormalNum` captures; peer kf276 for the money exception.
- `acceptance`: Reconcile conversion, retention and cascade order with these rows. Do not claim a measured grouping-separator route, a separated sign variant of any message key, or a conversion outcome for a scale magnitude between 100,000 and the faulting `2147483648`.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-13-14"></a>

### SPEC-2026-10-13-14 — the model consistency rule set, its order and the authored versus filtered model it reads

- `status`: pending
- `canonical`: [model consistency rules](../spec/01-data-model.md#12-model-consistency-rules).
- `delta`: A built model meets identifier uniqueness, Number value limits, attachment and multi-select group shapes, the generation of the declaration with the printed-bound formal check, and basic member checks, in that order, each notification reported in walk order; a model drawing any is refused. Every rule but the bound check reads the authored model, variant-filtered fields included. Duplicated identifiers report every occurrence; the value limit compares doubles at the raw declared maximum fraction digits; a field's bound check reports the maximum before the minimum and an identical class once. Six empty or repeated members fail the build with no class.
- `basis`: [consistency checkpoint](sources/model-structure-and-declaration-probes.md#src-model-consistency-k17), 89 rows at a12-dmkits `a4091041`, Kernel 30.8.1, with source reading at Kernel `cb66e51`.
- `acceptance`: Reconcile rule order, multiplicity and the authored/filtered split with these rows. Do not claim an order across distinct duplicated identifiers, attachment texts under another condition language, or two build failures in one model.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.

<a id="spec-2026-10-13-15"></a>

### SPEC-2026-10-13-15 — runtime Number bounds as printed double text and the runtime account of the fractional sentinel

- `status`: pending
- `canonical`: [other numeric constraints](../spec/04-numbers-and-decimals.md#4-other-numeric-constraints).
- `delta`: A declared `minValue`/`maxValue` is compared at runtime as the text printed from its nearest double, with fixed places rounding half up when both fractional members equal `n ≥ 0` and the plain shortest decimal otherwise. The `-1` sentinel resolves into an ordinary pair (`-1` minimum to zero, `-1` maximum to the minimum), except that a `-1` minimum beside a zero maximum arms neither the separator nor the fractional-count test.
- `basis`: [bounds checkpoint](sources/domain-ingestion-probes.md#src-number-declaration-bounds-k17), two requests at a12-dmkits `a4091041`, Kernel 30.8.1, both strategies agreeing.
- `acceptance`: Reconcile the printed bound and sentinel resolution with these rows. Do not claim a measured computed fractional result into a `(-1, 0)` field.
- `introducing commit`: first commit containing this stable entry ID, resolved by the ledger contract above.
