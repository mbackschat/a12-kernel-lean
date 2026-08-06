# Active implementation plan

This is the resumption checkpoint, not a work log. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

**Priority invariant:** eventual 100% semantic conformance with kernel 30.8.1 remains the primary goal, with consumer adequacy as the co-equal representation test.

## Verified baseline

**Last full gate, 2026-08-06:** `lake build` clean (728 jobs) · trust audit **1852 theorem roots; 43869 declarations in 425 modules** · `lake test` 51/51 · `check-spec-sync.sh` passed. Re-run the applicable tier commands in [`TESTING.md`](TESTING.md#tier-gates) before relying on these changing counts.

## Active semantic unit

**Kernel static-diagnostic identity, one operator family at a time.** This is a deliberate course correction, chosen 2026-08-05 after measuring that the goal's static-legality half was near zero: `spec/` names 34 of roughly 57 in-scope `MVK_` codes while Lean referenced six, all in comments. The first family is field-list operand admission, closed over three classes. The mechanism is a vocabulary of established classes plus a per-family projection that returns `none` where no class is established, so coverage stays countable and no unmeasured correspondence is asserted. Modelling only *that* a model is refused loses an observable, and it hid a real divergence: the elaborator refused at the first offending operand in authored order, where the Kernel's gate applies to the whole list and reports a different class. [`SG9`](SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion) owns the axis and its two open questions.

The thin lanes in priority order are SG4 computation scheduling and state transition — whose five open items are concrete and whose entry gate is already passed for String, scalar Number, and the conservative repeatable Number packet — and SG10 model-owned checked message-template authoring. Both are keystone-scale and want a fresh working context plus their audit packet.

## Immediate sequence

1. **Replace `unsupportedGroupCount` with the measured compute-side fixed multi-group count.** Newly unblocked and the smallest ready capsule. `Elaboration/NumericComputation/Evaluation.lean:140` throws on `.filledGroupCount`; the measured account is an ordinary exact count over a **compute-phase presence** predicate where a formally invalid descendant cell counts as filled and an empty group does not. The work is one new presence projection beside `GroupPresenceState`'s validation one — the two must stay separate, since the same operator inverts between the arms — plus descendant enumeration from the model for a `ResolvedGroupReference`, which carries only a path. Scope it to a fixed non-repeatable operand whose descendants are direct fields, matching the measurement, and keep an explicit boundary for repeatable operands, nested descendants, and structural or call-local group errors. Retain the peer's three rows as the separating matrix, including the empty-group zero control.
2. **Adopt the static-legality route for diagnostic identity.** The kernel consistency oracle is reachable locally, so the active unit's `MVK_` coverage no longer needs upstream requests. First use should be a calibration probe whose answer is already known — the `SPEC-2026-08-05-04` reordered-operand pair — so a method error shows up as disagreement with a measured result rather than as a plausible new fact.
3. **Extend diagnostic identity to the Number and token `FieldValuesNotUnique` overloads.** They share the Kernel's admission gates with the temporal one, so this is the second consumer that justifies lifting the comparability-category table from the temporal module to [`FieldEntityList`](../A12Kernel/Elaboration/FieldEntityList.lean). Their error types are the *shared* entity-list ones used by other operators too, so the blast radius is real and the slice should start by measuring which of those operators share which classes rather than by editing the shared type.
4. **Then the next operator family with measured refusal rows**, chosen by what the peer's admission-law tiers already assert. Prefer a family whose codes are measured over one that would need a new probe.
5. **The reference channel's older non-model-indexed `numeric` leaf** remains ready and small: it reuses the same declaration sieve the `flat` leaf now uses, since neither fragment carries a starred operand. [`SG10`](SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration) owns its remaining obligations, including the unstarred group operand that is refused and has no witness in the reused model.
6. Opening SG4 requires its own audit packet and consumer hypothesis; it remains the largest single semantic payoff and the thinnest lane, deferred rather than dropped.

## Blockers

**None.** Both former blockers closed on 2026-08-06 and neither needs an owner decision.

- [`SG13`](SEMANTICS-GAPS.md#sg13--group-list-and-group-count-completion) fixed-multi-group computation target is **measured** at a12-dmkits `677e2eb7` under accepted [`EXP-2026-08-06-01`](A12-DMKITS-SPEC-SYNC-LEDGER.md#exp-2026-08-06-01--a-fixed-multi-group-filled-count-may-be-special-cased-ahead-of-computation-poison). Replacing `unsupportedGroupCount` is now ordinary scheduled work, sequenced below.
- The SG7 starred-form firing locus is **withdrawn, not deferred**: its premise was that two a12-dmkits surfaces contradicted each other, and both halves of that reading were wrong. The locus is measured on both kernel strategies as one verdict at the first-row anchor, the peer's skill says the same, and Lean already matches.

The outbound ledger queue is empty. Before filing another `EXP-`, apply the route inventory in [the ledger's kinds of entry](A12-DMKITS-SPEC-SYNC-LEDGER.md#kinds-of-entry): static legality is measurable locally through the kernel consistency oracle and is never an `EXP-`; only kernel runtime questions cross the boundary.

## Parked boundaries

- Eager prepass invalidity needs no second snapshot because `CheckedDocument` already owns computation-phase checked cells. Its supplied messages enter the completed SG4 partition directly; no eager-prepass reconstruction or SG10 rendering belongs in that structural boundary.
- Computation scheduling, state transition, and the computation-result pointer partition remain under [`SG4`](SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition); message rendering remains under SG10; future operator-family admission and projections remain under their owning semantic gaps.
- Fixed multi-group `NumberOfFilledGroups` as a Number computation remains at the explicit `unsupportedGroupCount` boundary. Source audit yields rival zero-versus-clear accounts for an unavailable group, and no current unchanged a12-dmkits computation probe measures that exact value-producing shape; [`SG13`](SEMANTICS-GAPS.md#sg13--group-list-and-group-count-completion) owns the seeded-target separator and exact revision anchors.
- The a12-dmkits rule-template `$$` renderer correction is an isolated upstream implementation/test request against an already-correct canonical rule clause. The accepted field-owned experiment proves that String-pattern `$$` rejection and requiredness preservation are distinct behavior, not substitutes for that rule fix.
- Field-owned message locales beyond the measured `en_US` String-pattern producer, complete requiredness grammar, provider invocation, empty-value fallback, and other producer channels remain under SG10; they do not block SG4 computation work.
- Public protocol expansion, semantic shipments, dependencies, SMT integration, and new evidence/process machinery require their existing explicit adoption or approval gates.

## Stop and resume

- Stop if a required model fact or separating witness is absent, if an existing owner already closes the candidate, or before introducing a duplicate representation or unapproved infrastructure.
- Keep sibling repositories read-only and visibly unchanged. Never push without an explicit current request.
- On resumption, read the active semantic unit above, then inspect its implementation owner, recent history, cross-project handoffs, and applicable [`TESTING.md`](TESTING.md) rung before writing a red case.
