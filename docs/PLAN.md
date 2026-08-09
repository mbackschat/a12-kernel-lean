# Active implementation plan

This is the resumption checkpoint, not a work log. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

**Priority invariant:** eventual 100% semantic conformance with kernel 30.8.1 remains the primary goal, with consumer adequacy as the co-equal representation test.

## Verified baseline

**Last full gate, 2026-08-06:** `lake build` clean (729 jobs) · trust audit **1857 theorem roots; 43902 declarations in 425 modules** · `lake test` 51/51 · `check-spec-sync.sh` passed. Re-run the applicable tier commands in [`TESTING.md`](TESTING.md#tier-gates) before relying on these changing counts.

## Active semantic unit

**Kernel static-diagnostic identity, one operator family at a time.** This is a deliberate course correction, chosen 2026-08-05 after measuring that the goal's static-legality half was near zero: `spec/` names 34 of roughly 57 in-scope `MVK_` codes while Lean referenced six, all in comments. The first family is field-list operand admission, closed over three classes. The mechanism is a vocabulary of established classes plus a per-family projection that returns `none` where no class is established, so coverage stays countable and no unmeasured correspondence is asserted. Modelling only *that* a model is refused loses an observable, and it hid a real divergence: the elaborator refused at the first offending operand in authored order, where the Kernel's gate applies to the whole list and reports a different class. [`SG9`](SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion) owns the axis and its two open questions.

The thin lanes in priority order are SG4 computation scheduling and state transition — whose five open items are concrete and whose entry gate is already passed for String, scalar Number, and the conservative repeatable Number packet — and SG10 model-owned checked message-template authoring. Both are keystone-scale and want a fresh working context plus their audit packet.

## Immediate sequence

1. **Static-legality route: calibrated and ready for a clean-provenance rerun.** Resolve the exact-source JVM launcher through the preparation command in [`TESTING.md`](TESTING.md#structured-dmtool-probes-and-feedback), rerun the established calibration control, then use it for the compute-arm static admission rule for a fixed group count, which [`SG13`](SEMANTICS-GAPS.md#sg13--group-list-and-group-count-completion) names as its only remaining measurable axis.
2. **Extend diagnostic identity to the Number and token `FieldValuesNotUnique` overloads.** They share the Kernel's admission gates with the temporal one, so this is the second consumer that justifies lifting the comparability-category table from the temporal module to [`FieldEntityList`](../A12Kernel/Elaboration/FieldEntityList.lean). Their error types are the *shared* entity-list ones used by other operators too, so the blast radius is real and the slice should start by measuring which of those operators share which classes rather than by editing the shared type.
3. **Then the next operator family with measured refusal rows**, chosen by what the peer's admission-law tiers already assert. Prefer a family whose codes are measured over one that would need a new probe.
4. **The reference channel's older non-model-indexed `numeric` leaf** remains ready and small: it reuses the same declaration sieve the `flat` leaf now uses, since neither fragment carries a starred operand. [`SG10`](SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration) owns its remaining obligations, including the unstarred group operand that is refused and has no witness in the reused model.
5. Opening SG4 requires its own audit packet and consumer hypothesis; it remains the largest single semantic payoff and the thinnest lane, deferred rather than dropped.

## Blockers

**None for the selected static-legality unit.** The source-preparation route now supplies a clean exact-revision JVM launcher or refuses before evidence is collected.

The outbound ledger queue is empty. Before filing another `EXP-`, apply the route inventory in [the ledger's kinds of entry](A12-DMKITS-SPEC-SYNC-LEDGER.md#kinds-of-entry): static legality is measurable locally through the kernel consistency oracle and is never an `EXP-`; only kernel runtime questions cross the boundary.

## Parked boundaries

- Eager prepass invalidity needs no second snapshot because `CheckedDocument` already owns computation-phase checked cells. Its supplied messages enter the completed SG4 partition directly; no eager-prepass reconstruction or SG10 rendering belongs in that structural boundary.
- Computation scheduling, state transition, and the computation-result pointer partition remain under [`SG4`](SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition); message rendering remains under SG10; future operator-family admission and projections remain under their owning semantic gaps.
- Fixed multi-group `NumberOfFilledGroups` as a Number computation evaluates only for a fixed nonrepeatable operand whose fields are its direct children; wider shapes and its static admission on the computation arm stay refused under [`SG13`](SEMANTICS-GAPS.md#sg13--group-list-and-group-count-completion).
- The a12-dmkits rule-template `$$` renderer correction is an isolated upstream implementation/test request against an already-correct canonical rule clause. The accepted field-owned experiment proves that String-pattern `$$` rejection and requiredness preservation are distinct behavior, not substitutes for that rule fix.
- Field-owned message locales beyond the measured `en_US` String-pattern producer, complete requiredness grammar, provider invocation, empty-value fallback, and other producer channels remain under SG10; they do not block SG4 computation work.
- Public protocol expansion, semantic shipments, dependencies, SMT integration, and new evidence/process machinery require their existing explicit adoption or approval gates.

## Stop and resume

- Stop if a required model fact or separating witness is absent, if an existing owner already closes the candidate, or before introducing a duplicate representation or unapproved infrastructure.
- Keep sibling repositories read-only and visibly unchanged. Never push without an explicit current request.
- On resumption, read the active semantic unit above, then inspect its implementation owner, recent history, cross-project handoffs, and applicable [`TESTING.md`](TESTING.md) rung before writing a red case.
