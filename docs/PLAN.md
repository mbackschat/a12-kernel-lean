# Active implementation plan

This is the resumption checkpoint, not a work log. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

**Priority invariant:** eventual 100% semantic conformance with kernel 30.8.1 remains the primary goal, with consumer adequacy as the co-equal representation test.

## Verified baseline

**Last full gate, 2026-08-09:** `lake build` clean (729 jobs) · trust audit **1868 theorem roots; 44348 declarations in 425 modules** · `lake test` 51/51 · `check-spec-sync.sh` passed. Re-run the applicable tier commands in [`TESTING.md`](TESTING.md#tier-gates) before relying on these changing counts.

## Active semantic unit

**Kernel static-diagnostic identity, one operator family at a time.** This is a deliberate course correction, chosen 2026-08-05 after measuring that the goal's static-legality half was near zero: `spec/` names 34 of roughly 57 in-scope `MVK_` codes while Lean referenced six, all in comments. All three `FieldValuesNotUnique` overloads now share exact arity, kind, and category diagnostic identity, and fixed filled-group computation admission adds four exact classes plus its accepted surface. The mechanism is a vocabulary of established classes plus a per-family projection that returns `none` where no class is established, so coverage stays countable and no unmeasured correspondence is asserted. Modelling only *that* a model is refused loses an observable, and it hid a real divergence: the elaborator refused at the first offending operand in authored order, where the Kernel's gate applies to the whole list and reports a different class. [`SG9`](SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion) owns the broad axis; [`SG13`](SEMANTICS-GAPS.md#sg13--group-list-and-group-count-completion) owns the remaining filled-group runtime breadth.

The thin lanes in priority order are SG4 computation scheduling and state transition — whose five open items are concrete and whose entry gate is already passed for String, scalar Number, and the conservative repeatable Number packet — and SG10 model-owned checked message-template authoring. Both are keystone-scale and want a fresh working context plus their audit packet.

## Immediate sequence

1. **Select the next operator family with measured refusal rows**, chosen by what the peer's admission-law tiers already assert. Prefer a family whose codes are measured over one that would need a new probe, and keep its projection local unless a second completed consumer proves the gate is shared.
2. **The reference channel's older non-model-indexed `numeric` leaf** remains ready and small: it reuses the same declaration sieve the `flat` leaf now uses, since neither fragment carries a starred operand. [`SG10`](SEMANTICS-GAPS.md#sg10--message-construction-and-formal-output-integration) owns its remaining obligations, including the unstarred group operand that is refused and has no witness in the reused model.
3. Opening SG4 requires its own audit packet and consumer hypothesis; it remains the largest single semantic payoff and the thinnest lane, deferred rather than dropped.

## Blockers

**None for the selected static-legality unit.** The source-preparation route now supplies a clean exact-revision JVM launcher or refuses before evidence is collected.

The outbound ledger queue contains pending [`SPEC-2026-08-09-01`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-08-09-01--numberoffilledgroups-computation-admission-preserves-fixed-list-and-starred-mix-boundaries) and [`SPEC-2026-08-09-02`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-08-09-02--fieldvaluesnotunique-refuses-confirm-at-the-whole-list-kind-gate). Before filing another `EXP-`, apply the route inventory in [the ledger's kinds of entry](A12-DMKITS-SPEC-SYNC-LEDGER.md#kinds-of-entry): static legality is measurable locally through the kernel consistency oracle and is never an `EXP-`; only kernel runtime questions cross the boundary.

## Parked boundaries

- Eager prepass invalidity needs no second snapshot because `CheckedDocument` already owns computation-phase checked cells. Its supplied messages enter the completed SG4 partition directly; no eager-prepass reconstruction or SG10 rendering belongs in that structural boundary.
- Computation scheduling, state transition, and the computation-result pointer partition remain under [`SG4`](SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition); message rendering remains under SG10; future operator-family admission and projections remain under their owning semantic gaps.
- Fixed multi-group `NumberOfFilledGroups` as a Number computation is represented for at least two distinct disjoint fixed operands and evaluates only when each operand's fields are direct children. Kernel static admission is measured for lists of two and three; correspondence above three remains external evidence pending. Wider runtime shapes and starred computation evaluation remain refused under [`SG13`](SEMANTICS-GAPS.md#sg13--group-list-and-group-count-completion), even though the Kernel's static gate admits a starred repeatable group alone or beside a fixed operand.
- Number and token `FieldValuesNotUnique` admission now resolve their shared entity-list shape once, run the shared whole-list kind/category scans, and enter their existing family certificates only after the exact diagnostic class is known. BOOLEAN and CONFIRM take the earlier kind code; admissible cross-category lists take the mixing code; duplicate-shape and other unmeasured refusals project to `none`.
- The a12-dmkits rule-template `$$` renderer correction is an isolated upstream implementation/test request against an already-correct canonical rule clause. The accepted field-owned experiment proves that String-pattern `$$` rejection and requiredness preservation are distinct behavior, not substitutes for that rule fix.
- Field-owned message locales beyond the measured `en_US` String-pattern producer, complete requiredness grammar, provider invocation, empty-value fallback, and other producer channels remain under SG10; they do not block SG4 computation work.
- Public protocol expansion, semantic shipments, dependencies, SMT integration, and new evidence/process machinery require their existing explicit adoption or approval gates.

## Stop and resume

- Stop if a required model fact or separating witness is absent, if an existing owner already closes the candidate, or before introducing a duplicate representation or unapproved infrastructure.
- Keep sibling repositories read-only and visibly unchanged. Never push without an explicit current request.
- On resumption, read the active semantic unit above, then inspect its implementation owner, recent history, cross-project handoffs, and applicable [`TESTING.md`](TESTING.md) rung before writing a red case.
