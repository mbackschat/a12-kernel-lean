# Active implementation plan

This is the resumption checkpoint, not a work log. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

**Verified semantic baseline, 2026-08-18:** recursive fixed-group token `FirstFilledValue` is closed at `894f32fedd1900fff6ff2cf9021a7b2e7af3b0ec` against maintained a12-dmkits `08115206d99bf8417c99dff9a73f9005175ca7d7`. The exact guarded nonrepeatable-root `CurrentRepetition` specialization is closed at `e4aa22ba41adde1a1e3058fed9a156b11bcd9ffc` against a12-dmkits `feba4552110858b07966660bf7080441d3b90d00`; its Tier 1 gate and converged cold review passed. Same-group repeatable validation and the exact one-row structural-guard Number cascade now share one model-owned `CurrentRepetition` coordinate source against the maintained source batches recorded in [`SOURCES.md`](SOURCES.md#src-current-repetition-repeatable-condition) and [`SOURCES.md`](SOURCES.md#src-current-repetition-computation-dependency). Wider token-group routes remain SG5 obligations. Error-field-locus binding, captured `CurrentRepetition`, and the unexplained split between parallel RNU diagnostics remain SG9 gaps; a12-dmkits remained clean at `89aa03957034de620562eb23a095d878f6547dca`.

<a id="active-unit"></a>
## Selected work

- `state`: ready for the triggered bounded consumer probe after the one-row semantic capsule lands.
- `gap`: [SG4 computation scheduling and state transition](SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition).
- `objective`: qualify the exact checked `CurrentRepetition(/Shipment/Lines) > 0; First ← Base; Second ← First` representation for one bounded Execute/Analyze task, proving that a consumer can execute the two rich addressed outcomes and recover the structural group separately from the two real field edges without renewed source archaeology or dependency expansion.
- `oracle`: the semantic boundary and exact limits are owned by [§11](IMPLEMENTATION-MAP.md#11--calculations-and-formal-checking); the external checkpoint is [`SOURCES.md`](SOURCES.md#src-current-repetition-computation-dependency).
- `next`: inspect the existing Execute/Analyze task profiles in [`USE-CASES.md`](USE-CASES.md) and the bounded addressed-operation consumer before selecting the smallest existing consumer boundary; reuse `CheckedCurrentRepetitionNumberCascade.execute` and `.analyze` directly rather than adding another evaluator or dependency representation.
- `stop`: do not add a protocol, shipment, solver, generic graph/scheduler, condition tree, parser route, multi-row behavior, or qualification harness. If no existing consumer boundary can transport the exact structural-versus-field distinction without one of those expansions, record the blocker and recommend the narrowest later milestone.
- `blocked-on`: none.
- `consumer-probe-trigger`: active now. Execute/Analyze is required; SMT/Verify is excluded unless route inspection finds an existing decision procedure that consumes this arithmetic constraint rather than merely replaying the fixture. The expected outcome is no SMT probe because the current consumer decision is dependency identity and order, not arithmetic satisfiability.
- `resume`: `rg -n "Execute|Analyze|CheckedAddressedNumericOperation|analysis|structuralGroup|fieldDependencies" docs/USE-CASES.md docs/IMPLEMENTER-GUIDE.md A12Kernel/Elaboration A12Kernel/Proofs A12Kernel/Conformance`
