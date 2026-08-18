# Active implementation plan

This is the resumption checkpoint, not a work log. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

**Verified semantic baseline, 2026-08-18:** recursive fixed-group token `FirstFilledValue` is closed at `894f32fedd1900fff6ff2cf9021a7b2e7af3b0ec` against maintained a12-dmkits `08115206d99bf8417c99dff9a73f9005175ca7d7`. The exact guarded nonrepeatable-root `CurrentRepetition` specialization is closed at `e4aa22ba41adde1a1e3058fed9a156b11bcd9ffc` against a12-dmkits `feba4552110858b07966660bf7080441d3b90d00`; its Tier 1 gate and converged cold review passed. Same-group repeatable validation and the exact one-row structural-guard Number cascade share one model-owned `CurrentRepetition` coordinate source; the cascade is closed at `be3159bd43ed774cf17af246ae4f6ad50cd42f1b` against the maintained source batches recorded in [`SOURCES.md`](SOURCES.md#src-current-repetition-repeatable-condition) and [`SOURCES.md`](SOURCES.md#src-current-repetition-computation-dependency), and its bounded Execute/Analyze checked-client probe passed without a new consumer layer. Wider token-group routes remain SG5 obligations. Error-field-locus binding, captured `CurrentRepetition`, and the unexplained split between parallel RNU diagnostics remain SG9 gaps; a12-dmkits remained clean at `89aa03957034de620562eb23a095d878f6547dca`.

<a id="active-unit"></a>
## Selected work

- `state`: ready for red/green implementation after the existing static-diagnostic and rule-assembly owners are inventoried.
- `gap`: [SG9 paths, indices, and static legality completion](SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion).
- `objective`: close the rule-owned, one-repeatable-level error-field-locus admission projection for the measured unstarred repeatable group-list/count matrix. Outside the repeated group remains `MVK_NO_WILDCARD`; inside, positive group quantifiers are admitted, a sole filled-group count reaches `MVK_PARAMSIZE_INVALIDGN`, and a paired count reaches `MVK_NEG_CONDITION_IN_ITERATION`.
- `oracle`: [`SOURCES.md`](SOURCES.md#src-group-list-rnu-admission-correction) owns the reviewed a12-dmkits `2d384c59f18cf9a1019e1e8273f2d8e900f741e0` matrix and its one-level/static-only limits; the cross-clause diagnostic record in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md#cross-clause-implementation-notes) owns local coverage.
- `next`: inventory rule assembly, group-list/count resolution, iteration legality, and existing diagnostic projection; then write the exact error-locus matrix red with the error-field declaration as the sole moving discriminator before choosing the smallest rule-owned representation.
- `stop`: do not key admission on the declaring/rule group, change condition-level admission globally, invent evaluation behavior for newly admitted shapes, generalize to nested or parallel repeatable scope, add parser/protocol/harness work, or map an unmeasured refusal.
- `blocked-on`: none.
- `consumer-probe-trigger`: inactive after the completed structural-cascade probe. Reconsider only after a reusable static-legality family closes or before a public Translate/Explain capability; SMT/Verify is not implicated by diagnostic identity.
- `resume`: `rg -n "fromGroupList|filledGroupCount|groupListDiagnostic|groupCountDiagnostic|assembleResolvedValidationRule|errorField|negativeConditionInIteration" A12Kernel/Elaboration A12Kernel/Proofs A12Kernel/Conformance`
