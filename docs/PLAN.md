# Active implementation plan

This is the resumption checkpoint, not a work log. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

**Verified semantic baseline, 2026-08-18:** recursive fixed-group token `FirstFilledValue` is closed at `894f32fedd1900fff6ff2cf9021a7b2e7af3b0ec` against maintained a12-dmkits `08115206d99bf8417c99dff9a73f9005175ca7d7`. The exact guarded nonrepeatable-root `CurrentRepetition` specialization is closed at `e4aa22ba41adde1a1e3058fed9a156b11bcd9ffc` against a12-dmkits `feba4552110858b07966660bf7080441d3b90d00`; its Tier 1 gate and converged cold review passed. Same-group repeatable validation and the exact one-row structural-guard Number cascade share one model-owned `CurrentRepetition` coordinate source; the cascade is closed at `be3159bd43ed774cf17af246ae4f6ad50cd42f1b` and its bounded Execute/Analyze checked-client probe passed without a new consumer layer. The exact one-level rule-owned unstarred-group error-locus matrix and both existing whole-rule diagnostic projections are closed internally against the maintained source at [`SOURCES.md`](SOURCES.md#src-group-list-rnu-admission-correction), without runtime admission. Captured `CurrentRepetition`, nested error-locus binding, and the unexplained split between parallel RNU diagnostics remain SG9 gaps; a12-dmkits remained clean at `89aa03957034de620562eb23a095d878f6547dca`.

<a id="active-unit"></a>
## Selected work

- `state`: ready to select the next bounded unit with the whole-rule diagnostic projection closed.
- `gap`: none selected in this landing slice.
- `objective`: evaluate the triggered Translate/Explain consumer probe at the closed two-class whole-rule diagnostic boundary, then select the first ready open semantic obligation.
- `oracle`: [`USE-CASES.md`](USE-CASES.md) and [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md) own the consumer task and probe boundary; [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md) owns the remaining semantic obligations.
- `next`: inspect the existing checked-client projection surface and select a bounded probe only if it can reuse that surface without a new protocol, schema, harness, or adapter.
- `stop`: if the probe needs a new consumer layer, record that no compact trigger route exists and resume semantic selection instead; do not widen the just-closed diagnostic denominator.
- `blocked-on`: none.
- `consumer-probe-trigger`: active for one bounded Translate/Explain decision at the closed two-class whole-rule diagnostic family boundary; SMT/Verify is not implicated.
- `resume`: `rg -n 'Translate|Explain|diagnostic' docs/USE-CASES.md docs/IMPLEMENTER-GUIDE.md A12Kernel/Conformance`
