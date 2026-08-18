# Active implementation plan

This is the resumption checkpoint, not a work log. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

**Verified semantic baseline, 2026-08-18:** recursive fixed-group token `FirstFilledValue` is closed at `894f32fedd1900fff6ff2cf9021a7b2e7af3b0ec` against maintained a12-dmkits `08115206d99bf8417c99dff9a73f9005175ca7d7`. The exact guarded nonrepeatable-root `CurrentRepetition` specialization is closed at `e4aa22ba41adde1a1e3058fed9a156b11bcd9ffc` against a12-dmkits `feba4552110858b07966660bf7080441d3b90d00`; its Tier 1 gate and converged cold review passed. Same-group repeatable validation and the exact one-row structural-guard Number cascade share one model-owned `CurrentRepetition` coordinate source; the cascade is closed at `be3159bd43ed774cf17af246ae4f6ad50cd42f1b` and its bounded Execute/Analyze checked-client probe passed without a new consumer layer. The exact one-level rule-owned unstarred-group error-locus matrix and both existing whole-rule diagnostic projections are closed internally against the maintained source at [`SOURCES.md`](SOURCES.md#src-group-list-rnu-admission-correction), without runtime admission; their bounded Translate/Explain checked-client probe preserves acceptance, both exact mapped classes, and an unmapped typed refusal without a new consumer layer. Captured `CurrentRepetition`, nested error-locus binding, and the unexplained split between parallel RNU diagnostics remain SG9 gaps; a12-dmkits remained clean at `89aa03957034de620562eb23a095d878f6547dca`.

<a id="active-unit"></a>
## Selected work

- `state`: selected with a verified implementation route.
- `gap`: [nested addressed Number extrema](SEMANTICS-GAPS.md#gap-sg5-nested-addressed-number-extrema).
- `objective`: retain one nested same- or different-selector `Min`/`Max` call as one addressed extremum operand, preserving call boundaries, per-call literal budgets, scale union, dependencies, authored order, and row-local selection.
- `oracle`: [numeric extremum call boundaries](SOURCES.md#src-numeric-extremum-call-boundary) owns the maintained static separator; [numeric wrappers and extrema](IMPLEMENTATION-MAP.md#5--numbers-and-decimals) owns the implemented direct and bounded operation baseline.
- `next`: write the nested same-selector, different-selector, flattened-budget, scale, dependency, and evaluation-order cases red in the routed conformance owner before changing the checked operand.
- `stop`: do not admit division, power, surrounding arithmetic, parser lowering, partial execution, or wider scheduling; do not infer repeatable Kernel runtime correspondence from the static source matrix.
- `blocked-on`: none.
- `consumer-probe-trigger`: inactive after the whole-rule diagnostic probe; evaluate the next trigger only at another reusable family or risk boundary.
- `resume`: `rg -n 'gap-sg5-nested-addressed-number-extrema|SurfaceAddressedNumberExtremumOperand|CheckedAddressedNumberExtremumOperand' docs/SEMANTICS-GAPS.md A12Kernel/Elaboration/AddressedNumberExtremum.lean`
