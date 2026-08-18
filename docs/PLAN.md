# Active implementation plan

This is the resumption checkpoint, not a work log. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

**Verified semantic baseline, 2026-08-18:** recursive fixed-group token `FirstFilledValue` is closed at `894f32fedd1900fff6ff2cf9021a7b2e7af3b0ec` against maintained a12-dmkits `08115206d99bf8417c99dff9a73f9005175ca7d7`. The exact guarded nonrepeatable-root `CurrentRepetition` specialization is closed at `e4aa22ba41adde1a1e3058fed9a156b11bcd9ffc` against a12-dmkits `feba4552110858b07966660bf7080441d3b90d00`; its Tier 1 gate and converged cold review passed. Same-group repeatable validation and the exact one-row structural-guard Number cascade share one model-owned `CurrentRepetition` coordinate source; the cascade is closed at `be3159bd43ed774cf17af246ae4f6ad50cd42f1b` and its bounded Execute/Analyze checked-client probe passed without a new consumer layer. The exact one-level rule-owned unstarred-group error-locus matrix and both existing whole-rule diagnostic projections are closed internally against the maintained source at [`SOURCES.md`](SOURCES.md#src-group-list-rnu-admission-correction), without runtime admission; their bounded Translate/Explain checked-client probe preserves acceptance, both exact mapped classes, and an unmapped typed refusal without a new consumer layer. Captured `CurrentRepetition`, nested error-locus binding, and the unexplained split between parallel RNU diagnostics remain SG9 gaps; a12-dmkits remained clean at `89aa03957034de620562eb23a095d878f6547dca`.

<a id="active-unit"></a>
## Selected work

- `state`: ready for red/green on resolved DateRange construction equality after route discovery rejected three stale SG6 overlaps already owned by the implementation map.
- `gap`: [DateRange construction equality](SEMANTICS-GAPS.md#gap-sg6-date-range-construction-equality).
- `objective`: compare one resolved full-Date construction with one resolved stored DateRange under exact `==`/`!=` in either authored order, without adding a second range value carrier.
- `oracle`: maintained a12-dmkits [`DateRangeEqualityDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/DateRangeEqualityDiffTest.kt) plus the gap's endpoint-change and operand-swap separators.
- `next`: add the endpoint-change equality case red at the routed conformance owner, implement the smallest comparison capsule over `ResolvedDateRange`, then add the useful complement/swap laws.
- `stop`: do not widen into field/path authoring, DateFragment completion, parsing, empty/formal claims, construction-versus-construction, computation, target rendering, overlap arguments, or bound extraction.
- `blocked-on`: none.
- `consumer-probe-trigger`: inactive after the whole-rule diagnostic probe; evaluate the next trigger only at another reusable family or risk boundary.
- `resume`: `sed -n '/gap-sg6-date-range-construction-equality/,/^### /p' docs/SEMANTICS-GAPS.md`
