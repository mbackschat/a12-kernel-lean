# Active implementation plan

This is the resumption checkpoint, not a work log. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

**Verified semantic baseline, 2026-08-18:** recursive fixed-group token `FirstFilledValue` is closed at `894f32fedd1900fff6ff2cf9021a7b2e7af3b0ec` against maintained a12-dmkits `08115206d99bf8417c99dff9a73f9005175ca7d7`. The exact guarded nonrepeatable-root `CurrentRepetition` specialization is closed at `e4aa22ba41adde1a1e3058fed9a156b11bcd9ffc` against a12-dmkits `feba4552110858b07966660bf7080441d3b90d00`; its Tier 1 gate and converged cold review passed. Same-group repeatable validation and the exact one-row structural-guard Number cascade share one model-owned `CurrentRepetition` coordinate source; the cascade is closed at `be3159bd43ed774cf17af246ae4f6ad50cd42f1b` and its bounded Execute/Analyze checked-client probe passed without a new consumer layer. The exact one-level rule-owned unstarred-group error-locus matrix is closed internally against the maintained source at [`SOURCES.md`](SOURCES.md#src-group-list-rnu-admission-correction), without runtime admission. Captured `CurrentRepetition`, nested error-locus binding, and the unexplained split between parallel RNU diagnostics remain SG9 gaps; a12-dmkits remained clean at `89aa03957034de620562eb23a095d878f6547dca`.

<a id="active-unit"></a>
## Selected work

- `state`: ready to select the next semantic unit after the bounded error-locus projection lands.
- `gap`: none selected in this landing slice.
- `objective`: choose the first ready open semantic obligation whose existing owners and external discriminator support a bounded red/green capsule.
- `oracle`: [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md) owns the open set and verified routes; [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) owns the implemented baseline.
- `next`: select one gap, add or verify its exclusive route in that owner, then update this plan to link to it before semantic edits.
- `stop`: do not begin another semantic edit until its selected gap has a verified route; do not carry the current slice's review denominator into the next unit.
- `blocked-on`: none.
- `consumer-probe-trigger`: inactive after the structural-cascade probe; evaluate the next trigger only after selecting the next capability boundary.
- `resume`: `rg -n '^### SG|^- \`route-state\`:' docs/SEMANTICS-GAPS.md`
