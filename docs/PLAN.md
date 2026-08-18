# Active implementation plan

This is the resumption checkpoint, not a work log. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

**Verified semantic baseline, 2026-08-18:** recursive fixed-group token `FirstFilledValue` is closed at `894f32fedd1900fff6ff2cf9021a7b2e7af3b0ec` against maintained a12-dmkits `08115206d99bf8417c99dff9a73f9005175ca7d7`; the Tier 1 gate passed, and cold review round two closed its sole first-round vacuity finding with a two-row bound-coordinate mutant. Wider token-group routes remain SG5 obligations. Error-field-locus binding and the unexplained split between parallel RNU diagnostics remain SG9 gaps; a12-dmkits remained clean at `89aa03957034de620562eb23a095d878f6547dca`.

<a id="active-unit"></a>
## Selected work

- `state`: blocked at the selected representation stop condition; no semantic implementation is retained.
- `gap`: [SG9 paths, indices, and static legality](SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion).
- `objective`: add the measured nonrepeatable-root `CurrentRepetition` constant-`1` condition through an exact checked representation; do not widen computation, repeatable-row lookup, filters, partial validation, arithmetic wrappers, or concrete parsing.
- `oracle`: maintained a12-dmkits [`CurrentRepetitionDiffTest.aNonRepeatableGroupHasTheConstantIndexOneOnAllThreeEngines`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/CurrentRepetitionDiffTest.kt) introduced at `feba4552110858b07966660bf7080441d3b90d00` and present at clean `89aa03957034de620562eb23a095d878f6547dca`; dynamic Groovy, generated Java, and the interpreter agree that guarded equality fires and guarded inequality does not.
- `next`: with owner approval, add a dedicated `ValidationConditionLeaf` containing the direct guard, ordinary same-root group, and closed equality/inequality tag; reuse existing presence, numeric verdict, connective, and reference owners without adding a second condition tree.
- `stop`: stop if the bounded constructor cannot enforce its direct filled guard without a parallel condition tree, if evaluation requires an invented repeatable binding, or if any change to computation authoring or the filter-only correlation owner becomes necessary.
- `blocked-on`: the public ordered-numeric carrier cannot enforce the guard or operator boundary: generic checked assembly admits guardless and wider-comparison instances. Recommendation: approve the exact validation leaf because its type preserves the measured conjunction while remaining composable through the existing tree.
- `consumer-probe-trigger`: none for this exact constant specialization; reassess Execute/Analyze only when condition-level repeatable row lookup closes as the reusable group-level value source.
- `resume`: `sed -n '220,430p' A12Kernel/Elaboration/ValidationCondition/Core.lean && sed -n '55,90p' A12Kernel/Elaboration/ValidationCondition/Assembly.lean`
