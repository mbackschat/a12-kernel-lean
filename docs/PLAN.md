# Active implementation plan

This is the resumption checkpoint, not a work log. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

**Verified semantic baseline, 2026-08-18:** recursive fixed-group token `FirstFilledValue` is closed at `894f32fedd1900fff6ff2cf9021a7b2e7af3b0ec` against maintained a12-dmkits `08115206d99bf8417c99dff9a73f9005175ca7d7`; the Tier 1 gate passed, and cold review round two closed its sole first-round vacuity finding with a two-row bound-coordinate mutant. The exact guarded nonrepeatable-root `CurrentRepetition` specialization is closed in the current semantic baseline against a12-dmkits `feba4552110858b07966660bf7080441d3b90d00`. Wider token-group routes remain SG5 obligations. Error-field-locus binding, repeatable `CurrentRepetition`, and the unexplained split between parallel RNU diagnostics remain SG9 gaps; a12-dmkits remained clean at `89aa03957034de620562eb23a095d878f6547dca`.

<a id="active-unit"></a>
## Selected work

- `state`: ready for bounded route discovery; no representation choice is assumed.
- `gap`: [SG9 paths, indices, and static legality](SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion).
- `objective`: determine the smallest checked representation and red-test rung for the maintained same-group repeatable `CurrentRepetition` validation rows; preserve the direct filled-field guard, row-local index, comparison operator, and VALUE polarity without widening into captured-outer correlation, computation, filters, partial validation, arithmetic wrappers, or parsing.
- `oracle`: maintained a12-dmkits [`CurrentRepetitionDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/CurrentRepetitionDiffTest.kt), present at clean `89aa03957034de620562eb23a095d878f6547dca`, distinguishes rows 1/2/3 under `> 1`, `> 2`, and `>= 1`, including malformed firing and non-firing rows, across the real kernel and interpreter.
- `next`: inventory the checked validation iteration plan, addressed evaluation context, numeric comparison owners, and existing `Having`-only repetition resolver; identify whether the row coordinate can be exposed as one reusable resolved group value without admitting an unbound or guardless condition.
- `stop`: stop before implementation if the smallest carrier would admit `CurrentRepetition` without a bound same-group row, erase the direct guard, conflate current and captured environments, or require a second condition tree or a public computation/filter surface. Record the exact blocker and recommend the narrowest type boundary.
- `blocked-on`: none during route discovery.
- `consumer-probe-trigger`: none for this exact constant specialization; reassess Execute/Analyze only when condition-level repeatable row lookup closes as the reusable group-level value source.
- `resume`: `rg -n "ordinaryIterationScope|evalAddressed|CurrentRepetition|currentRepetition" A12Kernel/Elaboration A12Kernel/Semantics A12Kernel/Proofs A12Kernel/Conformance`
