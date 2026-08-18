# Active implementation plan

This is the resumption checkpoint, not a work log. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

**Verified semantic baseline, 2026-08-18:** recursive fixed-group token `FirstFilledValue` is closed at `894f32fedd1900fff6ff2cf9021a7b2e7af3b0ec` against maintained a12-dmkits `08115206d99bf8417c99dff9a73f9005175ca7d7`. The exact guarded nonrepeatable-root `CurrentRepetition` specialization is closed at `e4aa22ba41adde1a1e3058fed9a156b11bcd9ffc` against a12-dmkits `feba4552110858b07966660bf7080441d3b90d00`; its Tier 1 gate and converged cold review passed. Same-group repeatable `CurrentRepetition` validation is closed in the current semantic baseline against the maintained source batch recorded in [`SOURCES.md`](SOURCES.md#src-current-repetition-repeatable-condition). Wider token-group routes remain SG5 obligations. Error-field-locus binding, captured `CurrentRepetition`, and the unexplained split between parallel RNU diagnostics remain SG9 gaps; a12-dmkits remained clean at `89aa03957034de620562eb23a095d878f6547dca`.

<a id="active-unit"></a>
## Selected work

- `state`: ready for bounded route discovery; no computation representation choice is assumed.
- `gap`: [SG4 computation scheduling and state transition](SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition), with the remaining source-domain breadth also tracked by [SG9](SEMANTICS-GAPS.md#sg9--paths-indices-and-static-legality-completion).
- `objective`: determine the smallest checked computation representation and red-test rung for the maintained `CurrentRepetition(/Shipment/Lines) > 0` common precondition; retain the row coordinate as a structural dependency while the actual `First → Second` field dependency remains ordered, without widening to other bounds/operators, multiple rows, captured `$`, partial computation, parser lowering, or a generic computation expression surface.
- `oracle`: the exact three-engine checkpoint and limits are owned by [`SOURCES.md`](SOURCES.md#src-current-repetition-computation-dependency).
- `next`: inventory `ComputationCondition`, repeatable Number table/plan activation, structural dependency projection, and the selected environment boundary; determine whether validation's model-owned group-coordinate mechanism can be extracted as the shared second consumer without reopening unrelated scheduling.
- `stop`: stop before implementation if the route would make every field in the group a dependency, require a scheduler rewrite, expose unmeasured operators or bounds, conflate current with captured environments, or duplicate the condition/expression tree. Record the exact blocker and recommend the narrowest type boundary.
- `blocked-on`: none during route discovery.
- `consumer-probe-trigger`: after this computation source closes and the validation/computation users share one checked group-coordinate owner, run one bounded Execute/Analyze transport probe; add an SMT/Verify probe only if its selected decision procedure consumes this arithmetic constraint rather than merely replaying examples.
- `resume`: `rg -n "ComputationCondition|commonPrecondition|structural.*depend|dependency|outer : Env|CurrentRepetition" A12Kernel/Elaboration A12Kernel/Semantics A12Kernel/Proofs A12Kernel/Conformance`
