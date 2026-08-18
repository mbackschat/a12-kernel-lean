# Active implementation plan

This is the resumption checkpoint, not a work log. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

**Verified semantic baseline, 2026-08-18:** inbound static-admission corrections are reconciled at `bfa600284dbe639c10bd894553783db546b89479`; the fixed-group and starred-group `FirstFilledValue` order/polarity entries are accepted and Kernel-locked at `1c2bb7a5761e55399d6af94fd6e8992be5d40af1` against reviewed a12-dmkits `08115206d99bf8417c99dff9a73f9005175ca7d7`. The semantic Tier 1 gate and both frozen cold reviews passed. Error-field-locus binding and the unexplained split between parallel RNU diagnostics remain explicit SG9 gaps; a12-dmkits remained clean at `89aa03957034de620562eb23a095d878f6547dca`.

<a id="active-unit"></a>
## Selected work

- `state`: active under the owner's autonomous run-till-blocker instruction.
- `gap`: [SG5 Number and token group runtime](SEMANTICS-GAPS.md#gap-sg5-number-token-group-runtime).
- `objective`: execute a sole fixed token-group `FirstFilledValue` through its complete recursive checked-document expansion, including nested repeatable rows, without widening partial validation, computation, raw-`Document`, omitted-tail, or mixed-list routes.
- `oracle`: maintained a12-dmkits [`FirstFilledValueGroupOperandDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/FirstFilledValueGroupOperandDiffTest.kt) at `08115206d99bf8417c99dff9a73f9005175ca7d7`; its nested-row-2 and direct-before-nested separators run on both kernel strategies and the interpreter.
- `next`: add red checked-document cases for a value only in nested row 2 and for direct-before-nested encounter order, then remove only the fixed-group nonrepeatability restriction and reuse the existing declaration-major group resolver and generic first-filled evaluator.
- `stop`: stop if the capsule requires a second resolver, a raw-document topology inference, a new result domain, an unmeasured omitted-tail rule, or support for another authored operand shape.
- `blocked-on`: none.
- `consumer-probe-trigger`: assess an Execute probe after this recursive fixed-group capability closes; run an SMT/Verify probe only if the capsule produces a new stable proof-bearing relation rather than merely specializing the existing scan laws.
- `resume`: `sed -n '145,220p' A12Kernel/Elaboration/TokenFirstFilledValue.lean`
