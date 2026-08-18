# Active implementation plan

This is the resumption checkpoint, not a work log. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

**Verified semantic baseline, 2026-08-18:** inbound static-admission corrections are reconciled at `bfa600284dbe639c10bd894553783db546b89479`; the fixed-group and starred-group `FirstFilledValue` order/polarity entries are accepted and Kernel-locked at `1c2bb7a5761e55399d6af94fd6e8992be5d40af1` against reviewed a12-dmkits `08115206d99bf8417c99dff9a73f9005175ca7d7`. The semantic Tier 1 gate and both frozen cold reviews passed. Error-field-locus binding and the unexplained split between parallel RNU diagnostics remain explicit SG9 gaps; a12-dmkits remained clean at `89aa03957034de620562eb23a095d878f6547dca`.

<a id="active-unit"></a>
## Selected work

- `state`: paused by owner; both outbound semantic handbacks and the separate Bash fix have been consumed.
- `gap`: none selected while paused.
- `objective`: no active implementation unit.
- `next`: when the owner resumes work, select the next semantic capsule from the live gaps; no cross-project handback is pending.
- `stop`: do not begin another semantic capsule or consumer probe while paused.
- `blocked-on`: none.
- `consumer-probe-trigger`: the existing bounded diagnostic consumer covers Translate/Explain for the mapped static classes. Run an interpreter/Execute probe only after a reusable runtime family closes, and run an SMT/Verify probe only after a stable proof-bearing relation needs transport; neither is triggered now.
- `resume`: ``rg -n '^### SG|^#### |^- `state`: open' docs/SEMANTICS-GAPS.md``
