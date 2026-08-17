# Active implementation plan

This is the resumption checkpoint, not a work log. Detailed coverage belongs in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open semantic obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), durable conclusions in [`LEAN-FINDINGS.md`](LEAN-FINDINGS.md), and completed work in Git plus the [July 2026 work log](archived/SEMANTIC-WORK-LOG-2026-07.md).

## Verified baseline

**Verified semantic baseline, 2026-08-18:** inbound static-admission corrections are reconciled at `bfa600284dbe639c10bd894553783db546b89479`: shared entity-list duplicates follow authored encounter order, group-list/count root classes are mapped after overlap, and three RNU missing-repeatable shapes collapse. Error-field-locus binding and the unexplained split between parallel RNU diagnostics remain explicit SG9 gaps. The complete Tier 1 gate and a frozen A–L cold review passed; a12-dmkits remained clean at `086030e200e8f0d5d13a9eb6638424ad7dc8373a`.

<a id="active-unit"></a>
## Selected work

- `state`: paused by owner after the outbound handoffs below are delivered.
- `gap`: none selected while paused.
- `objective`: no active implementation unit.
- `next`: consume the reviewed a12-dmkits handback for pending [`SPEC-2026-08-17-02`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-08-17-02) and [`SPEC-2026-08-17-03`](A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-08-17-03); separately consume any fix returned for the macOS Bash 3.2 empty-array failure in `scripts/rehearse-interpreter-release.sh`. If neither handback exists when work resumes, select the next semantic capsule from the live gaps.
- `stop`: do not begin another semantic capsule or consumer probe while paused.
- `blocked-on`: none.
- `consumer-probe-trigger`: the existing bounded diagnostic consumer covers Translate/Explain for the mapped static classes. Run an interpreter/Execute probe only after a reusable runtime family closes, and run an SMT/Verify probe only after a stable proof-bearing relation needs transport; neither is triggered now.
- `resume`: `rg -n -A 18 '^### SPEC-2026-08-17-0[23]' docs/A12-DMKITS-SPEC-SYNC-LEDGER.md`
