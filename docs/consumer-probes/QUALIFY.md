# Qualify consumer lab

- `status`: green
- `contract`: a candidate implementation and pinned semantic profile produce agreement, detected divergence, or explicit unsupported status under finite qualification.
- `authority`: the exact addressed DateTime outcomes and result/application partitions in the [Lean conformance owner](../../A12Kernel/Conformance/AddressedDateTimeDayShiftComputation.lean).
- `candidate`: the disposable Python consumer from the matching [Execute lab](EXECUTE.md).

## Probe

The consumer's natural tests were run against four individually planted wrong accounts: elapsed 24-hour shifting, terminal-coordinate address flattening, eager amount poison before a formal source, and destination-relative change classification. Each mutant had to fail an existing natural assertion, then restoration had to recover the original source digest and green suite.

| Run | Status | Cost | Result |
|---|---|---:|---|
| `qualify-datetime-day-01` | red | included in the first Execute run | All four intended mutants were killed, but the natural baseline itself disagreed with Lean, proving mutation sensitivity cannot certify semantic correctness. |
| `qualify-datetime-day-02` | green | 76 mutation-runner lines beyond the candidate and tests | Five natural tests passed, every mutant was killed independently, restoration matched the baseline digest, and authoritative outputs agreed with Lean. |

## Conclusion

Finite mutation qualification is cheap and useful for testing whether a suite guards named semantic seams. It qualifies only the executed profile and cannot replace Lean reconciliation, Kernel evidence, or universal proof.
