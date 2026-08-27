# Explain consumer lab

- `status`: green
- `contract`: checked execution, proof, or change becomes a structured human account whose factual claims and limits are machine-checkable where practical.
- `authority`: [checked direct-field formal-input inventory](../../A12Kernel/Elaboration/ComputationFormalInput.lean), exact projection proofs for [Time construction](../../A12Kernel/Proofs/AddressedTimeConstructionFormalInput.lean), [`DateFromDateTime`](../../A12Kernel/Proofs/AddressedDateFromDateTimeFormalInput.lean), [Enumeration](../../A12Kernel/Proofs/AddressedEnumerationFormalInput.lean), and [DateTime day shift](../../A12Kernel/Proofs/AddressedDateTimeDayShiftComputation.lean), plus the source-first DateTime day-shift observation and exact-address result/application owners used by the [Execute lab](EXECUTE.md).
- `handover`: canonical clauses and the bounded capability record; prose style is not a Lean property.

## First probe

Produce a structured trace for three rows: formal source with malformed amount, absent source with malformed amount, and absent source with valid amount. The trace must name static dependencies separately from runtime reads, the first poison cause, exact addresses, result partition, and excluded later stages.

Lean acceptance checks the structured event and outcome fields. A human review checks whether the explanation is understandable without adding unsupported causality. Wrong accounts are eager dependency reads, conflating formal inventory with runtime trace, inventing a message from poison, and omitting insufficient-information boundaries.

## Cross-family formal-input probe

Explain the eager direct-field inventory for one nested Number-backed `Time(...)`, one root-source `DateFromDateTime` fanning out to two target rows, and direct-field versus literal addressed Enumeration. The artifact must preserve exact root, enclosing, and leaf placements; distinguish one static source placement from repeated runtime reads; keep a fieldless literal inventory empty; exclude computed targets and unrelated fields; and name the Time, FullDate, and String-shaped result channels separately.

Lean acceptance checks each exact placement, cause, exclusion, and result projection. Wrong accounts are per-read duplication, whole-document collection, leaf-normalized placement, automatic global abort or eager poison, invented rendered messages, and an unnamed result carrier shared across families. Group containment, generated preliminary findings, multi-operation union, scheduling, public shipment, and Kernel correspondence remain excluded.

## Lab record

| Run | Status | Cost | Current result |
|---|---|---:|---|
| `explain-source-first-01` | green | about 13 minutes | The cold reader produced exact addresses, ordered static dependencies, an eager static formal inventory, source-first runtime events, first-poison and clean no-value causes, conditional result partitions, and explicit apply/validation exclusions. All four wrong accounts were killed. The checked direct-field owner retains the runtime-hidden malformed amount and formal source at their exact addresses, excludes computed and unrelated fields, and the trusted projection theorem places that inventory exactly in `formalErrorsInOperands`, so root reconciliation certifies the complete bounded artifact. |
| `explain-cross-family-inputs-02` | green | about 8 minutes; 45-line artifact; no dependencies | A cold reader recovered all three nested Time placements, one root FullDate placement despite two reads, one root direct-Enumeration placement despite two reads, an empty literal-Enumeration inventory, computed/unrelated exclusion, and the three distinct result-family channels. Root reconciliation against the focused locks and registered projection theorems killed all six wrong accounts; the reader made no guesses and reported no semantic question. |

## Conclusion

The bounded Explain task is cheap and useful, and its static-versus-runtime distinction now transports without renewed archaeology across DateTime day shift, nested Time construction, FullDate extraction, and String-shaped direct/literal Enumeration. These green results cover checked direct field dependencies and a fieldless literal only. Group containment, generated index and preliminary findings, rendered messages, multi-operation union, scheduling, general whole-model formal checking, public shipment, and Kernel correspondence remain outside the probes.
