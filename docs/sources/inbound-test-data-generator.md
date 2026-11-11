# Inbound test data generator handbacks

[Source registry](../SOURCES.md) owns authority and drill routing. Handbacks from a12-dmkits' test data generator work on Q2 ([plan](../PLAN.md#q2-preparation-checklist)), each with its reviewed revision and claim limits; earlier handbacks stay in [the general shard](inbound-handbacks.md).

<a id="src-inbound-2026-11-11a"></a>
## Reviewed the 2026-11-11a Q2 progress handback: retained Number text keeps its length, is read by amount and counts every digit

- `source`: Peer handback `a12-kernel-lean-spec-corrections-2026-11-11a.md`, carried by the owner and kept as no file, answering Q2's retained-Number question; a progress handback, not Q2-P7's terminal one.
- `revision`: a12-dmkits `79a7171c873d8ed44767dac8411de2dd7960336e` on `feature/q2`, read with `git` only, with `933832ae0` and `6c78c7d8d` ancestors; KF686, KF687 and the `number-length-2026-11-11`, `retained-number-2026-11-11` and `retained-number-caps-2026-11-11` captures under `test-data-generator/evidence/` exist there, each recording dmtool 0.16.0, kernel 31.3.1 and a clean producer.
- `oracle`: kernel 31.3.1, both strategies, through `:adapter:kernelProbe` on the peer's own-domain models; read here from the committed artifacts, not rerun.
- `review`: A HIGH reconciliation on 2026-11-11 read every row's request document and both strategies' codes: on a two-place field allowing leading zeros, `"001.20"` meets a six-character minimum that native `1.20`, native `1.2000` and quoted `"1.20"` miss with `zahlZuKurz`, and a rule `[Weight] != 1.2` stays silent on it while its 1.3 twin fires; on an integer field of amount 1, retained `000000000000001` is admitted and `0000000000000001` reports `stelligkeitZuLang`, and under an integer-digit cap of 2 `01` is admitted and `001` reports `zahlZuvieleVorkommastellen`, which a cap of 3 admits. Lean's cascade agreed on every row before any change; [`NumberLengthLocks`](../../A12Kernel/Reference/Dm/NumberLengthLocks.lean) now locks the length and cap rows, while the rule row rests on the capture, Lean's own rule over retained text being only its unmeasured `0012` case.
- `limit`: signs, fractional parts, zero magnitude and the amount trait's cap on retained text are not varied against the caps.
- `adopted`: [spec/04 §4.8](../../spec/04-numbers-and-decimals.md#48-the-formal-check-of-a-stored-value) states the measured rows; [Q2-P1](../PLAN.md#q2-preparation-checklist)'s sample form admits retained text.
- `sync`: no ledger entry; the clause already held and the peer's evidence measures it.
