# Interpreter fixes from the corpus baseline

> **Status:** temporary upstream proposal, item IV-P7 of the [interpreter verification checklist](PLAN.md#interpreter-verification-checklist), carried to a12-dmkits by the owner under the [upstream engagement rule](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md#upstream-engagement-rule). Once a12-dmkits' handback is accepted, its durable facts move into their owners and this file is deleted.

## Request

The owner, as a12-dmkits' owner, asks a12-dmkits to fix the interpreter defects that this repository's classification (IV-P6) found in a12-dmkits' baseline table of kernel 31.3.1 against its interpreter, with one instrument correction, then to re-run the whole corpus and the power control. The code, the tests and the new table are a12-dmkits'; this repository supplies the defect list and checks the handback.

The work starts from a12-dmkits `9ece9d5e5f1d9b51160c6fd94a396575be0007c4`, the baseline's revision ([checkpoint](sources/cross-layer-routes.md#src-interpreter-baseline)), or a successor on `feature/q2`.

## How the defects were classified

Every call of the table that is not `ok`, 230 `diff`, 78 `unsupported` and 32 `raise`, and every `notRun` request was joined with the retained kernel 31.3.1 artifact of its request and with this repository's Lean replay of that request at the revision the owner's hand-off message pins. The retained artifacts match their tracked SHA-256 manifest, and the live kernel lines in the table equal them: 429 of the 430 kernel-side message lines (code, type, referenced and fill-to-fix sets) and all 65 kernel-side computed outcomes; the one exception is a hash-collision row whose retained artifact drops the row index. A disagreement is a **defect** below where the replay's verdict for that rule or computation is `match`, so Lean and the kernel agree and the interpreter differs. Under `validatePart` the replay compares the message, not its reference sets; a partial call's reference difference is decided by the kernel's retained partial messages and by Lean on the same row's full call.

The mechanism each group names is the spec clause Lean evaluates for it; isolating the cause inside the interpreter is part of each fix. Messages are paired per call by code, pointer and referenced set: a pair whose type differs, and with it usually fill-to-fix, is D2 or D3; a remaining pair of equal code and type whose pointers differ at most in row coordinates is D1, its reference sets naming different rows; an unpaired kernel message is D4, an unpaired interpreter message D6 under `validateFull` and D10 under `validatePart`. Kernel outcome lines are D5 when the kernel's value carries a `+` year and D4 otherwise. Where a message has two candidate partners the choice does not change the counts, and an unpaired kernel or interpreter message is D4, D6 or D10. Counts are calls and requests, then message pairs or lines; one call may belong to several groups.

## Defects to fix

| Group | Kernel and Lean | Interpreter | Calls / requests | Exemplar (request, row, call, code) | Spec |
|---|---|---|---|---|---|
| D1 keyed row choice | a selected row's references, pointer and fill-to-fix name the row the index-association cache selects, a later duplicate (`Rows[2]`, or `Rows[3]` in a third-row case) | names another row, mostly an earlier duplicate, in some pairs none | 66 / 21, 238 pairs | `date-validity-2026-10-06/request.json`, `duplicate`, `full`, `InvalidNumberComp` | [spec/08 §4.3 duplicate keys](../spec/08-paths-and-references.md#43-selected-references-in-validation-messages) |
| D2 omission typed as value | `OMISSION_ERROR` with fill-to-fix, on rows with empty, absent or over-limit repetitions, for example `full-then-empty-row`, `over-limit-only`, `no-rows`, `two-rows` and `invalid-row`'s empty second row | `VALUE_ERROR`, empty fill-to-fix | 44 / 14, 107 pairs | `below-star-group-runtime/request.json`, `full-then-empty-row`, `full`, `T1` | [spec/10 §3–§4](../spec/10-validation-and-polarity.md#3-every-fired-message-is-typed--value-vs-omission-) |
| D3 value typed as omission | `VALUE_ERROR`, empty fill-to-fix | `OMISSION_ERROR`, mostly with fill-to-fix, and an extra empty possible-cause alternative | 20 / 10, 23 pairs | `capacity-consumer-sweep/request.json`, `dup-in-capacity`, `full`, `NDVS1` | spec/10 §3–§4 |
| D4 temporal value from a keyed read | `Date(…)`, `Time(…)` and `MinValue` over `… For Key` operands compute their value and fire their rules; a month read from a day-unknown partial date fires its rule | a different outcome, mostly no value (`CLEARED`) where the kernel computes one, and no message | 47 / 6, 59 outcomes and 59 kernel-only messages | `date-components-2026-10-06/request.json`, `known`, `full`, `dateyearComp`; `temporal-row-placements-2026-10-24/request-k22t.json`, `d1`, `full`, `r5` | [spec/05 §3](../spec/05-dates-and-time.md#3-constructing-dates-and-checking-validity), [spec/08 §4](../spec/08-paths-and-references.md#4-rows-are-addressed-by-semantic-key-never-by-position-) |
| D5 errored year above 9999 | an errored DateTime outcome renders a five-digit year with a leading `+` | no `+` | 4 / 3, 6 outcomes | `datetime-errored-target-2026-10-02/request.json`, `e01-day-past-ceiling`, `full`, `DTA` | [spec/05 §3.1](../spec/05-dates-and-time.md#31-date) |
| D6 string expressions over a String with a formal finding | silent where `S` draws a length or charset finding (`a`, `abcdefg`, an emoji pair), on the fixed form and in `invalid-row`'s first row | fires `VALUE_ERROR` | 4 / 2, 28 interpreter-only messages | `string-expressions-2026-10-04/fixed/request.json`, `short-invalid`, `full`, `RangeSuffixPeerEq` | [spec/06 Part A](../spec/06-strings-and-enumerations.md#part-a--7-strings-and-patterns) |
| D10 partial message outside the relevant set | under `validatePart` with a key-only relevant set, no message | one message | 3 / 1 | `partial-carriers-2026-10-14/request.json`, `base-keyOnly`, `partial`, `k02` | [spec/10 §5](../spec/10-validation-and-polarity.md#5-full-vs-partial-validation) |
| D7 operand formal errors | the computation's formal errors in operands are the retained ones | additional `mandatoryField`, `uniqueIndex` and `zuGrosseKontextnummer` operand errors with their causes | 7 / 2, 92 lines | `over-limit-computation-target/request.seeded.json`, `seeded-in-capacity`, `full` | [spec/09 §5.1](../spec/09-computations.md#51-operand-reach-scope-the-level-walk-and-placement) |
| D8 power scale range | `POWER_SIGN` as one `VALUE_ERROR` with empty reference sets | raises `ArithmeticException` | 4 / 2 | a12-dmkits `test-data-generator/evidence/power-scale-2026-11-11/request-power-negative.json`, `scale-overflow`, `full` | [spec/04 §3](../spec/04-numbers-and-decimals.md#3-arithmetic-domain-failures-are-consumer-sensitive) |
| D9 undeclared locale | `validateFull` in a locale the model does not declare raises `IllegalArgumentException` before any rule | validates; any refusal satisfies the fix, and calls other than `validateFull` are unmeasured | 11 / 2 | `german-condition-language-terminals/request.json`, `feuert-auf-zeile-2-und-3`, `full` | not stated in spec |

Request paths are relative to `evidence/kernel-31.3.1/local/captures/` of the corpus extract, except D8's. D9 was measured on 2026-11-12 at the measurement checkout `505683610`: both `de_DE` requests raise on both kernel strategies under `en_US` and reproduce their retained artifacts under `de_DE`. Lean has no locale route, so D9 is kernel-decided alone.

## Reported, not gated

Lean does not model possible causes or rendered authored texts, so their lines are decided by the kernel alone. This request does not require fixing them; the handback reports what remains, for a later request:

- **K1, beside D1–D4 and D6.** 135 calls carry cause or authored-text lines beside their message disagreements. Many may resolve with the group they accompany.
- **K2, causes only.** 33 calls, 13 requests, disagree only in possible causes: on a duplicate, missing or unreached key the kernel's cause set leaves out the selected row's operand that the interpreter adds. Exemplar: `message-cache-topology-2026-10-10/request-selector.json`, `parent-ancestor-excluded`, `full`, `RefUnreached`.

## Instrument correction

The relation compares every request in `en_US`. Two corpus requests declare only `de_DE`, so the kernel refuses all eleven of their calls before any rule (D9), and nothing of their semantics is compared. `probeDifferential` compares a request whose model does not declare `en_US` in the request's own locale, red/green: `ProbeRequestDifferential.compare` reads the request's locale and passes it to the kernel calls in `DocumentDifferential.kt`, where `Locale.US` is hard-coded, and to every interpreter call, the support audit included, which today take the `en_US` default of `DmInterpreter` or of the public `Interpreter` (`InterpreterApi.kt`), the latter for the partial call without a clock and for the operand-error call.

A request whose model also declares `en_US`, such as `number-ingress-2026-10-13/request-de.json`, stays in `en_US`. This replaces IV-P1's and the `462e195f4` contract's fixed `en_US` for those requests only. D9 is then tested by its own red/green test alone, and any disagreement the two requests show in `de_DE` goes into the handback as an observation for this repository to classify, outside gate 2.

## Not requested

- **Declined rules (interpreter limits).** `unsupported` on 78 calls: `Valid`/`Invalid` over an undeclared type name (32 calls), `GroupFilled`/`GroupNotFilled` on a group beside a join or on the root group (30), `NumberOfValueInFields` over a keyed list (4), `AtLeastOneDateRangeOverlaps` over a keyed selection (11), and a custom field type (1). Lean decides every declined rule of the first four, so a later request can use them; widening the interpreter is not part of this one.
- **Agreements in kind.** Both sides raise on the two leap rows whose computation draws two diagnostics at one pointer ([KF541](../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf541)), and both refuse the documents of 15 calls that the kernel's reader rejects (`DocumentSerializationException` or `FaultException` against `DocumentInputError`).
- **Host-order boundary.** The three `message-cache-collision-2026-10-10` disagreements select among duplicates in one hash bucket, which [spec/08](../spec/08-paths-and-references.md#43-selected-references-in-validation-messages) leaves undecided; Lean reports them as a host-order boundary.
- **`notRun`.** 16 requests binding custom conditions or field types, which the relation refuses, and 6 whose model a consistency check refuses as their captures intend: 3 as `modelRefused` (`KernelRuntimeProbe.Refused`) and 3 as `refused` (`ConsistencyCheckFailedException`).

## Acceptance gates

1. **Red/green.** Each of D1–D10 and the instrument correction has a regression test that fails before its fix and passes after, built on the group's exemplar or a reduction of it.
2. **Corpus.** The corpus is re-run at the fix revision, or at a later revision whose interpreter sources (`interpreter/src`, `interpreter/build.gradle`, `shared-regex/src`) equal the fix revision's, under the table contract of a12-kernel-lean `462e195f4` that the baseline header names as `contractRevision`, with three changes:
   - `interpreter`: the unchanged-interpreter check (`gate3` in `scripts/typescript/interpreter-verification.ts`, and that contract's gate 3) no longer requires the diff against `d2ac4c039` to be empty; the header records the fix revision instead, and the checkout must still be clean before and after. When the run's revision R is later than the fix revision, the run checks that `git diff <fix> <R> -- interpreter/src interpreter/build.gradle shared-regex/src` is empty. The script's `contract` constant stays `462e195f4`, which selects the corpus. The support audit is the contract's procedure, run on the interpreter at the run's revision.
   - `locale`: the instrument correction above, and the header's single `locale` becomes a map from each request compared in a locale other than `en_US` to that locale.
   - `pass`: no call of D1–D8 or D10, the eight KF690 rows of [IV-P3](PLAN.md#interpreter-verification-checklist) included, keeps a `raise` or a `messages`, `outcomes`, `operand errors` or `operand causes` line; `causes` and `authored texts` lines may remain and are reported. D9's eleven calls are exempt, judged by D9's own test and reported as observations. Every other call keeps its baseline outcome or improves: a call `ok` at `9ece9d5e5` stays `ok`, and no call outside D1–D10 gains a line its baseline entry lacked.
3. **Consumers.** The test data generator's gates, and Q2-P9's and Q2-P10's, pass with their interpreter pin, the `interpreter` constant in `scripts/typescript/tdg-gates.ts`, moved to the fix revision; they may run at a later revision whose interpreter sources equal the fix revision's.

## Handback

The fix revision, each group's and the instrument correction's test names and the cause each fix removed, the two `de_DE` requests' disagreements as observations, the new table with its manifest and counts, the command as changed for gate 2, the remaining `causes` and `authored texts` lines by call, gate 3's commands and results, and any group a12-dmkits declines with its reason. A disagreement that looks like a kernel or Lean error goes into the handback as an observation, not as a fix.

## Excluded

Lean-proved laws as interpreter properties, which wait for this handback; the declined rules above; the channels the comparison names as not compared; the kernel's generated-Java strategy.
