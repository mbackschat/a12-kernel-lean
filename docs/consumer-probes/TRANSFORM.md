# Transform consumer lab

- `status`: green
- `contract`: a checked A12 artifact becomes another checked A12 artifact under an explicitly named observation relation and preconditions.
- `authority`: [addressed numeric-operation consumer laws](../../A12Kernel/Proofs/AddressedNumericOperationConsumer.lean), especially universal identity preservation of Analyze, Execute, and rich result views.
- `authority`: the fixed [Boolean/Confirm constant definition and result/application laws](../../A12Kernel/Proofs/BooleanConstantComputation.lean), exact [execution cases](../../A12Kernel/Conformance/BooleanConstantComputation.lean), and the shared [Boolean result/application owner](../../A12Kernel/Elaboration/BooleanComputationResult.lean).
- `handover`: the [bounded numeric-operation capability](../implementation/numeric.md#cap-addressed-numeric-operation-consumer), the [fixed Boolean/Confirm constant capability](../implementation/computations.md#cap-boolean-confirm-constant-computation-target-admission), and their explicit rule that fingerprint difference is not semantic inequivalence.

## First probe

Implement the exact identity Transform over one checked addressed numeric operation and validate its structural fingerprint. Then reject a tempting nonidentity rewrite that changes operation parameters while retaining source and target fields. The point is to experience the difference between producing a plausible rewrite and carrying a preservation relation.

Lean acceptance is universal identity preservation from the existing theorems plus one checked parameter-change counterexample. Wrong accounts are dependency-only identity, derived-scale-only identity, fingerprint equality as general equivalence, and finite example agreement as a universal preservation claim.

## Fixed Boolean declaration-relocation probe

Relocate only the authored declaration group of fixed Boolean `true`, Boolean `false`, and Confirm `true` constants between two valid fixed groups. Certify the exact `fixedBooleanConstantRuntimeProjection`, which covers execution, every public result channel, source-relative change classification, and separate-destination application while explicitly excluding checked-definition equality. Refuse changed payloads, targets, repeatable placement, malformed declaration paths, Confirm `false`, and a complete-definition equality claim without asserting semantic inequivalence.

Lean acceptance composes the existing checked execution, result, and application owners. A disposable theorem establishes projection and application equality for all checked source and destination documents across the three exact relocations, while a second theorem checks every normalized Boolean target-state branch for both values. An independent standard-library reconciliation fixes the exact 75-case signature. Wrong accounts are declaration-group iteration, destination-relative classification, applying source-identical results, incomplete structural identity, repeatable or malformed-path admission, Confirm `false`, and complete-definition equality.

## Addressed extremum fingerprint probe

Certify A1→A1 for one warning-suppressed addressed division extremum and return `not-certified` for division→power, operand reversal, and suppression change. The complete fingerprint includes the full operation identity, ordered field dependencies, target declaration, derived scale/capability summary, and warning suppression. A difference is only a refusal to certify under exact identity, never a semantic-inequivalence claim.

The accepted isolated consumer retained division and power as distinct identities, kept field order, and distinguished the suppression-only A4→A5 pair. Root independently killed both dependency-only and derived-scale-only certifiers as well as the generic-binary and ignored-suppression accounts while preserving the natural digest.

<a id="task-rule-negation"></a>
## Rule negation probe

Given an English condition text, produce the condition that fires exactly where the original is decided false, as Kernel-language text, or refuse it naming the predicate that has no complement. The handover is the [negation use case](../USE-CASES.md#cross-category-use-case-negation), the [rule-negation capability record](../implementation/validation-messages-and-custom.md#cap-rule-negation), and the [concrete syntax](../../spec/12-concrete-syntax.md) for reading and printing; the consumer receives no Lean source, no Kernel, and no expected output.

The fixture is the 33 inputs below. Lean acceptance parses each answer with `parseText`, requires the tree to equal the Lean `negateText` result up to parentheses that change no grouping and regrouping within one connective, and requires each refusal to name the predicate Lean refuses. The probe is green when all 33 agree and every wrong account below is killed by at least one named input.

| id | input |
|---|---|
| `N01` | `FieldFilled(Amount)` |
| `N02` | `FieldNotFilled(/Order/Lines*/Price)` |
| `N03` | `[Amount] > 100` |
| `N04` | `[Amount] < 0 And [Total] >= 10` |
| `N05` | `[Code] == "A" Or [Code] != "B"` |
| `N06` | `FieldFilled(A) And (FieldFilled(B) Or [C] <= 3)` |
| `N07` | `AllFieldsFilled(A, B, C)` |
| `N08` | `NotAllFieldsFilled(Rows*/R)` |
| `N09` | `AtLeastOneFieldFilled(A, Rows*/R, Detail)` |
| `N10` | `NoFieldFilled(A, B)` |
| `N11` | `FieldsNotCollectivelyFilled(A, B, C)` |
| `N12` | `FieldFilled(X) Or FieldsNotCollectivelyFilled(A, B)` |
| `N13` | `MoreThanOneFieldFilled(A, B, C)` |
| `N14` | `NotExactlyOneFieldFilled(A, B, C) And FieldFilled(D)` |
| `N15` | `GroupFilled(Address)` |
| `N16` | `AllGroupsFilled(G, H) Or NoGroupFilled(G, H)` |
| `N17` | `GroupsNotCollectivelyFilled(G, H)` |
| `N18` | `[Name] PatternMatched "[A-Z]+"` |
| `N19` | `FieldValueIncludedInValueList(Kind, "AB", "CD")` |
| `N20` | `AtLeastOneFieldValueIncludedInValueList(A, B In "x", "y")` |
| `N21` | `NoFieldValueIncludedInValueList(Rows*/Tag In "x")` |
| `N22` | `Valid(Iban, "IBAN")` |
| `N23` | `NumberOfFilledFields(A, B) == 1` |
| `N24` | `Sum(Rows*/Amount) > [Limit] And FieldFilled(Limit)` |
| `N25` | `FieldValuesNotUnique(A, B)` |
| `N26` | `[A] DiffersWithToleranceRange2 [B]` |
| `N27` | `FieldFilled(A) And DateRangesOverlap(P1, P2)` |
| `N28` | `CustomCondition CheckIt` |
| `N29` | `Valid(Date(D, M, Y)) Or FieldNotFilled(D)` |
| `N30` | `RepetitionNotUnique(A, B @From Rows)` |
| `N31` | `@SuppressWarning(MVK_INVALID_COMPARE_DEC_PLACES) [Rate] == 1.50` |
| `N32` | `(FieldFilled(A) Or FieldFilled(B)) And (FieldNotFilled(C) Or [D] > 2)` |
| `N33` | `FieldValuesNotUnique(A, B) Or CustomCondition CheckIt` |

Wrong accounts and the inputs that kill them: connectives kept rather than dualized (`N04`, `N06`, `N16`); `<` flipped to `>` (`N04`); a parenthesis dropped where the result would mix `And` and `Or` (`N06`, `N12`, `N32`); a complement invented for `FieldValuesNotUnique`, a tolerance comparison, `DateRangesOverlap` or `CustomCondition` (`N25` to `N28`); `Valid(Field, "Type")` negated to `Invalid` (`N22`); `FieldsNotCollectivelyFilled` given a single-predicate complement (`N11`, `N12`, `N17`); `MoreThanOneFieldFilled` or `NotExactlyOneFieldFilled` complemented by anything other than the stated count comparison (`N13`, `N14`); an `In` list or the suppression preamble dropped (`N20`, `N21`, `N31`); a complement invented for `RepetitionNotUnique` (`N30`); a refusal named by any leaf but the leftmost (`N33`); a guard conjunct kept un-negated, as a guarded pair would (`N14`, `N24`, `N29`).

Excluded: German spellings, whose complements the [keyword catalog](../../spec/12-concrete-syntax.md#5-keyword-catalog-english--german-verified-pairs) does not list; static legality, including the iteration-guard refusal; the negated rule's message, polarity and evaluation; Kernel correspondence beyond what the capability record cites.

## Lab record

| Run | Status | Current result |
|---|---|---|
| `transform-numeric-identity-01` | green | A cold standard-library consumer certified only an exact `RangeAsNumber(source, 1, 4)` identity and returned `not-certified` for an endpoint change, a Round-mode change, and ordered `Min` operand reversal. Dependency-only identity, derived-scale-only identity, mismatch-as-inequivalence, and finite-agreement-as-universal mutations were all killed. The Lean laws universally preserve Analyze, execution, and rich-result views for exact identity; conformance retains every changed parameter while making no inequivalence claim. The disposable artifact, implementation, and tests totaled 312 nonblank lines, took 148 seconds, and added no dependency or nonidentity semantic guess. |
| `transform-boolean-declaration-relocation-02` | green | A fresh isolated standard-library consumer used 289 implementation and 480 artifact/test/report nonblank lines, all capability-local, in about 307 seconds. It certified the three exact declaration relocations under `fixedBooleanConstantRuntimeProjection`, rejected seven structural or claim controls, and retained unequal definition identity. All 75 source/destination state comparisons agreed; an independent checker reproduced digest `91a53728ebbc84564f033a4e3e71ae220e456476e29d2d3ddd1b4d3e19e6caab`, and final disposable Lean witnesses compiled in 4.9 seconds. Nine tests passed and all ten wrong accounts failed with no dependency, semantic question, or guess. Repeatable relocation, wider operations, generated validation, scheduling, materialized topology, Kernel runtime correspondence, protocol, shipment, compatibility, and inequivalence of refused transforms remain outside. |
| `transform-extremum-domain-03` | green after corrected handover | Exact fingerprint identity certified only A1→A1; A1→A2, A1→A3, and A4→A5 remained `not-certified` without an inequivalence claim. Eleven natural tests passed, root reproduced digest `c1349a7330c9cbaaf4099fb335a801fad2cf99889b4b5f53cedb678b53c4b9e4`, and all eleven combined wrong accounts failed, including dependencies-only and scale-only certification. Wider rewrites, equivalence, recursive expressions, protocol, shipment, compatibility, and Kernel correspondence remain outside. |

<a id="run-transform-rule-negation-04"></a>
### Rule negation — `transform-rule-negation-04`

- `task`: [Rule negation probe](#task-rule-negation), in its first, 32-input revision.
- `status`: amber
- `started-at`: 2026-10-02T18:25:08+02:00
- `finished-at`: 2026-10-02T18:27:58+02:00
- `duration-seconds`: 170
- `semantic-basis`: `6f557ba962fe8b387a0ab62cb453db4e036328ce`
- `oracle`: the Lean `negateText` result per input, compared after `parseText` up to grouping-only parentheses and same-connective regrouping, refusals by predicate name; reconciliation passed on all 32 inputs.
- `consumer-access`: a fresh agent given only the task, the negation use case, the capability record and spec/12, with no repository, Lean source, Kernel, network or dependency access; it wrote Python 3 with the standard library.
- `cost`: 352 implementation and 29 test nonblank lines, all capability-local.
- `result`: all 32 answers agreed with Lean, 25 negations and seven refusals.
- `wrong-accounts`: every pre-registered account was killed by a mutant at its named input.
- `questions-and-guesses`: the capability record named the group-form and value-list pairs without spelling them, and the consumer guessed all four correctly; it also asked which leaf names a refusal when several refuse, and noted that `@From` is documented only on `RepetitionNotUnique`. The record now spells every pair, states the refusal order and the `@From` scope, and the task replaced `N30` and added `N33`.
- `exclusions`: German spellings, static legality, messages, polarity, evaluation, and Kernel correspondence beyond the record's citations.

<a id="run-transform-rule-negation-05"></a>
### Rule negation — `transform-rule-negation-05`

- `task`: [Rule negation probe](#task-rule-negation), 33 inputs.
- `status`: green
- `started-at`: 2026-10-02T18:30:54+02:00
- `finished-at`: 2026-10-02T18:34:08+02:00
- `duration-seconds`: 194
- `semantic-basis`: `151cfb48d2e8963b441ec30ee64454b61b20e841`
- `oracle`: the Lean `negateText` result per input, compared as in [`transform-rule-negation-04`](#run-transform-rule-negation-04); reconciliation passed on all 33 inputs.
- `consumer-access`: a fresh agent, isolated as in the previous run, with the corrected handover.
- `cost`: 326 implementation and 33 test nonblank lines, all capability-local; the finish time is when the result was read, after a concurrent build, and the agent itself reported 144 seconds.
- `result`: all 33 answers agreed with Lean, 23 negations and ten refusals, `N33` naming its leftmost refusal.
- `wrong-accounts`: all eleven pre-registered accounts were killed by a mutant at a named input.
- `questions-and-guesses`: none affected a fixture answer. The consumer noted that spec/12's keyword catalog is a sample, so no complete predicate inventory exists to tell a predicate such as `DateRangesOverlap` from a name, and that spec/12 showed only the parenthesised value list, which spec/12 now aligns with spec/06's bare form.
- `exclusions`: German spellings, static legality, messages, polarity, evaluation, and Kernel correspondence beyond the record's citations.
