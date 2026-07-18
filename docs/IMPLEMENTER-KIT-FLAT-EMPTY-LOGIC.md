# Independent implementer kit: flat empty handling and verdict logic

**Status:** frozen reference-semantics 0.2.0 cold-handover spike with a complete source-side mutation replay and checker-accepted isolated downstream qualification record, not a release-readiness claim or the current 0.3.0 shipment. `flat-validation-empty-logic-v1` packages eight retained kernel 30.8.1 runtime observations around empty Number, Boolean, and Confirm comparisons, the independent all-empty-row gate, malformed input, strong-Kleene `And`/`Or`, and VALUE/OMISSION polarity. The exact four-state verdicts are the historical Lean semantics-of-record for this capability; retained external output directly establishes authored firing and polarity when the authored message fires, but authored silence cannot reveal whether the kernel's hidden condition result was `notFired` or `unknown`. The limits are classified case by case below.

## Compatibility identity

| Item | Value |
|---|---|
| Capability | `flat-validation-empty-logic-v1` |
| Operation | `flatValidation.evaluateFull` |
| Reference semantics | `0.2.0` |
| Protocol | `1` |
| Manifest schema | `2` |
| Kernel behavior | `30.8.1` |
| Owning language sections | `§1` truth and verdict algebra, `§2` empty values and row eligibility, `§3` formal invalidity, `§12` validation polarity |
| Observable compatibility result | `notFired`, `fired.value`, `fired.omission`, or `unknown` |
| External evidence scope | Eight finite runtime observations; focused authored-message firing and polarity, not hidden kernel truth |

Pin these identifiers together. Passing this capability does not establish conformance to another semantics version or to the rest of the flat operation advertised by the development manifest. Current [`flat-validation-empty-logic-v2.conformance.json`](../reference/flat-validation-empty-logic-v2.conformance.json) belongs to reference semantics 0.3.0, preserves this suite's eight cases, and adds the directional Number witness; it does not retroactively change this kit or its completed Rust claims.

## Purpose and boundary

This is the deliberately small first cold-implementation exercise for a downstream interpreter. It is complex enough to expose A12-specific choices that an ordinary two-valued evaluator gets wrong, but it avoids repetition, `$` correlation, arithmetic, and general path resolution. An isolated implementer should be able to recover the complete decision procedure for the eight cases without inspecting Lean source, the kernel, a12-dmkits, or private conversation history.

The capability starts from normalized, already classified scalar cells. It does not parse EN/DE condition text or locale-sensitive raw field text. The normalized request still carries an expanded field model, absolute field paths, sparse cells, and the authoritative `hasContent` bit because those distinctions are needed to run the cases through the public process contract.

This is a finite semantic slice of `flatValidation.evaluateFull`, not a declaration that all accepted inputs of that wider development operation are research-closed. An implementation may share code with a larger flat evaluator, but its candidate qualification record must claim only this named suite.

## Exact handover material

The cold implementer receives an immutable bundle containing only these artifacts:

- this language-neutral capsule;
- the flat-operation wire contract in [`PROTOCOL.md`](PROTOCOL.md), especially the common request envelope, flat structured paths and conditions, sparse cells and row gate, and shared response contract;
- the generated flat-operation support declaration in [`supported-fragment-v1.json`](../reference/supported-fragment-v1.json);
- the generated machine-readable capability descriptor [`flat-validation-empty-logic-v1.capability.json`](../reference/flat-validation-empty-logic-v1.capability.json);
- the language-neutral eight-case suite [`flat-validation-empty-logic-v1.conformance.json`](../reference/flat-validation-empty-logic-v1.conformance.json);
- every request and expected response referenced by that suite under [`examples/reference-cli/`](../examples/reference-cli/);
- the typed retained projection [`projection.json`](../evidence/kernel-30.8.1/projection.json) and the eight retained case artifacts linked in the [evidence map](#evidence-to-decision-map);
- the `checkCandidateConformance` executable or an independently packaged equivalent runner;
- an artifact inventory containing the source project revision and a SHA-256 digest for every supplied file;
- a blank compatibility-report template recording toolchain, implementation revision, isolation boundary, test results, injected defects, questions, and final verdict.

The Lean source, `spec/`, sibling repositories, kernel source or binaries, a12-dmkits material, and prior conversation are deliberately absent. A reference executable may be introduced only after the implementer has produced a first suite-passing version, must be pinned to the 0.2.0 source revision recorded by [`reference-semantics-lineage-v1.json`](../reference/reference-semantics-lineage-v1.json), and may then be used only for Lean-account differentials clearly separated from retained kernel evidence. The current 0.3.0 binary is not a historical compatibility control merely because it agrees on these eight requests.

## Language-neutral model

The semantic distinctions needed by this capsule are:

```text
FieldKind      = Number(scale, signed) | Boolean | Confirm
Field          = id × absolute group path × name × FieldKind
RawCell        = Empty
               | ParsedNumber(exact decimal)
               | ParsedBoolean(boolean)
               | ParsedConfirm(true)
               | Rejected(cause)
CheckedRead    = Empty | Value(typed value) | Unknown(cause)
EqualityOp     = Equal | NotEqual
Condition      = Compare(op, typed field, typed literal)
               | FieldFilled(field)
               | FieldNotFilled(field)
               | And(left, right)
               | Or(left, right)
Polarity       = Value | Omission
Verdict        = NotFired | Fired(Polarity) | Unknown
```

The eight requests use non-repeatable fields, absolute paths, Number literal `0`, Boolean literal `true`, Confirm-versus-`true`, sparse empty cells, matching parsed Boolean `true`, and rejected malformed Number. `FieldNotFilled` is exercised for an empty Number. `FieldFilled`, present Number, present Confirm, other literals, other rejection causes, and non-absolute paths are part of the wider flat development operation but are not externally closed by this suite.

Sparse omission is semantic: absence of a field ID from `cells` means `RawCell.Empty`. It is not a missing JSON member error, a parsed default, or a reason to infer that the row has no content. `hasContent` is supplied by the document layer and remains independent of the sparse cell list.

The normalized model and path are checked before evaluation. A resolved field is formally checked with the policy of its unique declaration. A rejected cell and a parsed value of the wrong kind become `Unknown`; they do not acquire a nearby kind's empty default. The exact public diagnostics for malformed models or paths are outside this eight-positive-case cold exercise.

## The four verdict states

| Verdict | Truth | Authored message | Meaning in this capsule |
|---|---|---|---|
| `NotFired` | false | absent | The error condition is definitely false, or the full-validation row gate suppresses it |
| `Fired(Value)` | true | VALUE | The error condition is definitely true from given input; filling an omission is not the indicated repair |
| `Fired(Omission)` | true | OMISSION | The error condition is definitely true through a fillable empty substitution or a not-filled predicate |
| `Unknown` | unknown | absent | Formal invalidity prevents a definite authored-rule result; formal diagnostics remain a separate output concern |

Polarity exists only on a fired verdict. `Unknown` is not another polarity and must not be collapsed into `NotFired` inside the evaluator, even though both suppress the authored message at the external observation boundary.

For compact tables below, use `N = NotFired`, `V = Fired(Value)`, `O = Fired(Omission)`, and `U = Unknown`.

### Conjunction

`And` uses strong-Kleene truth. False dominates unknown; among two fired operands, omission wins.

| `And` | `N` | `V` | `O` | `U` |
|---|---:|---:|---:|---:|
| `N` | `N` | `N` | `N` | `N` |
| `V` | `N` | `V` | `O` | `U` |
| `O` | `N` | `O` | `O` | `U` |
| `U` | `N` | `U` | `U` | `U` |

### Disjunction

`Or` uses strong-Kleene truth. True dominates unknown; among two fired operands, value wins.

| `Or` | `N` | `V` | `O` | `U` |
|---|---:|---:|---:|---:|
| `N` | `N` | `V` | `O` | `U` |
| `V` | `V` | `V` | `V` | `V` |
| `O` | `O` | `V` | `O` | `O` |
| `U` | `U` | `V` | `O` | `U` |

An evaluator may evaluate both pure branches and apply these tables. If it short-circuits, the polarity table matters: `And` may safely stop after `NotFired`, and `Or` may safely stop after `Fired(Value)`. `Or` must not stop merely because its left side fired with omission polarity, because a right-side `Fired(Value)` changes the final polarity to value.

## Decision procedure

Apply the stages in this order.

### 1. Validate and resolve the normalized request

Require the pinned protocol and kernel-behavior versions, select `flatValidation.evaluateFull`, validate the expanded model, resolve each absolute field path uniquely, require an empty repeatable scope, enforce kind-compatible literals, and reject unsupported shapes. Build the checked context with each resolved field's model policy. An omitted cell reads as empty; rejected malformed input reads as unknown during validation.

The eight fixtures are all valid requests. This capsule does not claim exhaustive diagnostic precedence for invalid requests.

### 2. Decide all-empty-row eligibility structurally

```text
canFireOnEmpty(Compare)         = false
canFireOnEmpty(FieldFilled)     = false
canFireOnEmpty(FieldNotFilled)  = true
canFireOnEmpty(And(a, b))       = canFireOnEmpty(a) AND canFireOnEmpty(b)
canFireOnEmpty(Or(a, b))        = canFireOnEmpty(a) OR canFireOnEmpty(b)
```

If `hasContent` is false and `canFireOnEmpty(condition)` is false, return `NotFired` without using an empty substitution from the condition. Otherwise evaluate the selected condition. Never derive `hasContent` from the cell list.

### 3. Classify a comparison operand at its consuming clause

Empty handling is comparison-local, not a reusable field-kind default:

| Field kind and validation read | Comparison operand |
|---|---|
| empty Number | value `0`, marked not given |
| empty Boolean | not evaluated |
| empty Confirm | value `false`, marked not given |
| matching parsed value | that value, marked given |
| rejected, wrong-kind, or otherwise formally invalid | unknown with its formal cause |

Stored Confirm admits only affirmative `true`; `false` above is a comparison-local substitution, not a stored Confirm value.

For Number equality in the wider flat evaluator, compare exact values after rescaling both operands to 19 decimal places with decimal `HALF_UP`. Do not use binary floating point. The retained cases in this capsule exercise only empty Number against literal zero, so general decimal behavior remains outside their external-evidence claim.

### 4. Evaluate a comparison

```text
evaluateComparison(op, operand, expected):
  NotEvaluated  -> NotFired
  Unknown       -> Unknown
  Value(actual, given):
    equivalent = kindSpecificEquivalent(actual, expected)
    holds = equivalent if op is Equal else not equivalent
    if not holds: return NotFired
    if given:     return Fired(Value)
    otherwise:   return Fired(Omission)
```

`NotEqual` is its own operator. It is not generic verdict negation: `Equal` and `NotEqual` both return `Unknown` for an unknown operand.

### 5. Evaluate presence

```text
FieldFilled(Empty)    = NotFired
FieldFilled(Value)    = Fired(Value)
FieldFilled(Unknown)  = Unknown

FieldNotFilled(Empty)   = Fired(Omission)
FieldNotFilled(Value)   = NotFired
FieldNotFilled(Unknown) = Unknown
```

Only the `FieldNotFilled(Empty)` route is one of the eight retained cases.

### 6. Combine conditions

Evaluate `And` and `Or` with the complete verdict tables above. Preserve `Unknown` until a decisive operand suppresses it, and preserve polarity until the connective-specific precedence rule selects the result.

Equivalent high-level pseudocode is:

```text
evaluateFull(request):
  checked = validateResolveAndCheck(request)
  if not request.hasContent and not canFireOnEmpty(checked.condition):
    return NotFired
  return evaluateSelected(checked.condition, checked.context)
```

## Worked trace: empty Number versus the independent row gate

[`number-empty-equals-zero-content.request.json`](../examples/reference-cli/flat-evidence/number-empty-equals-zero-content.request.json) omits `Quantity`, compares it with Number literal zero, and supplies `hasContent = true`.

1. Sparse omission produces an empty checked Number cell.
2. The row is eligible because `hasContent` is true.
3. The Number comparison consumes empty as `0`, marked not given.
4. `0 == 0` is true.
5. A true comparison reached through a not-given substitution returns `Fired(Omission)`.

[`number-empty-equals-zero-empty-row.request.json`](../examples/reference-cli/flat-evidence/number-empty-equals-zero-empty-row.request.json) keeps the same evidence-derived model, cell, and comparison but supplies `hasContent = false`.

1. `canFireOnEmpty(Compare)` is false.
2. The full-validation gate returns `NotFired` before empty Number can become comparison-local zero.

The pair separates field consumption from row eligibility. An implementation that infers row content from the sparse cells or applies Number's zero substitution before the full-validation gate gets at least one case wrong.

## Worked trace: empty Boolean is not empty Confirm

[`boolean-empty-equals-true.request.json`](../examples/reference-cli/flat-evidence/boolean-empty-equals-true.request.json) has content but omits its Boolean cell. Empty Boolean makes the direct comparison not evaluated, so the result is `NotFired`. It is neither a stored `false` value nor `Unknown` in the Lean account.

[`confirm-empty-not-true.request.json`](../examples/reference-cli/flat-evidence/confirm-empty-not-true.request.json) instead omits Confirm. The Confirm comparison locally substitutes `false`, marks it not given, and evaluates `false != true`; the result is `Fired(Omission)`.

The semantic model must retain field kind and emptiness long enough to apply these distinct consuming clauses; it must not coerce every empty Boolean-like field to false before dispatch. This retained pair does not by itself distinguish empty Boolean's not-evaluated behavior from a hypothetical `false` substitution, because both are silent for `== true`; that evidence gap is explicit under [Open boundary](#open-boundary).

## Worked trace: a healthy branch beside malformed input

Both branch cases read a present Boolean `true` and a rejected malformed Number. The left comparison `true == true` returns `Fired(Value)`. The right comparison `malformed Number == 0` returns `Unknown`.

- In `healthy-or-malformed`, `Fired(Value) Or Unknown = Fired(Value)`. The retained kernel result contains both the authored VALUE message and the separate formal Number diagnostic.
- In `healthy-and-malformed`, `Fired(Value) And Unknown = Unknown`. The retained kernel result contains the formal Number diagnostic but no authored message.

The pair separates strong-Kleene evaluation from both common mistakes: treating unknown as a global poison would suppress the `Or`, while treating unknown as ordinary false would turn the `And` into `NotFired` rather than preserving `Unknown` internally.

## Evidence-to-decision map

All eight rows are projected from [`projection.json`](../evidence/kernel-30.8.1/projection.json) and replayed by `lake test`. They belong to the original retained runtime set documented in [`EVIDENCE.md`](EVIDENCE.md): the Groovy-dynamic and static-Java kernel strategies and the a12-dmkits interpreter agreed at capture time, with no recorded strategy divergence. The retained case artifact holds the complete canonically sorted message-signature list. Replay compares only signatures with the focused authored error code; formal diagnostics are retained but are not part of the normalized verdict response.

| Case | Lean response | Retained external observation | What the external evidence establishes |
|---|---|---|---|
| [`number-empty-equals-zero-content`](../evidence/kernel-30.8.1/cases/empty/number-empty-equals-zero-content.json) | `Fired(Omission)` | Focused `NUM_EMPTY_ZERO` OMISSION message present | Authored firing and omission polarity |
| [`number-empty-equals-zero-empty-row`](../evidence/kernel-30.8.1/cases/empty/number-empty-equals-zero-empty-row.json) | `NotFired` | Focused authored message absent | Authored silence under the empty-row control; not the hidden `NotFired`/`Unknown` distinction |
| [`boolean-empty-equals-true`](../evidence/kernel-30.8.1/cases/empty/boolean-empty-equals-true.json) | `NotFired` | Focused authored message absent | Authored silence; not the hidden reason for silence |
| [`confirm-empty-not-true`](../evidence/kernel-30.8.1/cases/empty/confirm-empty-not-true.json) | `Fired(Omission)` | Focused `CONFIRM_EMPTY_NOT_TRUE` OMISSION message present | Authored firing and omission polarity |
| [`malformed-number-equals-zero`](../evidence/kernel-30.8.1/cases/formal-error/malformed-number-equals-zero.json) | `Unknown` | Formal malformed-Number message present; focused `MALFORMED_ZERO` authored message absent | Formal invalidity and authored silence; `Unknown` rather than `NotFired` is the Lean/source account |
| [`healthy-or-malformed`](../evidence/kernel-30.8.1/cases/formal-error/healthy-or-malformed.json) | `Fired(Value)` | Focused authored VALUE message and formal malformed-Number message present | Final authored firing and value polarity despite malformed sibling; not the kernel's hidden branch value |
| [`healthy-and-malformed`](../evidence/kernel-30.8.1/cases/formal-error/healthy-and-malformed.json) | `Unknown` | Formal malformed-Number message present; focused authored message absent | Authored silence beside formal invalidity; `Unknown` rather than `NotFired` is the Lean/source account |
| [`number-not-filled-empty-row`](../evidence/kernel-30.8.1/cases/empty/number-not-filled-empty-row.json) | `Fired(Omission)` | Focused `NUMBER_NOT_FILLED` OMISSION message present | `FieldNotFilled` remains eligible on the all-empty row and fires with omission polarity |

The four fired rows have exact external support for final firing and polarity. The four silent rows use the Lean result as the exact normalized verdict because external validation output can observe only silence. A conformance suite must encode that distinction rather than labeling every complete expected response as mechanically derived from the retained projection.

These observations are finite adequacy evidence for kernel 30.8.1. They do not prove universal correspondence between the Lean evaluator, an independent implementation, and the kernel.

## Law index for downstream tests

The downstream implementation should turn the finite algebra laws into exhaustive tests and the evaluator clauses into focused properties. Lean theorem links are audit aids, not code to transliterate.

| Property | Exact domain and hypothesis | Assurance source |
|---|---|---|
| Verdict commutativity | For every pair of the four verdicts, swapping operands preserves both `And` and `Or`, including polarity | `conj_commutative`, `disj_commutative` in [`Proofs/Verdict.lean`](../A12Kernel/Proofs/Verdict.lean) |
| Verdict associativity | For every triple of verdicts, regrouping either connective preserves the exact verdict | `conj_associative`, `disj_associative` |
| Verdict idempotence | Combining any verdict with itself returns the same exact verdict | `conj_idempotent`, `disj_idempotent` |
| Conjunction identities | `Fired(Value)` is the exact `And` identity and `NotFired` is the exact absorber | `conj_fired_value_left/right`, `conj_notFired_left/right` |
| Disjunction identities | `NotFired` is the exact `Or` identity and `Fired(Value)` is the exact absorber | `disj_notFired_left/right`, `disj_fired_value_left/right` |
| Absorption and distributivity | The exact four-verdict operations satisfy both absorption and both distributive laws | `conj_absorbs_disj`, `disj_absorbs_conj`, `conj_distributes_over_disj`, `disj_distributes_over_conj` |
| Clean empty stays empty until consumed | For every field policy and phase, formally checking an absent raw cell still observes empty; substitution belongs to the comparison or presence clause | `formalCheck_empty_observes_empty` in [`Proofs/Observation.lean`](../A12Kernel/Proofs/Observation.lean) |
| Model-policy coherence | A field admitted by checked flat lowering reads a raw cell using the unique matching model declaration's policy | `checkContext_admittedField_coherent` in [`Proofs/Elaboration.lean`](../A12Kernel/Proofs/Elaboration.lean) |
| Lookup failure closes as unknown | A failed unique field-ID lookup becomes malformed and observes unknown in validation | `checkContext_lookup_error_observes_unknown` |
| Empty-row gate | For any condition with `hasContent = false` and `canFireOnEmpty = false`, the full result is `NotFired` regardless of its selected evaluator result | Executable definition and separating locks in [`Conformance/FlatValidation.lean`](../A12Kernel/Conformance/FlatValidation.lean) |
| Per-kind empty comparison | Selected empty Number `== 0` is `Fired(Omission)`; selected empty Boolean comparison is `NotFired`; selected empty Confirm `!= true` is `Fired(Omission)` | Executable locks in [`Conformance/FlatValidation.lean`](../A12Kernel/Conformance/FlatValidation.lean), with the finite external qualifications above |
| Malformed branch composition | `Fired(Value) Or Unknown = Fired(Value)` and `Fired(Value) And Unknown = Unknown` | Exhaustive verdict theorem surface plus the paired retained cases |

At minimum, a downstream test suite should enumerate all 16 input pairs for each verdict connective and all 64 triples for associativity. It should separately generate valid normalized fields/cells because the algebraic laws do not establish decoder, path-resolution, or raw-checking correctness.

## Checked non-laws and separating regressions

Preserve these boundaries as fixed tests:

- empty handling is not one uniform field-type default and is not a nullable-Boolean convention; Number, Boolean, and Confirm comparisons make different consuming-clause decisions;
- empty Number as zero is a direct comparison rule, not a kind-wide law for every function, aggregate, computation, or storage context;
- `Unknown` is not a global absorber: `NotFired And Unknown = NotFired`, while `Fired(Value) Or Unknown = Fired(Value)`;
- malformed comparison inequality is not the Boolean negation of malformed equality; both remain `Unknown`;
- authored silence is not evidence that an internal result was `NotFired`; it may be `Unknown`;
- `hasContent` is not derived from whether `cells` is empty and is not the same as `canFireOnEmpty`;
- polarity has no single global winner: omission wins between fired operands under `And`, while value wins under `Or`;
- truth-only short-circuiting is insufficient when it discards polarity; in particular a left `Fired(Omission)` does not determine an `Or` result before the right polarity is known;
- a formal malformed-field diagnostic and an authored-rule verdict are separate outputs; the normalized flat response exposes only the latter;
- external agreement on these eight outputs does not establish the behavior of other literals, parsed numbers, rejection causes, path forms, or condition shapes.

The executable neighboring witnesses live in [`Conformance/FlatValidation.lean`](../A12Kernel/Conformance/FlatValidation.lean) and the algebraic non-laws at the end of [`Proofs/Verdict.lean`](../A12Kernel/Proofs/Verdict.lean).

## Cold-test prompt contract

The separate downstream project should include the following ready-to-paste prompt with only path names adjusted to its local bundle layout:

```text
Implement only capability flat-validation-empty-logic-v1 as an independent command-line evaluator in the target language.

Your semantic source material is restricted to the enumerated files in HANDOVER-SHA256SUMS. Do not inspect the source a12-kernel-lean repository, Lean implementation or proof files, spec/, the A12 kernel, a12-dmkits, sibling repositories, web search results about A12 semantics, or prior conversation. General language and standard-library documentation is allowed.

Read the implementer capsule first, then the protocol excerpt and support declaration, then the conformance suite and retained evidence account. Preserve Empty, formally Unknown, NotFired, Fired(Value), and Fired(Omission) as distinct states. Use enum-based branching. Do not use floating point for A12 Number values.

Begin with a red test run. Implement the smallest clean evaluator and one-request process boundary that passes the supplied suite; fail closed rather than inventing behavior outside the named capability. Add exhaustive tests for the two four-verdict tables and the language-neutral laws listed in the capsule. Do not embed the Lean executable or expected responses in production code.

When the suite passes, run the supplied seeded-divergence exercises and show that each produces the predicted failure. Restore the implementation and rerun all checks. Record toolchain and dependency versions, every command, result, ambiguity, unsupported input, and the exact handover digests in COLD-IMPLEMENTATION-REPORT.md. If any semantic decision is not determined by the supplied material, stop guessing and record it as a handover defect.
```

The project skeleton may provide process plumbing, fixture loading, and failing tests, but it must contain no semantic implementation. The prompt, artifact inventory, and blank report must be committed before the cold implementation starts so later corrections remain auditable.

## Seeded divergence exercises

After the independent implementation passes naturally, inject each defect separately:

1. Treat empty Number comparison as not evaluated instead of substituting not-given zero. `number-empty-equals-zero-content` must change from `Fired(Omission)` to `NotFired`.
2. Ignore authoritative `hasContent` and infer row emptiness from sparse cells. The two empty-Number equality controls must no longer both match their distinct expected verdicts.
3. Treat empty Confirm as not evaluated instead of comparison-local not-given false. `confirm-empty-not-true` must stop firing.
4. Collapse malformed comparison to `NotFired`. Both the direct malformed case and `healthy-and-malformed` must expose the lost `Unknown` result, while the final firing of `healthy-or-malformed` remains a useful control.
5. Make `Unknown` a global poison for both connectives. `healthy-or-malformed` must be suppressed incorrectly.
6. Treat `Unknown` as ordinary false for both connectives. `healthy-and-malformed` must become `NotFired` instead of `Unknown`.
7. Mark an empty-substitution firing as value polarity. The empty Number, empty Confirm, and Number-not-filled cases must reject the polarity change.

Classify defects 1, 3, and 7 as consuming-clause or polarity evaluation errors; defect 2 as row-eligibility error; defects 4 through 6 as formal-observation or verdict-algebra errors. A failure to decode the fixture is transport, not semantic disagreement.

The suite cannot detect an implementation that substitutes `false` for empty Boolean only in the exercised `== true` case, because both false and not-evaluated are silent there. Do not use that ineffective mutation as evidence of suite sensitivity; it is an open evidence item.

The generated [`flat-validation-empty-logic-v1.mutation-plan.json`](../reference/flat-validation-empty-logic-v1.mutation-plan.json) is the exact machine-readable companion to these exercises. It derives canonical verdicts for changed cases and the complete unchanged-case ID set from the typed capability, records every reviewed expected mutant verdict, and exhaustively derives the complete connective-table deltas for exercises 5 and 6 from the frozen historical verdict algebra because the eight canonical cases observe only one connective-sensitive result from each mechanism. It also makes an exact consequence of exercise 2 explicit: sparse-cell inference suppresses both `number-empty-equals-zero-content` and `confirm-empty-not-true`, while empty Boolean remains silent under either row decision. Its result-record requirements use schema 2 and now identify `strictPacketResultAndLogCheckerAvailable`: the source-side checker enforces the closed packet/result shapes, exact patch and raw-log digest scopes, all eight ordered case observations, all 32 ordered connective cells for exercises 5 and 6, and path-and-byte restoration. The plan remains source-maintainer qualification material, not execution evidence, kernel evidence, or a retroactive member of the immutable first Rust bundle.

## Post-cold mutation qualification packet

The retired qualification implementation created a packet schema 2 and result schema 2 around the generated plan. Its export bound the semantics-project revision, frozen natural Rust revision `7606fd5b881a8bdb8c94daf409ff4c495e572b29`, exact candidate build/test-input closure, compatibility tuple, execution profile, canonical observer, observer-only baseline patch, seven semantic patches, expected observations, commands, and every payload file by SHA-256. The accepted implementation remains inspectable at source revision `e408c9bd87ab8de576c900f2e42e0f13e868da76` and in the common pre-deletion snapshot `03186c1`; it is not current project infrastructure.

The observer reads the frozen conformance suite and its eight canonical request fixtures; it does not reconstruct those requests in a second semantic harness. The natural observation and every mutation contain all eight case results, while exercises 5 and 6 additionally contain the complete 32-cell `And`-then-`Or` algebra. Predictions come from the typed plan, but the runner fills the result's observed values by parsing actual observer stdout. The checker binds those recorded observations back to the raw log bytes before comparing them with the prediction, and separately reconstructs every patch from the frozen natural library, tracked observer, and reviewed source edits so a self-consistent packet cannot replace the named mutation.

Restoration means exact paths and bytes for the packet-pinned candidate build/test-input closure after the natural gate, after each reversed mutation, and at the final gate. The closure includes the Cargo/toolchain inputs, source, tests, verification scripts, and consumed handover material frozen at the baseline revision; it deliberately excludes build output such as `target/` and unrelated reports, prompts, or agent instructions. This is not a claim that every filesystem or operating-system side effect was sandboxed.

Two assurance classes keep the execution claim honest. The source-owned self-test records `sourceExecutedReplay` because its runner actually executes the commands in a disposable candidate copy and captures the streams. A returned downstream record uses `isolatedSessionAttestation`: `--check` can establish that its packet identity, commands, statuses, logs, observations, and restoration inventories are digest-bound and internally consistent, but cannot independently prove that the isolated session executed those commands. Cedar supplies the structural precedent for separating specification, validation, theorems, differential tests, and integration machinery; the assurance classes and digest-bound external-attestation model are A12-specific and intentionally weaker than an execution attestation service.

The complete source-side replay of the natural baseline and all seven mutations is green. A separate isolated session produced the schema-2 downstream record committed at Rust revision `d213005b3972c2acd8f67e87f523a923d69f6a54`; the strict checker accepted its exact packet identity, command/status records, observer outputs, complete 138-log tree, and restoration inventories as an `isolatedSessionAttestation`. The [outcome section](#cold-test-and-qualification-outcome-2026-07-1415) records the precise boundary.

## Post-cold generated differential

The bounded generated-differential lane is deliberately separate from the original cold handover. The isolated implementer first had to construct the eight-case implementation without access to the Lean source or executable; only after that result and its mutation qualification were frozen does this lane introduce the Lean reference as a black-box comparison oracle. It tests whether the transported semantic mechanism generalizes beyond the handed-over fixtures, not whether an implementer can copy reference outputs.

The retired generated-differential implementation defined a closed profile schema and deterministically enumerated 52 supported positive requests: 12 leaf/cell-state combinations, all 32 ordered pairs of the four verdict atoms under `And` and `Or`, and 8 ordered authoritatively empty-row eligibility combinations where `hasContent=false` despite a present Boolean control cell. In a leaf case, the chosen sparse, parsed-Boolean-true, or rejected-malformed state is installed in the targeted field; parsed Boolean is therefore intentionally wrong-kind for Number and Confirm leaves. Every request stays inside the admitted three-field absolute/non-repeatable flat capability and is decoded through the public protocol before use. The comparison projects each strict success response only to `notFired`, `fired.value`, `fired.omission`, or `unknown`; negative protocol diagnostics remain outside this campaign. The exact source is preserved at revision `2cdc37746737d83241f91cd89fa0b56c99c2d47a` and in pre-deletion snapshot `03186c1`.

The historical runner required clean repositories at the profile-pinned revisions, repository-relative contained executable paths, exact executable/profile digests, and unchanged postflight identities. It invoked the Lean reference and candidate sequentially through the project-owned bounded relay, enforced per-process and aggregate time/input/output/result budgets, and wrote either a finite agreement receipt, a process/integrity failure, or every disagreement with both responses and deterministic minimal witnesses. This was a cooperative macOS/Linux resource boundary for candidates retaining the caller's credentials, not an untrusted-code sandbox.

The bounded relay remains a current command:

```sh
lake exe checkBoundedProcess
```

The generated-differential driver requires a clean checkout of Git revision `03186c1`; it is not available at current HEAD:

```sh
lake exe checkGeneratedDifferential --self-test
```

The reviewed [`flat-validation-empty-logic-v1.generated-differential-v1.json`](../reference/flat-validation-empty-logic-v1.generated-differential-v1.json) pins source `2cdc37746737d83241f91cd89fa0b56c99c2d47a` and Rust candidate `d213005b3972c2acd8f67e87f523a923d69f6a54`. At the historical checkout it can be validated without executing either implementation:

```sh
lake exe checkGeneratedDifferential --check-profile reference/flat-validation-empty-logic-v1.generated-differential-v1.json
```

Execute from the clean source checkout named by that profile. The result must be an absolute, absent file whose existing non-symlink parent is outside both pinned repositories; a new file under `/private/tmp` is suitable, while an ignored path inside either checkout is not:

```sh
lake exe checkGeneratedDifferential --run \
  --profile <profile.json> \
  --reference-repo <clean-pinned-source-checkout> \
  --reference .lake/build/bin/a12-kernel-reference \
  --candidate-repo <clean-pinned-candidate-checkout> \
  --candidate target/debug/a12-kernel-rust-spike \
  --result /private/tmp/a12-flat-generated-result.json
```

### Generated differential outcome (2026-07-15)

The exact pinned run is retained as [`generated-differential-v1.RESULT.json`](../qualification/flat-validation-empty-logic-v1-rust-v1/generated-differential-v1.RESULT.json). It executed 104 bounded processes and completed all 52 generated cases with no disagreement, process failure, or integrity failure. Lean and Rust both produced 14 `notFired`, 11 `fired.value`, 13 `fired.omission`, and 14 `unknown` verdicts. The measured campaign used 94,088 process-input bytes, 11,114 process-output bytes, and 4,997 ms on `arm64-apple-darwin24.6.0`, within every declared bound; the receipt binds the exact profile, runner, relay, reference, candidate, and source revisions by SHA-256 or Git identity.

At revision `03186c1`, the strict non-writing receipt-consistency command was `lake exe checkGeneratedDifferential --check-result reference/flat-validation-empty-logic-v1.generated-differential-v1.json qualification/flat-validation-empty-logic-v1-rust-v1/generated-differential-v1.RESULT.json`. The checker bounded-read the receipt, rejected duplicate or unknown JSON members and non-agreement records, reconstructed the profile's exact cases, compared both recorded distributions with the frozen historical distribution, and checked compatibility, revisions, counts, budgets, claim, admitted platform, and artifact-digest syntax. Current `checkReferenceProcess` instead pins and rehashes the immutable profile and result bytes; it does not authenticate the historical execution, rebuild or compare the historical macOS executable bytes on another platform, or reconstruct per-case green transcripts omitted by the compact receipt.

Downstream revision `6a4df4ebaf15efd5620d60caf6cf9ac9834b668e` later copied that canonical receipt into the Rust repository, added the report `GENERATED-DIFFERENTIAL-ADDENDUM.md`, and updated its entry documentation to report 52/52 finite-profile agreement while leaving the historical reports byte-for-byte unchanged. This is a documentation and receipt mirror only: the candidate actually executed and qualified by the pinned campaign remains Rust revision `d213005b3972c2acd8f67e87f523a923d69f6a54`, and the later downstream revision must not replace that candidate identity in the compatibility tuple or receipt.

Under the recorded attested isolation boundary, this result answers the spike's knowledge-transport question positively for the closed capability: the Rust implementation reported as reconstructed from the language-neutral handover generalized from the eight visible conformance fixtures to the separately generated 52-case matrix once black-box Lean comparison was permitted. It remains `finiteLeanAccountDifferential` with `kernelEvidence=none`; the run does not expand the supported fragment, establish universal candidate correctness, transfer Lean proofs, or add external-kernel correspondence.

The profile and result lifecycle belongs to [`ARTIFACTS.md`](ARTIFACTS.md#retained-rust-qualification-records), while [`TESTING.md`](TESTING.md#historical-rust-qualification-experiment) records the claim limits.

## Current and historical commands

The current checkout retains the candidate suite and frozen-byte gates:

Replay the retained kernel observations and run the reference process gate:

```sh
lake test
lake exe checkReferenceProcess
lake build checkCandidateConformance
```

`checkReferenceProcess` rehashes the immutable descriptor, eight request/response pairs, suite, mutation plan, generated profile, and retained result. A semantic or evidence-boundary change requires a new capability identity and current shipment path rather than regeneration of those historical artifacts in place.

Validate the suite's own metadata and evidence links:

```sh
lake exe checkCandidateConformance \
  --self-test \
  --suite reference/flat-validation-empty-logic-v1.conformance.json
```

Run the suite against an independently built reference only when that binary is pinned to historical source revision `9fa50276f5fb70dcd879b0a9712c8d69c0868967`:

```sh
lake exe checkCandidateConformance \
  --candidate <historical-0.2.0-reference> \
  --suite reference/flat-validation-empty-logic-v1.conformance.json
```

Run it against an independent candidate by replacing the candidate path. The candidate reads one JSON request from standard input, writes one JSON response followed by a newline to standard output, emits nothing on standard error, exits `0` for semantic results and domain diagnostics, and produces byte-identical output on repeated execution. The runner compares parsed JSON structurally, so object-key order is not normative. It validates this suite against the committed v1 manifest but does not call the candidate's `--manifest`; the qualification record must pin the candidate bytes and 0.2.0 claim separately.

The runner and suite establish only the eight indexed outputs and their metadata classifications. They do not transfer Lean proofs to the independent implementation. Each current candidate invocation has a 10-second deadline, 1-second cleanup deadline, 1 MiB stdin and stdout caps, and a 64 KiB stderr cap.

The old `syncFlatHandover`, `checkMutationQualification`, and `checkGeneratedDifferential` commands are available only from a clean checkout of Git revision `03186c1`. Their accepted packet and campaign identities are recorded above; use that revision only to audit or reproduce the completed experiment, never to regenerate its frozen outputs or as a reason to restore the machinery to current source.

## Compatibility report and escalation

The cold implementation report must record:

- source project revision and every handover artifact digest;
- target-language toolchain, direct and transitive dependencies, and implementation revision;
- the exact isolation rule and whether any forbidden source was consulted;
- all suite, exhaustive-algebra, and focused property commands and results;
- each seeded defect, predicted failing case, observed failing case, and classification;
- semantic questions, assumptions, unsupported shapes, and any deviation from the process contract;
- a verdict of `pass for named development spike`, `handover defect`, or `implementation defect`.

On disagreement, preserve the normalized request and both responses, then identify the first divergent stage: transport, model/path resolution, formal checking, row eligibility, comparison operand, comparison evaluation, presence, verdict combination, polarity, or response encoding. If this capsule decides the case, fix the violating implementation. If the capsule, Lean response, and retained observation do not determine it consistently, mark the capability incomplete and open a semantics defect here. A semantics maintainer performs any new kernel research through the clean-room evidence workflow and publishes a new compatibility tuple; the downstream implementer must not repeat kernel archaeology.

## Cold-test and qualification outcome, 2026-07-14–15

One isolated coding-agent run consumed the bundle exported from source revision `fb0a50d8715aaef07431692811ed89ac69a764c5`, produced the natural Rust implementation revision `7606fd5b881a8bdb8c94daf409ff4c495e572b29`, and recorded its first report containing mutation observations at revision `c39be53cb5031e60a8244d5feadda4c851846288` in downstream report `COLD-IMPLEMENTATION-REPORT.md`. Revision `91044000c7f71d98e1e67691be035b627e6f7508` corrected that report's inventory and evidence wording and synchronized the downstream lifecycle documentation; revision `9e308bf405ddc7c029a5d1297386ecb2415e5c4c` committed the separate downstream report `HANDOVER-FEEDBACK.md`. The implementer reported no use of Lean source, the kernel, a12-dmkits, sibling repositories, prior semantic conversation, or A12 web research, and no in-scope question required guessing. It implemented typed raw, checked, operand, condition, polarity, and verdict states rather than dispatching on fixture identities.

The eight canonical process cases, exhaustive four-verdict tables, associativity triples, focused staged tests, formatting, Clippy, and the complete Rust gate passed. In a post-cold source-side audit on 2026-07-14, `lake exe checkCandidateConformance --candidate ../a12-kernel-rust-spike/target/debug/a12-kernel-rust-spike --suite reference/flat-validation-empty-logic-v1.conformance.json` accepted the frozen Rust implementation with `8/8 cases passed`. This second execution confirmed process compatibility with the same finite suite but added no semantic breadth; the later generated differential recorded above supplied the separate non-fixture check.

The downstream Prompt 03 exercised three representative defects: bypassing the row gate, treating empty Confirm as not evaluated, and making `Unknown` poison `Or`. Each produced exactly the one predicted case divergence and the natural implementation was restored between mutations. Empty Confirm exactly matches declared exercise 3. The `Or` change detects the fixture named by exercise 5 but does not implement that exercise's full “global poison for both connectives” mechanism, so exercise 5 is only partially covered. Row-gate bypass is not declared exercise 2: exercise 2 infers an empty row from sparse cells and would suppress the content-bearing control, while bypass evaluates the empty-row control and is therefore an additional inverse defect. At that historical point, six exact exercises—1, 2, 4, 5, 6, and 7—remained from [Seeded divergence exercises](#seeded-divergence-exercises). The temporary patches and raw command transcripts were not retained, so Git establishes the immutable bundle and restored final code while the historical mutation execution remains an attested experiment record.

The later source-side qualification replay closes that tooling gap without rewriting the historical experiment. It applies each of the seven exact source-declared mutations separately to a disposable copy of the frozen natural implementation, captures the canonical fixture-driven observations and complete required algebra, reverses each patch, reruns the full Rust verification gate, verifies the restored path-and-byte inventory, and passes the strict checker. The complete adversarial checker set also passes. This establishes that the generated packet and source replay are executable and mutation-sensitive on the source maintainer's machine.

The packet exported from source revision `e408c9bd87ab8de576c900f2e42e0f13e868da76` pins candidate base revision `9e308bf405ddc7c029a5d1297386ecb2415e5c4c`, natural implementation revision `7606fd5b881a8bdb8c94daf409ff4c495e572b29`, and `PACKET.json` SHA-256 `28b1e0e074a53dc3abb7fe69f4ae97286f4fdf1e81a1d80e92e8a29709a8ab16`. The isolated consumer committed `RESULT.json` and its complete 138-log tree at downstream revision `d213005b3972c2acd8f67e87f523a923d69f6a54`. The natural gate, all seven pre-attested mutations, every per-mutation restoration, the final restoration gate, and the downstream `scripts/verify.sh` passed with no unresolved question. Running `--check` from a disposable clean checkout at the packet-pinned source revision accepted the record against downstream revision `d213005b3972c2acd8f67e87f523a923d69f6a54`. This is a digest-bound, internally consistent `isolatedSessionAttestation`; the source checker did not witness the external command history.

The run supports the handover method for this finite slice. The language-neutral state model, staged algorithm, complete tables, worked traces, separating pairs, exclusions, and evidence classifications carried the implementation knowledge; Lean theorem names were not required to write the Rust evaluator. The implementer kit was the primary semantic guide, the capability descriptor controlled scope, the protocol and fixtures controlled transport and executable behavior, the retained artifacts served provenance audit rather than a second specification, and the digest inventory made the isolation boundary concrete. The paired row-content and healthy/malformed branch cases were especially effective. The broader operation manifest and source-maintainer material created avoidable navigation tension, which motivates explicit artifact roles, a concise normative path with a maintainer appendix, generated machine-readable law vectors and mutation records, and a capability-specific positive profile with explicit exclusions. [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md#lessons-from-the-first-cold-implementation) owns these generalized process lessons; this section records only their capsule-specific basis.

This is knowledge-transport evidence, not new kernel evidence, a transferred Lean proof, release qualification, or a general claim about human or cross-language repeatability. The complete declared mutation set is green both as a source-executed replay and as a checker-accepted isolated downstream attestation under their distinct assurance classes, and the later 52-case generated differential is green under its separate finite-Lean-account claim. Exact negative-protocol compatibility and the external empty-Boolean distinction remain open.

## Repeatable production of a successor handover

This capsule is now an immutable historical projection, not an independently evolving semantics document. The retired typed bridge and its explicit verdict table remain inspectable at Git revision `03186c1`; current [`Reference/Lineage.lean`](../A12Kernel/Reference/Lineage.lean) pins the artifact bytes and `checkReferenceProcess` is their non-writing gate. The [`0.2.0 artifact lock`](../reference/reference-semantics-0.2.0.lock.json) pins the selected 152-entry historical evidence/example/principal-artifact inventory; it does not include this human handover document, and the post-revision separating request and replay receipt are bound separately by the lineage. The four source classes that produced it were:

1. the semantic definitions and checked cases at the pinned historical source revision, whose current descendants are [`Semantics/FlatValidation.lean`](../A12Kernel/Semantics/FlatValidation.lean) and [`Conformance/FlatValidation.lean`](../A12Kernel/Conformance/FlatValidation.lean);
2. the theorem and non-law boundaries at that revision, whose current descendants include [`Proofs/Verdict.lean`](../A12Kernel/Proofs/Verdict.lean), [`Proofs/Observation.lean`](../A12Kernel/Proofs/Observation.lean), and [`Proofs/Elaboration.lean`](../A12Kernel/Proofs/Elaboration.lean);
3. normalized transport and support declarations in [`PROTOCOL.md`](PROTOCOL.md) and [`supported-fragment-v1.json`](../reference/supported-fragment-v1.json);
4. retained kernel observations and the typed replay input in [`EVIDENCE.md`](EVIDENCE.md), [`projection.json`](../evidence/kernel-30.8.1/projection.json), and the eight case artifacts above.

No later change invalidates and regenerates this v1 bundle in place; a mismatch is evidence that the historical bytes or their checker drifted. For a successor, update the current owning semantics first, close its conformance and evidence gates, create a new capability/manifest/suite identity and a new typed bridge connected to that current account, generate a new allowlisted bundle and digest inventory, and repeat the isolated implementation exercise. Never patch only a downstream prompt or expected response. The existing mutation plan and post-cold qualification remain tied to the frozen 0.2.0 tuple and candidate inputs.

## Open boundary

This spike is intentionally useful before it is release-qualified:

- one isolated Rust implementation has demonstrated that this exact bundle is sufficient for the eight indexed cases; its historical Prompt 03 covered one exact source-declared mutation, the observable `Or` half of another, and one additional inverse row-gate variant, while the later schema-2 qualification completed all seven exact mutations in both the source-executed replay and a checker-accepted isolated downstream record; the retained bounded differential adds 52/52 finite Lean-account agreement, while broader-language or human replication and release qualification remain open;
- the suite covers eight finite positive semantic requests, not arbitrary valid flat requests or the public operation's negative-input diagnostics;
- the exact `NotFired` versus `Unknown` response in four silent cases comes from the Lean/source account because external message output cannot expose hidden kernel truth;
- the empty Boolean `== true` observation does not distinguish not-evaluated from a hypothetical false substitution; retain a separating empty Boolean `== false` or `!= true` kernel observation before claiming that distinction externally closed;
- Number evidence covers empty versus zero only; present nonzero, signed, fractional, scale-19 rounding, equality/inequality breadth, and other literals remain outside this finite external claim;
- only malformed rejection is exercised, and the public protocol's other formal causes have no case in this suite;
- the suite does not exercise `FieldFilled`, parsed Confirm, parsed Number, Boolean inequality, mixed fired polarities, omission beside unknown, or most nested `And`/`Or` shapes;
- all eight normalized field references are absolute and non-repeatable; parent-relative, bare-name, ambiguity, invalid-model, and repeatable-reference behavior is not handed over here;
- the checked bridge closes retained `projection.json` case → normalized protocol request → exact Lean response → suite association for these eight cases, but the earlier retained DM model/case → flat projection transcription remains outside that bridge and is guarded only by the existing evidence replay checks;
- the normalized result deliberately omits formal diagnostic messages, error pointers, message construction, and kernel emission order even though retained malformed artifacts preserve their formal messages;
- concrete DSL parsing, general DM-JSON adaptation, strings, dates, enumerations, arithmetic, required/index generation, iteration, `$` correlation, computation, partial validation, interpolation, and custom conditions are excluded;
- the eight-case `checkCandidateConformance` runner now uses bounded streamed process control with the current per-invocation limits, but it has no aggregate campaign budget and is not a security sandbox for untrusted binaries; the retired generated-differential runner's stronger campaign-wide controls apply only to the completed historical run.

These limits are part of the handover. A downstream implementation can implement and test the named semantic slice without researching the kernel, but it must not advertise a complete flat or A12 interpreter on that basis.
