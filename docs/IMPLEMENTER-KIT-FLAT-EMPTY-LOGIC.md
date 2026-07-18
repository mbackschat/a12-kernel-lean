# Independent implementer kit: flat empty handling and verdict logic

**Status:** current reference-semantics 0.3.0 development handover for the finite `flat-validation-empty-logic-v2` suite, not a release-readiness claim or a complete flat evaluator. Nine retained kernel 30.8.1 observations cover operator-sensitive empty Number, Boolean, and Confirm comparisons, the independent all-empty-row gate, malformed input, strong-Kleene `And`/`Or`, and directional VALUE/OMISSION polarity. External output directly establishes authored firing and polarity when a message fires, but authored silence cannot reveal whether the kernel's hidden result was `NotFired` or `Unknown`.

## Compatibility identity

| Item | Value |
|---|---|
| Suite | `flat-validation-empty-logic-v2` |
| Operation | `flatValidation.evaluateFull` |
| Reference semantics | `0.3.0` |
| Protocol | `1` |
| Manifest schema | `2` |
| Kernel behavior | `30.8.1` |
| Owning language sections | `§1` truth and verdict algebra, `§2` empty values and row eligibility, `§3` formal invalidity, `§12` validation polarity |
| Observable result | `notFired`, `fired.value`, `fired.omission`, or `unknown` |
| External evidence scope | Nine finite runtime observations; focused authored-message firing and polarity, not hidden kernel truth |

Pin these identifiers together. Passing this suite establishes only its finite normalized cases, not every accepted input of the wider development operation.

## Purpose and handover material

This is a small independent-implementation exercise. It exposes A12-specific choices that a nullable, two-valued evaluator gets wrong while avoiding repetition, `$` correlation, arithmetic, and general path resolution. The implementer should not need Lean source, the kernel, a12-dmkits, or undocumented conversation context.

The supplied material is:

- this language-neutral semantic capsule;
- the flat-operation wire contract in [`PROTOCOL.md`](PROTOCOL.md);
- the generated current support declaration [`supported-fragment-v2.json`](../reference/supported-fragment-v2.json);
- the nine-case suite [`flat-validation-empty-logic-v2.conformance.json`](../reference/flat-validation-empty-logic-v2.conformance.json);
- every request and expected response referenced by that suite under [`examples/reference-cli/`](../examples/reference-cli/);
- the retained flat projection [`projection.json`](../evidence/kernel-30.8.1/projection.json), the operator-sensitive projection [`operator-empty-projection.json`](../evidence/kernel-30.8.1/operator-empty-projection.json), and the retained cases linked below;
- the standalone `checkCandidateConformance` runner;
- the laws, non-laws, evidence qualifications, and open boundaries in this document.

The first eight requests use normalized, already classified Number, Boolean, and Confirm cells. The ninth adds one empty unsigned Number inequality against a negative literal and is the separating directional-polarity case introduced by reference semantics 0.3.0. There is deliberately no second current capability-descriptor file: the generated support manifest and closed suite own the machine-readable boundary.

The historical 0.2.0 cold Rust experiment is not relabeled as V2. Its exact identities, mutation outcome, 52-case differential, and recovery revisions are preserved in the [archived experiment record](archived/REFERENCE-SEMANTICS-0.2.0-AND-RUST-EXPERIMENT.md).

## Language-neutral model

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

Sparse omission is semantic: absence of a field ID from `cells` means `RawCell.Empty`. It is not a missing-member error or a reason to infer that the row has no content. The authoritative `hasContent` bit is supplied independently by the document layer.

The normalized model and path are checked before evaluation. A rejected cell and a parsed value of the wrong kind become `Unknown`; they do not acquire another kind's empty default. The suite uses non-repeatable declarations and absolute paths. Exact negative diagnostics outside its named cases remain part of the wider process contract rather than evidence-closed by this kit.

## The four verdicts

| Verdict | Truth | Authored message | Meaning |
|---|---|---|---|
| `NotFired` | false | absent | The condition is definitely false, or the full-validation row gate suppresses it |
| `Fired(Value)` | true | VALUE | The condition is definitely true and filling an omission cannot clear it |
| `Fired(Omission)` | true | OMISSION | The condition is true but filling in an available direction could clear it, or a not-filled predicate fires |
| `Unknown` | unknown | absent | Formal invalidity prevents a definite authored-rule result; formal diagnostics remain separate |

Polarity exists only on a fired verdict. `Unknown` must remain distinct from `NotFired` even though both suppress the authored message externally.

For the tables, `N = NotFired`, `V = Fired(Value)`, `O = Fired(Omission)`, and `U = Unknown`.

### Conjunction

False dominates unknown; among two fired operands, omission wins.

| `And` | `N` | `V` | `O` | `U` |
|---|---:|---:|---:|---:|
| `N` | `N` | `N` | `N` | `N` |
| `V` | `N` | `V` | `O` | `U` |
| `O` | `N` | `O` | `O` | `U` |
| `U` | `N` | `U` | `U` | `U` |

### Disjunction

True dominates unknown; among two fired operands, value wins.

| `Or` | `N` | `V` | `O` | `U` |
|---|---:|---:|---:|---:|
| `N` | `N` | `V` | `O` | `U` |
| `V` | `V` | `V` | `V` | `V` |
| `O` | `O` | `V` | `O` | `O` |
| `U` | `U` | `V` | `O` | `U` |

An implementation may short-circuit pure branches, but it must preserve polarity. `And` may stop after `NotFired`, and `Or` may stop after `Fired(Value)`. A left `Fired(Omission)` does not determine an `Or` result because a right `Fired(Value)` changes the final polarity.

## Decision procedure

### 1. Validate and resolve

Require the pinned protocol and kernel versions, select `flatValidation.evaluateFull`, validate the expanded model, resolve each absolute field path uniquely, require an empty repeatable scope, enforce literal compatibility, and reject unsupported shapes. An omitted cell reads as empty; rejected or wrong-kind input reads as unknown during validation.

### 2. Apply the independent all-empty-row gate

```text
canFireOnEmpty(Compare)         = false
canFireOnEmpty(FieldFilled)     = false
canFireOnEmpty(FieldNotFilled)  = true
canFireOnEmpty(And(a, b))       = canFireOnEmpty(a) AND canFireOnEmpty(b)
canFireOnEmpty(Or(a, b))        = canFireOnEmpty(a) OR canFireOnEmpty(b)
```

If `hasContent` is false and `canFireOnEmpty(condition)` is false, return `NotFired` before applying an empty substitution. Never derive `hasContent` from the sparse cell list.

### 3. Classify the consuming operand

Empty handling belongs to the consuming clause:

| Field kind and checked read | Comparison operand |
|---|---|
| empty unsigned Number | exact `0`, can grow but cannot shrink |
| empty signed Number | exact `0`, can grow and shrink |
| parsed Number | exact value, fixed |
| empty Boolean | not evaluated |
| empty Confirm | `false`, marked not given |
| matching parsed Boolean or Confirm | typed value, marked given |
| rejected, wrong-kind, or otherwise invalid | unknown with its formal cause |

Stored Confirm admits only affirmative `true`; `false` above is a comparison-local substitution, not a stored Confirm value. Number values are exact decimals normalized to scale 19 with decimal `HALF_UP`; never use binary floating point.

### 4. Evaluate comparison truth and polarity

Boolean and Confirm equality use the simple given/not-given rule: a true comparison over a given value fires VALUE, a true comparison over the Confirm substitution fires OMISSION, not-evaluated returns `NotFired`, and invalidity returns `Unknown`.

Number comparison is directional. First apply `Equal` or `NotEqual` to the two normalized exact values. If false, return `NotFired`; if unknown, return `Unknown`. If true, return OMISSION exactly when filling the left operand in an available direction could falsify the condition against the fixed literal:

```text
Equal:     growing or shrinking could break equality
NotEqual:
  actual < literal  -> growing could reach equality
  actual >= literal -> shrinking could reach equality
```

Otherwise return VALUE. `NotEqual` is not verdict negation: invalid equality and invalid inequality both remain `Unknown`.

### 5. Evaluate presence

```text
FieldFilled(Empty)      = NotFired
FieldFilled(Value)      = Fired(Value)
FieldFilled(Unknown)    = Unknown
FieldNotFilled(Empty)   = Fired(Omission)
FieldNotFilled(Value)   = NotFired
FieldNotFilled(Unknown) = Unknown
```

### 6. Combine recursively

Apply the complete `And` and `Or` tables. The full operation is:

```text
evaluateFull(request):
  checked = validateResolveAndCheck(request)
  if not request.hasContent and not canFireOnEmpty(checked.condition):
    return NotFired
  return evaluateSelected(checked.condition, checked.context)
```

## Separating traces

### Empty Number versus row eligibility

With `hasContent = true`, omitted unsigned Number `Quantity == 0` consumes empty as grow-only zero. Equality holds and filling could break it, so [`number-empty-equals-zero-content`](../examples/reference-cli/flat-evidence/number-empty-equals-zero-content.request.json) returns `Fired(Omission)`.

The otherwise matching [`number-empty-equals-zero-empty-row`](../examples/reference-cli/flat-evidence/number-empty-equals-zero-empty-row.request.json) has `hasContent = false`. `Compare` cannot fire on an empty row, so the row gate returns `NotFired` before substitution.

### Empty Boolean versus empty Confirm

[`boolean-empty-equals-true`](../examples/reference-cli/flat-evidence/boolean-empty-equals-true.request.json) is not evaluated and returns `NotFired`. [`confirm-empty-not-true`](../examples/reference-cli/flat-evidence/confirm-empty-not-true.request.json) substitutes not-given `false`; `false != true` returns `Fired(Omission)`. The field kind must therefore survive until the consuming clause.

### Healthy branch beside malformed input

A present Boolean comparison returns `Fired(Value)` while malformed Number comparison returns `Unknown`. The suite separates `Fired(Value) Or Unknown = Fired(Value)` from `Fired(Value) And Unknown = Unknown`. Malformed input is neither a global poison nor ordinary false.

### Directional Number inequality

[`empty-unsigned-number-not-equal-negative`](../examples/reference-cli/empty-unsigned-number-not-equal-negative.request.json) compares omitted unsigned Number with `-1`. Empty supplies grow-only zero. `0 != -1` is true, but reaching `-1` would require shrinking, which unsigned empty cannot do, so the response is `Fired(Value)`, not OMISSION. The retained operator-sensitive matrix also contains the predicted controls: `0 != 1` is OMISSION, signed empty `0 != -1` is OMISSION, and filled zero against `-1` is VALUE.

## Evidence-to-decision map

| Case | Lean response | External qualification |
|---|---|---|
| `number-empty-equals-zero-content` | `Fired(Omission)` | Authored OMISSION firing |
| `number-empty-equals-zero-empty-row` | `NotFired` | Authored silence under the row gate; hidden reason not observable |
| `boolean-empty-equals-true` | `NotFired` | Authored silence; not-evaluated versus false substitution not externally separated |
| `confirm-empty-not-true` | `Fired(Omission)` | Authored OMISSION firing |
| `malformed-number-equals-zero` | `Unknown` | Formal invalidity and authored silence; exact hidden verdict is the Lean/source account |
| `healthy-or-malformed` | `Fired(Value)` | Authored VALUE firing despite the malformed sibling |
| `healthy-and-malformed` | `Unknown` | Formal invalidity and authored silence; exact hidden verdict is the Lean/source account |
| `number-not-filled-empty-row` | `Fired(Omission)` | Empty-row-eligible OMISSION firing |
| `number-empty-not-equal-negative-directional` | `Fired(Value)` | Authored VALUE firing under directional fillability |

The first eight rows come from [`projection.json`](../evidence/kernel-30.8.1/projection.json). The ninth is mechanically associated with [`operator-empty-projection.json`](../evidence/kernel-30.8.1/operator-empty-projection.json) by [`OperatorProtocolBridge.lean`](../A12Kernel/Evidence/OperatorProtocolBridge.lean). Groovy-dynamic and static-Java kernel routes agree on these observations; a12-dmkits is triangulation rather than the oracle. Fired rows externally establish firing and polarity. Silent rows cannot reveal the kernel's hidden `NotFired`/`Unknown` distinction.

## Law and non-law index

Downstream tests should enumerate all 16 verdict pairs for both connectives and all 64 triples for associativity. Audit links:

- commutativity, associativity, idempotence, identities, absorption, and distributivity are in [`Proofs/Verdict.lean`](../A12Kernel/Proofs/Verdict.lean);
- clean empty remains empty until consumed, and lookup failure observes unknown, in [`Proofs/Observation.lean`](../A12Kernel/Proofs/Observation.lean) and [`Proofs/Elaboration.lean`](../A12Kernel/Proofs/Elaboration.lean);
- fixed and directional numeric polarity laws are in [`Proofs/NumericComparison.lean`](../A12Kernel/Proofs/NumericComparison.lean);
- executable row-gate, per-kind empty, connective, malformed, and directional witnesses are in [`Conformance/FlatValidation.lean`](../A12Kernel/Conformance/FlatValidation.lean).

Preserve these checked non-laws as regressions:

- empty handling is not one universal field-type default;
- empty Number as zero is not a kind-wide rule for functions, aggregates, computations, or storage;
- `Unknown` is not a global absorber;
- invalid `NotEqual` is not Boolean negation of invalid `Equal`;
- authored silence does not identify the hidden verdict;
- `hasContent`, sparse cell presence, and `canFireOnEmpty` are independent;
- polarity has no global winner across both connectives;
- a substituted numeric firing is not always OMISSION; direction and signedness matter;
- formal diagnostics and authored-rule verdicts are separate outputs;
- nine observed cases do not establish arbitrary accepted flat inputs or negative diagnostic precedence.

## Independent implementation playbook

1. Define closed enums or sum types for field kind, sparse raw cell, checked read, numeric fillability, simple operand, condition, polarity, and verdict. Do not collapse empty, invalid, and omitted transport.
2. Decode the normalized request strictly and lower model paths before evaluation. Use exact decimal arithmetic.
3. Implement the independent row gate before any empty substitution.
4. Implement simple Boolean/Confirm comparison and directional Number comparison as separate consuming clauses.
5. Implement presence and then the complete verdict tables.
6. Expose the one-request process boundary from [`PROTOCOL.md`](PROTOCOL.md).
7. Run the nine-case suite, exhaustive algebra tests, the directional controls, and at least these injected defects: infer row content from sparse cells, treat empty Confirm as not evaluated, flatten unknown to false, make unknown globally poison `Or`, and classify every substituted numeric firing as OMISSION.
8. Escalate an undetermined A12 case to this project. Do not inspect the kernel or infer from a nearby operator.

## Commands

```sh
lake build a12-kernel-reference checkCandidateConformance
lake exe checkCandidateConformance --self-test --suite reference/flat-validation-empty-logic-v2.conformance.json
lake exe checkCandidateConformance --candidate .lake/build/bin/a12-kernel-reference --suite reference/flat-validation-empty-logic-v2.conformance.json
lake exe checkReferenceProcess
lake test
./scripts/check-lean-trust.sh
```

For an independent candidate, replace `.lake/build/bin/a12-kernel-reference` with its executable path. The runner invokes the command without a shell through the bounded relay, requires exit `0`, empty standard error, one normalized JSON response plus newline, deterministic repeated bytes, and structural JSON agreement. It validates the suite against the committed current manifest but does not query the candidate's manifest; a qualification record must pin candidate bytes and the claimed compatibility tuple separately.

## Escalation and open boundary

Preserve the first complete divergent request and both responses. Classify the mismatch as decoding, model/path lowering, row eligibility, checked-cell classification, comparison truth, directional polarity, presence, connective algebra, or response encoding. If this kit decides the case, fix the candidate. If the kit, current Lean result, and retained evidence do not decide it consistently, suspend the affected claim and open a semantics defect here.

This kit remains intentionally finite:

- arbitrary negative-input compatibility and diagnostic precedence are not closed by the nine cases;
- hidden `NotFired` versus `Unknown` for silent external rows remains a Lean/source classification;
- the empty Boolean observation does not externally distinguish not-evaluated from a hypothetical false substitution;
- present, fractional, signed, scale-boundary, and two-fillable-operand Number behavior is not broadly evidenced;
- only malformed rejection is exercised;
- most presence, nested-condition, path, repeatable, message, and operation shapes remain outside the suite;
- the current numeric helper covers one fillable left expression against a fixed literal, not general arithmetic, aggregates, two-sided fillability, dates, strings, or filtered polarity;
- concrete DSL parsing, general DM-JSON adaptation, iteration, correlation, computation, partial validation, interpolation, and custom conditions are excluded;
- the bounded runner is cooperative same-credential process control, not a sandbox for untrusted binaries.

These limits let an independent implementer build the named V2 slice without repeating kernel archaeology while preventing a stronger flat-interpreter or release claim.
