# Independent implementer kit: single-group captured-outer correlation

**Status:** current reference-semantics 0.3.0 development handover for the finite `single-group-correlation-v2` suite, not a release-readiness claim or a complete correlation evaluator. Twelve runtime firing-membership cases and four static authoring cases are retained kernel 30.8.1 observations. The normalized JSON shapes, diagnostics, contiguous-row restriction, resource limits, and candidate-runner behavior are project-defined compatibility decisions. The accepted mixed-scale ordering fixture combines externally observed static acceptance with a labeled Lean-account runtime projection.

## Compatibility identity

| Item | Value |
|---|---|
| Suite | `single-group-correlation-v2` |
| Operation | `singleGroupCorrelation.firingRows` |
| Reference semantics | `0.3.0` |
| Protocol | `1` |
| Manifest schema | `2` |
| Kernel behavior | `30.8.1` |
| Owning language section | `§9` repetition, iteration, and `$` correlation |
| Observable result | Ordered outer-row firing membership only |

Pin these identifiers together. Passing this suite establishes only its finite normalized cases, not every accepted input of the wider development operation. Its 16-case body descends unchanged from the retired 0.2.0 suite, but historical results are not relabeled as current qualification.

## Exact handover material

A Rust developer receives these project-local artifacts and does not need the kernel, a12-dmkits, the local `a12-rulekit/` checkout, or private conversation history:

- this language-neutral capsule;
- the exact wire contract in [`PROTOCOL.md`](PROTOCOL.md#single-group-captured-outer-correlation-operation);
- the generated positive support declaration in [`supported-fragment-v2.json`](../reference/supported-fragment-v2.json);
- the language-neutral 16-case suite in [`single-group-correlation-v2.conformance.json`](../reference/single-group-correlation-v2.conformance.json);
- its runnable request/response files under [`examples/reference-cli/`](../examples/reference-cli/), beginning with [`correlation-direction.request.json`](../examples/reference-cli/correlation-direction.request.json);
- the retained runtime and static evidence projections, [`correlation-projection.json`](../evidence/kernel-30.8.1/correlation-projection.json) and [`correlation-elaboration-projection.json`](../evidence/kernel-30.8.1/correlation-elaboration-projection.json), referenced case-by-case by the suite;
- the current `a12-kernel-reference` executable for development differentials;
- the standalone `checkCandidateConformance` runner for any command-line implementation;
- the theorem and checked-non-law audit links in this document.

The suite is the downstream test input. The evidence projections establish why the listed expected choices are credible; a downstream implementation does not have to decode their Lean replay schemas.

## Language-neutral checked model

The capability starts after concrete DSL parsing, model loading, row instantiation, and locale-sensitive scalar classification. Its closed model is:

```text
RowIndex       = integer in the normalized sequence 1..n
FieldId        = non-negative structural integer
RawNumberCell  = Empty | Parsed(exact decimal) | Rejected(Malformed)
Origin         = Inner | Outer
CompareOp      = Equal | NotEqual | Less
NumberRef      = Origin × direct-child Number field
RepetitionRef  = Origin × the selected repeatable group
Having         = CompareNumbers(op, left, right)
               | CompareRepetitions(op, left, right)
               | And(left, right)
Rule           = error field × outer guard field × one starred value field × Having
Result         = ordered list of firing outer RowIndex values
```

The expanded model may contain multiple valid repeatable-group declarations and unused fields. One rule resolves exactly one starred repeatable group. Every error, guard, value, and `Having` field admitted into that rule must be a direct child of the selected group with its exact singleton repeatable scope; a reference into a declared sibling group is rejected at correlation elaboration rather than making the whole model invalid. The error and guard paths must resolve to the same Number field. Equality and inequality require identical declared scales on their two Number fields; ordering permits different scales. The whole `Having` tree must contain at least one `Inner` and at least one `Outer` reference.

Ordinary correlation field and group paths admit only absolute and direct child-relative forms. Parent-relative and bare forms remain available in the shared flat resolver but are deliberately outside this public correlation capsule. The one-star value path is separately classified and has exactly the absolute `{"base":"absolute","groupsBeforeStar":["Order"],"starredGroup":"Items","field":"Count"}` and direct child-relative `{"base":"relative","parents":0,"groupsBeforeStar":[],"starredGroup":"Items","field":"Count"}` shapes, generalized only by valid segment names and path length. An absolute star path must omit `parents`; a relative star path with `parents > 0` or a nonempty `groupsBeforeStar` is rejected.

Candidates are a non-empty contiguous one-based list `[1, 2, …, n]`. This is deliberately narrower than the reusable Lean core, which can evaluate arbitrary positive unique row IDs: retained kernel cases cover only actual contiguous repetition indices, while repetition comparison uses the numeric index. Sparse omission of a `(row, field)` cell means `Empty`; an explicit empty state is not part of the transport. Only parsed Number and malformed-rejected correlation cell states are admitted by this operation.

## Decision procedure

Implement these stages in order. Fail closed at the first rejected boundary; do not merge elaboration, filter truth, consumer observation, and public projection into one Boolean shortcut.

1. **Decode and bound the normalized input.** Reject duplicate JSON members, unknown members, non-canonical structural numbers, invalid exact-decimal strings, oversized inputs, unsupported tags, and operation-specific members from the wrong request shape.
2. **Validate the expanded model and lower paths.** Resolve the declaring group, the single direct-child star group, error/guard/value fields, every Number reference, and every repetition reference. Check unique declarations, exact group/scope membership, Number kind, supported operator, equality-scale legality, both origins, and error/guard identity.
3. **Validate the row view.** Require candidates exactly `[1..n]`, reject duplicate `(row, field)` cells, reject cells for non-candidate rows or undeclared fields, and reject declared cells outside the resolved repeatable group and scope.
4. **Evaluate one filter frame.** For one captured outer row and one scanned inner row, route `Inner` references to the scanned row and `Outer` references to the captured row. A missing Number cell becomes comparison-local exact zero; a parsed Number supplies its exact rational value; a malformed or wrong-kind operand becomes `Unknown`. Rescale both numeric operands to 19 decimal places with `HALF_UP`, then apply the comparison. Repetition comparisons apply the operator directly to the two row indices. `And` is strong-Kleene conjunction.
5. **Select before consuming.** Scan every candidate inner row in order, including the outer row itself. Keep only frames whose filter truth is definitely `True`; both `False` and `Unknown` are dropped. There is no implicit self-exclusion.
6. **Observe the selected consumer and outer guard.** Only after selection, observe the starred value field on selected rows: empty is `False`, a valid Number is `True`, and malformed is `Unknown`; fold with strong-Kleene `Or`. Observe the guard field on the outer row with the same validation-presence classification and combine guard and selected presence with strong-Kleene `And`.
7. **Project firing membership.** Keep an outer candidate exactly when the guarded result is definitely `True`. Preserve candidate order. Return only `firingRows`; do not expose selected inner rows, hidden three-valued truth, kernel message pointers or emission order, or VALUE/OMISSION polarity.

Equivalent pseudocode for the dynamic core is:

```text
firingRows = []
for outer in candidates:
    selected = []
    for inner in candidates:
        frame = { inner, outer }
        if evalHaving(frame) is True:
            selected.append(inner)

    selectedPresence = kleeneAny(observeValue(row) for row in selected)
    guarded = kleeneAnd(observeGuard(outer), selectedPresence)
    if guarded is True:
        firingRows.append(outer)
return firingRows
```

An optimized implementation may index candidates, but it must refine this ordered nested-loop meaning and preserve malformed, empty, self-match, and observation-footprint behavior.

## Worked trace: asymmetric `$` routing

The canonical [`correlation-direction.request.json`](../examples/reference-cli/correlation-direction.request.json) has candidates and `Count` values `(1,5), (2,6), (3,9)`. Guard, filter key, and consumer are `Count`; the filter is `Inner Count < Outer Count`.

| Outer | Inner comparisons kept | Selected | Fires? |
|---:|---|---|---|
| 1 | none: no value is below 5 | `[]` | no |
| 2 | row 1: `5 < 6` | `[1]` | yes |
| 3 | rows 1 and 2: `5 < 9`, `6 < 9` | `[1,2]` | yes |

The result is `[2,3]`. Reversing the two origins gives `[1,2]`; collapsing both origins to the current row gives `[]`. This single case therefore separates both common implementation mistakes.

## Worked trace: filter before malformed consumer

[`correlation-consumer-first-malformed.request.json`](../examples/reference-cli/correlation-consumer-first-malformed.request.json) has two rows with equal `StockQty = 7`, valid outer `Count = 1` guards, and this filter:

```text
CurrentRepetition(Inner) != CurrentRepetition(Outer)
And StockQty(Inner) == StockQty(Outer)
```

`UnitWeight` is malformed on row 1 and valid on row 2. For outer row 1, self-exclusion drops row 1, row 2 is selected, and only valid row-2 `UnitWeight` is consumed, so row 1 fires. For outer row 2, self-exclusion drops row 2, malformed row 1 is selected, selected presence becomes `Unknown`, and row 2 does not fire. The result is `[1]`. An eager whole-column scan or global-invalidity flag produces the wrong answer.

## Evidence-to-decision map

Every runtime row below is manually cross-referenced by the conformance suite to [`correlation-projection.json`](../evidence/kernel-30.8.1/correlation-projection.json). Groovy-dynamic kernel, static-Java kernel, a12-dmkits, retained external messages, and the Lean projection agree for these exact cases. The public operation's projected external observable is firing membership; the retained artifacts also contain complete message signatures and polarity that this operation does not expose.

| Case | Decision locked | Expected `firingRows` |
|---|---|---:|
| `correlation-direction` | `Inner < Outer` is directional | `[2,3]` |
| `correlation-self-included` | self is scanned unless explicitly excluded | `[1,2,3]` |
| `correlation-self-excluded-distinct` | explicit repetition inequality drops self | `[]` |
| `correlation-self-excluded-duplicate` | equal peers remain selectable after self-exclusion | `[1,2]` |
| `correlation-consumer-all-valid` | selected-presence control | `[1,2]` |
| `correlation-consumer-first-malformed` | dropped malformed consumer is irrelevant; selected malformed matters | `[1]` |
| `correlation-consumer-second-malformed` | symmetric footprint witness | `[2]` |
| `correlation-filter-empty-equals-zero` | empty Number filter operand compares as zero | `[1,2]` |
| `correlation-filter-malformed-local` | malformed filter operand drops locally; healthy peers continue | `[2,3]` |
| `correlation-number-not-equal` | numeric inequality route | `[1,2]` |
| `correlation-repetition-equal` | repetition equality selects self | `[2]` |
| `correlation-repetition-less-than` | inner repetition ordering selects predecessors | `[2,3]` |

The suite's final four cases are manually cross-referenced to [`correlation-elaboration-projection.json`](../evidence/kernel-30.8.1/correlation-elaboration-projection.json): all-outer maps to public `elaboration/missingInner`; mixed-scale equality maps to `elaboration/equalityScaleMismatch`; the same fields under `<` elaborate successfully; and an inner field in sibling repeatable `Supply` maps to `elaboration/fieldOutsideGroup` while starring `Demand`. The retained observations establish the three rejection classes or static acceptance; the public diagnostic category/code, `at`, and `details` are project-defined normalized projections. For the accepted ordering case, the fixture's empty `firingRows` runtime answer is a Lean-account expectation over its normalized empty cells, not a kernel runtime observation.

## Law index for property tests

The statements below are language-neutral requirements of the Lean account. Their Lean proofs live in [`Proofs/Correlation.lean`](../A12Kernel/Proofs/Correlation.lean) and [`Proofs/CorrelationElaboration.lean`](../A12Kernel/Proofs/CorrelationElaboration.lean); exact theorem names are provided for audit.

| Property | Exact hypothesis and result domain | Lean theorem |
|---|---|---|
| Outer-reference stability | Holding context, field, and outer row fixed, changing only inner row cannot change resolution of an `Outer` Number reference; result domain is value-or-unknown operand | `outer_number_reference_stable` |
| Inner-reference locality | Holding context, field, and inner row fixed, changing only outer row cannot change resolution of an `Inner` Number reference | `inner_number_reference_local` |
| Truth bridge | For any closed `Having` and frame, executable truth is definitely `True` iff the independent declarative `Holds` predicate is derivable; it does not identify `False` with `Unknown` | `correlatedHaving_truth_iff_holds` |
| Ordered selector bridge | For any candidates and output list, executable selection equals that list iff the independent keep/drop relation derives it from the complete candidate sequence | `selectCorrelatedRows_iff` |
| Filter-before-consumer footprint | Equal selected lists, equal outer-guard observation, and equal consumer observations on selected rows imply equal guarded result in three-valued truth; dropped consumer cells need not agree | `evalGuardedAnyFilledOn_filter_before_consumer` |
| Self inequality | `CurrentRepetition(Inner) != CurrentRepetition(Outer)` is false when inner equals outer | `currentRepetition_selfExclusion_false` |
| Explicit self-exclusion | A conjunction beginning with that repetition inequality never selects the outer row | `explicitSelfExclusion_drops_outer` |
| Same-field self-match | If inner/outer equality uses the same field, the row is a candidate, and its operand resolves to a value, the row selects itself; a value of zero may come from empty substitution | `sameFieldEquality_selfMatches` |
| Topology certificate | Successful raw context validation implies positive, duplicate-free candidates in the semantic context | `rawSingleGroupContext_validate_wellFormed` |
| Scale certificate | Successful checked lowering implies every equality/inequality comparison satisfies the declared-scale law | `resolvedSingleCorrelatedRule_wellFormed_equalityScalesAgree` |

Useful generator split:

- **Exact retained-case lane:** replay the twelve named runtime requests and compare their `firingRows` with the retained observations; only those exact cases and later actually retained additions are kernel-backed.
- **Lean differential lane:** additionally generate canonical exact decimals, signed values, arbitrary admitted conjunction trees, and checked model variations; compare with the Lean reference, but label results beyond retained cases as Lean-account conformance rather than new kernel evidence.
- Generate `Having` trees that contain both origins. Generate rejected trees separately and require the documented diagnostic rather than forcing them into the evaluator.

## Checked non-laws

Preserve these as fixed regressions because each bounds a tempting but false optimization or generalization:

- self-exclusion is not implicit;
- swapping `Inner` and `Outer` is not semantics-preserving;
- invalid numeric `notEqual` is not ordinary Boolean negation of invalid numeric `equal`; both comparisons are not definitely true and therefore drop the affected frame;
- unselected consumer cells are not part of the consumer observation footprint;
- a selected valid consumer can make selected presence true even when another selected consumer is malformed; malformed is not a global poison flag for this operator;
- equality-scale legality does not generalize to ordering; mixed-scale `<` is admitted;
- candidate order is the normalized document order, not evidence of external kernel message-emission order;
- an all-inner filter is not kernel-invalid merely because the internal correlated lowering reports `missingOuter`; the public operation maps that route distinction to `unsupported/uncorrelatedHaving` because it belongs to the separate uncorrelated evaluator.

The executable witnesses are in [`Conformance/Correlation.lean`](../A12Kernel/Conformance/Correlation.lean) and [`Conformance/CorrelationElaboration.lean`](../A12Kernel/Conformance/CorrelationElaboration.lean).

## Rust implementation playbook

1. Define enums for raw cell state, origin, comparison operator, three-valued truth, `Having`, response outcome, and every supported diagnostic category/code. Do not use nullable numbers to represent both empty and malformed.
2. Decode the closed JSON shapes with unknown-member and duplicate-member rejection. Use an exact decimal or rational representation; never pass A12 Number values through `f64`.
3. Implement checked model/path lowering as a separate phase that returns either a resolved rule or a stable diagnostic. Keep the admitted absolute and direct child-relative ordinary paths distinct from the separately shaped absolute-or-direct-child one-star value path; reject ordinary parent-relative/bare forms, parent navigation through the star, and nested relative star prefixes.
4. Implement the direct nested-loop decision procedure above before optimizing. Keep the captured outer row explicit in the frame and keep selection separate from consumer observation.
5. Make the binary obey the one-request process contract: JSON on standard input, one JSON response plus newline on standard output, empty standard error, and exit `0` for semantic results and domain diagnostics.
6. Run the canonical suite, then implement the law index as Rust property tests and the non-law index as regressions. Use the Lean executable only as a development differential, never as a production dependency.
7. Record any undetermined input as a handover issue in this project. Do not inspect the kernel or infer behavior from a nearby operator.

## Tools and exact commands

Build the current reference and candidate runner:

```sh
lake build a12-kernel-reference checkCandidateConformance
.lake/build/bin/a12-kernel-reference --manifest
.lake/build/bin/a12-kernel-reference < examples/reference-cli/correlation-direction.request.json
```

Expected output for the sample is:

```json
{"firingRows":[2,3],"kernelBehaviorVersion":"30.8.1","outcome":"ok","protocolVersion":1}
```

Run the project regression and retained-evidence gates:

```sh
lake exe checkReferenceProcess
lake test
./scripts/check-lean-trust.sh
```

Run the current suite integrity guard:

```sh
lake exe checkCandidateConformance \
  --self-test \
  --suite reference/single-group-correlation-v2.conformance.json
```

Run the suite against the current Lean reference:

```sh
lake exe checkCandidateConformance \
  --candidate .lake/build/bin/a12-kernel-reference \
  --suite reference/single-group-correlation-v2.conformance.json
```

For an independent candidate, replace the candidate path:

```sh
lake exe checkCandidateConformance \
  --candidate target/debug/a12-rust-reference \
  --suite reference/single-group-correlation-v2.conformance.json
```

The runner invokes the candidate directly without a shell through the bounded relay, requires exit `0`, empty standard error, one normalized JSON response ending in a newline, and deterministic repeated output bytes. It compares parsed JSON structurally, so the candidate need not reproduce Lean's object-key ordering. It uses bounded duplicate-safe parsing, enforces closed suite/case/evidence objects, selects exactly one matching operation from the committed manifest, validates the compatibility identity and retained case counts, checks every evidence classification and case ID, and exercises 17 negative integrity guards. It does not query the candidate's manifest; a qualification record must pin candidate bytes and the claimed suite identity separately.

Candidate execution has a 10-second invocation deadline, 1-second cleanup deadline, 1 MiB standard-input and standard-output caps, and a 64 KiB standard-error cap. It is cooperative same-credential process control, not a sandbox for hostile binaries.

The suite pins exact full responses for its 16 current cases, including diagnostic `at` and `details` objects. A future compatible protocol implementation may add diagnostic detail members for ordinary consumers, as documented in [`PROTOCOL.md`](PROTOCOL.md#responses), but that future version must update the conformance policy or fixtures deliberately; adding details to a candidate claiming this exact suite identity will fail structural comparison.

The historical 0.2.0 documentation audit and its corrections are retained in the [archived experiment record](archived/REFERENCE-SEMANTICS-0.2.0-AND-RUST-EXPERIMENT.md). It was not an executable V2 candidate qualification.

## Seeded divergence exercise

Deliberately reverse `Inner` and `Outer` lookup in a candidate implementation while leaving the comparison operator unchanged. The first suite case must fail: the correct result is `[2,3]`, while the reversed implementation returns `[1,2]`. Classify this as an evaluation-origin-routing defect, not a fixture, transport, or external-evidence disagreement. Restore the routing and rerun all 16 cases.

A second useful injection is to scan every consumer cell before filtering. `correlation-consumer-first-malformed` then fails because the dropped malformed row incorrectly contaminates outer row 1. Classify it as a filter-before-consumer observation-footprint defect.

## Escalation protocol

Preserve the complete normalized request and the first divergent response. Classify the first mismatch as decoding, elaboration, row/cell validation, origin routing, filter truth, selection, consumer observation, firing projection, or response encoding. If this capsule already decides it, fix the violating implementation. If the capsule, Lean result, and retained evidence do not determine the input consistently, mark the capability incomplete and open a semantics defect here; a semantics maintainer closes it through the clean-room evidence workflow and publishes a new compatibility tuple. The Rust implementer must not repeat kernel archaeology.

## Open boundary

This spike is materially usable but is not yet a release-ready closed capsule:

- no isolated Rust implementation has yet completed the full cold-implementer gate; the documentation audit above is not a substitute for executable Rust conformance;
- arbitrary negative-input compatibility remains under-specified beyond the closed shapes, staged checks, manifest classifiers, and exact diagnostics exercised by the suite; path/model edge rules and within-stage precedence must be closed before a full-protocol release claim;
- suite-to-evidence association is manually cross-referenced and case-ID checked rather than mechanically derived; a checked projection-to-protocol export or equivalent integrity bridge remains release-blocking;
- retained parsed runtime Number cells are non-negative integers, while malformed cells are retained separately and the Lean account/normalized decoder admit general canonical exact decimals and signed values; fractional scale-19 behavior and negative correlation values remain externally unverified;
- mixed-scale `notEqual`, empty or malformed outer guards, dynamic mixed-scale ordering, and the selected-valid-plus-selected-malformed consumer case have internal Lean coverage or static evidence but no dedicated retained kernel runtime observation;
- the bounded candidate runner is cooperative same-credential process control rather than a security sandbox for hostile binaries;
- general `Document` adaptation, concrete EN/DE DSL, ordinary parent-relative/bare correlation paths, nested or multiple stars, cross-group execution, general guards or consumers, message construction, filtered-result polarity, computation, and partial validation are explicitly outside the capability.

These gaps are visible so a Rust developer can implement the named Lean-compatible spike without researching the kernel while avoiding a stronger release claim than the evidence permits.
