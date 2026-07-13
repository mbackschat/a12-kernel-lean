# Normalized reference protocol v1

This document owns the exact process and JSON contract of the product-shaped Lean reference interpreter. Protocol v1 currently exposes two disjoint normalized operations over existing checked evaluators: flat validation and one direct-child captured-outer correlation shape. It is not the concrete English/German A12 DSL, general DM-JSON, or raw user-input parsing.

## Invocation and process contract

The executable is the Lake target `a12-kernel-reference`:

```sh
lake exe a12-kernel-reference < examples/reference-cli/empty-number-equals-zero.request.json
```

The generated manifest is available through the same executable:

```sh
lake exe a12-kernel-reference --manifest
```

The channel guarantee applies to the compiled executable. `lake exe` is a build wrapper and may write build or elaboration notices to standard error before it launches that executable. Channel-sensitive consumers should build once and invoke the artifact directly; on Unix-like systems:

```sh
lake build a12-kernel-reference
.lake/build/bin/a12-kernel-reference < examples/reference-cli/empty-number-equals-zero.request.json
```

The captured-outer sample uses the same process contract:

```sh
.lake/build/bin/a12-kernel-reference < examples/reference-cli/correlation-direction.request.json
```

Protocol v1 accepts exactly one complete JSON request from standard input and writes exactly one compact deterministic JSON response followed by one newline to standard output. Object keys are emitted in the pinned Lean toolchain's sorted order; this is a deterministic encoding, not a claim of general RFC canonical JSON. `--manifest` writes the generated supported-fragment manifest. Any other argument is an invocation error.

Exit `0` means a complete machine-readable response or manifest was written, including invalid UTF-8, malformed JSON, unsupported input, model rejection, and elaboration rejection. Exit `2` means invalid command-line arguments; standard output is empty and standard error contains the invocation diagnostic. Exit `1` is reserved for an actual IO failure or internal invariant failure; domain errors never use standard error.

## Common request envelope and operation selection

Every request requires `protocolVersion`, `kernelBehaviorVersion`, `operation`, `model`, `declaringGroup`, and `cells`. `flatValidation.evaluateFull` additionally requires `condition` and `hasContent`; `singleGroupCorrelation.firingRows` instead requires `rule` and `candidates`. Every operation and selected tagged variant has a closed member set: members belonging to another shape are rejected. Unknown object members are rejected at every level. Duplicate JSON object members are rejected before decoding; they are never accepted with last-member-wins behavior.

This is the flat-operation schematic, not a runnable request; `condition` and the model contents must be complete forms below. Use the linked fixtures for runnable data.

```json
{
  "protocolVersion": 1,
  "kernelBehaviorVersion": "30.8.1",
  "operation": "flatValidation.evaluateFull",
  "model": {
    "fieldRefByShortNameAllowed": false,
    "repeatableGroups": [],
    "fields": []
  },
  "declaringGroup": ["Order"],
  "condition": {"tag": "fieldNotFilled", "field": {}},
  "cells": [],
  "hasContent": true
}
```

`kernelBehaviorVersion` is a required compatibility assertion, not informational metadata. Protocol v1 rejects any value other than `30.8.1`; it never silently falls forward to another kernel behavior version.

The process reads at most 1 MiB plus one detection byte; oversized input is rejected before the remainder is allocated. Before ordinary JSON parsing, a flat lexical preflight tracks JSON nesting without constructing a syntax tree, rejects non-canonical JSON numbers, and limits nesting to 128 and numeric tokens to 16 characters. Every JSON number in a request is a canonical non-negative structural integer bounded by `9,007,199,254,740,991` (`2^53−1`) for portable JavaScript/TypeScript interchange. A12 Number values are not JSON numbers; they use the exact decimal strings described below.

The remaining request bounds are 1,024 fields, 1,024 cells, 1,024 correlation candidates, 128 repeatable-group declarations, 64 condition or correlated-`Having` levels, 4,096 condition or `Having` nodes, 64 segments per complete field path or group path, 64 repeatable-scope levels, 256 UTF-8 bytes per path segment, and 256 characters per normalized decimal. The generated [supported-fragment manifest](../reference/supported-fragment-v1.json) is the machine-readable owner of every numeric limit.

## Expanded model

One field declaration has this shape:

```json
{
  "id": 0,
  "groupPath": ["Order"],
  "name": "Quantity",
  "kind": {"tag": "number", "scale": 0, "signed": false},
  "repeatableScope": []
}
```

The other admitted field-kind objects are `{"tag":"boolean"}` and `{"tag":"confirm"}`. Unknown kinds are diagnosed as unsupported. A repeatable-group declaration is `{"level":10,"path":["Order","Items"]}`. Number `scale` and `signed` are expanded-model metadata used by the checked semantics; this normalized adapter does not re-run locale-sensitive scalar parsing or enforce raw text against those declarations.

Protocol v1 carries `repeatableGroups` and each field's `repeatableScope` so an expanded model can be checked faithfully. The flat operation rejects repeatable references and row-addressed evaluation, so every field it evaluates must have an empty repeatable scope. The correlation operation permits a valid model to declare sibling repeatable groups but resolves exactly one direct-child starred group for one request. It checks all runtime cells and rule references admitted into that rule against the selected group's singleton scope; a reference into a declared sibling group is a correlation elaboration rejection, not a model-shape rejection.

## Flat structured paths and conditions

An absolute field path is:

```json
{"base":"absolute","groups":["Order"],"field":"Quantity"}
```

A parent-relative path uses `{"base":"relative","parents":1,...}`. A bare name is the exact relative shape `{"base":"relative","parents":0,"groups":[],"field":"Quantity"}` and follows the model's explicit `fieldRefByShortNameAllowed` policy. An absolute path must not carry `parents`. The superficially plausible child-relative shape with `parents:0` and nonempty `groups` is not part of the admitted concrete path subset and is rejected as `pathForm` rather than silently exposed as an unlisted capability.

The supported condition variants are shown schematically here; each `{}` stands for a complete nested path, literal, or condition of the corresponding form:

```json
{"tag":"compare","operator":"equal","field":{},"literal":{}}
{"tag":"fieldFilled","field":{}}
{"tag":"fieldNotFilled","field":{}}
{"tag":"and","left":{},"right":{}}
{"tag":"or","left":{},"right":{}}
```

The six recognized comparison operator tags are `equal`, `notEqual`, `less`, `lessEqual`, `greater`, and `greaterEqual`. Only `equal` and `notEqual` are supported in the flat evaluator; the four ordering tags deliberately reach a stable unsupported-operator diagnostic rather than being guessed or treated as malformed JSON.

Number literals and parsed Number cells use exact canonical decimal strings such as `"0"`, `"-12"`, or `"12.34"`. The protocol rejects exponent notation, leading `+`, negative zero, leading integer zeroes, a decimal point without a nonzero final fractional digit, and trailing fractional zeroes. Conversion is directly to Lean `Rat`; it never passes through floating point. Comparison then follows the core semantic clause: both exact rationals are rescaled to 19 decimal places with `HALF_UP` before equality or inequality is decided. The helper's separating `4e-20`/`6e-20` boundaries remain checked directly in [`Conformance/FlatValidation.lean`](../A12Kernel/Conformance/FlatValidation.lean); the legal whole-rule kernel witness requires arithmetic, which this operation does not expose, so the public sample set does not fabricate an over-scale classified field value.

This protocol begins after scalar classification. A matching `parsedNumber`, `parsedBoolean`, or `parsedConfirm` state is trusted as the supplied classified value; a wrong-kind parsed value is passed through model-derived formal checking and becomes malformed/`unknown`, rather than being reinterpreted. Stored Confirm `false` is rejected at the transport boundary because the admitted stored Confirm form represents only the checked affirmative value.

Literal objects are `{"tag":"number","value":"12.34"}` and `{"tag":"boolean","value":true}`. Number fields compare with Number literals, Boolean fields with Boolean literals, and Confirm fields with the Boolean literal `true`; Confirm-versus-`false` is a structured elaboration rejection.

## Sparse raw cells and the row gate

Cells are sparse. A declared field ID omitted from `cells` becomes `RawCell.empty`; there is no second explicit-empty encoding, and an explicit `{ "tag": "omitted" }` state is rejected. The manifest records this distinction as `emptyCellEncoding: "sparseOmission"` plus the separate `explicitRawCellForms` list. The admitted present states are:

```json
{"fieldId":0,"state":{"tag":"parsedNumber","value":"12.34"}}
{"fieldId":1,"state":{"tag":"parsedBoolean","value":true}}
{"fieldId":2,"state":{"tag":"parsedConfirm","value":true}}
{"fieldId":0,"state":{"tag":"rejected","cause":"malformed"}}
```

The five rejection causes are `malformed`, `declaredConstraint`, `unsupportedCharacter`, `leadingOrTrailingSpace`, and `customValidation`, exactly the current `BaseFormalCause` boundary. Contextual findings such as requiredness, duplicate indices, and over-repetition are not accepted here. Duplicate cell IDs and cells for undeclared fields are input diagnostics. A cell for a repeatable field is unsupported because protocol v1 has no row address.

`hasContent` is authoritative and must be supplied even when every listed cell is empty or `cells` is empty. It represents the document layer's independently known row eligibility and is never inferred from this sparse cell list.

## Single-group captured-outer correlation operation

`singleGroupCorrelation.firingRows` exposes the implemented one-group, one-star, direct-child Number validation capsule. The complete runnable shape is [`correlation-direction.request.json`](../examples/reference-cli/correlation-direction.request.json); the semantic implementation handover is [`IMPLEMENTER-KIT-CORRELATION.md`](IMPLEMENTER-KIT-CORRELATION.md).

Its operation-specific members have this outer shape:

```json
{
  "protocolVersion": 1,
  "kernelBehaviorVersion": "30.8.1",
  "operation": "singleGroupCorrelation.firingRows",
  "model": {},
  "declaringGroup": ["Order"],
  "rule": {
    "errorField": {},
    "guardField": {},
    "valueField": {},
    "having": {}
  },
  "candidates": [1, 2],
  "cells": []
}
```

`candidates` must be the non-empty contiguous one-based repetition sequence `[1,2,…,n]`. This is a normalized, evidence-bounded protocol choice; candidates are never inferred from present cells. One sparse cell is `{"row":1,"fieldId":0,"state":{"tag":"parsedNumber","value":"5"}}`. Omission of a `(row, fieldId)` address means empty. Duplicate addresses, non-candidate rows, undeclared IDs, and declarations outside the resolved repeatable group/scope are input errors. This operation accepts parsed Number cells and `rejected/malformed`; Boolean, Confirm, and other rejected-cause states are not admitted correlation cell forms.

Correlation error, guard, `Having` field, and repetition-group paths admit only absolute paths and direct child-relative paths such as `{"base":"relative","parents":0,"groups":["Items"],"field":"Count"}`. A group path has the same object without `field`. Parent-relative and bare forms are deliberately rejected in this operation even though the flat resolver supports them; conversely, this admission does not widen the flat operation to child-relative paths. The one-star value path is a different closed shape: it names the starred segment explicitly and admits either `{"base":"absolute","groupsBeforeStar":["Order"],"starredGroup":"Items","field":"UnitWeight"}` or the direct child-relative form below. An absolute form must omit `parents`; a relative star path with `parents > 0` or nonempty `groupsBeforeStar` is rejected rather than generalized into an unlisted capability.

```json
{"base":"relative","parents":0,"groupsBeforeStar":[],"starredGroup":"Items","field":"UnitWeight"}
```

The closed `having` forms are:

```json
{"tag":"compareNumbers","operator":"equal","left":{"origin":"inner","field":{}},"right":{"origin":"outer","field":{}}}
{"tag":"compareRepetitions","operator":"notEqual","left":{"origin":"inner","group":{}},"right":{"origin":"outer","group":{}}}
{"tag":"and","left":{},"right":{}}
```

The admitted operators are `equal`, `notEqual`, and `less`. Both origins must occur in the whole `Having`. Error and guard fields must resolve to the same direct-child Number field; value and all referenced fields must belong to the selected group and exact scope. Equality and inequality require equal declared scales, while ordering does not. `missingInner` is an externally anchored elaboration diagnostic; an all-inner filter reaches `unsupported/uncorrelatedHaving` because it belongs to the separate uncorrelated route rather than being kernel-invalid.

For runtime cells, the decoder accepts any canonical exact decimal supported by the shared Number transport. The retained correlation runtime observations use non-negative integers only; fractional and negative correlation behavior is therefore Lean-account behavior with external evidence pending, as recorded in the manifest and implementer kit.

## Responses

A semantic result is successful even when it is `unknown`:

```json
{"kernelBehaviorVersion":"30.8.1","outcome":"ok","protocolVersion":1,"verdict":{"polarity":"omission","tag":"fired"}}
{"kernelBehaviorVersion":"30.8.1","outcome":"ok","protocolVersion":1,"verdict":{"tag":"notFired"}}
{"kernelBehaviorVersion":"30.8.1","outcome":"ok","protocolVersion":1,"verdict":{"tag":"unknown"}}
```

The correlation operation instead returns only ordered outer-row firing membership:

```json
{"firingRows":[2,3],"kernelBehaviorVersion":"30.8.1","outcome":"ok","protocolVersion":1}
```

It deliberately omits selected inner rows, hidden three-valued truth, external message pointers or emission order, and VALUE/OMISSION polarity.

A domain rejection uses a stable category/code pair, a JSON-location hint, and structured details. Public diagnostics never expose Lean constructor `repr` text:

```json
{"diagnostic":{"at":"$.condition","category":"unsupported","code":"operator","details":{"operator":"less"}},"kernelBehaviorVersion":"30.8.1","outcome":"error","protocolVersion":1}
```

The complete protocol-v1 category/code inventory is generated from the finite Lean `DiagnosticCode` enum into the manifest's `diagnostics` table; category cannot be paired with an arbitrary code. The response envelope, category, and code are compatibility identifiers. `at` and `details` are deterministic diagnostic aids, but ordinary consumers must tolerate additional detail members in a compatible implementation update instead of treating the current detail object as a second discriminant. A conformance suite pins each complete expected response for its exact suite identity, so candidate implementations must reproduce the current fixture details until that suite or its comparison policy changes. A future internal constructor must be explicitly classified before it can cross this boundary. The impossible checked-lowering result `incoherentCore` is an internal failure and therefore cannot masquerade as an ordinary unsupported request.

## Supported fragment and exclusions

The generated [`supported-fragment-v1.json`](../reference/supported-fragment-v1.json) is a schema-2 closed positive support declaration mechanically compared with the CLI's `--manifest` output. Its `operations` array gives flat and correlation separate accepted sets and unsupported comparison lists; correlation separately declares finite ordinary-path, star-path, and cell-form sets plus whole-rule and operator-specific scale constraints. The shared diagnostics, limits, compatibility versions, and precise exclusions remain top-level. Decoder acceptance uses the same finite operation, comparison, path, field-kind, condition/`Having`, raw-cell, origin, and diagnostic classifiers that generate the manifest. Black-box probes guard sparse omission, operation-specific absolute/child-relative success, parent-relative/bare rejection, parent/nested relative stars, row topology, cell addresses, rejected causes, error/guard identity, and origin near misses. The known exclusions include concrete DSL and general DM-JSON/`Document` adaptation, general ordering and arithmetic beyond the named comparison cells, general repeatable evaluation, nested or multiple stars, cross-group correlation, general correlation consumers, filtered-result polarity, computation, partial validation, and message construction.

## Regression-checked sample data

The files under [`examples/reference-cli/`](../examples/reference-cli/) are both runnable sample data and black-box test fixtures:

- [`empty-number-equals-zero.request.json`](../examples/reference-cli/empty-number-equals-zero.request.json) demonstrates that an omitted Number cell compares as zero and fires with omission polarity.
- [`empty-boolean-equals-true.request.json`](../examples/reference-cli/empty-boolean-equals-true.request.json) demonstrates that an omitted Boolean suppresses a direct comparison and does not fire.
- [`empty-confirm-not-equal-true.request.json`](../examples/reference-cli/empty-confirm-not-equal-true.request.json) demonstrates that an omitted Confirm behaves as the fillable negative value and fires inequality with omission polarity.
- [`present-number-equals-literal.request.json`](../examples/reference-cli/present-number-equals-literal.request.json) demonstrates a legal present scale-2 Number and exact canonical decimal transport.
- [`empty-row-gate.request.json`](../examples/reference-cli/empty-row-gate.request.json) holds the omitted Number comparison fixed but sets `hasContent` false, demonstrating the independent full-validation row gate.
- [`malformed-number.request.json`](../examples/reference-cli/malformed-number.request.json) demonstrates that rejected input yields the successful semantic verdict `unknown`.
- [`boolean-confirm-composition.request.json`](../examples/reference-cli/boolean-confirm-composition.request.json) exercises Boolean and Confirm comparisons, inequality, filled/not-filled, `And`/`Or`, and absolute, parent-relative, and bare paths in one accepted request.
- [`unsupported-ordering.request.json`](../examples/reference-cli/unsupported-ordering.request.json) demonstrates a recognized but unsupported operator.
- [`illegal-confirm-false.request.json`](../examples/reference-cli/illegal-confirm-false.request.json) demonstrates a checked elaboration rejection.
- [`unsupported-version.request.json`](../examples/reference-cli/unsupported-version.request.json) demonstrates protocol-version fail-closed behavior.
- [`malformed-json.input`](../examples/reference-cli/malformed-json.input) demonstrates malformed JSON as a structured input response rather than a process failure.
- [`correlation-direction.request.json`](../examples/reference-cli/correlation-direction.request.json) is the smallest asymmetric captured-outer sample and returns `[2,3]`.
- [`correlation-self-included.request.json`](../examples/reference-cli/correlation-self-included.request.json), [`correlation-self-excluded-distinct.request.json`](../examples/reference-cli/correlation-self-excluded-distinct.request.json), and [`correlation-self-excluded-duplicate.request.json`](../examples/reference-cli/correlation-self-excluded-duplicate.request.json) separate implicit self-match from authored self-exclusion.
- [`correlation-consumer-first-malformed.request.json`](../examples/reference-cli/correlation-consumer-first-malformed.request.json) and its mirrored second-malformed fixture expose filter-before-consumer observation order.
- the complete 12-runtime-case plus four-static-case handover set is indexed by [`single-group-correlation-v1.conformance.json`](../reference/single-group-correlation-v1.conformance.json), with each expected result linked to its retained evidence case and the accepted static ordering case's runtime projection labeled separately.

Each adjacent `.response.json` file is the expected response and can be run with the same redirection pattern shown above. [`A12Kernel/ReferenceProcessTestMain.lean`](../A12Kernel/ReferenceProcessTestMain.lean) invokes the compiled executable, checks exit status and both output channels, compares deterministic compact JSON for both operations, compares the shipped manifest with `--manifest`, runs the candidate-runner integrity self-test, and runs the full 16-case suite against the compiled reference as a control. Its generated adversarial cases additionally cover invalid UTF-8, capped input, hostile JSON numbers and nesting, portable-natural and decimal bounds, all recognized ordering operators, version and operation assertions, model/cell/repeatable rejection, complete-path boundaries, explicit omission, wrong-kind classified values, the flat child-relative near miss, correlation candidate topology and limits, duplicate/foreign/undeclared/out-of-group row cells, unsupported correlation cell states/rejected causes/operators/origins, parent-navigating and nested-relative stars, bare/parent/nested-relative ordinary correlation paths, all-outer rejection, all-inner routing, and error/guard mismatch.

An independent command-line implementation can run only the handover suite, without implementing the flat operation or the Lean product's `--manifest` behavior:

```sh
lake exe checkCandidateConformance \
  --candidate target/debug/a12-rust-reference \
  --suite reference/single-group-correlation-v1.conformance.json
```

The runner requires deterministic candidate bytes but compares expected and actual JSON structurally, so object-key order is not cross-language normative. Its current lack of a wall-clock timeout and streamed output cap is a documented spike limitation, not a production qualification.

The runner also has an in-memory integrity mode that first validates all canonical case metadata/evidence links, then corrupts sixteen independent suite/manifest boundaries and requires rejection; `checkReferenceProcess` invokes it automatically and the direct command prints `16/16 guards passed`:

```sh
lake exe checkCandidateConformance \
  --self-test \
  --suite reference/single-group-correlation-v1.conformance.json
```
