# Normalized reference protocol v1

This document owns the exact process and JSON contract of the first product-shaped Lean reference interpreter. It describes a normalized transport over the existing checked flat evaluator, not the concrete English/German A12 DSL, general DM-JSON, or raw user-input parsing.

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

Protocol v1 accepts exactly one complete JSON request from standard input and writes exactly one compact deterministic JSON response followed by one newline to standard output. Object keys are emitted in the pinned Lean toolchain's sorted order; this is a deterministic encoding, not a claim of general RFC canonical JSON. `--manifest` writes the generated supported-fragment manifest. Any other argument is an invocation error.

Exit `0` means a complete machine-readable response or manifest was written, including invalid UTF-8, malformed JSON, unsupported input, model rejection, and elaboration rejection. Exit `2` means invalid command-line arguments; standard output is empty and standard error contains the invocation diagnostic. Exit `1` is reserved for an actual IO failure or internal invariant failure; domain errors never use standard error.

## Request envelope

The eight top-level members shown below are required. Every selected tagged variant has its own closed required member set; members belonging to another variant are rejected and some shapes require a member to be absent. Unknown object members are rejected at every level. Duplicate JSON object members are rejected before decoding; they are never accepted with last-member-wins behavior.

This is an envelope schematic, not a runnable request; `condition` and the model contents must be one of the complete forms below. Use the linked fixtures for runnable data.

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

The remaining request bounds are 1,024 fields, 1,024 cells, 128 repeatable-group declarations, 64 condition levels, 4,096 condition nodes, 64 segments per complete field path or group path, 64 repeatable-scope levels, 256 UTF-8 bytes per path segment, and 256 characters per normalized decimal. The generated [supported-fragment manifest](../reference/supported-fragment-v1.json) is the machine-readable owner of every numeric limit.

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

Protocol v1 carries `repeatableGroups` and each field's `repeatableScope` so an expanded model can be checked faithfully and an attempted repeatable reference can be rejected by the existing elaborator. It does not expose row-addressed cells or repeatable evaluation. Every field actually evaluated by this operation must have an empty repeatable scope.

## Structured paths and conditions

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

## Responses

A semantic result is successful even when it is `unknown`:

```json
{"kernelBehaviorVersion":"30.8.1","outcome":"ok","protocolVersion":1,"verdict":{"polarity":"omission","tag":"fired"}}
{"kernelBehaviorVersion":"30.8.1","outcome":"ok","protocolVersion":1,"verdict":{"tag":"notFired"}}
{"kernelBehaviorVersion":"30.8.1","outcome":"ok","protocolVersion":1,"verdict":{"tag":"unknown"}}
```

A domain rejection uses a stable category/code pair, a JSON-location hint, and structured details. Public diagnostics never expose Lean constructor `repr` text:

```json
{"diagnostic":{"at":"$.condition","category":"unsupported","code":"operator","details":{"operator":"less"}},"kernelBehaviorVersion":"30.8.1","outcome":"error","protocolVersion":1}
```

The complete protocol-v1 category/code inventory is generated from the finite Lean `DiagnosticCode` enum into the manifest's `diagnostics` table; category cannot be paired with an arbitrary code. The response envelope, category, and code are compatibility identifiers. `at` and `details` are deterministic diagnostic aids, but consumers must tolerate additional detail members in a compatible implementation update instead of treating the current detail object as a second discriminant. A future internal constructor must be explicitly classified before it can cross this boundary. The impossible checked-lowering result `incoherentCore` is an internal failure and therefore cannot masquerade as an ordinary unsupported request.

## Supported fragment and exclusions

The generated [`supported-fragment-v1.json`](../reference/supported-fragment-v1.json) is a closed positive support declaration mechanically compared with the CLI's `--manifest` output. Decoder acceptance uses the same finite comparison, path, field-kind, condition, raw-cell, and diagnostic classifiers that generate the manifest; black-box boundary probes guard the sparse-omission and child-relative near misses. `recognizedButUnsupportedComparisonOperators` is intentionally outside `accepted`. The `knownExclusions` are useful named boundaries, not an exhaustive inventory of the A12 language universe. In particular, protocol v1 excludes the concrete DSL, general DM-JSON and `Document` adaptation, String/date/time/enumeration values, ordering and arithmetic, repeatable evaluation and correlation, computations, partial validation, and message construction.

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

Each adjacent `.response.json` file is the expected response and can be run with the same redirection pattern shown above. [`A12Kernel/ReferenceProcessTestMain.lean`](../A12Kernel/ReferenceProcessTestMain.lean) invokes the compiled executable, checks exit status and both output channels, compares deterministic compact JSON, repeats and reorders the success request, and compares the shipped manifest with `--manifest`. Its generated adversarial cases additionally cover invalid UTF-8, capped input, hostile JSON numbers and nesting, portable-natural and decimal bounds, all recognized ordering operators, version and operation assertions, model/cell/repeatable rejection, complete-path boundaries, explicit omission, wrong-kind classified values, and the unlisted child-relative near miss.
