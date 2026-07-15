# Normalized reference protocol v1

This document owns the exact process and JSON contract of the product-shaped Lean reference interpreter. Protocol v1 currently exposes two disjoint normalized operations over existing checked evaluators: flat validation and one direct-child captured-outer correlation shape. The current executable semantics is reference semantics 0.3.0; protocol 1 also has a frozen historical 0.2.0 line described below. This is not the concrete English/German A12 DSL, general DM-JSON, or raw user-input parsing.

## Invocation and process contract

The executable is the Lake target `a12-kernel-reference`:

```sh
lake exe a12-kernel-reference < examples/reference-cli/empty-number-equals-zero.request.json
```

The generated manifest is available through the same executable:

```sh
lake exe a12-kernel-reference --manifest
```

The manifest is how a consumer detects the reference-semantics account implemented by those exact executable bytes. The current output is [`supported-fragment-v2.json`](../reference/supported-fragment-v2.json) and carries `referenceSemanticsVersion: "0.3.0"`. A request carries `protocolVersion` and `kernelBehaviorVersion`, but it has no `referenceSemanticsVersion` member and there is no per-request selector for 0.2.0 versus 0.3.0. Responses likewise do not echo the reference-semantics identity. A production consumer must therefore inspect `--manifest` before use and pin the executable or release digest with that manifest; response shape alone cannot distinguish two accounts that agree on a particular request.

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

The remaining request bounds are 1,024 fields, 1,024 cells, 1,024 correlation candidates, 128 repeatable-group declarations, 64 condition or correlated-`Having` levels, 4,096 condition or `Having` nodes, 64 segments per complete field path or group path, 64 repeatable-scope levels, 256 UTF-8 bytes per path segment, and 256 characters per normalized decimal. The current generated [supported-fragment manifest](../reference/supported-fragment-v2.json) is the machine-readable owner of every numeric limit.

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

An empty Number still compares through its kind-specific zero value, but a true comparison's polarity depends on whether filling the declared field could make that comparison false. For an unsigned field, `empty != -1` fires with VALUE polarity: filling can only grow from zero, so no legal value can reach the negative literal and the omission is not responsible for the error. The regression fixture [`empty-unsigned-number-not-equal-negative.request.json`](../examples/reference-cli/empty-unsigned-number-not-equal-negative.request.json) locks that directional distinction through the public process.

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

### Development flat cold-handover slice

[`flat-validation-empty-logic-v1.capability.json`](../reference/flat-validation-empty-logic-v1.capability.json) narrows this wider flat operation to eight evidence-derived inputs suitable for the first cold independent-implementation exercise. Its language-neutral semantics and exclusions are in [`IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md), its runnable index is [`flat-validation-empty-logic-v1.conformance.json`](../reference/flat-validation-empty-logic-v1.conformance.json), and its requests and responses live under [`examples/reference-cli/flat-evidence/`](../examples/reference-cli/flat-evidence/).

This descriptor, suite, and the two implementer kits are frozen reference-semantics 0.2.0 shipments. They remain available to audit the completed Rust experiment and are not the current executable's advertised compatibility line. Current candidate testing uses [`flat-validation-empty-logic-v2.conformance.json`](../reference/flat-validation-empty-logic-v2.conformance.json) and [`single-group-correlation-v2.conformance.json`](../reference/single-group-correlation-v2.conformance.json), both pinned to reference semantics 0.3.0 and [`supported-fragment-v2.json`](../reference/supported-fragment-v2.json).

The frozen typed evidence bridge re-derives those requests directly from the retained flat projection and pairs them with its explicit historical 0.2.0 verdict table. It is deliberately decoupled from today's decoder and evaluator, so a later current-semantics correction cannot reinterpret the completed handover. Four responses are fired and their final polarity is directly supported by the focused external message. Four are externally silent; their exact historical `notFired` or `unknown` response remains a Lean-account projection because external validation output cannot distinguish those hidden verdicts. The capability descriptor and suite state that source classification for every case.

Run `lake exe syncFlatHandover --check` to verify the frozen generated descriptor, suite, [fixtures](../examples/reference-cli/flat-evidence/), support-manifest evidence boundary, and adjacent source-maintainer [mutation qualification plan](../reference/flat-validation-empty-logic-v1.mutation-plan.json) against their historical typed projection. Because that v1 shipment is now immutable, `lake exe syncFlatHandover --write` deliberately rejects it; a changed capability must receive a new identity and generator path rather than rewriting these files. The mutation plan targets candidate behavior exposed through protocol 1 but is not part of the wire contract or the immutable first cold bundle.

This is a `developmentColdHandover` capability, not full flat-operation release closure. It excludes the wider accepted path, value, condition, and negative-diagnostic surface, and passing its indexed cases supports only the named finite slice.

The later operator-sensitive evidence capsule does not widen this frozen capability descriptor or its eight-case Rust qualification boundary. Its directional Number witness instead appears as the ninth case of the current flat v2 suite. Direct String comparison and `Length(String)` exist only in the internal checked semantics/evidence lane today; protocol v1 still admits only Number, Boolean, and Confirm field kinds and has no String or `Length` request form.

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

The response envelope intentionally identifies protocol 1 and kernel behavior 30.8.1, not the executable semantics line. This preserves the wire shape across the correction but means a caller cannot detect 0.2.0 versus 0.3.0 from a response. Use the exact binary's `--manifest` result and a binary or release digest as the compatibility pin.

A domain rejection uses a stable category/code pair, a JSON-location hint, and structured details. Public diagnostics never expose Lean constructor `repr` text:

```json
{"diagnostic":{"at":"$.condition","category":"unsupported","code":"operator","details":{"operator":"less"}},"kernelBehaviorVersion":"30.8.1","outcome":"error","protocolVersion":1}
```

The complete protocol-v1 category/code inventory is generated from the finite Lean `DiagnosticCode` enum into the manifest's `diagnostics` table; category cannot be paired with an arbitrary code. The response envelope, category, and code are compatibility identifiers. `at` and `details` are deterministic diagnostic aids, but ordinary consumers must tolerate additional detail members in a compatible implementation update instead of treating the current detail object as a second discriminant. A conformance suite pins each complete expected response for its exact suite identity, so candidate implementations must reproduce the current fixture details until that suite or its comparison policy changes. A future internal constructor must be explicitly classified before it can cross this boundary. The impossible checked-lowering result `incoherentCore` is an internal failure and therefore cannot masquerade as an ordinary unsupported request.

## Supported fragment and exclusions

The generated [`supported-fragment-v2.json`](../reference/supported-fragment-v2.json) is the current schema-2 closed positive support declaration mechanically compared with the CLI's `--manifest` output. Its `operations` array gives flat and correlation separate accepted sets and unsupported comparison lists; correlation separately declares finite ordinary-path, star-path, and cell-form sets plus whole-rule and operator-specific scale constraints. The shared diagnostics, limits, compatibility versions, and precise exclusions remain top-level. Decoder acceptance uses the same finite operation, comparison, path, field-kind, condition/`Having`, raw-cell, origin, and diagnostic classifiers that generate the manifest. Black-box probes guard sparse omission, operation-specific absolute/child-relative success, parent-relative/bare rejection, parent/nested relative stars, row topology, cell addresses, rejected causes, error/guard identity, and origin near misses. The known exclusions include concrete DSL and general DM-JSON/`Document` adaptation, general ordering and arithmetic beyond the named comparison cells, general repeatable evaluation, nested or multiple stars, cross-group correlation, general correlation consumers, filtered-result polarity, computation, partial validation, and message construction.

[`reference-semantics-lineage-v1.json`](../reference/reference-semantics-lineage-v1.json) is the readable history generated from [`Reference/Lineage.lean`](../A12Kernel/Reference/Lineage.lean). Each line records its complete reference-semantics/protocol/manifest-schema/kernel-behavior tuple plus its suite IDs and operations. Historical 0.2.0 is pinned to source revision `9fa50276f5fb70dcd879b0a9712c8d69c0868967`; its retained [`separating replay receipt`](../reference/reference-semantics-0.2.0-separating-replay.json) records `fired.omission`, while the current 0.3.0 process yields `fired.value` for the same directional-Number request. The lineage pins [`reference-semantics-0.2.0.lock.json`](../reference/reference-semantics-0.2.0.lock.json); the process gate verifies that lock's own digest and rehashes every dependency it inventories, in addition to checking the principal v1 manifest, suites, capability, differential profile, mutation plan, and retained result. It requires the current flat v2 suite to preserve the historical eight-case prefix and add exactly the typed evidence-bound witness, and requires the current correlation v2 suite to preserve the historical 16-case body. It never relabels the 0.2.0 Rust qualification as 0.3.0.

## Regression-checked sample data

The files under [`examples/reference-cli/`](../examples/reference-cli/) are both runnable sample data and black-box test fixtures. Start with these separating examples:

- [`empty-number-equals-zero.request.json`](../examples/reference-cli/empty-number-equals-zero.request.json) demonstrates that an omitted Number cell compares as zero and fires with omission polarity.
- [`empty-unsigned-number-not-equal-negative.request.json`](../examples/reference-cli/empty-unsigned-number-not-equal-negative.request.json) demonstrates that an omitted unsigned Number under `!= -1` fires with VALUE polarity because no legal filling can reach the negative literal.
- [`empty-boolean-equals-true.request.json`](../examples/reference-cli/empty-boolean-equals-true.request.json) demonstrates that an omitted Boolean suppresses a direct comparison and does not fire.
- [`empty-row-gate.request.json`](../examples/reference-cli/empty-row-gate.request.json) holds the omitted Number comparison fixed but sets `hasContent` false, demonstrating the independent full-validation row gate.
- [`malformed-number.request.json`](../examples/reference-cli/malformed-number.request.json) demonstrates that rejected input yields the successful semantic verdict `unknown`.
- [`boolean-confirm-composition.request.json`](../examples/reference-cli/boolean-confirm-composition.request.json) exercises Boolean and Confirm comparisons, inequality, filled/not-filled, `And`/`Or`, and absolute, parent-relative, and bare paths in one accepted request.
- [`correlation-direction.request.json`](../examples/reference-cli/correlation-direction.request.json) is the smallest asymmetric captured-outer sample and returns `[2,3]`.

Each adjacent `.response.json` file is the expected response and can be run with the same redirection pattern shown above. The generated flat set under [`flat-evidence/`](../examples/reference-cli/flat-evidence/) and the curated correlation set are completely indexed for the current account by their [flat v2](../reference/flat-validation-empty-logic-v2.conformance.json) and [correlation v2](../reference/single-group-correlation-v2.conformance.json) suites; those machine-readable suites, not a duplicated Markdown list, own their complete finite case inventories. The frozen v1 suites remain the exact 0.2.0 handover indices. [`ARTIFACTS.md`](ARTIFACTS.md#examples-human-examples-and-regression-fixtures) explains which examples are generated or curated and how they evolve.

[`A12Kernel/ReferenceProcessTestMain.lean`](../A12Kernel/ReferenceProcessTestMain.lean) invokes the compiled executable, checks the process and JSON contract, compares the current shipped manifest and lineage mirror, digest-checks frozen v1 artifacts, exercises hostile and near-miss inputs, runs every suite's structural integrity self-test, and uses the compiled current Lean reference as a control candidate only for v2 suites. [`TESTING.md`](TESTING.md#reference-process-harness-and-sample-data) owns these harness mechanics; this document owns the observable wire contract.

An independent command-line implementation can run only its selected suite without implementing the other operation or the Lean product's `--manifest` behavior. For a candidate claiming the current flat v2 suite:

```sh
lake exe checkCandidateConformance \
  --candidate target/debug/a12-rust-reference \
  --suite reference/flat-validation-empty-logic-v2.conformance.json
```

The `checkCandidateConformance` suite runner validates the selected suite against the committed support manifest named by that suite, then requires deterministic candidate responses and compares expected and actual JSON structurally, so object-key order is not cross-language normative. It does not call the candidate's `--manifest` or prove that the candidate advertises that identity independently; the suite path and any surrounding qualification record supply the claim being tested. Its current lack of a wall-clock timeout and streamed output cap is a documented spike limitation, not a production qualification. The separate bounded generated-differential runner is maintainer qualification machinery and does not change this public protocol.

The runner also has an in-memory integrity mode that validates canonical case metadata and evidence links, then mutates independent suite, manifest, and fixture boundaries and requires rejection. `checkReferenceProcess` runs structural self-tests for historical v1 and current v2 suites, but executes the compiled current Lean reference as a control candidate only for v2:

```sh
lake exe checkCandidateConformance \
  --self-test \
  --suite reference/flat-validation-empty-logic-v2.conformance.json
```

The frozen [flat](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) and [correlation](IMPLEMENTER-KIT-CORRELATION.md) kits deliberately retain their v1 commands and 0.2.0 identities for historical reproduction. Do not pair those claims with an arbitrary current binary merely because its response happens to agree on the indexed cases.
