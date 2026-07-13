# External kernel evidence

This document owns the portable evidence boundary between the external A12 kernel harness and the Lean theory. It describes what is retained, what `lake test` checks, and which correspondence claims the artifacts do and do not support.

## Roles and provenance

[`../evidence/kernel-30.8.1/`](../evidence/kernel-30.8.1/) contains 11 focused, own-domain conformance cases and their standalone DM-JSON models. They were captured outside this repository through a12-dmkits' [`CorpusCapture`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/CorpusCapture.kt) boundary in the local `a12-rulekit/` checkout. Capture records the Groovy-dynamic kernel result as the anchor, rejects a case if the clean-room interpreter disagrees, executes the static-Java kernel strategy, and records any strategy split. These retained cases have no recorded divergence, so both kernel strategies and the interpreter agreed at capture time.

The cases use a12-dmkits' portable conformance shape: pinned kernel version, model reference, ordered document placements, operation, complete observed message signatures, and optional divergence records. The models and full signatures are retained rather than replacing them with Lean-shaped expected values. This repository contains no kernel binary, binding, or runtime dependency.

## Why replay uses a focused projection

The portable a12-dmkits case format deliberately starts from full DM-JSON and stored condition text. The current Lean capsule starts later: expanded field declarations, classified scalar cells, and structured parser-independent conditions. Consuming the full corpus directly would force a premature DM-JSON loader and bilingual condition parser into a capsule whose semantics intentionally begin after those boundaries.

[`projection.json`](../evidence/kernel-30.8.1/projection.json) therefore carries only the closed input projection needed by the current Lean fragment: field declarations, structured paths/conditions, classified cells, row-content eligibility, and operation kind. It does not contain an expected Lean verdict. [`A12Kernel/EvidenceMain.lean`](../A12Kernel/EvidenceMain.lean) loads each referenced external case, verifies its ID, kernel version, retained model, and absence of strategy divergence, filters the complete raw signatures by the focused authored rule code, executes the typed projection through public Lean elaboration/evaluation, and compares the observable emissions.

This is an observation-level bridge. A fired Lean verdict maps to its VALUE/OMISSION message signature; both `notFired` and `unknown` map to no authored message because the external validation output cannot distinguish them. Consequently the malformed cases support the claim that the authored rule is suppressed while formal errors remain externally visible, but they do not by themselves prove that the kernel's hidden intermediate result is specifically Lean's `unknown`. That stronger internal treatment remains grounded in source/findings plus the Lean definition and its internal laws.

The evidence transport and IO driver stay outside [`A12Kernel.lean`](../A12Kernel.lean), [`A12Kernel/Conformance.lean`](../A12Kernel/Conformance.lean), and [`A12Kernel/Proofs.lean`](../A12Kernel/Proofs.lean). The pure replay projection is not part of the trusted semantic theorem root; it is an empirical adequacy check over retained observations.

## Current coverage

The retained bundle covers these focused observable witnesses:

- empty Number comparison in a content-bearing row and its suppression by the all-empty row gate;
- empty Boolean and Confirm comparison asymmetry;
- `FieldNotFilled` eligibility on an otherwise empty row;
- malformed Number suppression and the `healthy Or malformed` / `healthy And malformed` branch behaviors;
- positive plain parent-relative and bare ancestor Number resolution;
- an empty absolute/non-repeatable required Number producing `mandatoryField`.

This closes the external evidence gap for those exact observations, not for the whole implemented surface. Requiredness still needs filled and malformed companions. Path coverage still needs separating witnesses for local-versus-ancestor precedence, model-wide fallback, absolute paths, no-fire values, and the supported static rejection boundaries. The current bare-ancestor positive witness alone does not distinguish ancestor lookup from a model-wide unique-name fallback. These remain explicit obligations in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md).

## Running the gate

```sh
lake test
```

The test driver rejects an unsupported schema/kernel version, empty or duplicate case identities, duplicate or undeclared projected cells, invalid projected models, unsafe references, missing retained models, kernel-strategy divergences, elaboration failures, and signature mismatches. A successful run reports the number of agreeing projections.

`lake build` remains the pure internal build and executable-example gate. `lake test` adds retained external correspondence evidence; [`scripts/check-lean-trust.sh`](../scripts/check-lean-trust.sh) independently audits the trusted theorem closure. None substitutes for the others.
