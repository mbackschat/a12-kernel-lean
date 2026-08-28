# Transform consumer lab

- `status`: green
- `contract`: a checked A12 artifact becomes another checked A12 artifact under an explicitly named observation relation and preconditions.
- `authority`: [addressed numeric-operation consumer laws](../../A12Kernel/Proofs/AddressedNumericOperationConsumer.lean), especially universal identity preservation of Analyze, Execute, and rich result views.
- `authority`: the fixed [Boolean/Confirm constant definition and result/application laws](../../A12Kernel/Proofs/BooleanConstantComputation.lean), exact [execution cases](../../A12Kernel/Conformance/BooleanConstantComputation.lean), and the shared [Boolean result/application owner](../../A12Kernel/Elaboration/BooleanComputationResult.lean).
- `handover`: the [bounded numeric-operation capability](../implementation/numeric-and-temporal.md#cap-addressed-numeric-operation-consumer), the [fixed Boolean/Confirm constant capability](../implementation/computations.md#cap-boolean-confirm-constant-computation-target-admission), and their explicit rule that fingerprint difference is not semantic inequivalence.

## First probe

Implement the exact identity Transform over one checked addressed numeric operation and validate its structural fingerprint. Then reject a tempting nonidentity rewrite that changes operation parameters while retaining source and target fields. The point is to experience the difference between producing a plausible rewrite and carrying a preservation relation.

Lean acceptance is universal identity preservation from the existing theorems plus one checked parameter-change counterexample. Wrong accounts are dependency-only identity, derived-scale-only identity, fingerprint equality as general equivalence, and finite example agreement as a universal preservation claim.

## Fixed Boolean declaration-relocation probe

Relocate only the authored declaration group of fixed Boolean `true`, Boolean `false`, and Confirm `true` constants between two valid fixed groups. Certify the exact `fixedBooleanConstantRuntimeProjection`, which covers execution, every public result channel, source-relative change classification, and separate-destination application while explicitly excluding checked-definition equality. Refuse changed payloads, targets, repeatable placement, malformed declaration paths, Confirm `false`, and a complete-definition equality claim without asserting semantic inequivalence.

Lean acceptance composes the existing checked execution, result, and application owners. A disposable theorem establishes projection and application equality for all checked source and destination documents across the three exact relocations, while a second theorem checks every normalized Boolean target-state branch for both values. An independent standard-library reconciliation fixes the exact 75-case signature. Wrong accounts are declaration-group iteration, destination-relative classification, applying source-identical results, incomplete structural identity, repeatable or malformed-path admission, Confirm `false`, and complete-definition equality.

## Lab record

| Run | Status | Current result |
|---|---|---|
| `transform-numeric-identity-01` | green | A cold standard-library consumer certified only an exact `RangeAsNumber(source, 1, 4)` identity and returned `not-certified` for an endpoint change, a Round-mode change, and ordered `Min` operand reversal. Dependency-only identity, derived-scale-only identity, mismatch-as-inequivalence, and finite-agreement-as-universal mutations were all killed. The Lean laws universally preserve Analyze, execution, and rich-result views for exact identity; conformance retains every changed parameter while making no inequivalence claim. The disposable artifact, implementation, and tests totaled 312 nonblank lines, took 148 seconds, and added no dependency or nonidentity semantic guess. |
| `transform-boolean-declaration-relocation-02` | green | A fresh isolated standard-library consumer used 289 implementation and 480 artifact/test/report nonblank lines, all capability-local, in about 307 seconds. It certified the three exact declaration relocations under `fixedBooleanConstantRuntimeProjection`, rejected seven structural or claim controls, and retained unequal definition identity. All 75 source/destination state comparisons agreed; an independent checker reproduced digest `91a53728ebbc84564f033a4e3e71ae220e456476e29d2d3ddd1b4d3e19e6caab`, and final disposable Lean witnesses compiled in 4.9 seconds. Nine tests passed and all ten wrong accounts failed with no dependency, semantic question, or guess. Repeatable relocation, wider operations, generated validation, scheduling, materialized topology, Kernel runtime correspondence, protocol, shipment, compatibility, and inequivalence of refused transforms remain outside. |
