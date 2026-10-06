# Public-process and candidate testing

Read the applicable sections when a public process, candidate suite, shipment or release check is triggered. These procedures belong to the [testing methodology](TESTING.md); its [command ladder](TESTING.md#command-ladder), [assurance cadence](TESTING.md#default-assurance-cadence) and [tier gates](TESTING.md#tier-gates) remain authoritative. Reading this guide does not itself trigger its commands or authorize external actions.

## Reference-process harness and sample data

[`A12Kernel/ReferenceProcessTestMain.lean`](../A12Kernel/ReferenceProcessTestMain.lean) discovers the sibling `a12-kernel-reference` build artifact and invokes it as an operating-system process. It does not call `evaluateText` or any protocol decoder directly, so it covers executable wiring, arguments, stdin/stdout/stderr, and exit behavior in addition to JSON semantics. Lake's `needs` edge builds the tested executable first without making this gate part of the retained-kernel `lake test` claim.

The requests and adjacent expected responses under [`examples/reference-cli/`](../examples/reference-cli/) are committed sample data as well as test inputs. The harness parses each readable expected JSON file and compares the executable's deterministic compact encoding, so whitespace in the maintained fixture is irrelevant while every JSON value is locked. [`PROTOCOL.md`](PROTOCOL.md#regression-checked-sample-data) gives representative runnable examples, and the machine-readable suites own the complete finite capability inventories; this methodology document does not duplicate either list.

The eight fixtures under [`examples/reference-cli/flat-evidence/`](../examples/reference-cli/flat-evidence/) were mechanically produced from retained typed flat cases, the historical 0.2.0 verdict table, and case-level observation classifications. They remain unchanged inputs for the corresponding current V2 cases. The deleted bridge, artifacts, hashes, and recovery revisions are recorded in the historical archive (`docs/archived/REFERENCE-SEMANTICS-0.2.0-AND-RUST-EXPERIMENT.md` at `a050f150`); `checkReferenceProcess` tests the retained fixtures and current V2 suites rather than reconstituting or digest-checking the retired shipment.

Generated-in-test adversaries cover hostile transport, numeric and path bounds, closed-object decoding, version and operation mismatches, model/cell/repeatable validation, operation-specific near misses, candidate topology, unsupported semantic constructors, invocation classes, and deterministic repeated success. The executable test source is authoritative for the exact adversarial matrix. `--manifest` output is compared structurally with current [`supported-fragment-v2.json`](../reference/supported-fragment-v2.json), ensuring the shipped readable mirror agrees with the Lean-generated manifest without requiring identical whitespace. The candidate-conformance control also loads the SHA-pinned compact [validation bundle](../evidence/kernel-30.8.1/captures/validation-core-v1/semantic-observations.json), requires each selected evidence case's exact normalized request, and compares the suite response only at the observation's declared fidelity. This single association check covers all 25 current public cases, including the directional witness, without a case-specific bridge.

Run the public process gate with:

```sh
lake exe checkReferenceProcess
```

[`PROTOCOL.md`](PROTOCOL.md) owns the exact public contract and gives the invocation pattern shared by every request fixture. This harness establishes compatibility of that boundary; it adds no kernel observation and therefore does not change the external-evidence count.

### Independent candidate suites

[`flat-validation-empty-logic-v2.conformance.json`](../reference/flat-validation-empty-logic-v2.conformance.json) and [`single-group-correlation-v2.conformance.json`](../reference/single-group-correlation-v2.conformance.json) are the current portable downstream indices for reference semantics 0.3.0. Each pins the capability, operation, reference-semantics, wire-protocol, manifest-schema, and kernel-behavior identities plus the support-manifest path, and each case names a normalized request, expected response, separating coverage labels, evidence kind, projection, retained case ID, exact externally supported projection, and expected-response source. [`A12Kernel/CandidateConformanceMain.lean`](../A12Kernel/CandidateConformanceMain.lean) uses bounded duplicate-safe JSON parsing for all inputs, enforces closed suite/case/evidence objects, validates the suite's compatibility tuple and finite evidence boundary against selected members of its committed support manifest, checks the allowed evidence/source combination and case-ID existence, invokes the candidate directly without a shell, requires exit `0`, empty standard error, normalized JSON plus a final newline, and byte-identical repeated output, then compares expected and actual JSON structurally so language-specific object-key ordering is irrelevant. It does not query a candidate manifest; a separate qualification record must pin the candidate and selected suite. Support-manifest and retained-projection objects intentionally remain extensible outside the members this runner consumes.

The eight flat [fixtures](../examples/reference-cli/flat-evidence/) were produced through the historical checked projection-to-protocol bridge before the independent implementation started and remain current V2 inputs. Their case-specific distinction between what the external observation supports and what the exact Lean response supplies remains normative; [`EVIDENCE.md`](EVIDENCE.md) and the [flat kit](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) own that classification. The correlation kit owns its different projection-association boundary. Historical machinery and results are archived (`docs/archived/REFERENCE-SEMANTICS-0.2.0-AND-RUST-EXPERIMENT.md` at `a050f150`); these integrity levels must not be blurred.

The selected committed-manifest operation must be unique and its `externalEvidenceBoundary` must agree with the suite's identity, finite claim scope, and case composition. The runner's in-memory integrity self-test validates the canonical metadata and evidence links, then mutates compatibility, manifest, count, evidence, duplicate-member, and closed-object boundaries and requires rejection. Run the current flat suite explicitly:

```sh
lake exe checkCandidateConformance \
  --self-test \
  --suite reference/flat-validation-empty-logic-v2.conformance.json
```

Run the suite against the reference as a control:

```sh
lake exe checkCandidateConformance \
  --candidate .lake/build/bin/a12-kernel-reference \
  --suite reference/flat-validation-empty-logic-v2.conformance.json
```

Replace `--candidate` with a Rust, Kotlin, or TypeScript executable to test that implementation without requiring it to implement the other operation, `--manifest`, or Lean's compact key order. Because the runner does not query a candidate manifest, pin the candidate bytes and claimed suite identity separately in any qualification record. A suite establishes only its indexed observable cases and does not transfer Lean's theorems to the candidate; use the current [flat kit's law and non-law index](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md#law-and-non-law-index) or [correlation kit's law index](IMPLEMENTER-KIT-CORRELATION.md#law-index-for-property-tests) as applicable. The current flat v2 suite is still a development slice, not full flat release closure. Each candidate invocation has a 10-second deadline, 1-second cleanup deadline, 1 MiB stdin and stdout caps, and a 64 KiB stderr cap. The relay streams both output channels and terminates the owned process group on timeout or overflow. This is cooperative macOS/Linux resource control for same-credential candidates, not a security sandbox, and the suite currently has no aggregate elapsed or byte budget.

### Historical Rust qualification experiment

The completed Rust experiment is immutable history rather than a live harness. The archived record (`docs/archived/REFERENCE-SEMANTICS-0.2.0-AND-RUST-EXPERIMENT.md` at `a050f150`) owns its exact source and candidate revisions, packet and result hashes, seven-mutation outcome, 52/52 generated-differential result, verdict distribution, limits, and recovery route. Those outcomes establish finite knowledge transport and mutation sensitivity only. They add no kernel evidence, transfer no Lean proof, approve no release, and say nothing beyond the pinned historical profile and mutations.
