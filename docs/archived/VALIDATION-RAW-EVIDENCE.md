# Historical validation evidence estate

> **Status:** archived 2026-07-19 after exact legacy/compact agreement. This is the recovery and provenance record for the removed flat, path, required, operator-sensitive, iteration, correlation-runtime, and correlation-authoring raw evidence estates. It is not a live replay specification.

## What remains live

Routine replay consumes the project-reviewed compact [`semantic-observations.json`](../../evidence/kernel-30.8.1/captures/validation-core-v1/semantic-observations.json), SHA-256 `bd8f9411cd479b009a71e7c5a93e0369815c0a0b4647f6eacb5a4b1957532db7`, through [`ValidationProjection.lean`](../../A12Kernel/Evidence/ValidationProjection.lean). The 116,974-byte bundle contains seven closed families and 49 records: 25 normalized public evidence associations and 24 private semantic replays. There are 48 distinct external observations because the directional empty-Number case intentionally appears once in each half.

The public associations are enforced by `lake exe checkReferenceProcess` and the candidate-conformance runner. The runner pins the whole bundle, selects the declared case, requires exact normalized-request equality, and compares the expected response only at the fidelity the external observation supports. `lake test` separately replays the 24 private cases through the live checked semantics. The compact bundle's SHA-256 is the sole exact byte identity; readable family identities, counts, and duplicate checks protect routing without duplicating a second manifest of every pinned byte.

The required-empty record retains the externally observed `mandatoryField` code and `/Order[1]/Quantity` pointer in addition to firing and omission polarity. The compact path and iteration records do not retain incidental authored fixture codes or pointers that their current Lean results do not model.

## One-time migration assurance

Commit `a04d6d9f51227dbe47014a5181590507e1b269bd` is the immutable validation dual-path agreement checkpoint. In that revision one `lake test` run checked all 48 validation cases through their complete legacy binders and also replayed the 24 private compact validation records. The already-settled 22-case root-String and five-case cascade compact lanes passed in the same run; their own archives record their earlier complete-binder comparisons. Both current V2 conformance suites passed their reference and self-test gates against the 25 compact public associations. The compact request/response/case binding also rejected a changed normalized request, a changed projected response, and an alias to another existing retained case.

The migration review independently checked the compact bundle against all five legacy projection digests, the operator receipt, the public fixtures, and the live semantics. It found and closed two information-boundary defects before the checkpoint: static rejection observations now require `kernelCode` and `rejectionClass` together, and the required-empty compact observation retains its modeled message identity. After this checkpoint the legacy readers and raw estate were removed; there is no permanent converter, dual reader, or raw packet binder.

The clean pre-migration revision is `e3f90367df18d504319ea65d29558b5a6c567f3a`. It contains the complete legacy estate before the compact validation bundle was added.

## Recovery identities

| Historical unit | Identity |
|---|---|
| Flat/path/required projection SHA-256 | `cee1f64ed7395dcd87da5488ebb4e602c332d9ea1bde50fc06886c1c1e08b468` |
| Operator-sensitive projection SHA-256 | `f0cd23eaf7f6e6f7a7109be6d6ed73848542281597a2a51e92cd37d1892b301b` |
| Operator capture receipt SHA-256 | `fe86642caf0354bcdec217801824e64aa9725e1a1662e41b1d55d81185d3c7e2` |
| Iteration projection SHA-256 | `d9b470e94fc577940d7bab2a8b4be9dd303acff31145fe03de68872dd2088be5` |
| Correlation-runtime projection SHA-256 | `d7da5dcca7e743a7216e3de6a194a243e1fe4af91285fad4779f410dd58db787` |
| Correlation-authoring projection SHA-256 | `fadb3eaf1e0192ca81291de11786d9aa1b5a9e2fff2d1ffcd6a4a2e972bc6b0e` |
| Compact validation bundle SHA-256 | `bd8f9411cd479b009a71e7c5a93e0369815c0a0b4647f6eacb5a4b1957532db7` |
| Full `evidence/kernel-30.8.1` Git tree before migration | `0dbad82892810e1f33d8da60752ff9a9152c2352` |
| Full `A12Kernel/Evidence` Git tree before migration | `e46d23b6813cc01aee85f6813f45acd2e4980e55` |
| Correlation case-directory Git tree | `aca1fb3d1bdc63e95da3a704b603c1eef9d435f4` |
| Diagnostics-directory Git tree | `7bd2461a3976a8396dcb0f4de8785a17b990eba5` |
| Models-directory Git tree | `e309f18ddfd2943e19550e07b26aa5064f1ece3a` |
| Iteration case-directory Git tree | `35bf3451fcc7a169c946cb3a4c97c109ef8281aa` |

The principal introduction and correction revisions are:

| Area | Revision |
|---|---|
| Initial flat evidence replay | `49b782d806fe3f745a80afb0567d59bb461a739d` |
| Corrected two-tier path resolution and expanded flat evidence | `819623f90f39563c5ced571d279168c9d8036347` |
| Uncorrelated filtered iteration | `3b4262ed9785405e0b5b01740a88121a3a51d54b` |
| Correlated consumer evidence extension | `4374b4b8604328642e5f5cc31b96d90b8feaef9a` |
| Initial captured-outer correlation | `658185dbe6a9e25bbbe6cf59b1922972c556a1c0` |
| Focused correlation evidence closure | `1b148de3283aa45ca7f5152630cc07267857476c` |
| Checked correlation-authoring evidence | `63b14def7e50b2b5c171129676b9c5b3801fa236` |
| Operator-sensitive empty-value evidence | `ced07282ca56fa44a6b9d5e81d768cf6d8162b18` |

Use `git show a04d6d9f51227dbe47014a5181590507e1b269bd:<path>` to inspect a removed artifact, or `git archive a04d6d9f51227dbe47014a5181590507e1b269bd -- <paths>` to reconstruct a disposable audit tree. Do not restore the historical stack to current `main` merely to run ordinary evidence replay.

## Operator receipt

The operator-sensitive receipt was produced by a12-dmkits revision `699e8619ac1667c861e14b285c5924ac57a705f1`. Its anchor was `kernel-groovy-dynamic`; `kernel-java-static` supplied cross-route confirmation and the a12-dmkits interpreter supplied triangulation. All six rules were accepted by the kernel consistency check, and all three strategy signature lists agreed in all six cases.

| Retained input | SHA-256 |
|---|---|
| String/Length model | `d38409305bd5bdc6928f582e21290592c8701fa49d248e0469ef5af81161c76a` |
| Directional Number model | `94e6d86eaf60b27bef5ca19e276eea20ef5c449b22b2f4360cbab72662e9dcd7` |
| `string-length-empty-content` | `e59c8d136973d935127df11c1272a20c223f8ce53cc5c168b2cae276254f1af6` |
| `string-length-filled-abc` | `76dd43aa9d844cf59e7bc3ffb9df3b2c94196558008ec2b9e1cd5b218d6bcb6d` |
| `string-length-filled-six` | `2f117d41624c1953d23b259638e167a4396f282b4ce715c782f79fcd4c987db1` |
| `string-length-empty-row` | `ae0d4cbc5dde8924c2fce010b1b4daf0b166b1f1d53645c1f5a94d89a8a68652` |
| `number-directional-empty-content` | `eaae2304709e777c5aebd800db99b79bfad1f1a02a4d87e390a23cdf49f34b94` |
| `number-directional-filled-zero` | `3d8ac8e0454cf08b32b7c6e99a0a29890ed4a261d3417331e54a7211ef4ee06e` |

The historical capture command and complete rule/model/case declarations remain recoverable at the checkpoint. The command is not a current maintained interface and must not be described as runnable capture support.

## Preserved claims and deliberate reductions

The flat/path/required estate contained 19 cases. All 17 runtime observations agreed across both kernel routes and the a12-dmkits interpreter at capture time, with no recorded kernel-strategy divergence; the two path-resolution rejection records were static diagnostics. Current public flat cases retain exact normalized requests and externally supported firing/polarity or suppression. Silent authored output establishes only suppression and cannot distinguish the kernel's hidden `NotFired` from `Unknown`.

The six operator-sensitive cases retain direct empty String comparison, empty String consumed by `Length`, empty-row gating, filled String controls, signed and unsigned directional Number polarity, exact authored codes, pointers, and omission/value polarity. The public directional witness and the private operator matrix intentionally share one external observation.

Both kernel routes agreed on all seven uncorrelated iteration cases. The historical a12-dmkits interpreter disagreed on `having-malformed-filter-drops`; that disagreement remains a triangulation fact and is not flattened into agreement. The compact replay derives selection and truth through the live one-star evaluator. Its omission label is the retained authored-message polarity, not a theorem that `K.tru` alone determines arbitrary validation polarity.

Both kernel routes and the a12-dmkits interpreter agreed on all 12 correlation-runtime cases. The historical raw models preserved the authored `$` condition, complete signatures, formal errors, and canonical-list ordering. The current public operation retains the exact normalized request and externally supported firing rows; it does not claim that kernel output order was canonical or expose the richer hidden channels.

The four correlation-authoring records retained complete seeded models, candidate drafts, and diagnostic observations. They establish three rejection code/class pairs and one static acceptance. The accepted case does not externally establish runtime firing rows; its public empty-row answer remains a Lean-account evaluation after accepted lowering.

The compact path and cell transcription is project-reviewed rather than producer-certified. Four source-projection digests and the operator receipt remain embedded in the compact bundle and are bound by its whole-file digest; the separate operator-projection digest remains in this archive and the dual-path checkpoint. The deleted raw estate is not re-audited during routine replay.

## Removed estate

The deletion removed 85 raw data files totaling 761,310 bytes: five projection files, the operator receipt, all legacy cases, diagnostics, models, and the one triangulation record. It also removed 12 schema/replay/bridge modules totaling 103,241 bytes and 2,061 nonblank Lean lines, then replaced the 1,000-line legacy evidence driver with a small dispatcher. The permanent validation replacement is the 116,974-byte compact bundle plus 428 nonblank lines of typed projection and focused tests.
