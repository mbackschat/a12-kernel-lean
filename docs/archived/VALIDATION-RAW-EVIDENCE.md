# Historical validation evidence estate

> **Status:** archived 2026-07-19 after exact legacy/compact agreement. This is the recovery and provenance record for the removed flat, path, required, operator-sensitive, iteration, correlation-runtime, and correlation-authoring raw evidence estates. It is not a live replay specification.

## What remains live

Routine replay consumes the project-reviewed compact [`semantic-observations.json`](../../evidence/kernel-30.8.1/captures/validation-core-v1/semantic-observations.json), SHA-256 `e781b94e94fcc8b589aafcbbd11b64efca5a2ae175e8994b1e0db0c2e844661c`, through [`ValidationProjection.lean`](../../A12Kernel/Evidence/ValidationProjection.lean). The 116,974-byte bundle contains seven closed families and 49 records: 25 normalized public evidence associations and 24 private semantic replays. There are 48 distinct external observations because the directional empty-Number case intentionally appears once in each half.

The public associations are enforced by `lake exe checkReferenceProcess` and the candidate-conformance runner. The runner pins the whole bundle, selects the declared case, requires exact normalized-request equality, and compares the expected response only at the fidelity the external observation supports. `lake test` separately replays the 24 private cases through the live checked semantics. The compact bundle's SHA-256 is the sole exact byte identity; readable family identities, counts, and duplicate checks protect routing without duplicating a second manifest of every pinned byte.

The required-empty record retains the externally observed `mandatoryField` code and `/Order[1]/Quantity` pointer in addition to firing and omission polarity. The compact path and iteration records do not retain incidental authored fixture codes or pointers that their current Lean results do not model.

## One-time migration assurance

Commit `fe26645a5f6807e79d8a42c6ea0591acf3d51d96` is the immutable validation dual-path agreement checkpoint. In that revision one `lake test` run checked all 48 validation cases through their complete legacy binders and also replayed the 24 private compact validation records. The already-settled 22-case root-String and five-case cascade compact lanes passed in the same run; their own archives record their earlier complete-binder comparisons. Both current V2 conformance suites passed their reference and self-test gates against the 25 compact public associations. The compact request/response/case binding also rejected a changed normalized request, a changed projected response, and an alias to another existing retained case.

The migration review independently checked the compact bundle against all five legacy projection digests, the operator receipt, the public fixtures, and the live semantics. It found and closed two information-boundary defects before the checkpoint: static rejection observations now require `kernelCode` and `rejectionClass` together, and the required-empty compact observation retains its modeled message identity. After this checkpoint the legacy readers and raw estate were removed; there is no permanent converter, dual reader, or raw packet binder.

The clean pre-migration revision is `42c05a6e8ab3c58500260be103bbcc19a37d26e2`. It contains the complete legacy estate before the compact validation bundle was added.

## Recovery identities

| Historical unit | Identity |
|---|---|
| Flat/path/required projection SHA-256 | `cee1f64ed7395dcd87da5488ebb4e602c332d9ea1bde50fc06886c1c1e08b468` |
| Operator-sensitive projection SHA-256 | `f0cd23eaf7f6e6f7a7109be6d6ed73848542281597a2a51e92cd37d1892b301b` |
| Operator capture receipt SHA-256 | `fe86642caf0354bcdec217801824e64aa9725e1a1662e41b1d55d81185d3c7e2` |
| Iteration projection SHA-256 | `d9b470e94fc577940d7bab2a8b4be9dd303acff31145fe03de68872dd2088be5` |
| Correlation-runtime projection SHA-256 | `d7da5dcca7e743a7216e3de6a194a243e1fe4af91285fad4779f410dd58db787` |
| Correlation-authoring projection SHA-256 | `fadb3eaf1e0192ca81291de11786d9aa1b5a9e2fff2d1ffcd6a4a2e972bc6b0e` |
| Compact validation bundle SHA-256 | `e781b94e94fcc8b589aafcbbd11b64efca5a2ae175e8994b1e0db0c2e844661c` |
| Full `evidence/kernel-30.8.1` Git tree before migration | `0dbad82892810e1f33d8da60752ff9a9152c2352` |
| Full `A12Kernel/Evidence` Git tree before migration | `e46d23b6813cc01aee85f6813f45acd2e4980e55` |
| Correlation case-directory Git tree | `aca1fb3d1bdc63e95da3a704b603c1eef9d435f4` |
| Diagnostics-directory Git tree | `7bd2461a3976a8396dcb0f4de8785a17b990eba5` |
| Models-directory Git tree | `e309f18ddfd2943e19550e07b26aa5064f1ece3a` |
| Iteration case-directory Git tree | `35bf3451fcc7a169c946cb3a4c97c109ef8281aa` |

The principal introduction and correction revisions are:

| Area | Revision |
|---|---|
| Initial flat evidence replay | `9eead0d14704677c50c9fc49aa6754ce37c7a7b2` |
| Corrected two-tier path resolution and expanded flat evidence | `239ed71f7ab2be245c7f9a4742b6dd2701c4ee58` |
| Uncorrelated filtered iteration | `7c49ce8e1cbff5c78a18e8f572fed203c8d28e0b` |
| Correlated consumer evidence extension | `b4f0c05bb7080367a2eaf158ddae79e583694fe2` |
| Initial captured-outer correlation | `605915be4a60275fc04bbb6e02ba8768956e3525` |
| Focused correlation evidence closure | `97c705fb5b65723ebf6c0103cd3deaf72f4a55bd` |
| Checked correlation-authoring evidence | `3132cd82438874cbb34c2e6c73ee07a7a2e6f2f1` |
| Operator-sensitive empty-value evidence | `8fea77d6e37d8d45cd0cf39c109b9d0f963955fb` |

Use `git show fe26645a5f6807e79d8a42c6ea0591acf3d51d96:<path>` to inspect a removed artifact, or `git archive fe26645a5f6807e79d8a42c6ea0591acf3d51d96 -- <paths>` to reconstruct a disposable audit tree. Do not restore the historical stack to current `main` merely to run ordinary evidence replay.

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
