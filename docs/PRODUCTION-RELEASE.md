# Production release engineering

**Status:** draft production-release engineering contract and experiment log, not an adopted public-release commitment. [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md) owns the proposed product and public claim; this document owns artifact qualification, reproducibility, optimization, packaging, signing, publication, and rollback. Current semantic support remains owned by [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md) and the generated [`supported-fragment-v1.json`](../reference/supported-fragment-v1.json).

## Scope and ownership

This document defines what must be true before a build of `a12-kernel-reference` can be called a production release. It is both the durable release-engineering contract and the home for measured artifact experiments. A platform is not supported merely because the executable builds or passes on one developer machine.

The product boundary and narrow public claim remain in [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md). The exact process contract remains in [`PROTOCOL.md`](PROTOCOL.md), ordinary verification methodology in [`TESTING.md`](TESTING.md), semantic and evidence coverage in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), retained-observation limits in [`EVIDENCE.md`](EVIDENCE.md), and implementation structure in [`ARCHITECTURE.md`](ARCHITECTURE.md). This document must link to those authorities rather than redefine them.

No production release has been qualified yet. The current `0.1.0` identifiers describe the implemented reference boundary; they are not evidence of an immutable public `v0.1.0` release.

## Release artifact contract

The release unit is more than an executable. Every downloadable artifact must be tied to one source revision and one explicit semantic, protocol, evidence, toolchain, and platform identity.

| Artifact | Purpose | Canonical source or gate | Current state |
|---|---|---|---|
| Platform-specific `a12-kernel-reference` executable | Direct reference-oracle invocation | [`PROTOCOL.md`](PROTOCOL.md) and packaged-binary process gate | Builds locally; no platform is qualified |
| Supported-fragment manifest | Machine-readable fail-closed operation and evidence boundary | [`Support.lean`](../A12Kernel/Reference/Support.lean) and [`supported-fragment-v1.json`](../reference/supported-fragment-v1.json) | Implemented for the flat and one-group correlation development operations; not a release-readiness declaration |
| Capability descriptor, evaluator shipment, and conformance suite | Pin one independently implementable semantic slice, its evidence classifications, exclusions, and cold-consumer contract | [`IMPLEMENTER-GUIDE.md`](IMPLEMENTER-GUIDE.md), [`flat-validation-empty-logic-v1.capability.json`](../reference/flat-validation-empty-logic-v1.capability.json), and shipment-specific artifacts | Current support and evidence readiness are owned by [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md); the exact flat cold-consumer outcome and remaining qualification work are owned by [`IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) |
| Runnable requests and expected responses | Minimal integration examples and packaged smoke tests | [`examples/reference-cli/`](../examples/reference-cli/) | Implemented for protocol v1 |
| Source archive, tag, and commit identity | Exact source correspondence | Git release process | Not yet defined |
| [`LICENSE`](../LICENSE) and third-party notices | Source and bundled-runtime licensing | Package-content, SBOM, and license review | Project license exists; bundled-runtime inventory and GMP compliance are open |
| SHA-256 checksums | Pin the final downloadable bytes | Post-build or post-signing publication gate | Not yet defined |
| SPDX or CycloneDX SBOM | Inventory statically linked and packaged components | Release build inputs and final package scan | Not yet generated |
| Build-provenance attestation | Record builder, inputs, commands, and output digests | Immutable release workflow | Not yet defined |
| Distribution trust record | Bind checksums, arrival path, platform behavior, and any adopted signing/notarization | Platform-specific final-artifact gate | Initial unsigned terminal-distribution posture proposed below |
| GMP compliance material or an approved non-GMP toolchain record | Preserve exact arithmetic while satisfying the selected runtime's redistribution obligations | Dependency decision, qualification evidence, and release legal review | Unresolved; blocks binary distribution |
| Retained kernel evidence bundle and digest | Bind the empirical correspondence claim | [`EVIDENCE.md`](EVIDENCE.md) | Evidence exists in-repository; release bundle identity is open |
| Theorem, counterexample, and trust report | Bind internal proof claims to exact roots and exclusions | Trust audit and future report generator | Trust gate exists; packaged report is open |

Following dmtool-release, the initial delivery shape should be a bare executable per target plus adjacent `SHA256SUMS`, support manifest, concise usage information, applicable license/compliance material, and explicitly selected runnable samples. The downloader or installer must checksum the executable before use and set the Unix executable bit. The release asset set must not contain the kernel, a kernel binding, a sibling-project binary, disposable probe output, `.lake/`, conformance executables, or unreviewed evidence. Debug symbols, relinkable compliance material, the complete evidence bundle, and extended documentation may be separate named assets. The exact contents cannot be finalized until the GMP compliance route is approved.

## Version identity

These identities are different and must never be silently collapsed:

| Identity | Current source | Meaning |
|---|---|---|
| Project/release version | [`lakefile.toml`](../lakefile.toml) | Package lineage and immutable release name |
| `referenceSemanticsVersion` | [`Support.lean`](../A12Kernel/Reference/Support.lean) | Version of the executable reference boundary |
| `protocolVersion` | [`Support.lean`](../A12Kernel/Reference/Support.lean) | Compatibility of request and response shapes |
| `manifestSchemaVersion` | [`Support.lean`](../A12Kernel/Reference/Support.lean) | Compatibility of the support-manifest shape |
| Capability and conformance-suite identities | Capability descriptor and suite shipped for the selected fragment | Exact finite downstream handover, exclusions, fixtures, and per-case evidence/response-source classifications |
| `kernelBehaviorVersion` | [`Basic.lean`](../A12Kernel/Basic.lean) | External behavior version to which retained evidence refers |
| Evidence-bundle identity and digest | Future release metadata governed by [`EVIDENCE.md`](EVIDENCE.md) | Exact empirical observations included in the claim |
| Lean and Lake toolchain | [`lean-toolchain`](../lean-toolchain) plus recorded Lean commit | Compiler, runtime, and build-system input |
| Source commit and release tag | Git release metadata | Exact source from which the artifact was built |

A release gate must verify that the project and reference-semantics versions agree or record an explicit mapping between them. Protocol and manifest schema versions change for their own compatibility reasons; expanding the manifest does not imply support outside its listed capabilities. Once published, an executable, manifest, evidence bundle, checksum file, or attestation must never be replaced under the same release version.

The project version currently has a SemVer-shaped value, but no public versioning policy, bump matrix, or tag format has been adopted. Before the first release, decide how semantic support expansion, semantic correction, protocol/schema incompatibility, and evidence-only changes affect the project version; define the tag format; and bind the executable to its source/release identity through a `--version` surface or signed release metadata. The support manifest's semantic versions are necessary but do not identify a source commit or public release by themselves.

## Platform qualification

Every supported target needs a native build, the complete development gates, a staged-package test on a clean host, a dynamic-dependency inventory, an oldest-supported-OS run, and verification of the chosen distribution/trust path. Cross-compilation alone is insufficient.

| Candidate target | Current observation | Qualification gap | Status |
|---|---|---|---|
| Linux x86-64 | CI currently runs on mutable `ubuntu-latest` | Pin a release builder and oldest supported glibc baseline; inspect PIE, NX, RELRO, and dynamic dependencies; test staged bytes | Not qualified |
| macOS arm64 | Local build and process gates run on arm64 macOS | Choose and verify a real deployment target; test oldest supported macOS; strip and test the final bytes; verify terminal and browser-download instructions | Not qualified |
| macOS x86-64 or universal | No release observation | Decide whether needed; build and test natively or qualify a deliberately constructed universal artifact | Not qualified |
| Windows x86-64 | No release observation | Test `.exe` discovery, newline bytes, invalid UTF-8, exit codes, DLL inventory, arrival-path behavior, and clean-host execution | Not qualified |

Protocol output bytes must be compared across every qualified platform. Cross-platform protocol determinism is a separate claim from reproducible executable bytes.

## Reproducible build contract

A release build records the exact source commit and tag, a clean worktree, the pinned Lean toolchain and full Lean commit, Lake/compiler/linker/SDK versions, target triple, deployment baseline, effective compile and link flags, build-image digest, workflow revision, dependency inputs, support-manifest digest, and evidence-bundle digest.

To claim bit-for-bit reproducibility, build the unsigned payload independently at least twice from distinct absolute checkout paths and compare it before signing. Normalize archive member order, timestamps, modes, uid/gid, and compression settings. Signing and notarization may add intentionally variable data, so final signed artifacts can have different bytes even when their unsigned inputs match.

Until that comparison succeeds, the accurate term is **provenance-recorded build**, not **reproducible build**. Checksums always describe the actual final downloadable bytes, regardless of the reproducibility result.

Release automation must use immutable tool and action identities, minimum required permissions, an isolated clean checkout, and an allowlisted package layout. It must scan the staged bytes and metadata for absolute machine paths, usernames, hostnames, credentials, and forbidden kernel material before publication.

## Qualification gates

The ordinary gates remain owned by [`TESTING.md`](TESTING.md):

```sh
lake build
lake test
lake exe syncFlatHandover --check
lake exe checkReferenceProcess
./scripts/check-lean-trust.sh
```

A release candidate additionally requires:

1. clean-checkout and version-consistency checks;
2. semantic equality between the executable's generated manifest and the committed readable mirror, plus a clean drift check against the reproducibly generated form of every packaged capability descriptor, suite, and derived fixture;
3. every packaged request/response fixture and selected candidate suite exercised against the packaged executable, not only the build-tree binary;
4. process checks for arguments, exit status, stdout/stderr separation, malformed and invalid-UTF-8 input, resource limits, and deterministic bytes on the final artifact;
5. a package-content allowlist, relocation test, clean-host smoke test, and dynamic-library inventory for each target;
6. the oldest-supported-OS execution for each target and an explicit ABI/deployment-baseline check;
7. recorded size, compressed size, startup latency, peak RSS, and representative throughput against adopted budgets;
8. a successful reproducibility comparison for the unsigned payload, as required by [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md); a provenance-recorded but non-reproducible build remains a candidate unless the product-level gate is explicitly changed;
9. generated SBOM, third-party notice audit, clean-room review, and evidence-redistribution review;
10. checksums, provenance, and the selected platform trust path verified after the final byte-changing step, including signatures and notarization only where the adopted distribution policy requires them.

The commands and exact retained evidence inventory are the authorities; fixed test counts are experiment observations, not permanent release policy. The process gate, retained-evidence replay, and trust audit establish different things and do not substitute for one another.

## Packaging and distribution

Use deterministic bare-asset names containing the release version and target triple. Invoke the downloaded executable directly in production; `lake exe` is a development wrapper and is not part of the stable process contract. The installer flow must acquire the expected digest through the selected trusted release path, verify the executable bytes, run `chmod +x` on Unix, apply the macOS quarantine step only when the actual arrival path requires it, and then execute the packaged smoke checks.

The initial distribution recommendation follows dmtool-release's terminal-CLI posture, documented by a12-dmkits in [`RELEASE-SPEC.md`](../../a12-rulekit/docs/RELEASE-SPEC.md#7-distribution--trust): publish per-platform binaries with `SHA256SUMS`, deliver primarily through `curl`, an agent installer, or a package manager, and do not make code signing a 0.x prerequisite without observed user friction. Terminal delivery does not normally attach macOS quarantine metadata; a browser-downloaded artifact may carry `com.apple.quarantine` and need `chmod +x ./a12-kernel-reference` plus the checksum-aware escape hatch `xattr -d com.apple.quarantine ./a12-kernel-reference`, with the actual executable path substituted when it differs. Signing and notarization remain available later if the audience, distribution channel, or organizational policy requires them.

This project should reuse dmtool-release's release principles—native per-platform artifacts, exact checksums, final-artifact executable gates, immutable publication, and measured size/startup tradeoffs—without copying GraalVM-specific mechanics. a12-dmkits' [`NATIVE-IMAGE-GRAALVM.md`](../../a12-rulekit/docs/NATIVE-IMAGE-GRAALVM.md) is a useful precedent for separating release-only native work from the development loop and for measuring shrink levers against the actual runnable binary.

The current macOS executable is operationally self-contained and dynamically depends only on the system C++ and system libraries, while the Lean runtime, libraries, and GMP are linked into it. Do not promote that observed static shape to the release policy yet: the user must approve any dependency/linkage strategy, and static GMP creates a compliance obligation described below. A shared runtime or shared GMP is not an automatic fix; it would add loader, versioning, packaging, and platform work and likewise requires prior approval.

The initial dmtool-release-like channel uses bare executable assets, so archive compression is only a later channel experiment and must be reported separately from installed executable size. Executable packers such as UPX should not be used: they complicate signing, notarization, antivirus behavior, debugging, and startup without improving the semantic product.

## Dependency approval and bundled-runtime licensing

No package, runtime library, vendored component, or static/shared linkage choice may be added, removed, upgraded, or replaced without consulting the user and receiving explicit approval; [`CLAUDE.md`](../CLAUDE.md) owns that operational rule. The narrow-import experiment adds no dependency and changes no linkage.

“No external Lake dependencies” does not mean that a native Lean executable contains only this project's MIT code. The current link response includes `-lgmp`, the binary contains `__gmp*` symbols, and the pinned Lean toolchain identifies GNU MP as LGPLv3. The binary also incorporates Lean and other toolchain components whose licenses and notices must appear in the SBOM and release review.

Before distributing the current statically linked shape, the release owner must select a reviewed LGPLv3 compliance route. The [LGPLv3 Combined Works terms](https://www.gnu.org/licenses/lgpl-3.0.en.html#section4) require more than an SBOM or notice file: the applicable license texts and notices are required, and static distribution ordinarily needs suitable corresponding/relinkable application material and any necessary installation information; a suitable shared-library mechanism is the alternative named by the license. This document does not select between those routes and is not legal advice. Binary publication remains blocked until the user approves a technical strategy and the resulting release contents receive a compliance review.

## GMP alternatives outlook

**Decision status:** no dependency or linkage change is adopted or scheduled. The current recommendation is to retain the official toolchain's statically linked GMP for the first release and satisfy its reviewed redistribution requirements. Lean's built-in non-GMP bigint backend is the most credible later experiment if removing GMP becomes a concrete product requirement; shared GMP is a deployment alternative, not a size solution.

GMP is not the source of the approximately 100 MB executable. The pinned macOS toolchain's `libgmp.a` is 829,224 bytes, while the current unstripped executable is 99,045,584 bytes and still initializes Lean's full compiler/metaprogramming closure. Removing that archive cannot save its full size because another arbitrary-precision implementation must replace it. This project also uses arbitrary precision materially: [`Decimal.lean`](../A12Kernel/Reference/Decimal.lean) admits exact finite decimals up to 256 characters and constructs a `Rat` with an arbitrary-size power-of-ten denominator, so replacing the number domain with fixed-width machine integers would change the protocol semantics.

| Path | What it preserves or improves | Cost and risk | Outlook |
|---|---|---|---|
| Current official toolchain with static GMP | Pinned upstream toolchain, mature optimized bigint arithmetic, one-file executable, and the current evidence baseline | Requires a reviewed LGPLv3 static-distribution route, notices, source availability, and suitable relinkable application material or another license-compliant mechanism | Recommended first-release path; no technical dependency change |
| Lean-native bigint backend with `USE_GMP=OFF` | Retains arbitrary-size `Nat`/`Int` while removing GMP and its library-specific redistribution work | Requires a complete custom Lean toolchain and project rebuild, separate caches, cross-platform release ownership, and size/performance qualification; the relevant [no-GMP CI jobs in the pinned Lean revision are present but disabled](https://github.com/leanprover/lean4/blob/68218e876d2a38b1985b8590fff244a83c321783/.github/workflows/ci.yml#L386-L410) | Best later dependency-removal experiment, only after explicit approval |
| Dynamically linked GMP | Keeps GMP's arithmetic implementation and can reduce the executable file measured in isolation | Still distributes or requires GMP; adds a shared library, loader paths, ABI/minimum-version policy, multi-file packaging, and platform signing/notarization work; total installed size changes much less than the front executable | Consider only for a concrete deployment or compliance reason, not for the current size problem |
| GMP-compatible MPIR | Could satisfy [Lean's existing GMP-facing build probe](https://github.com/leanprover/lean4/blob/68218e876d2a38b1985b8590fff244a83c321783/src/cmake/Modules/FindGMP.cmake#L6-L8) without designing a new arithmetic interface | Has no demonstrated Lean release qualification here, retains a third-party GMP-compatible bigint dependency, and adds a new supplier and maintenance surface without a known product benefit | Do not pursue without a distinct platform requirement |
| Another bigint library or a fixed-width representation | Could theoretically target a different license, implementation, or footprint | Lean exposes no general bigint plug-in boundary beyond its GMP and native compile-time branches; another library means maintaining a Lean runtime/toolchain modification, while fixed width violates Lean and this project's exact-number semantics | Reject for the foreseeable release path |

The recommended static path still needs engineering, not just a notice file. A release candidate should identify the exact GMP archive provenance and build configuration; include or provide equivalent access to the applicable notices, license texts, exact GMP source and patches, application source or object material, and relink instructions; retain any installation information needed to run a relinked executable; and prove the package is usable by actually relinking against an ABI-compatible modified GMP and rerunning the packaged process gate. The precise release contents and offer mechanism require compliance review, but a tested companion relink kit is the technical baseline for evaluating this path. The pinned Lean [macOS release preparation script copies a prebuilt `libgmp.a`](https://github.com/leanprover/lean4/blob/68218e876d2a38b1985b8590fff244a83c321783/script/prepare-llvm-macos.sh#L47-L56), so an embedded version string alone is not adequate dependency provenance.

The no-GMP path is real but is not a Lake option for this repository. Lean 4.31.0 declares [`USE_GMP` as a CMake option that defaults to `ON`](https://github.com/leanprover/lean4/blob/68218e876d2a38b1985b8590fff244a83c321783/src/CMakeLists.txt#L106-L116), selects the external library when enabled, and contains a complete [`NON GMP VERSION` of its internal `mpz`](https://github.com/leanprover/lean4/blob/68218e876d2a38b1985b8590fff244a83c321783/src/runtime/mpz.cpp#L318-L360) when disabled. The choice changes the persisted-bignum encoding: [`.olean` headers record the selected backend](https://github.com/leanprover/lean4/blob/68218e876d2a38b1985b8590fff244a83c321783/src/library/module.cpp#L104-L124), the loader rejects a mismatched header, and Lean's top-level build [forwards `USE_GMP` to stage 0 because it creates an incompatible `.olean` format](https://github.com/leanprover/lean4/blob/68218e876d2a38b1985b8590fff244a83c321783/CMakeLists.txt#L14-L29). Therefore a no-GMP trial must rebuild the full pinned toolchain and this project consistently; swapping only `libgmp.a`, `leanrt`, or the final link is invalid.

Shared GMP is technically possible in a custom build: [GMP supports both shared and static builds](https://gmplib.org/manual/Build-Options), and Lean's [pinned Linux release setup](https://github.com/leanprover/lean4/blob/68218e876d2a38b1985b8590fff244a83c321783/script/prepare-llvm-linux.sh#L73-L80) distinguishes its portable static internal link from a normal dynamic `-lgmp` link. GMP notes that a shared build can make an executable smaller at a small per-call cost, but it moves code into a separately managed runtime component rather than solving the full Lean-initializer footprint. GMP is [dual-licensed under LGPLv3 or GPLv2 at the recipient's choice](https://gmplib.org/manual/Copying); the exact obligations of any chosen packaging route still require release review.

If a no-GMP experiment is later approved, its success criterion is not merely “builds.” Build the exact pinned Lean commit in a fresh isolated toolchain with `USE_GMP=OFF`; rebuild all project artifacts without sharing `.olean` caches; run the complete semantic, process, evidence, and trust gates; add cross-backend stress cases for maximum-length positive and negative decimals, normalization, division, comparison, and large intermediate values; and compare final executable and total package size, startup, peak RSS, throughput, reproducibility, and every supported platform. Only those measurements can establish whether removing GMP improves the production product rather than merely changing its dependency inventory.

## Binary-size experiment method

Each experiment used to choose a production optimization must record source revision, target triple, OS/SDK, Lean/Lake/compiler versions, build command, the single changed variable, raw executable bytes, stripped executable bytes, separate debug-symbol bytes, compressed package bytes, code/data/link-edit sizes, symbol count, startup latency, peak RSS, dynamic libraries, and every regression gate. A preliminary probe may omit metrics only when it names every omission and makes no production decision that depends on them. An experiment that changes more than one variable does not establish which change caused the result.

Size optimization must not weaken protocol limits, diagnostics, checked lowering, the supported-fragment boundary, retained-evidence agreement, or trusted proofs. A smaller binary with different observable semantics is a regression, not an optimization.

## Experiment 2026-07-13: narrow runtime JSON imports

**Question:** Does replacing umbrella `Lean.Data.Json` imports with the smallest used JSON modules materially reduce the arm64 macOS executable?

**Controlled change:** [`StrictJson.lean`](../A12Kernel/Reference/StrictJson.lean) now imports `Lean.Data.Json.Parser`, and [`Support.lean`](../A12Kernel/Reference/Support.lean) now imports `Lean.Data.Json.FromToJson.Basic`. The protocol and evaluator receive the needed types and printer operations transitively. No request, response, manifest, or semantic definition changes.

**Environment:** source commit `b5dcf8da3c2c0d1905868d82ed26233530e4c7a9` plus the two import edits; Lean 4.31.0 at commit `68218e876d2a38b1985b8590fff244a83c321783`, whose distribution reports build target `arm64-apple-darwin24.6.0`; Lake 5.0.0; the Lean toolchain's clang/LLD 22.1.4 targeting `arm64-apple-darwin25.5.0`; arm64 macOS/Darwin 25.5.0. The produced Mach-O reports the unqualified toolchain default `minos 99.0` and `sdk 99.0`, discussed below. The command was `lake build a12-kernel-reference` with the toolchain's ordinary release configuration.

| Metric | Umbrella-import baseline | Narrow imports | Difference |
|---|---:|---:|---:|
| Raw executable | 99,045,856 bytes | 99,045,584 bytes | -272 bytes (-0.000275%) |
| Mach-O `__text` | 62,891,620 bytes | 62,891,620 bytes | 0 |
| Mach-O `__LINKEDIT` | 31,445,472 bytes | 31,445,200 bytes | -272 bytes |
| `nm` symbol entries | 217,836 | 217,836 | 0 |
| Dynamic libraries | `libc++.dylib`, `libSystem.B.dylib` | Same | None |

**Result:** the source imports are more precise and reduce the elaboration dependency surface, so they remain. They are not an artifact-size optimization: the 272-byte change is effectively zero and all executable behavior still needs the complete regression gates before handoff.

**Regression result:** after the narrow imports, `lake build` passed, retained kernel replay reported `42/42`, the independent process gate reported `30/30`, the trust audit passed, the generated and committed manifests were semantically equal, and the shipped empty-Number sample produced the committed response. These counts record this source revision and are not permanent release-policy constants.

**Preliminary-probe limits:** stripped baseline size, a baseline debug-symbol companion, compressed package size, startup latency, and peak RSS were not measured as controlled before/after pairs. The separate stripping probe below changes a different variable and cannot fill those cells. The narrow-import result therefore supports dependency hygiene and establishes that raw native size did not materially improve; it does not choose a production size profile.

**Mechanism:** the executable still uses modules under `Lean`, principally Lean's JSON API. Lean 4.31's [C emitter](https://github.com/leanprover/lean4/blob/68218e876d2a38b1985b8590fff244a83c321783/src/Lean/Compiler/LCNF/EmitC.lean#L1074-L1113) detects that module dependency and generates a call to `lean_initialize()` rather than `lean_initialize_runtime_module()`. The linked `lean_initialize` implementation references the master `initialize_Lean`, so the compiler and metaprogramming closure remains reachable even after JSON elaborator modules disappear from this project's direct imports. Dead-code stripping cannot remove an initializer that remains reachable.

**Conclusion:** ordinary import narrowing cannot solve the approximately 100 MB binary in this architecture. A meaningful later experiment must remove every runtime dependency on modules under `Lean`—most notably replace `Lean.Json` with an audited `Init`/`Std`-only transport implementation—and verify that generated C switches to `lean_initialize_runtime_module()`. That is a transport-architecture change requiring red/green protocol tests and full semantic gates; hand-editing generated C or supplying an unverified custom launcher is not acceptable.

## Experiment 2026-07-13: stripping probe

This separate disposable-copy probe measures symbol stripping, not import narrowing:

| Artifact | Bytes | Reduction from unstripped |
|---|---:|---:|
| Current unstripped executable | 99,045,584 | — |
| `strip -S` | 99,045,576 | 8 bytes |
| `strip -x` | 79,275,816 | 19,769,768 bytes |
| Full `strip` | 71,236,664 | 27,808,920 bytes (28.1%) |

These values were remeasured on disposable copies named exactly `a12-kernel-reference`; macOS `strip` regenerates an ad-hoc code signature whose identifier includes the executable name, so measurements under arbitrary temporary basenames differ slightly. The fully stripped final-named copy passed the current independent black-box process gate at `30/30`. This is encouraging but not yet a release policy: each target must test its own final packaged bytes, after signing only when signing is part of that target's adopted policy, and crash-diagnostic requirements must be decided first. The current release-mode build contains no DWARF sections, so a symbol-table-derived companion is not a source-line debug artifact; evaluate a `relWithDebInfo` workflow if line-level crash symbolication is required.

## Size optimization order

Use this order so each step answers one question and preserves operational simplicity:

1. define the release profile and correct platform deployment baseline;
2. preserve the chosen diagnostic symbols, fully strip a disposable release copy, and run the final-artifact process gate;
3. measure deterministic archive compression separately from installed size;
4. prototype an `Init`/`Std`-only JSON transport and require generated runtime-only initialization before comparing size, startup, RSS, and behavior;
5. measure `minSizeRel`, LTO, and linker tuning individually on every target;
6. consider a shared Lean runtime only for a concrete deployment need and compare total bundle size and compatibility risk, not just the front executable.

No target size should be promised before these measurements. The current final-named macOS probe is 71,236,664 bytes after full stripping; a much larger reduction requires an approved change to the Lean runtime dependency boundary, not adding more import aliases.

## Verified macOS release findings

The current local Mach-O reports `LC_BUILD_VERSION minos 99.0` and `sdk 99.0`. Lean/Lake 5 sets `MACOSX_DEPLOYMENT_TARGET=99.0` when the environment does not provide a value, as documented in the pinned [Lake build source](https://github.com/leanprover/lean4/blob/68218e876d2a38b1985b8590fff244a83c321783/src/lake/Lake/Build/Actions.lean#L139-L148). This suppresses bundled-sysroot warnings but does not express a releasable compatibility baseline. A production build must set an intentional target, inspect the resulting load command, and execute on the oldest advertised macOS version.

The current executable is linker/ad-hoc signed, has no Team ID, and `spctl` rejects it. That is expected for an unsigned local CLI and is not itself a release blocker under the proposed dmtool-release pattern: a `curl` or package-manager download normally has no quarantine attribute and can be executed from the shell after checksum verification and `chmod +x`. A browser download may be quarantined; the release instructions must explain verification, executable permission, and `xattr -d com.apple.quarantine ./a12-kernel-reference` explicitly, with the actual path substituted, rather than implying that the binary is signed.

If later evidence or policy adopts Developer ID signing, first choose a supported Apple distribution container and then define the exact sign, notarize, staple where supported, Gatekeeper, final-artifact, checksum, and publication order for that container. Do not copy a generic ZIP/DMG sequence into the runbook before that decision. This conditional path must not be described as a v0.x requirement while the unsigned terminal-distribution policy is in force.

## Publication and rollback

Promote an artifact through candidate, qualified, trust-verified, staged clean-host verification, and immutable publication states. Retain the last-known-good artifacts, their checksums, provenance, manifest, evidence identity, and trust report.

If a semantic, security, evidence, or packaging fault is found, preserve the original digest for audit, mark the affected release withdrawn through the release index or advisory mechanism, publish a corrected higher version, and name the affected protocol, kernel-behavior, semantics, manifest, and evidence versions. Never silently replace a published executable or metadata file.

Consumers should pin both release version and checksum. A compatibility claim must be derived from the exact support manifest and retained evidence accompanying those bytes, not from the newest documentation on the default branch.

## Public claim and nonclaims

A qualified release may carry only the narrow public claim owned by [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md#proposed-first-0x-release); this document qualifies the bytes and supporting artifacts but does not restate or broaden that claim.

The release manifest and each released capability descriptor together form the admitted support boundary; a development operation record alone is not permission to publish every input it accepts as research-closed. Internal proofs establish consequences of the Lean definitions, not universal equivalence to the external kernel, and retained observations establish agreement only for their recorded projection. Current support and evidence readiness are owned by [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md); capability-specific research, integrity, and cold-consumer gaps remain in the owning [`flat`](IMPLEMENTER-KIT-FLAT-EMPTY-LOGIC.md) and [`correlation`](IMPLEMENTER-KIT-CORRELATION.md) kits. A capability is not release-ready until those gates and the packaging gates in this document are complete. A checksum identifies bytes only when its expected digest arrives through an already trusted path; an adjacent unsigned `SHA256SUMS` file does not independently authenticate the publisher. Reproducibility connects source and unsigned artifact bytes, signed provenance can authenticate that build statement, and optional platform signing can authenticate a publisher to the platform. None of those mechanisms establishes semantic correctness.

The first CLI is a reference and CI oracle, not a replacement production runtime or throughput claim. It does not parse the concrete bilingual DSL or general DM-JSON. Its deterministic JSON is the pinned protocol encoding, not a claim of general RFC canonical JSON. It is not an official mgm artifact, and no kernel code or binding is distributed.

## Open blockers before the first production release

- adopt the product proposal for a concrete non-Lean consumer rather than treating this engineering contract as a release decision;
- close the active qualification and generated-differential gaps in [`PLAN.md`](PLAN.md), or explicitly exclude the affected development capability from the release;
- complete and retain the isolated cold-implementation report for every released capability, with no kernel or sibling-source research by the downstream implementer;
- either mechanically bind the correlation suite to its retained projection as the flat bridge does or explicitly keep correlation outside the first released capability set;
- define the supported platform, architecture, ABI, and oldest-OS matrix;
- add immutable release builders and demonstrate the reproducibility required by [`PRODUCT-PROPOSAL.md`](PRODUCT-PROPOSAL.md); any provenance-only relaxation requires an explicit product-level decision;
- implement final-packaged-artifact testing rather than relying solely on Lake's build-tree layout;
- qualify and obtain compliance review for the recommended static-GMP companion relink kit; any move to shared GMP or a no-GMP toolchain remains a separate dependency decision requiring prior approval;
- define the public versioning/bump/tag policy and bind release/source identity into the executable or authenticated metadata;
- define the trusted checksum/provenance path, SBOM, third-party notice generation, executable-permission and installer/browser instructions, and the explicit initial no-signing threat model;
- bind a packaged evidence digest and theorem/counterexample/trust report into the release metadata;
- decide crash-symbol requirements and qualify the stripping strategy on every target;
- correct and test the macOS deployment target and verify both terminal and quarantined-browser arrival paths;
- make an explicit public-release adoption decision.
