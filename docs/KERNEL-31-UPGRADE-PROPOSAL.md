# Kernel 31 upgrade readiness — review and proposal

**Status:** proposal, 2026-10-04. Review of whether this project's method, evidence, and Lean design are prepared for a later move from kernel 30.8.1 to 31.x. Nothing here is executed. The peer's change inventory is [a12-dmkits' Kernel 31.1.0 upgrade proposal](../../a12-rulekit/docs/KERNEL-31-UPGRADE-PROPOSAL.md), which recommends deferring the bump until its kernel-decoupling programme lands; this document only filters that inventory to this repository's consequences.

**Pick up here:** the [immediate work](#immediate-work) section is self-contained. Each item names its target, the change, and how to verify it. The rest of the document is the supporting analysis.

## Immediate work

These are cheap, independent of the peer's timing, and prevent the expensive mistakes described below. Do them in any order; each is one small commit.

### I1 — Replace the reserved namespace-fork plan with a delta-profile rule

- **Target:** [`ARCHITECTURE.md`](ARCHITECTURE.md) line 30, the sentence beginning "Before a second kernel behavior version …", which reserves migrating the semantic namespace to `A12Kernel.V30_8_1`.
- **Why:** the theory estate is about 238k nonblank lines in 1,228 files (measured 2026-10-04 over `Semantics/`, `Elaboration/`, `Proofs/`, `Conformance/`). A namespace fork either duplicates the evaluator wholesale, which the module and duplication rules forbid, or is a large rename that buys nothing for a largely compatible release. See [gap 2](#g2--the-theory-has-no-release-dimension-and-the-reserved-plan-is-the-wrong-one).
- **Proposed replacement (owner decision):** one theory; a release selector injected like `ModelZoneRules` that carries only the mechanisms measured to differ between supported releases (first candidates: the calendar profile and the static-legality code table). Laws are stated over every release where they hold and per release where they do not. Conformance cases apply to every supported release by default; a case that locks a difference names its release. The selector is introduced at the first **measured** divergence, never in advance.
- **Done when:** the sentence is replaced, no other owned document still reserves `A12Kernel.V30_8_1` (`grep -rn 'V30_8_1' docs spec CLAUDE.md`), and `./scripts/check-doc-hygiene.sh` passes.

### I2 — Make the coverage report refuse a mismatched kernel checkout

- **Target:** [`report-conformance-coverage.sh`](../scripts/report-conformance-coverage.sh).
- **Why:** line 166 hard-codes the kernel runtime package path `_30_8`, and the script reads whatever revision `../a12-kernel` has checked out without checking it. Once that sibling is pulled to 31, the report either fails or silently mixes 31 vocabulary with 30.8.1 evidence. Lines 299 and 526 also hard-code `evidence/kernel-30.8.1`.
- **Change:** before scanning, compare `git -C ../a12-kernel rev-parse HEAD` with the kernel revision [`SOURCES.md`](SOURCES.md) records (line 10, currently `cb66e51fa7ab90b650698f861bf670754e2e1e66`) and fail with a clear message on mismatch. Derive the evidence root from one variable instead of repeating the literal. Keep the `_30_8` path as is; it becomes a release-table entry only when 31 is actually adopted.
- **Covered by:** the 2026-09-07 standing authorization for throughput tooling (it prevents a costly silent wrong answer); name that cost in the commit body.
- **Done when:** the script still regenerates [`CONFORMANCE-COVERAGE.md`](CONFORMANCE-COVERAGE.md) unchanged at the recorded revision, and a run with a deliberately wrong expected revision (temporarily edited variable, not a sibling change) fails before scanning. Never change the sibling checkout to test it.

### I3 — Prepare, but do not yet send, the model-migration request to a12-dmkits

- **When to send:** when a12-dmkits starts its Kernel 31 stage (its decoupling Stage 5), not before. Sending earlier starts peer work with no consumer ready.
- **Route:** an instrument capability, so it goes to the a12-dmkits session directly, never into this repository's ledger ([routing rule](A12-DMKITS-SPEC-SYNC-LEDGER.md#entry-kinds-and-routing)); the dated `~/Downloads` note is the fallback ([TESTING.md](TESTING.md#structured-dmtool-probes-and-feedback)).
- **Content to send:** on a 31-backed `:adapter:kernelProbe`, explicitly migrate an input model whose `modelVersion` is older than the kernel's minimum through the kernel's own model migrator before deserialization, and stamp both the original and the migrated model version in the artifact. Rationale: the peer's proposal (§7) found that 31's direct model deserializer does not invoke the migrator, so the 180 retained requests here, all carrying 28.4.0 models, would otherwise not re-run unchanged. Acceptance: one retained 30.8.1 request re-runs on 31 byte-identically as input and its artifact records `28.4.0 → 29.4.0`.
- **Done when (now):** nothing to do beyond keeping this section; it is the ready text.

## Bottom line

The worry that much information is tied too closely to 30.8.1 and must be costly migrated is mostly unfounded. Of 2,818 occurrences of `30.8.1` (2026-10-04), the overwhelming share is provenance that stays true after an upgrade: the immutable evidence bundle itself, protocol fixtures that correctly assert their behavior version, and "measured on kernel 30.8.1" notes in Lean and checkpoints. The real readiness gaps are the missing release dimension in the theory (with a costly reserved plan), the dependence of every re-measurement on the peer's deferred upgrade and on model migration, a few single-version plumbing points, and one semantic family — calendar arithmetic — that is probably not compatible.

## What 31.1 changes that matters here

Filtered from the [peer's inventory](../../a12-rulekit/docs/KERNEL-31-UPGRADE-PROPOSAL.md). Java module renames, Jackson 3, V1 document API removal, native-image metadata, and CI keys are adapter-side only; they reach this project solely by deciding when the kernel probe route can run on 31.

- **Model format 28.4 → 29.4:** include restructure, variant filter removed, `Unspecified` type removed. Affects retained request models (696 evidence files carry `28.4.0`), not the Lean DM-JSON reader, which never checks `modelVersion`.
- **New operator `SumOfTerms`:** sums an arbitrary numeric term over a starred group; a sibling of `SumOfProducts`.
- **Static legality:** two relaxations (comparisons between mismatched Enumerations, and `+` with display-value Enumerations, are now admitted); three filter → set-expression code renames; three code removals; `MVK_WILDCARD_AT_LOWEST_LEVEL_REQUIRED` keeps its name but changes meaning.
- **Runtime:** date/time handling moves from `java.util.Calendar` to `java.time`; the code-generation path is restructured.

## What is already well prepared

Keep these as they are.

1. **Version-scoped, immutable evidence.** Captures live under `evidence/kernel-30.8.1/`, and [`ARTIFACTS.md`](ARTIFACTS.md) (lines 60 and 141) already requires a new bundle per kernel version. 444 artifacts stamp `producer.kernel.{builtAgainst,runtime}` and the producing a12-dmkits revision.
2. **Request-backed replay is the strongest upgrade asset.** 180 of 301 capture directories are kernel-probe requests; `a12-kernel-replay` replays 1,495 rows covering 19,224 rule and computation instances (coverage report, 2026-10-04). The mechanism is version-agnostic: re-capture the same requests on 31, replay, and the disagreeing (`tier1`) rows are exactly the behaviour-change worklist.
3. **Error codes are separate from their meaning.** `KernelStaticDiagnostic` is an abstract type and kernel code strings come from one function, `kernelCode` ([`StaticDiagnostic.lean`](../A12Kernel/Elaboration/StaticDiagnostic.lean) line 440), so code renames touch one table.
4. **Calendar behaviour is isolated.** About 30 named modules (about 4,900 nonblank lines, roughly 2% of the theory) carry it, under a versioned profile identity that names the mechanism rather than the kernel (`europe-berlin-java-util-timezone-jdk21-tzdb2026a-v1`), and it reaches evaluation through `World` as `ModelZoneRules`. This is the right shape for a second profile.
5. **Variant selection is deliberately not modelled** (owner decision, 2026-09-29), which matches 31 removing it.
6. **Provenance notes are history, not stale text.** Do not rewrite "measured on kernel 30.8.1" in bulk. The protocol's strict `kernelBehaviorVersion` check ([`PROTOCOL.md`](PROTOCOL.md) line 61) is correct by design.

## Gaps, most serious first

### G1 — The only measurement route depends on a deferred peer upgrade

Every kernel observation comes from a12-dmkits' `:adapter:kernelProbe`, and the peer recommends deferring 31 until its decoupling work lands, so this project cannot measure 31 earlier. Additionally, 31's deserializer does not auto-migrate (peer proposal §7), so the 180 retained requests carrying 28.4 models would not re-run unchanged. Remedy: [I3](#i3--prepare-but-do-not-yet-send-the-model-migration-request-to-a12-dmkits). The alternative, migrating every retained model locally, is exactly the costly migration to avoid.

### G2 — The theory has no release dimension, and the reserved plan is the wrong one

[`ARCHITECTURE.md`](ARCHITECTURE.md) line 30 reserves a namespace split to `A12Kernel.V30_8_1`. For a 238k-line theory and a largely compatible release that means a wholesale copy or a meaningless rename. Remedy: [I1](#i1--replace-the-reserved-namespace-fork-plan-with-a-delta-profile-rule).

### G3 — Calendar arithmetic is the largest semantic risk (⚠ unverified)

**Source reading only, not discharged.** Reading kernel 31.1 at `f10b920` read-only: its main sources no longer use `GregorianCalendar` or `java.util.Calendar` (one unrelated hit in `JoinProblem.java`); `BedingungsOperatorHelper` uses `ZonedDateTime.plusYears`/`plusMonths`, and the conversion `DateUtil` uses `LocalDate.of`. Hypothesis: these 30.8.1 behaviours may change in 31 — Julian-side reality of a constructed `Date("29", "2", "1500")`, forward normalization of month/year shifts landing in the missing 1582 cutover labels, the February-28 correction on the Julian side, and possibly the `java.util.TimeZone`-based Europe/Berlin profile. These are the clauses at [`spec/05-dates-and-time.md`](../spec/05-dates-and-time.md) lines 80 and 135. Only a 31 measurement settles them. Not a blocker while the upgrade is deferred; it is the first family to re-capture and the natural first user of the I1 release selector.

### G4 — Single-version plumbing (small, mechanical)

- [`Basic.lean`](../A12Kernel/Basic.lean) line 12 holds one `kernelVersion` constant; [`ObservationBundle.lean`](../A12Kernel/Evidence/ObservationBundle.lean) line 217 rejects any other; [`EvidenceMain.lean`](../A12Kernel/EvidenceMain.lean) line 12 hard-codes `evidence/kernel-30.8.1`; `CandidateConformanceMain.lean` line 222 compares against it. Generalize at upgrade time, not now.
- The coverage script's unchecked sibling revision and hard-coded paths: [I2](#i2--make-the-coverage-report-refuse-a-mismatched-kernel-checkout).

### G5 — About 40% of the evidence is re-runnable only by hand

121 capture directories are not kernel-probe requests (dmtool batch `ops.json`, `rcc-N`, `obs`, `raw`, and similar); 111 have no command record in the directory, and their recipe lives in the `route`/`revision` lines of the owning [`sources/`](sources/) checkpoint. Many are static-admission probes, exactly where 31 renames and relaxes codes, and their expected values are transcribed into conformance cases rather than replayed. Do not retrofit a harness; at upgrade time re-run only checkpoints touching changed mechanisms (codes and Enumeration comparison, filters, dates).

### G6 — Static legality needs more than code renames

- **Enumeration relaxations open a semantic question.** Lean currently rejects these comparisons ([`EnumerationComparability.lean`](../A12Kernel/Conformance/EnumerationComparability.lean) lines 27–32, [`LiteralComparisonDiagnostic.lean`](../A12Kernel/Elaboration/LiteralComparisonDiagnostic.lean) line 213). Under 31 they are admitted, so the comparison needs a runtime meaning, not a different code.
- **A constructor is named after a code whose meaning moves.** `.wildcardAtLowestLevelRequired` mirrors `MVK_WILDCARD_AT_LOWEST_LEVEL_REQUIRED`; rename it after its meaning when first touched, and let the per-release code table carry the string.
- **Possible partial-validation change (⚠ unverified).** The filter → set-expression refactor makes the rule that partial validation first skips filtered rules ([`spec/10-validation-and-polarity.md`](../spec/10-validation-and-polarity.md) line 140) a re-measurement candidate. The peer inventory does not mention it.
- **`SumOfTerms`** belongs with the shared aggregate mechanism that owns `SumOfProducts`.

### G7 — Charter and document scoping

[`spec/SEMANTICS-MAP.md`](../spec/SEMANTICS-MAP.md) lines 14 and 18 scope the whole spec to 30.8.1 in one place, with a few clauses scoped inline; that is fine. The goal in [`CLAUDE.md`](../CLAUDE.md) names 100% conformance with 30.8.1. **Recommendation:** once a12-dmkits runs 31, target the latest supported release and keep 30.8.1 as the release backed by its immutable evidence, with differences carried by the I1 selector. This is balanced; full dual support is warranted only if a consumer still runs the upstream-maintained 2025.06 line in production. Optionally, new [`sources/`](sources/) checkpoint headings could carry the kernel version: none of the current 477 do, so heading-first search cannot separate releases after an upgrade.

## Suggested order

1. **Now:** [I1](#i1--replace-the-reserved-namespace-fork-plan-with-a-delta-profile-rule) and [I2](#i2--make-the-coverage-report-refuse-a-mismatched-kernel-checkout).
2. **When a12-dmkits starts its Kernel 31 stage:** send [I3](#i3--prepare-but-do-not-yet-send-the-model-migration-request-to-a12-dmkits).
3. **At the upgrade:**
   1. Create `evidence/kernel-31.1.0/`; never rewrite the 30.8.1 bundle.
   2. Re-capture the 180 retained requests on 31 and replay them; triage the disagreeing rows.
   3. Re-run the calendar (G3) and static-admission (G5, G6) checkpoints by their recorded recipes.
   4. Introduce the release selector at the first confirmed difference.
   5. Generalize the single-version plumbing (G4).
   6. Record each `spec/` change together with its ledger entry, and decide the charter target (G7).

## Basis

Counts measured on 2026-10-04 at HEAD `54706581` with tracked-file greps; the replay figures come from the generated [`CONFORMANCE-COVERAGE.md`](CONFORMANCE-COVERAGE.md) of the same date. Kernel 31.1 source was read only through `git grep`/`git show` on the fetched commit `f10b9203822cd2a2d86bacccfa1ace615606b3c8` named in the peer proposal; the sibling worktree was not changed.
