# Feedback queue for a12-dmkits

This document is the a12-kernel-lean maintainers' actionable feedback queue for the a12-dmkits project, whose local checkout is `../a12-rulekit/`. It records concrete upstream improvements discovered while formalizing and transporting semantics here; it does not redefine a12-dmkits behavior, authorize writes to the sibling checkout, or claim that an item has been accepted upstream. The source review below is pinned to a12-dmkits revision `699e8619ac1667c861e14b285c5924ac57a705f1` and kernel behavior version 30.8.1.

## Recommended corrections

### F1 — Correct the contradictory `Length` implementation comment

**Finding:** [`ExprEval.kt`](../../a12-rulekit/interpreter/src/commonMain/kotlin/io/github/mbackschat/a12/dm/interpreter/eval/ExprEval.kt) describes an empty or absent `Length` operand as producing `Unknown`, immediately above code that deliberately returns numeric zero for a check-relevant empty operand. The implementation agrees with the settled finding and differential tests; the comment does not.

**Recommendation:** Change the local comment to say that a check-relevant empty String produces `0`, while a malformed, wrong-kind, or otherwise non-evaluable operand produces `Unknown`. Keep the rationale local because this is an operator-specific exception to direct String comparison.

**Acceptance check:** The comment agrees with the branch it describes and points briefly to IF73 or the corresponding differential; no semantic code change is needed.

### F2 — Name the `Length` unit precisely in public descriptions

**Finding:** [`LengthOf.java`](../../a12-rulekit/rulekit/src/main/java/io/github/mbackschat/a12/dm/rulekit/dsl/LengthOf.java) and the [`operators.json`](../../a12-rulekit/rulekit/src/main/resources/catalog/operators.json) catalog call the result a “character length.” a12-dmkits' interpreter account uses UTF-16 code units, as recorded in [`KERNEL-FINDINGS.md`](../../a12-rulekit/docs/KERNEL-FINDINGS.md) and locked by the multiplatform [`LengthUnicodeCountTest.kt`](../../a12-rulekit/interpreter/src/commonTest/kotlin/io/github/mbackschat/a12/dm/interpreter/LengthUnicodeCountTest.kt). The kernel differential [`AbsLengthDiffTest.kt`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/AbsLengthDiffTest.kt) anchors `Length` behavior but does not by itself establish a supplementary-plane Unicode separator; the operator-sensitive evidence retained here is ASCII-only.

**Recommendation:** Say “UTF-16 code-unit length” for the a12-dmkits interpreter and portable consumer contract, with a short reader-facing note that this differs from code-point and grapheme-cluster counts. Do not label the supplementary-plane boundary kernel-confirmed until a focused real-kernel observation separates it.

**Acceptance check:** Public API and catalog text use the same exact unit for a12-dmkits, the interpreter retains a supplementary-plane separating case, and any kernel-correspondence wording names only the Unicode cases actually run against the kernel.

### F3 — Narrow or complete the “Kernel tri-checked” claim

**Finding:** [`EmptyOperandFiringDiffTest.kt`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/EmptyOperandFiringDiffTest.kt) labels the `Length(empty) >= 0` polarity witness “Kernel tri-checked,” but its helper compares Groovy-dynamic kernel output with the a12-dmkits interpreter; that test does not execute the Java-static strategy.

**Recommendation:** Either add the Java-static leg for this witness or narrow the comment to the two strategies actually executed. Prefer the static leg because this is the distinguishing grow-only polarity case and the corpus already treats strategy identity as evidence metadata.

**Acceptance check:** The test's prose names exactly the executed engines, and a deliberately changed static result would fail if “tri-checked” remains.

## Recommended corpus and capture improvements

### F4 — Reject kernel-invalid authored scenarios before capture

**Finding:** [`CorpusCapture.kt`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/CorpusCapture.kt) executes the Groovy anchor, interpreter, and Java-static strategy, but it does not first require the authored rule or computation to pass the kernel consistency/MVK acceptance surface. Deserialization and runtime code generation are not a substitute for an explicit legality claim. [`CatalogFacetProbesTest.java`](../../a12-rulekit/adapter/src/test/java/io/github/mbackschat/a12/dm/adapter/laws/CatalogFacetProbesTest.java) demonstrates the stronger sequence: require `RuleValidator` acceptance, then execute the runtime probe.

**Recommendation:** Add an explicit kernel-confirmed consistency gate before any scenario becomes committable, and add a negative guard proving that a deliberately illegal rule is rejected even if a runtime strategy happens to produce an output. Record the acceptance result in capture provenance rather than relying only on the generator succeeding.

**Acceptance check:** A legal seed still captures identically; an illegal comparison or rule placement fails at the acceptance stage with a classified diagnostic and cannot write a case.

### F5 — Separate conformance capture from characterization export

**Finding:** The strict behavior in [`CorpusCapture.kt`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/CorpusCapture.kt) blocks a case whenever the interpreter differs from the Groovy anchor. That is correct for the green portable conformance corpus, but it also prevents the same machinery from exporting a kernel observation precisely when an interpreter defect or still-unsupported semantic mechanism is being researched.

**Recommendation:** Preserve strict mode as the default and as the only path that can update the conformance corpus. Add a separately named, opt-in characterization/export mode that retains the Groovy anchor, Java-static result, interpreter result, divergence classification, source revision, kernel version, and payload hashes without requiring interpreter agreement. Its artifacts must be unmistakably non-conformance evidence until the divergence is resolved.

**Acceptance check:** Strict capture still rejects an interpreter split; characterization mode exports the same split without relabeling it PASS or allowing it into the green corpus.

### F6 — Promote operator-sensitive empty and directional-polarity controls into the portable corpus

**Finding:** [`CorpusScenarios.kt`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/CorpusScenarios.kt) currently exposes only the small seed set, while the concise operator-sensitive knowledge remains mostly in repository-local differential tests. The Lean capsule needed portable paired observations for direct empty String comparison versus `Length(empty)`, and for directional Number polarity where kind and empty value stay fixed but signedness, literal direction, or filled state changes.

**Recommendation:** Add corpus cases that preserve the complete external message list for at least: empty String direct equality suppressed; the same empty String under `Length < 5` firing OMISSION; `Length >= 0` firing VALUE; unsigned empty Number `!= -1` firing VALUE; signed empty Number `!= -1` firing OMISSION; unsigned empty Number `!= 1` firing OMISSION; and filled zero `!= -1` firing VALUE. Keep content-bearing and all-empty-row controls separate so operator semantics are not confused with row eligibility.

**Acceptance check:** The standard three-engine corpus replay covers every added case, and paired case metadata identifies the one varied axis.

### F7 — Generate an auditable capture receipt

**Finding:** [`CorpusGenerator.kt`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/CorpusGenerator.kt) writes cases and deduplicated models, and each case carries a kernel version, but there is no single generated receipt binding the exact capture schema, a12-dmkits revision, kernel version, strategy identities, model/case inventory, byte counts, and SHA-256 digests.

**Recommendation:** Generate a closed receipt or manifest beside the corpus and verify it in the ordinary replay gate. Treat it as provenance and drift control, not a second semantic specification. A changed case or model then has one reviewable inventory delta, and external consumers can prove which bytes they received.

**Acceptance check:** Replay rejects an added, removed, renamed, or byte-modified retained artifact until the reviewed receipt is regenerated; the receipt itself contains no machine-specific path.

### F8 — Retain a rerunnable capture recipe for focused external consumers

**Finding:** The focused `operator-sensitive-empty` capture used for the Lean capsule was produced by a temporary adapter test in an ignored disposable workspace; the portable observations and receipt were retained here, but the source-side capture command/test was intentionally removed. The generic [`corpus/README.md`](../../a12-rulekit/corpus/README.md) documents full corpus regeneration, not a small read-only export recipe for a named set of rules and documents.

**Recommendation:** Add a maintained focused-capture entry point or recipe in a12-dmkits that accepts an explicitly authored scenario set and writes only to a caller-supplied ignored/output directory. It should run the legality gate, both kernel strategies, the interpreter, and receipt generation without rewriting the committed corpus unless a distinct promotion command is invoked.

**Acceptance check:** A clean checkout can reproduce the named String/Length and Number-directional observations into an ignored directory with one documented command; `git status --short` remains unchanged.

### F9 — Correct the superseded bare-name ancestor claim

**Finding:** The later source-backed account in [`KERNEL-FINDINGS.md`](../../a12-rulekit/docs/KERNEL-FINDINGS.md) correctly states that a bare `[Name]` lookup tries the declaring group and then, only when `fieldRefByShortNameAllowed` is enabled, a model-wide unique field short name. The older “relative path forms” supplement in the same document still says a miss walks ancestor groups without `../`. Those mechanisms are contradictory: the apparent ancestor success can be explained by the model-wide unique fallback, while explicit parent navigation remains the `../` form. The a12-dmkits interpreter and its IF119 tests already implement the corrected local-or-global mechanism.

**Recommendation:** Amend the older supplement in place with a visible correction or supersession pointer to the later source-backed finding. Remove the claim that bare lookup performs an ancestor walk, and state the flag precondition for the model-wide fallback so readers cannot reintroduce the retired mechanism in another interpreter or importer.

**Acceptance check:** Searching the live documentation yields one non-contradictory bare-field resolution rule: declaring-group first, then flag-gated model-wide unique field fallback; an ancestor field requires either explicit `../` navigation or qualification through that separately named fallback.

### F10 — Treat a final empty String computation as no stored value

**Finding:** At a12-dmkits revision `699e8619ac1667c861e14b285c5924ac57a705f1`, the interpreter correctly lets a clean empty String field contribute `""` inside concatenation, but it then reports the resulting final empty text as `VALUE ""`. Kernel 30.8.1 applies a second root-store decision: a final empty String is no computed value. The retained [`String-computation receipt`](../evidence/kernel-30.8.1/captures/string-computation-2026-07-15.json) records both kernel strategies agreeing and the already kernel-granularity-projected interpreter disagreeing in exactly three cases: a stale target becomes `CLEARED`, while an absent target remains silent in both a content-bearing and an otherwise empty row. The nonempty control `[Source] + "-X"` still produces `VALUE "-X"`, so the problem is not empty operand substitution; it is the final String store boundary.

**Recommendation:** Keep expression evaluation and target storage separate. Concatenation should continue to map clean missing operands to empty contributions, but the root String store must convert a final empty text to the same no-value store decision as a bare empty copy. Apply kernel delta granularity only afterward: no-value clears a previously filled target and reports nothing for an already empty target. Preserve poison separately even where its immediate delta is also `CLEARED`.

**Acceptance check:** Add paired interpreter and kernel-differential cases for filled-plus-empty, empty-plus-nonempty, all-empty with stale target, and all-empty with absent target. Mutation controls must independently catch skipping empty contribution, storing final empty text, and clearing an already empty target. The three retained mismatch cases then agree without weakening the comparison or treating a12-dmkits as the oracle.

## Handoff use

When feeding this queue back to a12-dmkits, open or update items in that project's own gap/plan surfaces and link back to the specific evidence or capsule that motivated them. Close an item here only after recording the upstream revision and outcome; if upstream rejects or supersedes it, retain the disposition so later formalization work does not rediscover the same question.
