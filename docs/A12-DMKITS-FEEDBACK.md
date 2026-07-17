# Feedback queue for a12-dmkits

This document is the a12-kernel-lean maintainers' feedback ledger for the a12-dmkits project, whose local checkout is `../a12-rulekit/`. It records concrete upstream improvements discovered while formalizing and transporting semantics here, then reconciles their reported dispositions; it does not redefine a12-dmkits behavior, authorize writes to the sibling checkout, or become a second owner for upstream implementation status. The original source review below is pinned to a12-dmkits revision `699e8619ac1667c861e14b285c5924ac57a705f1` and kernel behavior version 30.8.1.

## Disposition at the repaired capture baseline

The findings below remain the immutable record of what was observed at `699e8619ac1667c861e14b285c5924ac57a705f1`. Their upstream dispositions were reconciled read-only against clean a12-dmkits revision `3ebe756422e8f2dea447fbd62f9b26c2f774b7e5` on 2026-07-17; an upstream fix never rewrites an older retained observation or triangulation result.

| Item | Disposition |
|---|---|
| F1, F2, F3, F9 | **Fixed** at `0d4a5f56` |
| F4, F5, F7, F8 | **Superseded** by the maintained portable capture boundary and fulfilled by its repaired V1 implementation; the first retained official packet remains pending |
| F6 | **Open, re-sequenced:** promotion of the seven controls is outside capture V1 and follows the capture program |
| F10 | **Confirmed and fixed** as IF123 at `b5a69d9c`; the three mismatches in the retained 699e-era String-computation packet remain immutable history |
| F11a, documentation of payloadful `ERRORED` | **Fixed** at `0d4a5f56` |
| F11b, rich evidence transport | **Superseded** by `compute-observation-v1` with explicit per-runner fidelity; this is not a new general rich interpreter signature |
| F12 | **Confirmed, broadened, and fixed** as IF124 at `0093fc86`, with evidence hardening at `311d190e`; the separate review discriminator IF125 was fixed at `c9c5550a` |

### Capture-boundary audit disposition

The initial Prompt-1 handback at `c0c29b76` was rejected locally before an external packet was accepted because several declared contracts were parsed or recorded without being enforced. No V1 packet had escaped, so a12-dmkits repaired the pre-acceptance V1 identities in place rather than minting V2. The repaired boundary uses one request-bound policy mechanism (`490fa915`), per-runner consumed-document binding (`a1137046`), an in-packet capabilities declaration (`698fa30b`), pre/post implementation and runtime closure identity (`7f74efaa`), and one closed relational packet verifier (`24119589`). Its 40-mutation process-qualification receipt landed at `e7242b09`; stale guard references were closed at `8b8a9f60`; the reconciled clean revision is `3ebe7564`.

These mutations qualify capture and verification machinery, not A12 semantics. The V1 transport identities are now frozen: a12-kernel-lean successfully ran the exact [`string-direct-cascade-v1` question](../evidence/scenarios/string-direct-cascade-v1/README.md) through real `capture` and `captureVerify` at `3ebe7564`. The run printed packet-receipt SHA-256 `f84e38fa6307cda755dbf660e31044db54d5e1ff0e4332c7d416de096c034463` and qualification-receipt SHA-256 `2a0db1f4f6a16fb576c9dbe21944ac950b522ecc2b056336aae2470ce43cc9df`; the artifacts were then deleted, so the digests can no longer be checked against retained bytes and are only a historical process trace. The run freezes compatibility but contributes no retained kernel observation; a complete official handback remains pending. The interpreter's IG72 absence-versus-present-empty fidelity gap remains declared and does not block `kernel-route-confirmed-v1`, because only the two kernel routes qualify that policy. Consolidating duplicate in-memory Java-static bootstrap code is also deferred until the retained cascade run succeeds or a third copy demonstrates the abstraction; neither item weakens the current transport acceptance.

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

### F11 — Document and transport payloadful `ERRORED` computation results

**Finding:** At the pinned revision, [`Computed`](../../a12-rulekit/interpreter/src/commonMain/kotlin/io/github/mbackschat/a12/dm/interpreter/model/Model.kt) documents its `value` as present only for `ComputeOutcome.VALUE`, although [`ComputationEngine.toComputed`](../../a12-rulekit/interpreter/src/commonMain/kotlin/io/github/mbackschat/a12/dm/interpreter/ComputationEngine.kt) also returns the attempted rendered value for `ERRORED`; the `toComputed` KDoc itself describes only VALUE/CLEARED despite that branch. The implementation therefore carries more useful information than its public comment admits. Conversely, [`InterpreterReplay.sigOf`](../../a12-rulekit/interpreter/src/commonMain/kotlin/io/github/mbackschat/a12/dm/interpreter/conformance/InterpreterReplay.kt) renders every error only as `pointer|ERRORED`, erasing the attempted value, while `computedOutcome` reduces `typeFormatError` to a Boolean and discards the target-check cause. The nine-case String target-validation experiment had to use a purpose-built rich observation to retain attempted `ABCD` plus `stringZuLang`/`stringZuKurz`. This is an evidence-transport and API-description gap, not a claim of semantic disagreement: the a12-dmkits interpreter agrees with all nine retained kernel outcomes at projected-delta and stored-value application granularity.

**Recommendation:** Correct the `Computed.value` and `toComputed` comments to state that an errored result retains its attempted rendered value. Add a versioned or explicitly named rich computation-result/signature surface that also preserves the structured target-check cause, while keeping the compact legacy corpus signature only where compatibility requires it and labeling that projection as lossy. Avoid reconstructing the cause from the rendered value downstream; retain the `typeFormatError` result at the point where `computedOutcome` currently collapses it.

**Acceptance check:** Public KDoc matches every constructor path; a String `maxLength` violation is available as an `ERRORED` result containing both attempted value and cause; the same invalid value is retained for absent, stale, and equal prior targets; and a deliberate attempted-value or cause mutation fails the rich replay. Any unchanged compact `pointer|ERRORED` route explicitly documents that it cannot support attempted-value or cause correspondence claims.

### F12 — Probe CRLF normalization before String target-length checks

**Finding:** On the ordinary full-check route with `noValueValidation = false`, kernel [`FormatDefinitionString.validiereFormat`](../../a12-kernel/kernel-rt/kernel-core-runtime/src/main/java/com/mgmtp/a12/kernel/core/rt/_30_8/internal/formatdef/FormatDefinitionString.java) applies the line-break-permission check, calls [`RuntimeUtils.normalizeLinebreaks`](../../a12-kernel/kernel-rt/kernel-core-runtime/src/main/java/com/mgmtp/a12/kernel/core/rt/_30_8/internal/util/RuntimeUtils.java) to normalize CRLF to LF, and only then applies String minimum/maximum length. The earlier no-value/non-full-check exits are separate. At the pinned a12-dmkits revision, the clean-room [`stringConstraintError`](../../a12-rulekit/interpreter/src/commonMain/kotlin/io/github/mbackschat/a12/dm/interpreter/eval/FormalError.kt) route appears to reject newline text when line breaks are forbidden but to measure the unnormalized host String when line breaks are permitted. That creates a source-level divergence candidate for a permitted `"\r\n"` value near a one-code-unit length boundary: the kernel may measure one normalized LF while a12-dmkits may measure two UTF-16 code units. This is not yet an observed disagreement and must not be promoted as one without a focused differential packet.

**Recommendation:** Add paired kernel-strategy and interpreter probes on the full-check route with `noValueValidation = false` and line breaks permitted, holding the String kind and source constant while varying a minimum or maximum around the normalized CRLF length. Preserve the pre-normalized input, normalized stored/result form, target-error cause, and final delta separately so the probe identifies whether normalization belongs before validation, before storage, or only in rendering.

**Acceptance check:** Groovy-dynamic and static-Java agree on the exact CRLF boundary behavior; the a12-dmkits result either agrees or records a reviewed mismatch without weakening projection granularity. A mutation that counts raw CRLF where normalization is required must fail, and ordinary LF plus a no-line-break-permitted rejection control must keep the clause order visible.

## Handoff use

When feeding this queue back to a12-dmkits, open or update items in that project's own gap/plan surfaces and link back to the specific evidence or capsule that motivated them. Close an item here only after recording the upstream revision and outcome; if upstream rejects or supersedes it, retain the disposition so later formalization work does not rediscover the same question.
