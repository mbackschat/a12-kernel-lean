# Kernel lock source index

<a id="src-kernel-lock-index"></a>
## Known Kernel locks and deliberate non-locks

This index preserves assurance distinctions that the implementation map's `L` dimension cannot express by itself.

| Seam | Current source assurance |
|---|---|
| Malformed `Having` consumer drop (`LF7`) | Locally calibrated by the retained validation observation; not an upstream lock. |
| Computation precondition skip before poison (`LF19`) | Kernel-locked by `CascadeClearedDependencyDiffTest` and `ComputationPreconditionDiffTest`. |
| Ordered computation connectives (`LF21`) | Kernel-locked by `ComputePoisonReadDiffTest`. |
| Partial-validation filtered-rule skip (`LF23`) | Source-closed by `rulesDir/CodeGenRuleDefinition.st` in all three dialects; the enclosing `CodeGenRules.st` is not the deciding locus. |
| One-pass division lowering (`LF32`) | Kernel-locked by the maintained controls for `SPEC-2026-07-19-08`, `SPEC-2026-07-19-09`, and `SPEC-2026-07-19-14`. |
| Numeric receiver/argument order (`LF35`) | Source-closed by `CompositeOperation.getFeldOperationCodeJava`; no target-language branch exists at that lowering locus. |
| Branch-independent RNU relation (`LF45`) | Kernel-locked by `RepetitionNotUniqueGuardedDiffTest`. |
| Prefix-sensitive `FirstFilledValue` (`LF48`) | Kernel-locked by `FirstFilledValueOmittedTailDiffTest`. |
| Computation fill-quantifier scan order (`LF50`) | Kernel-locked by `ComputePoisonReadDiffTest`, `BareGroupComputeExactnessDiffTest`, and `ComputationFillQuantifierRestartDiffTest`. |
| Semantic-index and parallel-index route timing (`LF53`) | Kernel-locked on the ordinary route by `IndexedReadSuppressionDiffTest` and `SemanticIndexMatchedInvalidCellDiffTest`, and on the parallel route by `ParallelIterationIndexMarkingDiffTest`. |
| Numeric no-fit prefix order (`LF64`) | Source-confirmed and locally separated, but deliberately not Kernel-locked. |
| Ordinary `FieldValueAsNumber` source-domain refusal | Peer [`FieldValueAsNumberDomainLawsTest`](../../../a12-rulekit/src/test/java/io/github/mbackschat/a12/dm/rulekit/validate/laws/FieldValueAsNumberDomainLawsTest.java) at `483af8164b9b7b80db8a9f53d8925f60a2b22625` locks `MVK_NO_CONVERT_IN_NUMBER` for wrong String pattern, excessive or absent maximum length, and invalid or over-budget selected category tokens, with admitted String and category controls. Kernel `CheckEntityUtils.checkIsConvertableToNumber` owns the gate; peer [KF111](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf111) owns the broader conversion account. This class identifies the reached conversion gate, not whole-model precedence; supplementary-plane tokens are a source-level parser boundary, and this citation makes no new whole-model reachability claim. |
| Traversal order versus cause blindness (`LF69`) | Kernel-locked only for the observable prefix; public output erases cause identity. |
| Value-list `AtLeastOne`/`No` values-first behavior | Kernel-locked by `ValueListQuantifierOrderDiffTest` S4/S5. |
| Value-list `NotAll` prepass | No known authorable input separates the routes; the observable result is Kernel-locked. |
| Kept-successor filter lookahead | Kernel-locked by `FirstFilledValueKeptSuccessorDiffTest` S1–S4. |
| Groovy condition-line splitting | Kernel-locked by `ConditionLineSplitDiffTest`, including route engagement. |
| Groovy calculation-closure splitting | Kernel-locked by `CalculationClosureSplitDiffTest`, including later-chunk winners and no-winner clearing. |
| Custom field-type acceptance arm | Kernel-locked by the peer's `CustomFieldTypeContextDiffTest`, `CustomFieldTypeRejectionCodeDiffTest`, and `CustomFieldTypeMessageDiffTest` across both strategies, including per-cell observation cardinality. |
| Custom field-type conversion arm | **Source-read only, deliberately not locked.** The 30.8.1 SPI declares display-to-internal and internal-to-display conversions beside acceptance; no retained observation shows whether, where, or in which direction the engine invokes either, so no behavioral claim is made. Reading the interface establishes the shape a consumer must host, not the engine's use of it. |

“Not assessed,” “source-confirmed but not Kernel-locked,” and “no known observable discriminator” are different assurance states. Exact retained observation identities remain in [`EVIDENCE.md`](../EVIDENCE.md).
