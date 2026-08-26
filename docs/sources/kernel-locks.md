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
| Traversal order versus cause blindness (`LF69`) | Kernel-locked only for the observable prefix; public output erases cause identity. |
| Value-list `AtLeastOne`/`No` values-first behavior | Kernel-locked by `ValueListQuantifierOrderDiffTest` S4/S5. |
| Value-list `NotAll` prepass | No known authorable input separates the routes; the observable result is Kernel-locked. |
| Kept-successor filter lookahead | Kernel-locked by `FirstFilledValueKeptSuccessorDiffTest` S1–S4. |
| Groovy condition-line splitting | Kernel-locked by `ConditionLineSplitDiffTest`, including route engagement. |
| Groovy calculation-closure splitting | Kernel-locked by `CalculationClosureSplitDiffTest`, including later-chunk winners and no-winner clearing. |

“Not assessed,” “source-confirmed but not Kernel-locked,” and “no known observable discriminator” are different assurance states. Exact retained observation identities remain in [`EVIDENCE.md`](../EVIDENCE.md).
