# a12-dmkits specification synchronization ledger

This ledger records reconciliation of changes to the project-owned language-neutral semantics under [`../spec/`](../spec/). Pending entries form the outbound queue. Those files are the semantic bridge between a12-kernel-lean and a12-dmkits: kernel-verified discoveries may arrive here from a12-dmkits, while corrections and additions canonized in `spec/` must be reconciled back into a12-dmkits. This ledger tracks that reconciliation without becoming a second semantic specification.

## Ledger contract

Every commit that corrects, narrows, or extends kernel behavior in `spec/` must add or update a ledger entry here in the same change. The spec clause owns the complete semantic account; an entry links to that clause and records only the transport facts needed by the other project.

Pure spelling, formatting, link, or non-semantic navigation edits do not enter the ledger. One entry may group several clauses only when they express one coherent behavioral correction with one upstream acceptance decision. Keep entries concise: do not copy the full spec text, Lean implementation status, or evidence inventory into this ledger.

Each entry has a stable `SPEC-YYYY-MM-DD-NN` ID and records:

- status: `pending`, `handed-off`, `accepted`, or `superseded`;
- the changed spec file and section;
- a concise delta summary;
- the kernel version and evidence or source basis;
- the exact a12-dmkits revision whose source, prose, and tests were audited as the entry's basis;
- the expected a12-dmkits reconciliation surfaces;
- compatibility and testing consequences;
- the local introducing revision and, after acceptance, the reviewed a12-dmkits revision and disposition;
- a `Supersedes` or `Superseded by` link when applicable.

Status advances as follows:

1. `pending` — committed here but not yet delivered to the a12-dmkits maintainer or agent;
2. `handed-off` — delivered with the exact entry IDs and local revision; a returned handback remains here until reviewed;
3. `accepted` — this repository reviewed the exact a12-dmkits revision against the entry's acceptance condition and relevant gates, then recorded the result;
4. `superseded` — a successor replaced a pending or handed-off entry and names it explicitly.

Stable IDs are never reused. An accepted entry is an immutable reconciliation receipt; a later correction creates a new entry with `Supersedes`, while the accepted predecessor remains accepted. Compact accepted and superseded entries stay in this ledger rather than being deleted or copied into an archive.

The user transfers pending entries. Agents working in this repository never edit `../a12-rulekit/`. When a handback arrives, review the exact upstream revision and update the same entry with its outcome; do not create a second feedback ledger. A no-code disposition is valid when a12-dmkits already implements and tests the behavior but needs only documentation reconciliation or an explicit acknowledgement.

If a12-dmkits returns contrary evidence, do not mark the entry accepted. Verify the disagreement against the real kernel. An inconclusive handback remains `handed-off`; a confirmed local error is corrected in `spec/` by a successor entry that supersedes the old pending/handed-off entry, while a confirmed upstream error is returned for correction under the same entry.

The introducing revision cannot name itself inside the same commit. Until handoff, `introducing commit` means the first commit containing the stable entry ID; resolve it with:

```sh
git log -S 'SPEC-YYYY-MM-DD-NN' --format='%H' -- docs/A12-DMKITS-SPEC-SYNC.md
```

## Copy-ready handoff prompt

Use this prompt for one or more pending IDs, replacing both placeholders with the exact values:

> Requested entries: `<SPEC-YYYY-MM-DD-NN, ...>`. a12-kernel-lean revision: `<full introducing revision>`. Work only in the a12-dmkits repository. Read those entries in `../a12-kernel-lean/docs/A12-DMKITS-SPEC-SYNC.md` and the linked canonical clauses under `../a12-kernel-lean/spec/` read-only. For each entry, reconcile the language-neutral semantic change into the appropriate a12-dmkits semantic documentation, findings, interpreter, catalog, corpus, and focused kernel differential surfaces—but change only the surfaces the entry actually affects. Treat the real kernel as the behavioral oracle, preserve a12-dmkits' clean-room boundary, and do not infer broader behavior from the named case. Run the relevant master gates and commit any changes. If an entry is already satisfied and requires no change, do not create an empty commit; return the exact audited a12-dmkits revision. Return that exact revision plus a per-entry disposition of documentation-only, implementation/test change, already satisfied, rejected with evidence, or superseded. Do not write into a12-kernel-lean.

## Entries

### SPEC-2026-07-19-01 — computation `And`/`Or` stop conditions

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `0a9fc9b21ae76588e0f88266936fcaff0eb13568`
- **Kernel behavior:** 30.8.1
- **Canonical clause:** [`09-computations.md` §3.2](../spec/09-computations.md#32-an-invalidity-clear-poisons)
- **Delta:** The earlier sentence attached “a false or unknown left skips the right” to `And` and `Or` collectively. The corrected clause is operator-specific: computation `And` skips its right when the clean left is false or unknown; computation `Or` skips its right when the clean left is true; poison already encountered on the left aborts either connective.
- **Basis:** a12-dmkits [`KERNEL-FINDINGS.md` §11/IF85](../../a12-rulekit/docs/KERNEL-FINDINGS.md) and [`ComputePoisonReadDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/ComputePoisonReadDiffTest.kt), which check false/unknown-left `And`, true-left `Or`, poison abort, and remaining-alternative skipping across both kernel strategies and the peer interpreter.
- **Requested a12-dmkits reconciliation:** Check the canonical computation prose and any operator/control-flow summaries for the same collective-wording ambiguity. Preserve the already-correct interpreter and differential behavior. Add or adjust documentation only if the live wording is ambiguous; make no implementation change merely to produce a nonempty diff.
- **Compatibility:** Semantic precision for an already observed 30.8.1 behavior. The current a12-dmkits implementation and focused tests are expected to remain behaviorally unchanged.
- **Acceptance:** a12-dmkits documentation states the distinct `And` and `Or` stop conditions; the IF85 controls remain green; the handback supplies an exact revision and per-surface disposition.
- **a12-dmkits revision:** pending
- **Disposition:** pending

### SPEC-2026-07-19-02 — empty-operand provenance is not one universal `given` bit

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `0a9fc9b21ae76588e0f88266936fcaff0eb13568`
- **Kernel behavior:** 30.8.1
- **Canonical clauses:** [`03-empty-and-required.md` §A.1 and checklist](../spec/03-empty-and-required.md#a1-the-per-kind-default), read with [`10-validation-and-polarity.md` §4](../spec/10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing)
- **Delta:** The earlier §A.1 modelling note and checklist generalized one `given` bit to every substituted operand. The corrected account separates evaluation from consumer-specific polarity provenance: a one-bit not-given flag may serve a simple symmetric clause, numeric expressions and numeric aggregates use directional fillability, counts are grow-only, date and string families use their own not-given propagation, and filters and other families retain explicit rules.
- **Basis:** the operator-sensitive [validation bundle](../evidence/kernel-30.8.1/captures/validation-core-v1/semantic-observations.json), [`LF10`](LEAN-FINDINGS.md#lf10--numeric-polarity-needs-directional-fillability-not-a-given-bit), the canonical directional account already present in `spec/10`, and a12-dmkits [`DirectionalPolarityDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/DirectionalPolarityDiffTest.kt) plus the [`empty-polarity` corpus](../../a12-rulekit/corpus/cases/empty-polarity/); the retained cases separate empty unsigned, empty signed, fixed Number, and grow-only `Length` polarity.
- **Requested a12-dmkits reconciliation:** Check `KERNEL-SEMANTICS.md`, interpreter design/specification prose, catalog guidance, and any public modelling summaries for an equivalent universal-one-bit claim. Preserve the existing directional implementation and tests. Make no implementation change if those surfaces already distinguish the operator families correctly.
- **Compatibility:** Internal spec consistency and modelling precision for already observed 30.8.1 behavior. No current Lean or a12-dmkits evaluator change is expected.
- **Acceptance:** a12-dmkits has no prose that promotes one `given` bit to the universal polarity representation; its directional Number/`Length` controls remain green; the handback supplies an exact revision and per-surface disposition.
- **a12-dmkits revision:** pending
- **Disposition:** pending

### SPEC-2026-07-19-03 — concrete repetition indices are 1-based

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `0a9fc9b21ae76588e0f88266936fcaff0eb13568`
- **Kernel behavior:** 30.8.1
- **Canonical clauses:** [`01-data-model.md` §§1 and 2.1](../spec/01-data-model.md#21-repetition-contexts-the-iteration-environment) and [`02-logic-and-formal-errors.md` §A.4](../spec/02-logic-and-formal-errors.md#a4-fill-quantifiers-group-scopes-and-the-two-iteration-ranges)
- **Delta:** Correct the zero-based wording and examples. Concrete repetition rows and semantic fold ranges use indices `1, 2, …`; the declared fold spans `1 .. repeatability`, the instantiated fold spans `1 .. rowCount`, and `0` is a document-path API wildcard/special value rather than the first row.
- **Basis:** kernel `PathPart.repetitionIndex()` documentation, a12-dmkits [`CurrentRepetitionDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/CurrentRepetitionDiffTest.kt), [`GroupScopedFieldFillDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/GroupScopedFieldFillDiffTest.kt), and the [`current-repetition` corpus](../../a12-rulekit/corpus/cases/current-repetition/), which establish the 1-based concrete rows and declared-versus-instantiated ranges.
- **Requested a12-dmkits reconciliation:** Check language-neutral data-model, document-addressing, fill-quantifier range, and interpreter documentation and examples for zero-based concrete-row or semantic-fold wording. Preserve the already-correct 1-based runtime and corpus behavior.
- **Compatibility:** Documentation correction for existing 30.8.1 behavior; no evaluator change is expected.
- **Acceptance:** All concrete-row examples and semantic fold ranges are 1-based, `0` is described only in its special/wildcard role, current-repetition and group-scoped fill controls remain green, and the handback supplies an exact revision and disposition.
- **a12-dmkits revision:** pending
- **Disposition:** pending

### SPEC-2026-07-19-04 — exact primitive empty-default tier

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `0a9fc9b21ae76588e0f88266936fcaff0eb13568`
- **Kernel behavior:** 30.8.1
- **Canonical clause:** [`03-empty-and-required.md` §A.1](../spec/03-empty-and-required.md#a1-the-per-kind-default)
- **Delta:** State the catalog header's exact eight kinds: Number→zero, Confirm→false, and Boolean/String/Enumeration/Date/Time/DateTime→not evaluated. DateFragment, DateRange, Custom, and other model types remain explicit type-family or validator clauses rather than being inferred from this header.
- **Basis:** a12-dmkits [`operators.json.emptyOperandDefaults`](../../a12-rulekit/rulekit/src/main/resources/catalog/operators.json) and its catalog probes; [`LF5`](LEAN-FINDINGS.md#lf5--empty-handling-is-a-layered-consuming-clause-policy-not-a-field-kind-function) records why the header is only the default tier.
- **Requested a12-dmkits reconciliation:** Check canonical prose and public summaries for the exact eight-kind inventory and for accidental inference from it to custom or composite types. Preserve the catalog and interpreter behavior if already exact.
- **Compatibility:** Semantic scope precision for existing catalogued 30.8.1 defaults; no implementation change is expected unless a prose-driven default leaked into code.
- **Acceptance:** a12-dmkits prose matches the catalog header exactly, keeps other type families explicit, all header probes remain green, and the handback supplies an exact revision and disposition.
- **a12-dmkits revision:** pending
- **Disposition:** pending

### SPEC-2026-07-19-05 — `Having` keeps known truth and includes self by default

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `0a9fc9b21ae76588e0f88266936fcaff0eb13568`
- **Kernel behavior:** 30.8.1
- **Canonical clause:** [`07-repetition-and-iteration.md` §3](../spec/07-repetition-and-iteration.md#3-the-filter-having-the--correlation-and-aggregation)
- **Delta:** Make three implicit rules explicit: a `Having` candidate is kept only when its complete filter result is known true; a false or unknown candidate is dropped before its selected cell is consumed; and a same-group correlated star includes the outer row unless an authored `CurrentRepetition` inequality excludes it.
- **Basis:** retained `having-malformed-filter-drops` observations and [`LF7`](LEAN-FINDINGS.md#lf7--a-malformed-having-filter-drops-its-row-before-consumption), plus a12-dmkits [`OuterCorrelationDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/OuterCorrelationDiffTest.kt), [`SelfCorrelatedOverlapQuantifierDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/SelfCorrelatedOverlapQuantifierDiffTest.kt), and the [`filter` corpus](../../a12-rulekit/corpus/cases/filter/).
- **Requested a12-dmkits reconciliation:** Check §9 prose, interpreter documentation, and rule-authoring guidance for the exact known-true keep rule and explicit self-inclusion. Preserve ordinary three-valued condition composition: the rule concerns the complete filter result, not an eager ban on every unknown subexpression.
- **Compatibility:** Clarification of already tested 30.8.1 behavior. Existing interpreter and differential results are expected to remain unchanged.
- **Acceptance:** a12-dmkits states the known-true keep rule, filter-before-consumer order, and explicit self-exclusion requirement without weakening ordinary `Or` dominance; focused controls remain green; the handback supplies an exact revision and disposition.
- **a12-dmkits revision:** pending
- **Disposition:** pending

### SPEC-2026-07-19-06 — first-match computation differs from all-alternatives validation

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `175d643596f8def7072467bf27a63ad7d63ac31b`
- **Kernel behavior:** 30.8.1
- **Canonical clauses:** [`SEMANTICS-MAP.md` taxonomy and invariant](../spec/SEMANTICS-MAP.md#5-cross-cutting-invariants), [`01-data-model.md` §3.2](../spec/01-data-model.md#32-computations), and [`09-computations.md` §§5 and 6](../spec/09-computations.md#5-where-a-computation-runs--scope-and-the-parallel-join)
- **Delta:** Complete the ordered alternative rule and correct every summary of the former internal contradiction. Computation selects the first known-true alternative, clean false/unknown falls through, poison aborts, and selection terminates before the operation result can feed back into the scan. A multi-alternative table guards every row; an unconditional alternative is legal only as the sole row. The implicit validation rule does not reuse first-match selection: it retains one guarded mismatch disjunct per alternative, so overlap can compute the first result while validation still fires because a later holding operation differs.
- **Basis:** the kernel's [computation-table documentation](../../a12-kernel/documentation/_merged/kernel-ba.md#computation-tables), overlapping-precondition example, [`ICalculationInfo`](../../a12-kernel/kernel-tool/kernel-core-tool-api/src/main/java/com/mgmtp/a12/kernel/core/tool/a12internal/api/ado/serviceparams/ICalculationInfo.java) selection contract, and Java/Groovy [`CodeGenCalculationAlternative` template](../../a12-kernel/kernel-tool/kernel-core-codegen/src/main/resources/internal/templates/validation/java/calcDir/CodeGenCalculationAlternative.st), whose terminal branch makes selected-operation no-fallthrough kernel-source-inferred but not yet project-locally observed; a12-dmkits [`ComputationPreconditionDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/ComputationPreconditionDiffTest.kt), [`ComputePoisonReadDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/ComputePoisonReadDiffTest.kt), [`ComputationEvaluationLawsTest`](../../a12-rulekit/adapter/src/test/java/io/github/mbackschat/a12/dm/adapter/laws/ComputationEvaluationLawsTest.java), [`ComputationTierExclusivityLawsTest`](../../a12-rulekit/src/test/java/io/github/mbackschat/a12/dm/rulekit/validate/laws/ComputationTierExclusivityLawsTest.java), and the direct all-alternatives implicit-validation differential [`ComputationGuardedValidationDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/ComputationGuardedValidationDiffTest.kt); the non-test clean-room triangulation is [`ComputationEngine.kt`](../../a12-rulekit/interpreter/src/commonMain/kotlin/io/github/mbackschat/a12/dm/interpreter/ComputationEngine.kt).
- **Requested a12-dmkits reconciliation:** Check the canonical §11 prose, interpreter specification, authoring guidance, and implicit-computation-validation description for any claim that compute and validation share one first-tier selector. Keep runtime first-match behavior, no-match-versus-poison, kernel-source-inferred selected-operation termination, the no-unconditional-default authoring boundary, and the generated all-alternatives validation rule distinct. Make no implementation change if the current code and prose already satisfy the corrected account.
- **Compatibility:** This corrects semantic prose and formalization obligations without changing the already tested a12-dmkits runtime. It blocks an unsound future proof or refactoring that would implement generated validation by reusing computation's first-match selector.
- **Acceptance:** a12-dmkits states the two distinct mechanisms, preserves the focused selection/poison/overlap/implicit-validation controls, and returns the exact audited revision plus a per-surface disposition.
- **a12-dmkits revision:** pending
- **Disposition:** pending

### SPEC-2026-07-19-07 — rounding accepts zero places and preserves the two-stage mode

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `2ceee778cbcbd16a63e456fb662d3b61a13c99a8`
- **Kernel behavior:** 30.8.1
- **Canonical clause:** [`04-numbers-and-decimals.md` §§2 and 5](../spec/04-numbers-and-decimals.md#2-rounding)
- **Delta:** Correct the authored `DecimalPlaces` range from `1..14` to **`0..14` inclusive**, state that omission is exactly zero places for both expression and `…Value(field[, n])` forms, and qualify `FLOOR`/`CEILING` direction against the scale-19 `HALF_UP` pre-rounded operand rather than the raw higher-precision input. The field-value forms honor an explicit places argument and share the same arithmetic as expression rounding.
- **Basis:** kernel `CheckOpUtils` and the parser-error contract establish `0..14`, both rounding parse-tree creators lower omission to zero, both checked forms assign the requested result scale, and `BigDecimalUtils` applies scale-19 `HALF_UP` before target-scale `FLOOR`, `CEILING`, or `HALF_UP` at kernel revision `cb66e51fa7ab90b650698f861bf670754e2e1e66`. a12-dmkits `NumberLawsTest`, `RoundingLawsTest`, `RoundDiffTest`, and `SingleArgRoundDiffTest` lock rejection at `15` and exercise zero places, directions, ties, pre-round, omission, and the parameterized value form against kernel 30.8.1; they do not yet contain a focused accepted-`14` control.
- **Requested a12-dmkits reconciliation:** Correct `docs/KERNEL-SEMANTICS.md` and catalog/Javadoc claims that still say `1..14`, toward-zero/away-from-zero, integer-only value forms, or banker's rounding. Preserve the already-correct interpreter arithmetic and differentials. Extend the typed DSL/read model only as needed so `RoundDownValue`, `RoundUpValue`, and `RoundAccountingValue` retain and render an optional explicit places argument instead of discarding it during conversion.
- **Compatibility:** This corrects canonical semantics and exposes a currently lost legal authored form in a12-dmkits's typed representation; it does not change kernel behavior. Preserve the existing one-argument DSL factories, their zero-place meaning, and their rendering. A new places-bearing factory overload is additive, but the handback must explicitly classify source, binary, serialization, and exhaustive-consumer compatibility for whichever public sealed-AST representation carries the argument rather than assuming that a record or variant change is additive.
- **Acceptance:** a12-dmkits prose, catalog, Javadocs, typed read/model/rendering, and focused tests agree that `0` and `14` are legal, `15` is rejected, omission equals zero, `…Value(field, 2)` round-trips without losing the argument, negative floor/ceiling directions are correct, and accounting ties round away from zero. The handback supplies the exact reviewed revision and per-surface disposition.
- **a12-dmkits revision:** pending
- **Disposition:** pending
