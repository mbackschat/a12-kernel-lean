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
git log -S 'SPEC-YYYY-MM-DD-NN' --format='%H' -- docs/A12-DMKITS-SPEC-SYNC-LEDGER.md
```

## Copy-ready handoff prompt

Use this prompt for one or more pending IDs, replacing both placeholders with the exact values:

> Requested entries: `<SPEC-YYYY-MM-DD-NN, ...>`. a12-kernel-lean revision: `<full introducing revision>`. Work only in the a12-dmkits repository. Read those entries in `../a12-kernel-lean/docs/A12-DMKITS-SPEC-SYNC-LEDGER.md` and the linked canonical clauses under `../a12-kernel-lean/spec/` read-only. For each entry, reconcile the language-neutral semantic change into the appropriate a12-dmkits semantic documentation, findings, interpreter, catalog, corpus, and focused kernel differential surfaces—but change only the surfaces the entry actually affects. Treat the real kernel as the behavioral oracle, preserve a12-dmkits' clean-room boundary, and do not infer broader behavior from the named case. Run the relevant master gates and commit any changes. If an entry is already satisfied and requires no change, do not create an empty commit; return the exact audited a12-dmkits revision. Return that exact revision plus a per-entry disposition of documentation-only, implementation/test change, already satisfied, rejected with evidence, or superseded. Do not write into a12-kernel-lean.

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
- **Disposition:** Partial at `517ef65b93ded2775355175dcec18877f8bc8106`: implementation and focused tests already distinguish the operators; only the ambiguous collective wording in canonical prose remains pending.

### SPEC-2026-07-19-02 — empty-operand provenance is not one universal `given` bit

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `0a9fc9b21ae76588e0f88266936fcaff0eb13568`
- **Kernel behavior:** 30.8.1
- **Canonical clauses:** [`03-empty-and-required.md` §A.1 and checklist](../spec/03-empty-and-required.md#a1-the-per-kind-default), read with [`10-validation-and-polarity.md` §4](../spec/10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing)
- **Delta:** The earlier §A.1 modelling note and checklist generalized one `given` bit to every substituted operand. The corrected account separates evaluation from consumer-specific polarity provenance: a one-bit not-given flag may serve a simple symmetric clause, numeric expressions and numeric aggregates use directional fillability, counts are grow-only, date and string families use their own not-given propagation, and filters and other families retain explicit rules.
- **Basis:** the operator-sensitive [validation bundle](../evidence/kernel-30.8.1/captures/validation-core-v1/semantic-observations.json), [`LF10`](LEAN-FINDINGS.md#lf10--numeric-polarity-needs-directional-fillability-not-a-given-bit), the canonical directional account already present in `spec/10`, and a12-dmkits [`DirectionalPolarityDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/DirectionalPolarityDiffTest.kt) plus the [`empty-polarity` corpus](../../a12-rulekit/corpus/cases/empty-polarity/); the retained cases separate empty unsigned, empty signed, fixed Number, and grow-only `Length` polarity.
- **Requested a12-dmkits reconciliation:** No source or documentation change is requested. Confirm the relevant existing directional controls against the exact returned revision.
- **Compatibility:** Internal spec consistency and modelling precision for already observed 30.8.1 behavior. No current Lean or a12-dmkits evaluator change is expected.
- **Acceptance:** a12-dmkits has no prose that promotes one `given` bit to the universal polarity representation; its directional Number/`Length` controls remain green; the handback supplies an exact revision and per-surface disposition.
- **a12-dmkits revision:** pending
- **Disposition:** Read-only audit at `517ef65b93ded2775355175dcec18877f8bc8106` found the prose, implementation, and test sources already satisfied; acceptance awaits exact-revision gate confirmation.

### SPEC-2026-07-19-03 — concrete repetition indices are 1-based

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `0a9fc9b21ae76588e0f88266936fcaff0eb13568`
- **Kernel behavior:** 30.8.1
- **Canonical clauses:** [`01-data-model.md` §§1 and 2.1](../spec/01-data-model.md#21-repetition-contexts-the-iteration-environment) and [`02-logic-and-formal-errors.md` §A.4](../spec/02-logic-and-formal-errors.md#a4-fill-quantifiers-group-scopes-and-the-two-iteration-ranges)
- **Delta:** Correct the zero-based wording and examples. Concrete repetition rows and semantic fold ranges use indices `1, 2, …`; the declared fold spans `1 .. repeatability`, the instantiated fold spans `1 .. rowCount`, and `0` is a document-path API wildcard/special value rather than the first row.
- **Basis:** kernel `PathPart.repetitionIndex()` documentation, a12-dmkits [`CurrentRepetitionDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/CurrentRepetitionDiffTest.kt), [`GroupScopedFieldFillDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/GroupScopedFieldFillDiffTest.kt), and the [`current-repetition` corpus](../../a12-rulekit/corpus/cases/current-repetition/), which establish the 1-based concrete rows and declared-versus-instantiated ranges.
- **Requested a12-dmkits reconciliation:** No source or documentation change is requested. Confirm the relevant current-repetition and group-scoped fill controls against the exact returned revision.
- **Compatibility:** Documentation correction for existing 30.8.1 behavior; no evaluator change is expected.
- **Acceptance:** All concrete-row examples and semantic fold ranges are 1-based, `0` is described only in its special/wildcard role, current-repetition and group-scoped fill controls remain green, and the handback supplies an exact revision and disposition.
- **a12-dmkits revision:** pending
- **Disposition:** Read-only audit at `517ef65b93ded2775355175dcec18877f8bc8106` found the prose, implementation, and test sources already satisfied; acceptance awaits exact-revision gate confirmation.

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
- **Disposition:** Partial at `517ef65b93ded2775355175dcec18877f8bc8106`: the catalog and probes carry the exact eight defaults; only the canonical prose inventory remains pending.

### SPEC-2026-07-19-05 — `Having` keeps known truth and includes self by default

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `0a9fc9b21ae76588e0f88266936fcaff0eb13568`
- **Partial handback revisions:** `c15036b5d4ee7ff76ffaf5cb1f860a86317ae272`, `e3cc376229ced8c2d8c8460562e30b8e3c9b282c`
- **Kernel behavior:** 30.8.1
- **Canonical clause:** [`07-repetition-and-iteration.md` §3](../spec/07-repetition-and-iteration.md#3-the-filter-having-the--correlation-and-aggregation)
- **Delta:** Make the filter and exclusion rules explicit: a `Having` candidate is kept only when its complete filter result is known true; a false or unknown candidate is dropped before its selected cell is consumed; and a same-group correlated star includes the outer coordinate unless an authored `CurrentRepetition` inequality excludes it. `CurrentRepetition(G)` compares the resolved coordinate at level `G`, not an opaque physical row; in `A*/B*`, comparing only `B` may exclude candidates in several `A` rows when they share the outer `B` leaf index.
- **Basis:** retained `having-malformed-filter-drops` observations and [`LF7`](LEAN-FINDINGS.md#lf7--a-malformed-having-filter-drops-its-row-before-consumption), plus a12-dmkits [`OuterCorrelationDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/OuterCorrelationDiffTest.kt), [`SelfCorrelatedOverlapQuantifierDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/SelfCorrelatedOverlapQuantifierDiffTest.kt), [`MultiStarOuterCorrelationDiffTest`](../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/MultiStarOuterCorrelationDiffTest.kt), and the [`filter` corpus](../../a12-rulekit/corpus/cases/filter/).
- **Requested a12-dmkits reconciliation:** State the exact known-true keep rule, default self-inclusion, and named-coordinate exclusion rule in canonical/public prose. Preserve the already-correct interpreter and focused controls, ordinary three-valued condition composition, filter-before-consumer behavior, and first-star binding.
- **Compatibility:** Clarification of already tested 30.8.1 behavior. Existing interpreter and differential results are expected to remain unchanged.
- **Acceptance:** a12-dmkits states the known-true keep rule, filter-before-consumer order, and named-coordinate self-exclusion requirement without weakening ordinary `Or` dominance or the first-star binding rule; focused controls remain green; the handback supplies an exact revision and disposition.
- **a12-dmkits revision:** pending
- **Disposition:** Partial at `517ef65b93ded2775355175dcec18877f8bc8106`, `c15036b5d4ee7ff76ffaf5cb1f860a86317ae272`, and `e3cc376229ced8c2d8c8460562e30b8e3c9b282c`: implementation, differentials, and findings establish the known-true, self-inclusion, and multi-star coordinate behavior; general canonical/public wording remains pending. This does not close the separate parent-versus-descendant captured-coordinate discriminator in `SPEC-2026-07-19-16`.

### SPEC-2026-07-19-06 — first-match computation differs from all-alternatives validation

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `73f039a9e2954e9c1cf8813668b12ad336f14d23`
- **Kernel behavior:** 30.8.1
- **Canonical clauses:** [`SEMANTICS-MAP.md` taxonomy and invariant](../spec/SEMANTICS-MAP.md#5-cross-cutting-invariants), [`01-data-model.md` §3.2](../spec/01-data-model.md#32-computations), and [`09-computations.md` §§5 and 6](../spec/09-computations.md#5-where-a-computation-runs--scope-and-the-parallel-join)
- **Delta:** Complete the ordered alternative rule and correct every summary of the former internal contradiction. Computation selects the first known-true alternative, clean false/unknown falls through, poison aborts, and selection terminates before the operation result can feed back into the scan. A multi-alternative table guards every row; an unconditional alternative is legal only as the sole row. The implicit validation rule does not reuse first-match selection: it retains one guarded mismatch disjunct per alternative, so overlap can compute the first result while validation still fires because a later holding operation differs.
- **Basis:** the kernel's [computation-table documentation](../../a12-kernel/documentation/_merged/kernel-ba.md#computation-tables), overlapping-precondition example, [`ValidationModelConverter`](../../a12-kernel/kernel-md/kernel-md-model/src/main/java/com/mgmtp/a12/kernel/md/model/internal/service/ValidationModelConverter.java), [`ComputationAlternativesJoiner`](../../a12-kernel/kernel-md/kernel-md-model/src/main/java/com/mgmtp/a12/kernel/md/model/internal/service/utils/ComputationAlternativesJoiner.java), and Java/Groovy/JavaScript [`CodeGenCalculationAlternative` template](../../a12-kernel/kernel-tool/kernel-core-codegen/src/main/resources/internal/templates/validation/java/calcDir/CodeGenCalculationAlternative.st). At the audited a12-dmkits revision, [`ComputationEngine.kt`](../../a12-rulekit/interpreter/src/commonMain/kotlin/io/github/mbackschat/a12/dm/interpreter/ComputationEngine.kt) correctly scans first-match while [`ParsedModel.kt`](../../a12-rulekit/interpreter/src/commonMain/kotlin/io/github/mbackschat/a12/dm/interpreter/ParsedModel.kt) correctly synthesizes all guarded mismatch disjuncts, but comments in `ParsedModel.kt`, `KERNEL-FINDINGS.md`, and `INTERPRETER-FINDINGS.md` still describe one shared selection mechanism. Existing first-match, overlap-legality, and all-alternatives tests cover the ingredients separately; none composes the canonical case in which both guards hold, computation selects operation `1`, stored target `1`, and implicit validation fires because operation `2` also remains.
- **Requested a12-dmkits reconciliation:** Correct every claim that computation and implicit validation share one selection mechanism: they share authored guards and operations but have distinct consumers. Preserve the already-correct first-match runtime and all-alternatives synthesis. Add one focused existing-harness control that composes both observations in the same overlapping two-row model, with equal-result and nonholding-second-row controls; do not build a new capture facility. Keep no-match-versus-poison, selected-operation termination, the no-unconditional-default authoring boundary, and validation-phase polarity distinct.
- **Compatibility:** This corrects semantic prose and formalization obligations without changing the already tested a12-dmkits runtime. It blocks an unsound future proof or refactoring that would implement generated validation by reusing computation's first-match selector.
- **Acceptance:** a12-dmkits states the two distinct mechanisms, the composed overlap discriminator and its two controls pass through the existing differential/interpreter facilities, the focused selection/poison/implicit-validation tests remain green, and the handback returns the exact audited revision plus a per-surface disposition.
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

### SPEC-2026-07-19-08 — every arithmetic node uses precision-50 `HALF_UP`

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `2ceee778cbcbd16a63e456fb662d3b61a13c99a8`
- **Partial handback revisions:** `41ecfc511d3828aa841bbbb2c5655ebbbacc10df`, `7dc0a52fba5ffc2d90fdfef76cc8ac94e1d8dc4d`
- **Kernel behavior:** 30.8.1
- **Canonical clause:** [`04-numbers-and-decimals.md` §5](../spec/04-numbers-and-decimals.md#5-internal-precision--the-constants-that-must-match-exactly)
- **Delta:** Correct the former claim that `+` and `−` stay exact. The kernel applies one precision-50 decimal `MathContext`, default `HALF_UP`, independently to every `+`, `−`, `×`, `÷`, and `^` node. Before evaluation/code generation, it performs one order-sensitive post-order pass: each original multiplication pulls only immediate root-division operands, keeps ordinary factors first in their existing order, appends extracted numerators and denominators in division encounter order, left-folds multi-factor products, and never revisits newly created products. Authored fold order is therefore not always evaluated fold order, but the mechanism is not global or fixed-point normalization.
- **Basis:** kernel `VkBigDecimal` constructs one `MathContext(50)` and passes it to `add`, `subtract`, `multiply`, `divide`, and `pow`; `DivisionTransformer`, parse-tree traversal, and composite code generation establish the exact one-pass/order/left-fold mechanism at kernel revision `cb66e51fa7ab90b650698f861bf670754e2e1e66`. In particular, `a * {b / c}` and `{b / c} * a` both become `{a * b} / c`, while a newly created product containing a nested extracted division is not revisited. The formerly cited `[q] / 3 * 3` rounding example is not a scale-19 pre-round discriminator because this rewrite makes it exact; three separately braced thirds joined by addition are the corrected discriminator. a12-dmkits' JVM `Dec` and `KERNEL-FINDINGS.md` currently cap only multiplication/division/power, while `ArithmeticDiffTest` has a genuine 52-to-50-digit multiplication separator but no above-50 addition/subtraction or division-rewrite separator.
- **Requested a12-dmkits reconciliation:** Apply the precision boundary to JVM addition and subtraction as well as the existing operations; reconcile the common contract, JS gap/account, interpreter findings, kernel semantics, catalog/operator guidance, staged implementation guidance, and any evaluator optimization that assumes exact `+`/`−`. Determine one clean-room ordered single-pass lowering mechanism for division-bearing multiplication rather than accumulating expression-shape patches or flattening factors into an unordered/global fraction. Preserve braces through the authoring checks even though they do not block the later rewrite. Replace the superseded `[q] / 3 * 3` staging example wherever it appears. Add focused kernel differentials that separate rounded `+` and `−` from exact arithmetic, direct authored-tree evaluation from the one-pass lowered tree, one pass from a fixed point, and the real three-thirds scale-19 pre-round from direct flooring.
- **Compatibility:** This changes a12-dmkits results for legal expressions whose addition or subtraction produces more than 50 significant digits and may change division-bearing products whose authored and one-pass rewritten trees round differently. Classify JVM, JS, public interpreter, serialization, and dmtool-release consequences explicitly; do not describe the correction as documentation-only.
- **Acceptance:** Both kernel strategies and the JVM interpreter agree on focused above-50 `+`/`−` witnesses, order-sensitive one-pass division-rewrite witnesses, a nested no-second-pass witness, and the corrected three-thirds pre-round witness; all five operations use the same precision/rounding contract at each evaluated node; JS either conforms or remains an explicit fail-closed/nonconforming capability; prose and operator metadata contain neither “`+`/`−` stay exact” nor global/fixed-point normalization claims. The handback supplies the exact reviewed revision and per-surface disposition.
- **a12-dmkits revision:** pending
- **Disposition:** Partial at `41ecfc511d3828aa841bbbb2c5655ebbbacc10df` and `7dc0a52fba5ffc2d90fdfef76cc8ac94e1d8dc4d`: JVM and Node now share the precision-50 contract for all five arithmetic operations; `DecimalHostParityTest`, `DecimalPrecisionParityDiffTest`, and `DecimalPowerGrowthTest` cover host parity, observable tri-engine addition/subtraction/division/power separators, and bounded JavaScript power work. The exact order-sensitive one-pass division-bearing multiplication lowering remains outside this evidence, so the entry stays pending.

### SPEC-2026-07-19-09 — numeric scale gating tracks signed scale and constant expandability

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `2ceee778cbcbd16a63e456fb662d3b61a13c99a8`
- **Kernel behavior:** 30.8.1
- **Canonical clause:** [`04-numbers-and-decimals.md` §§1, 3, and 4](../spec/04-numbers-and-decimals.md#1-scale-gates----checked-at-parse-time)
- **Delta:** Replace the blanket “numeric literals are scale-exempt” and “power always has unknown scale” account. Checked numeric expressions carry a known signed scale or unknown plus a multiplicative-constant capability. Equality/inequality may pad only a capable smaller-scale side; a scale-2 field compared with `0` is legal, while a scale-0 field compared with `0.00` is not. A scale-0 base raised to a syntactically simple nonnegative constant exponent derives scale 0; the exponent must itself have known scale no greater than 0. The power endpoints `±1000`, `0^0`, and brace-based nesting/region rules are explicit.
- **Basis:** kernel parser `CheckKonstanteImpl` retains fractional literal length and strips trailing zeros from integer literals, `CheckOperationImpl` derives power/addition/multiplication summaries and propagates the multiplicative-constant capability, and `CheckVergleichsBedingungImpl` applies the asymmetric smaller-side rule at kernel revision `cb66e51fa7ab90b650698f861bf670754e2e1e66`. The committed a12-dmkits prose still states global literal exemption and always-unknown power scale; its focused laws cover neighboring field/expression gates but not the asymmetric literal-scale or scale-0 power matrix.
- **Requested a12-dmkits reconciliation:** Correct canonical prose, typed authoring/checking summaries, operator metadata, and any implementation that represents the gate as only `Option<Nat>` or treats every literal as exempt. Add a focused legal/illegal matrix for both operand orders, `0` versus `0.00`, negative stripped integer-literal scales, scale-0 versus fractional/unknown power bases and exponents, and the admitted/quiet power endpoints. Preserve ordering's scale exemption and warning suppression.
- **Compatibility:** This narrows and widens distinct authored equality/power shapes to match the kernel. Classify parser/read/typed-builder compatibility and diagnostic effects; runtime arithmetic values are unaffected when the model was already legal.
- **Acceptance:** a12-dmkits reproduces the asymmetric scale gate and narrow power-scale exception against both kernel strategies, carries enough checked metadata to express the rule without syntax-specific patches, and returns the exact reviewed revision plus a per-surface disposition.
- **a12-dmkits revision:** pending
- **Disposition:** pending

### SPEC-2026-07-19-10 — power preserves staged Java precision and reciprocal-first negative order

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `2ceee778cbcbd16a63e456fb662d3b61a13c99a8`
- **Partial handback revisions:** `41ecfc511d3828aa841bbbb2c5655ebbbacc10df`, `7dc0a52fba5ffc2d90fdfef76cc8ac94e1d8dc4d`
- **Kernel behavior:** 30.8.1
- **Canonical clauses:** [`04-numbers-and-decimals.md` §3](../spec/04-numbers-and-decimals.md#3-arithmetic-domain-failures-are-consumer-sensitive) and [`§5`](../spec/04-numbers-and-decimals.md#5-internal-precision--the-constants-that-must-match-exactly)
- **Delta:** Specify the numeric mechanism behind admitted powers. Positive power follows the OpenJDK 21 X3.274 numeric-value algorithm, rounding binary-exponentiation intermediates at precision `50 + decimalDigits(exponent) + 1` before the final precision-50 round. Negative power is kernel-specific: it first rounds `1 / base` at precision 50, then applies the positive algorithm. Exact rational power plus one final round and reciprocal-after-positive-power are both observably different.
- **Basis:** kernel `VkBigDecimal.power` and `getKehrwert` at revision `cb66e51fa7ab90b650698f861bf670754e2e1e66`, together with the OpenJDK 21 `BigDecimal.pow(int, MathContext)` X3.274 contract. The positive separator `0.473471768303411 ^ 7` ends in `…3319` under staged power but `…3318` under exact-power/final-round. The negative separator `3 ^ -3` ends in `…7036` under the kernel's reciprocal-first order but `…7037` under a final reciprocal. Revision `41ecfc51` moved both peer backends to the reciprocal-first negative mechanism, added host-level positive/negative precision locks, and closed the negative separator against both kernel routes. Canonical prose and the complete dual-route edge matrix remain open.
- **Requested a12-dmkits reconciliation:** Preserve the reciprocal-first mechanism at its shared power locus; correct any stale exact/bit-for-bit or reciprocal-after-power prose; and complete the dual-kernel-route matrix with the positive staged-precision separator, `±1000`, `±1001`, `0^0`, `0^-1`, and fractional-exponent controls. Do not use the peer interpreter as the oracle.
- **Compatibility:** The partial handback already corrected legal negative powers that differ in the last retained digit and aligned both peer backends. Remaining work should add prose and evidence without changing that mechanism unless a named kernel separator disagrees.
- **Acceptance:** Both kernel strategies and the JVM interpreter agree on discriminating positive and negative precision cases and the named known-value domain-edge matrix; the implementation performs reciprocal-first staging structurally rather than special-casing examples; prose makes the OpenJDK 21 algorithm and external-evidence boundary explicit; the handback supplies the exact reviewed revision and per-surface disposition.
- **a12-dmkits revision:** pending
- **Disposition:** Partial handbacks accepted at `41ecfc511d3828aa841bbbb2c5655ebbbacc10df` and `7dc0a52fba5ffc2d90fdfef76cc8ac94e1d8dc4d`: positive staged work and reciprocal-first negative power are implemented and tri-checked, with host zero and exponent controls. The complete named dual-kernel-route matrix for `±1000`, `±1001`, `0^0`, `0^-1`, and fractional exponents was not independently verified in this review, so the entry stays pending.

### SPEC-2026-07-19-11 — arithmetic fillability uses joint terms and conservative power dispatch

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `2ceee778cbcbd16a63e456fb662d3b61a13c99a8`
- **Kernel behavior:** 30.8.1
- **Canonical clause:** [`10-validation-and-polarity.md` §4](../spec/10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing)
- **Delta:** Replace the non-executable “sign-dependent/parity” summary with the exact `+`, `−`, `×`, reciprocal, and `÷` direction formulas and the kernel's conservative power dispatch. Multiplication includes joint movement terms that survive when current signs are zero; division rejects current zero before transforming divisor fillability; power depends on fixedness, base regions around `−1/0/1`, exponent directions and parity, reciprocal-first negative staging, and conservative fallback branches. Invalidity and result-empty provenance remain independent of the two direction flags.
- **Basis:** kernel `VkBigDecimal.add`, `subtract`, `multiply`, `produktKannGroesserWerden`, `produktKannKleinerWerden`, `divide`, `getKehrwert`, `power`, and `powCanChange*` at revision `cb66e51fa7ab90b650698f861bf670754e2e1e66`. a12-dmkits `ArithFill` implements the same mechanism, while `ArithmeticFillPolarityDiffTest` and `ArithmeticFillTest` cover basic addition/subtraction, fixed-sign multiplication/division, and several power examples but do not isolate multiplication joint terms, reciprocal fillability, most power branches, or both direction bits independently.
- **Requested a12-dmkits reconciliation:** Make the exact formulas and the heuristic—not exact-reachability—power boundary durable in canonical prose and pure tests. Add separating controls for multiplication's joint terms and zero-sign case; a fillable nonzero divisor in both directions; zero-divisor invalid absorption; fixed exponent `0`; fixed bases `1`, `0.5`, `0`, and `−1`; negative reciprocal staging; the both-variable grow-only special case; and invalid power domains. Probe-lock the surprising `0` raised to empty unsigned versus empty signed exponents against both kernel strategies before presenting it as intentional policy. Preserve the existing clean-room implementation where those controls confirm it; fix one shared mechanism if any branch diverges.
- **Compatibility:** The current peer fillability implementation is source-aligned, so the expected change is stronger specification and branch coverage rather than a public fillability result change. This does not supersede the separate negative-power value-order defect in `SPEC-2026-07-19-10`. Any contrary probe must be classified before altering the interpreter because the flags decide VALUE versus OMISSION in authored and implicit computation validations.
- **Acceptance:** a12-dmkits documents the executable formulas and conservative power boundary; pure tests inspect both output bits; both kernel strategies agree on the separating matrix including the zero-base discriminator; no invalid operation reaches a comparison as an ordinary fixed value; and the handback supplies the exact reviewed revision plus per-surface disposition.
- **a12-dmkits revision:** pending
- **Disposition:** pending

### SPEC-2026-07-19-12 — division-by-zero computations poison despite a cleared delta

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `2ceee778cbcbd16a63e456fb662d3b61a13c99a8`
- **Kernel behavior:** 30.8.1
- **Canonical clauses:** [`04-numbers-and-decimals.md` §3](../spec/04-numbers-and-decimals.md#3-arithmetic-domain-failures-are-consumer-sensitive), [`09-computations.md` §§3.1–3.2](../spec/09-computations.md#31-a-precondition-clear-cascades-as-empty), and [`09-computations.md` §4](../spec/09-computations.md#4-the-stored-form--a-computed-value-lands-as-a-string-in-the-targets-shape)
- **Delta:** Correct the former globally quiet/clean-empty reading. Division by zero is a domain failure: a validation comparison maps it to not-fired, but the legal `RoundAccounting(div, 2)` computation route preserves the invalid result, marks the target invalid with `berechnungsWertFehler`, and poisons a dependent read. Fresh no-value-output and stale CLEARED are delta observations, not proof of a clean target. Numeric arithmetic evaluates the one-pass lowered tree left-to-right: a domain-invalid numeric result does not suppress evaluation of the later operand, while a poison already thrown by the lowered left subtree aborts before the right subtree.
- **Basis:** kernel `VkBigDecimal.divide`, `VkBigDecimal.setScale`, `BigDecimalUtils.runden`, `CompositeOperation`, `CalculationController`, `CalculationCache`, the generated calculation-alternative handler, and `DocumentComputationResultImpl` at revision `cb66e51fa7ab90b650698f861bf670754e2e1e66` establish the invalid-number result, post-lowering Java receiver/argument order, target invalidation, formal calculation error, and dependent-read exception/cascade. Java evaluates the generated receiver before its argument and the argument before the arithmetic method call; the kernel represents zero division as an invalid numeric value rather than a thrown read. a12-dmkits [`ComputationEvaluationLawsTest`](../../a12-rulekit/adapter/src/test/java/io/github/mbackschat/a12/dm/adapter/laws/ComputationEvaluationLawsTest.java) currently observes only fresh no-field-output and stale clearing through [`RuntimeLaws.computeDetailOf`](../../a12-rulekit/adapter/src/test/java/io/github/mbackschat/a12/dm/adapter/laws/RuntimeLaws.java), which omits `formalErrorsInOperands`; it does not read the target from a dependent computation.
- **Requested a12-dmkits reconciliation:** Correct prose, tests, and interpreter behavior that treat division-by-zero computation as a clean-empty cascade. Add one focused dual-kernel-route `RoundAccounting(div, 2)` observation that retains `formalErrorsInOperands` and one dependent computation that distinguishes an EMPTY read from poison, with the interpreter used only for triangulation. Also lock the lowered-tree read-order class with distinct invalid operands: one case in which a domain-invalid lowered left still reaches a poisoned right, and one division-lowering case in which the lowered operand order—not authored syntax—selects the first poison. Preserve the public value/delta observation while adding the missing invalidity channels.
- **Compatibility:** This corrects the downstream division semantic classification without changing the already observed fresh/stale value delta. Local Lean preserves value, domain failure through `RoundAccounting`, and inherited read poison as distinct expression results; maps domain failure to a target-local no-value invalidity carrying the language-neutral `berechnungsWertFehler` cause; applies the result at one exact address; and projects the full target outcome to a cause-free clean-empty, exact-value, or poisoned dependency observation. Downstream context/read integration, general document scheduling, and portable dual-route confirmation remain open. An interpreter that currently clears zero division cleanly requires a root fix at the arithmetic-domain-failure-to-computation-target boundary. This entry does not classify invalid-power computation.
- **Acceptance:** a12-dmkits records the consumer-sensitive domain-failure and lowered-tree read-order rules at its shared semantic root; both kernel routes agree on the legal wrapper's formal-error/dependent-read discriminator and the two ordered poison separators; the interpreter triangulates or records an explicit mismatch; and the handback supplies an exact revision plus per-surface disposition.
- **a12-dmkits revision:** pending
- **Disposition:** pending

### SPEC-2026-07-19-13 — tolerance normalizes operands first and uses directional inequality polarity

- **Status:** accepted
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `2ceee778cbcbd16a63e456fb662d3b61a13c99a8`
- **Partial handback revision:** `d6a08f5b53022d9caae35e6d842a2b7b22cd5b25`
- **Completion handback revision:** `7b39728eafdb53b0a69fcafd34817980bb900632`
- **Kernel behavior:** 30.8.1
- **Canonical clauses:** [`04-numbers-and-decimals.md` §§4–5 and checklist](../spec/04-numbers-and-decimals.md#4-other-numeric-constraints), [`09-computations.md` §6 and checklist](../spec/09-computations.md#6-the-implicit-validation-rule-precisely), and [`10-validation-and-polarity.md` §4 and checklist](../spec/10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing)
- **Delta:** Correct tolerance truth from rounding the completed difference to independently normalizing both operands before subtraction: `|R₁₉(a) − R₁₉(b)| > N` for the fixed `N ∈ {1,2,5,10}`, with a closed exact boundary. Correct the former equality-like polarity claim: tolerance reuses directional `!=` polarity, so only movement of the normalized smaller side upward or larger side downward can type a firing OMISSION. Tolerance accepts numeric `BaseYear`, bypasses the ordinary exact-comparison scale-agreement gate, and an implicit computation-validation alternative preserves its declared `toleranceRangeOp` instead of always using strict `!=`.
- **Basis:** kernel `BedingungsOperatorHelper` independently scale-19-normalizes both operands, applies the strict four-band predicate, and routes all four tolerance operators through its directional inequality polarity helper at revision `cb66e51fa7ab90b650698f861bf670754e2e1e66`; the parser's tolerance branch establishes number-like typing and scale-gate bypass, and the computation-alternative generator preserves the optional tolerance operator. a12-dmkits revisions `73f039a9` and `d6a08f5b` completed the formerly missing metadata path: a closed tolerance enum now survives loading, generated-validation synthesis, and consumer read-modify-write. The evaluator still rounds after subtraction in `evalTolerance`, and `PolarityWalk` still uses `Polarity.anyMove`; its current signed-field differentials cannot separate either remaining defect.
- **Requested a12-dmkits reconciliation:** Preserve the completed per-alternative `toleranceRangeOp` path. Fix the shared tolerance evaluator to normalize both operands before subtraction and reuse the existing ordered-inequality fillability mechanism rather than `anyMove`. Add focused existing-harness controls for the independent-rounding separator `ε = 49 / 10²¹`, `a = 1 + ε`, `b = −ε`, range 1; unsigned empty `0` versus `−2` VALUE and versus `+2` OMISSION; the signed and swapped controls; every fixed strict boundary; malformed and empty-row suppression; mixed declared scales and numeric `BaseYear` authoring; and implicit-computation inside/at/outside-band behavior. Cover both kernel strategies and JVM/JS where the existing facilities support them; do not create a new capture framework.
- **Compatibility:** The per-alternative metadata arm is complete and should not change again. The remaining operand-normalization and directional-polarity mechanisms are behavioral corrections to the a12-dmkits interpreter for legal tolerance rules. The four public syntax tokens and kernel behavior version do not change. The local Lean capsule covers the parser-independent checked same-group Number-expression leaf, including authored checks, scale-gate bypass, one-pass lowering, full-row gating, formal/domain projection, directional polarity, and fixed thresholds; concrete syntax, `BaseYear`, implicit computation lowering, and portable tolerance evidence remain explicit later work.
- **Acceptance:** The metadata arm was accepted at `d6a08f5b53022d9caae35e6d842a2b7b22cd5b25`; completion at `7b39728eafdb53b0a69fcafd34817980bb900632` supplies one source of truth for independent operand normalization and directional tolerance polarity, agrees with both kernel strategies on the separating matrix, retains the affected metadata and authoring routes, and supplies the exact reviewed revision.
- **a12-dmkits revision:** `7b39728eafdb53b0a69fcafd34817980bb900632`
- **Disposition:** accepted — the earlier metadata handback at `d6a08f5b53022d9caae35e6d842a2b7b22cd5b25` is preserved; `7b39728eafdb53b0a69fcafd34817980bb900632` completes one shared `ToleranceOps` mechanism for independent scale-19 operand normalization and directional `!=` polarity, retains numeric `BaseYear` and per-alternative metadata, and locks the separating matrix through `ToleranceExactnessDiffTest`, cross-host `ToleranceOpsTest`, and the existing broader tolerance suites.

### SPEC-2026-07-19-14 — numeric authoring regions are structural and function wrappers remain unclosed

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `2ceee778cbcbd16a63e456fb662d3b61a13c99a8`
- **Kernel behavior:** 30.8.1
- **Canonical clause:** [`04-numbers-and-decimals.md` §4 and checklist](../spec/04-numbers-and-decimals.md#4-other-numeric-constraints)
- **Delta:** Replace the vague “one division per calculation subtree” account with the exact plain-arithmetic region rule: multiplication/division combines open division contributions and adds one for `/`; grouping, addition, subtraction, and power validate fresh children and expose zero. The separate power check rejects only a power whose direct left operand is an ungrouped power; left-associative grammar makes this the reachable unbraced chain. Operation-valued function wrappers are not covered by that compositional summary: the legacy walk descends through them, and a nested reset aborts the enclosing scan.
- **Basis:** kernel grammar and `CheckOperationImpl.checkOnlyOneDiv`/`checkOnlyOnePow` at revision `cb66e51fa7ab90b650698f861bf670754e2e1e66` establish the plain recursion, direct-left power rule, brace behavior, and control-flow-exception wrapper caveat. The tracked BA examples separate chained division from brace-isolated division but do not exercise wrappers. a12-dmkits currently delegates `MVK_TOO_MANY_DIV_FOR_CALC` and `MVK_TOO_MANY_POW_FOR_CALC` to the kernel, summarizes division as a calculation subtree, and its typed arithmetic tree does not retain grouping.
- **Requested a12-dmkits reconciliation:** Correct canonical prose and the MVK ledger to state the exact plain structural rule and the parser-shape precondition. Preserve kernel delegation unless a source-maintained clean-room authoring checker has a real consumer. Before admitting function wrappers to such a checker, use the existing adapter facilities to characterize focused ordered `Round`/other operation-valued cases against both kernel strategies; do not invent a new capture framework or assume wrappers are uniformly transparent/reset. If a typed precheck is pursued, retain grouping rather than reconstructing it from rendered precedence.
- **Compatibility:** The kernel and currently delegated authoring path do not change. A future a12-dmkits precheck or grouping-preserving AST may affect typed-source/serialization compatibility and diagnostic timing, so classify those surfaces before implementation. The wrapper caveat is explicitly an open evidence boundary, not a new public legality promise.
- **Acceptance:** a12-dmkits prose distinguishes the exact plain rule, direct-left power rule, parser reachability, and unclosed wrapper surface; focused plain cases agree with both kernel strategies; any wrapper expansion is probe-locked with the existing harness; no current interpreter/runtime claim is broadened; and the handback supplies the exact reviewed revision plus per-surface disposition.
- **a12-dmkits revision:** pending
- **Disposition:** pending

### SPEC-2026-07-19-15 — computed Number storage has distinct fit and warning-suppressed no-fit branches

- **Status:** accepted
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `a00bfc0861396b82409d51ae1c474347f37ca032`
- **Handback revisions:** `77e3220fb07096f8017dfeef8e763b020fd784b4`, `41ecfc511d3828aa841bbbb2c5655ebbbacc10df`, `7dc0a52fba5ffc2d90fdfef76cc8ac94e1d8dc4d`, `d1cab3b35be31a38ba71aed3bffe99d003bf1990`, `7b39728eafdb53b0a69fcafd34817980bb900632`
- **Kernel behavior:** 30.8.1
- **Canonical clauses:** [`09-computations.md` §4 and checklist](../spec/09-computations.md#4-the-stored-form--a-computed-value-lands-as-a-string-in-the-targets-shape) and the [`SEMANTICS-MAP.md` glossary](../spec/SEMANTICS-MAP.md#7-glossary)
- **Delta:** Correct the former single-path summary. Every computed Number is pre-rounded to scale 19 `HALF_UP`. When its stripped natural scale fits the target maximum, rendering pads to `max(naturalScale, minFractionalDigits)` with no length cap, so an over-15-digit result is retained in full and target-rejected. A legal no-fit result requires `MVK_INVALID_COMPARE_DEC_PLACES` suppression, uses the separate 16-significant-digit length-bounded renderer where the integer part permits that bound, and is invalid unconditionally. Both branches always store plain dot-decimal text and never exponent/scientific notation; stored-form equality is decimal-scale-sensitive.
- **Basis:** kernel `CalculationController.handleBerechnetenWert(VkBigDecimal, id)`, `FormatDefinitionZahl`, `BigDecimalUtils.toStringWertLaengenBeschraenkt`, the computation scale-warning gate, and the scale-sensitive change path `DocumentComputationResultImpl` → `FieldInstanceImpl.fieldValuesEqual` at revision `cb66e51fa7ab90b650698f861bf670754e2e1e66`. a12-dmkits records and implements the two store branches in `KERNEL-FINDINGS.md` IF82/IF92, `ComputedNumberStore.kt`, and `ComputationEngine.kt`; IF153 at `41ecfc51` improved ordinary JS plain rendering but the IG89 review retains exponent-boundary and other host-exactness gaps. Focused scale, overflow, target-error, delta-granularity, and exact-application differentials provide clean-room triangulation but remain outside this repository's retained evidence.
- **Requested a12-dmkits reconciliation:** Correct the known stale single-path Number paragraph in `docs/KERNEL-SEMANTICS.md`, then verify that canonical and consumer-facing prose retain the fit/no-fit distinction, warning-suppression precondition, uncapped fit attempt, unconditional no-exponent storage, and scale-sensitive stored equality. Preserve `ComputedNumberStore.kt`, its comments, and IF82/IF92 controls where they already satisfy this account; fix the shared host rendering boundary rather than special-casing magnitudes. Division-domain invalidity and dependent poison remain solely the separate open correction in `SPEC-2026-07-19-12`.
- **Compatibility:** This corrects the language-neutral specification and known stale peer prose without changing the already-correct a12-dmkits fit/no-fit implementation. A consumer that modeled one universal “round to target scale” path or compared only numeric `Rat`/value equality would change behavior. The local Lean fragment implements only the ordinary fit path plus universal digit and signedness checks; it fails closed on the warning-suppressed no-fit surface and leaves other Number constraints outside its current claim.
- **Acceptance:** a12-dmkits has one source of truth for both render branches, the warning-suppression gate, and unconditional plain dot-decimal storage; `docs/KERNEL-SEMANTICS.md` no longer presents one universal target-scale rounding path; no legal magnitude emits exponent notation; existing focused multi-route controls remain green; and the handback supplies the exact reviewed revision plus per-surface disposition.
- **a12-dmkits revision:** `7b39728eafdb53b0a69fcafd34817980bb900632`
- **Disposition:** accepted — the earlier implementation and focused evidence already distinguished the fit and warning-suppressed no-fit branches; `7dc0a52fba5ffc2d90fdfef76cc8ac94e1d8dc4d` removes finite exponent thresholds for unconditional JVM/Node plain rendering, `d1cab3b35be31a38ba71aed3bffe99d003bf1990` replaces the stale universal-path prose, and `7b39728eafdb53b0a69fcafd34817980bb900632` states the two-arm, no-exponent contract canonically. Division-domain invalidity remains separate under `SPEC-2026-07-19-12`.

### SPEC-2026-07-19-16 — `$` correlation captures every named outer repetition level

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `5fd309d36c3bd43811ac9f298fdf88dd85f51706`
- **Kernel behavior:** 30.8.1
- **Canonical clauses:** [`07-repetition-and-iteration.md` §3](../spec/07-repetition-and-iteration.md#3-the-filter-having-the--correlation-and-aggregation) and [`08-paths-and-references.md` §§3–4](../spec/08-paths-and-references.md#3-the-asterisk-and-)
- **Delta:** A `$`-marked reference resolves against the complete captured outer repetition environment, and its resolved group/path chooses the corresponding level's coordinate. Parent and nested-descendant references may therefore observe different indices in one rule instance; one scalar outer-row representation is unsound.
- **Basis:** Kernel 30.8.1 source at `cb66e51fa7ab90b650698f861bf670754e2e1e66`: `IterationState` retains the complete repetition-index vector and outer state, `EbenenIterator` carries that capture into candidate evaluation, and `RtInternalIdentifier` resolves every marked path level from it. At the audited a12-dmkits revision, `Interpreter.havingInterp` passes the complete outer `EvalContext`, and `CurrentRepetition` uses path-specific `repsOf(...).last()`, so its implementation appears structurally aligned; no focused diagonal/off-diagonal differential currently closes the behavior.
- **Requested a12-dmkits reconciliation:** Clarify §9 prose and interpreter-facing documentation, then add one focused existing-harness control over a nested rule context with one ancestor star. The filter requires candidate `CurrentRepetition(Parent)` to equal both `CurrentRepetition($Parent)` and `CurrentRepetition($Parent/Child)`. Hold the captured parent row at `1`; compare a diagonal descendant row `1`, which selects parent candidate `1`, against descendant row `2`, which selects none. Exercise both kernel strategies and the interpreter. Do not add a capture framework.
- **Compatibility:** A scalar captured-row implementation changes valid cross-level filter truth. The current a12-dmkits interpreter is expected to remain behaviorally unchanged if the source reading is correct. The local Lean public one-group protocol is unchanged.
- **Acceptance:** Prose states the full-environment rule; the diagonal/off-diagonal discriminator agrees across both kernel routes and the interpreter; no broader nested/multi-star claim is inferred; and the handback supplies the exact reviewed revision and disposition.
- **a12-dmkits revision:** pending
- **Disposition:** Adjacent evidence only at `c15036b5d4ee7ff76ffaf5cb1f860a86317ae272` and `e3cc376229ced8c2d8c8460562e30b8e3c9b282c`: deep multi-star binding is covered, but the exact parent-versus-descendant captured-coordinate discriminator and canonical prose remain pending.

### SPEC-2026-07-19-17 — bare-group fill quantifiers use an ordered field-major stream

- **Status:** accepted
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `b52de06ead0eba254838f5513235dfded64c9568`
- **Kernel behavior:** 30.8.1
- **Canonical clauses:** [`01-data-model.md` §1](../spec/01-data-model.md#1-model--a-typed-tree), [`02-logic-and-formal-errors.md` §A.4](../spec/02-logic-and-formal-errors.md#a4-fill-quantifiers-group-scopes-and-the-two-iteration-ranges), and [`09-computations.md` §3.2](../spec/09-computations.md#32-an-invalidity-clear-poisons)
- **Delta:** Make the observable scan order explicit: recursively flatten fields in declaration order; complete each field's instantiated repetitions in repetition order; place that field's operator-relevant declared omissions immediately afterward; then advance to the next field. Stop when the result is decided, so an unread malformed tail cannot poison computation. A reached valid non-scalar `DAY_OPTIONAL` value remains FILLED.
- **Basis:** a12-dmkits IF147 and the focused `BareGroupComputeExactnessDiffTest`, `BareGroupComputePoisonDiffTest`, `BareGroupComputeExactnessTest`, and `BareGroupScanLazinessTest` at `b52de06e` separate field order, per-field declared omissions, valid non-scalar values, deciding-cell stops, and reached poison across both kernel strategies and the peer evaluator.
- **Requested a12-dmkits reconciliation:** None. The exact reviewed revision already implements and documents the ordered stream and focused separators; this entry records an inbound semantic handback rather than creating a new upstream request.
- **Compatibility:** A consumer that reorders the flattened cells or appends every declared omission as one group-wide tail can change VALUE/CLEARED into poison. Existing a12-dmkits behavior remains unchanged.
- **Acceptance:** The reviewed revision has one declaration-order expansion mechanism, genuinely stops before unread cells, retains the declared-versus-instantiated operator distinction, and carries focused dual-kernel-route and portable controls for the separating cases.
- **a12-dmkits revision:** `b52de06ead0eba254838f5513235dfded64c9568`
- **Disposition:** accepted — already satisfied by the reviewed implementation, prose, and tests.

### SPEC-2026-07-19-18 — custom field validators produce one project-coded formal observation

- **Status:** accepted
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `955ccdc7251350383a43733621e80b8f7e8629e2`
- **Kernel behavior:** 30.8.1
- **Canonical clauses:** [`06-strings-and-enumerations.md` §A.3](../spec/06-strings-and-enumerations.md#a3-custom-field-type-validation), with cross-cutting summaries in [`01-data-model.md`](../spec/01-data-model.md), [`02-logic-and-formal-errors.md`](../spec/02-logic-and-formal-errors.md), [`11-messages-and-custom.md`](../spec/11-messages-and-custom.md), and [`SEMANTICS-MAP.md`](../spec/SEMANTICS-MAP.md)
- **Delta:** Specify the registered custom-field callback as a formal-observation boundary: preserve raw optional bounds but supply effective `1`/`999`, locale, and stored-value mode; sample one pure result per relevant concrete-valued cell; reuse it for emission, suppression, poison, and RNU filtering; and preserve a rejection's project code plus optional field-placeholder-aware message. The checked Lean world requires complete registration, while the kernel itself fails loudly only when a missing validator is reached.
- **Basis:** a12-dmkits IF150/IF152 and `CustomFieldTypeContextDiffTest`, `CustomFieldTypeRejectionCodeDiffTest`, `CustomFieldTypeMessageDiffTest`, `CustomFieldTypeContextCacheTest`, and `CustomFieldTypeLoadTest` at `955ccdc7` establish the registered callback context, result identity, project code, message substitution, and raw/effective-bound distinction.
- **Requested a12-dmkits reconciliation:** None for the registered path. The reviewed revision already implements and documents it. a12-dmkits' lenient unregistered-validator outcome remains an explicit native-tool divergence rather than a kernel-equivalence claim; the canonical checked Lean account simply excludes an incomplete registry as ill-formed.
- **Compatibility:** Consumers must not generically enforce the declared bounds, replace omitted callback bounds with null, resample a stateful validator per semantic consumer, or collapse a project code to `customFieldTypeInvalid`. Existing registered a12-dmkits behavior remains unchanged.
- **Acceptance:** The reviewed revision forwards the exact registered context, shares one complete result across consumers, preserves code and optional message, excludes nonrelevant cells before sampling, and locks the registered surface against both kernel strategies plus portable JVM/Node controls.
- **a12-dmkits revision:** `955ccdc7251350383a43733621e80b8f7e8629e2`
- **Disposition:** accepted — the registered path is already satisfied; the separately documented lenient missing-registration behavior is outside its exactness claim.

### SPEC-2026-07-19-19 — legal charset definitions are bounded and combined entries match atomically

- **Status:** accepted
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `1903cd8046a81c3689e6b02a4131c3633f095425`
- **Kernel behavior:** 30.8.1
- **Canonical clauses:** [`06-strings-and-enumerations.md` §A.2](../spec/06-strings-and-enumerations.md#a2-legal-charset-definitions-and-atomic-matching), with summaries in [`01-data-model.md`](../spec/01-data-model.md), [`02-logic-and-formal-errors.md`](../spec/02-logic-and-formal-errors.md), and [`SEMANTICS-MAP.md`](../spec/SEMANTICS-MAP.md)
- **Delta:** Distinguish absent/empty-list defaulting from an illegal empty entry; define legal singleton, inclusive range, and bounded surrogate-free combined entries; retain legal shared and terminal prefixes while applying the pinned narrower ambiguity predicate; and match configured combined entries atomically with positive progress and singleton/range fallback. String length remains UTF-16-unit based.
- **Basis:** a12-dmkits IF151, the source-characterized overlap predicate, and `SupportedCharactersDefinitionDiffTest`, `SupportedCharactersGraphemeDiffTest`, `LegalCharsetDefinitionTest`, and `LegalCharsetGraphemeTest` at `1903cd80` separate malformed definitions, legal prefix shapes, atomic full-sequence acceptance, component leakage, and fallback behavior across both kernel strategies and the peer evaluator.
- **Requested a12-dmkits reconciliation:** None. The exact reviewed revision already has one validated definition mechanism, one atomic matcher, and focused differential/portable controls; this entry records the inbound handback.
- **Compatibility:** Flattening a combined entry into independently legal components is observably wrong, while banning all prefix overlap rejects legal models. Definition validation must exclude empty transitions and bound entries, but no implementation layout or performance target is prescribed.
- **Acceptance:** The reviewed revision distinguishes empty list from empty entry, enforces the bounded legal-entry and exact ambiguity rules, matches combined entries atomically with guaranteed progress, and retains focused controls against both kernel strategies and on JVM/Node.
- **a12-dmkits revision:** `1903cd8046a81c3689e6b02a4131c3633f095425`
- **Disposition:** accepted — already satisfied by the reviewed implementation, prose, and tests.

### SPEC-2026-07-19-20 — repetition uniqueness composes ordinarily and projects complete duplicate peers

- **Status:** accepted
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `07fb8c03f36a19e91eb018679e04dacbc95e57e1`
- **Kernel behavior:** 30.8.1
- **Canonical clauses:** [`07-repetition-and-iteration.md` §6](../spec/07-repetition-and-iteration.md#6-repetitionnotunique-precisely), [`10-validation-and-polarity.md` §5](../spec/10-validation-and-polarity.md#5-full-vs-partial-validation), and the message shape in [`01-data-model.md` §3.1](../spec/01-data-model.md#31-rules-validation)
- **Delta:** Complete the RNU account: it is an ordinary per-row 3VL leaf in every model-legal `And`/`Or` tree; partial duplicate construction admits a row only when every composite-key component is relevant; and RNU-owned `referenced`/`fillToFix` sets expand over every key in the complete duplicate cluster while independent branch references stay on the current row.
- **Basis:** a12-dmkits IF149 and `RepetitionNotUniqueCompositionDiffTest`, `RepetitionNotUniqueExactnessDiffTest`, `PartialValidationRepetitionNotUniqueDiffTest`, and `RepetitionNotUniqueExactnessTest` at `07fb8c03` establish ordinary composition, typed keys, all-key relevance, peer-exact pointer sets, branch ownership, and VALUE/OMISSION projection across both kernel strategies and portable JVM/Node evaluation.
- **Requested a12-dmkits reconciliation:** None. The exact reviewed revision replaced the positional recognizer with the ordinary predicate mechanism and already carries the focused handback tests.
- **Compatibility:** Consumers must not recognize only standalone/top-level-conjunct RNU, gate duplicate construction by an enclosing branch, inspect only one composite-key field for relevance, or discard duplicate peers before message projection. No generic negation surface or pointer ordering is introduced.
- **Acceptance:** The reviewed revision evaluates RNU through the ordinary legal Boolean tree, builds duplicate outcomes independently of surrounding branches, requires complete-key relevance, retains typed equality and every peer, and matches both kernel strategies for composition and rich-message separators.
- **a12-dmkits revision:** `07fb8c03f36a19e91eb018679e04dacbc95e57e1`
- **Disposition:** accepted — already satisfied by the reviewed implementation, prose, and tests.

### SPEC-2026-07-20-01 — Groovy-dynamic is the normative observation anchor

- **Status:** accepted
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `978991836ce298c6382b65e0559d3ccf9af24b3c`
- **Kernel behavior:** 30.8.1
- **Canonical clauses:** [`13-lean-encoding-guide.md` §§4–5](../spec/13-lean-encoding-guide.md#4-regression-conformance-and-theorem-guards), [`SEMANTICS-MAP.md` §9](../spec/SEMANTICS-MAP.md#9-drilling-into-the-authoritative-sources), and [`01-data-model.md` §5](../spec/01-data-model.md#5-what-is-not-modelled-here)
- **Delta:** Name the kernel's Groovy-dynamic runtime service as the normative behavioral observation anchor. Generated static-Java remains required co-evidence and a strategy-split detector; a legal split is recorded and does not override Groovy-dynamic. The a12-dmkits interpreter remains a clean-room triangulation peer, never an oracle.
- **Basis:** a12-dmkits IF136 and its conformance divergence enforcement establish the ratified strategy policy; this repository's [`TESTING.md`](TESTING.md) already used the same contract.
- **Requested a12-dmkits reconciliation:** None. This is an inbound policy synchronization from the reviewed peer account.
- **Compatibility:** Evidence classification only. It changes neither an evaluator nor previously retained observations.
- **Acceptance:** a12-dmkits's canonical policy and executable conformance selection enforce the same hierarchy and preserve strategy divergences explicitly.
- **a12-dmkits revision:** `53507298b3ca8dee4a73d851ecc3ca5f5e6b70ba`
- **Disposition:** accepted — the exact policy originated upstream and was already enforced there.

### SPEC-2026-07-20-02 — one `RepetitionNotUnique` leaf is legal per condition

- **Status:** accepted
- **Local revision:** introducing commit
- **a12-dmkits basis revisions:** `ced53da4ab16ab0c34f105fe37598ed034038795`, `07fb8c03f36a19e91eb018679e04dacbc95e57e1`
- **Kernel behavior:** 30.8.1
- **Canonical clause:** [`07-repetition-and-iteration.md` §6 and checklist](../spec/07-repetition-and-iteration.md#6-repetitionnotunique-precisely)
- **Delta:** A model-legal condition contains at most one `RepetitionNotUnique` leaf. A second is rejected after parsing with `MVK_INVALID_COMBINATION_OF_REPETITON_NOT_UNIQUE`; this is separate from the ordinary runtime 3VL semantics accepted under `SPEC-2026-07-19-20`.
- **Basis:** kernel `ParserService` delegates to `AnalyseService.containsMultipleRepetitionNotUnique`; a12-dmkits's MVK ledger preserves the exact diagnostic and its RNU findings preserve the separate runtime mechanism.
- **Requested a12-dmkits reconciliation:** None. a12-dmkits already owns this model-legality knowledge and delegates the gate to the kernel; its broader authoring/public capability work remains in its own existing backlog rather than becoming a duplicate sync request.
- **Compatibility:** A clean-room authoring checker must reject a second leaf before evaluation but must not special-case the legal single leaf's Boolean composition.
- **Acceptance:** the peer knowledge surfaces distinguish the one-leaf legality gate from the runtime predicate semantics and retain the kernel's misspelled diagnostic code exactly.
- **a12-dmkits revision:** `53507298b3ca8dee4a73d851ecc3ca5f5e6b70ba`
- **Disposition:** accepted — inbound semantic knowledge already owned by a12-dmkits; no redundant handoff is required.

### SPEC-2026-07-20-03 — patterns use Java admission and Java runtime semantics

- **Status:** accepted
- **Local revision:** introducing commit
- **a12-dmkits basis revisions:** `517ef65b93ded2775355175dcec18877f8bc8106`, `128f3f99f0e86765f809f6318dcedf88af7c9d02`, `380267fd12625c87146795b2fa63d2ef5e03973c`
- **Kernel behavior:** 30.8.1
- **Canonical clauses:** [`06-strings-and-enumerations.md` Pattern admission and execution](../spec/06-strings-and-enumerations.md#pattern-admission-and-execution) and [`SEMANTICS-MAP.md` §§3 and 9](../spec/SEMANTICS-MAP.md#3-the-taxonomy)
- **Delta:** Replace the false portable-regex-subset account with two-stage model legality—Java `Pattern` compilation plus the finite `PatternUtils` blacklist—and normative whole-value Java-Pattern execution. Ordinary lookahead is not categorically blacklisted; the kernel TypeScript target's raw-RegExp differences are recorded strategy splits.
- **Basis:** a12-dmkits IG90/IF154 source characterization, selected JS translation increment, and follow-up review enumerate the exact blacklist, admitted separators, and remaining peer-runtime gap.
- **Requested a12-dmkits reconciliation:** None. The peer already owns the exact semantic account and explicitly tracks incomplete JS coverage under IG90; this ledger does not duplicate that implementation backlog.
- **Compatibility:** A consumer must not infer JavaScript portability from model legality. A partial implementation must fail closed or declare its narrower capability instead of silently substituting raw host regex behavior.
- **Acceptance:** a12-dmkits's findings and gap surfaces state Java semantics as normative, preserve the limited blacklist exactly, and expose IF154 as partial rather than claiming full parity.
- **a12-dmkits revision:** `53507298b3ca8dee4a73d851ecc3ca5f5e6b70ba`
- **Disposition:** accepted — the semantic correction is inbound and already durable upstream; IG90 remains a separate peer implementation gap.

### SPEC-2026-07-20-04 — time zones use the legacy accepted-id domain and versioned Berlin history

- **Status:** accepted
- **Local revision:** introducing commit
- **a12-dmkits basis revisions:** `ac743157c5ba990183a51bf00950c46703c7a7b5`, `4777b982e7cd79beeebd0f8edcb4298dd22efbec`, `bde3a581cba3c5da51f1095058c71c3ab9cf59ab`, `318d92f74661e4012570b7d868b2e843543f75af`, `82c1d005e863fef11a0012b4b37bc8b8e7edda6d`
- **Kernel behavior:** 30.8.1
- **Canonical clauses:** [`01-data-model.md` §§1.1 and 4](../spec/01-data-model.md#11-the-two-special-model-level-configurations), [`05-dates-and-time.md` §5 and checklist](../spec/05-dates-and-time.md#5-time-zones-and-the-sub-day-difference), and [`SEMANTICS-MAP.md` §9](../spec/SEMANTICS-MAP.md#9-drilling-into-the-authoritative-sources)
- **Delta:** State the legacy `java.util.TimeZone` accepted-id rule and `MVK_INVALID_TIME_ZONE`, make `SimpleDateFormat` parsing and the Groovy-dynamic evidence anchor explicit, and add the versioned 62-transition `Europe/Berlin` profile with flat pre-1916 CET, CEMT periods, gap rejection, smaller/after-offset overlap resolution, and the post-1997 EU recurrence.
- **Basis:** a12-dmkits IG83/IF155 characterization and pinned peer table at JDK 21.0.11/tzdb 2026a, representative Groovy-dynamic historical differentials, limited static-Java tri-checks, and the recorded Route-B review boundary.
- **Requested a12-dmkits reconciliation:** None. The canonical kernel-wide domain and the peer's narrower `{UTC, GMT, Europe/Berlin}` fail-closed product scope are already distinguished upstream; the deferred general-zone Route A and review residuals remain its own explicit backlog.
- **Compatibility:** Products may support a strict subset of kernel-legal ids only by refusing unsupported ids before evaluation. They must not substitute `java.time` history, collapse typos to GMT, or claim TypeScript/static-Java coverage beyond exercised evidence.
- **Acceptance:** a12-dmkits preserves the complete Berlin profile, exact accepted-id knowledge, and narrower fail-closed consumer capability; the exact reviewed revision records the remaining peer evidence-wording overclaim rather than being treated as proof that every documentation surface already states the representative evidence boundary exactly.
- **a12-dmkits revision:** `53507298b3ca8dee4a73d851ecc3ca5f5e6b70ba`
- **Disposition:** accepted as an inbound semantic receipt — the canonical knowledge and pinned table originated upstream, while the review-caught IF155/KERNEL-FINDINGS evidence-wording residual remains explicitly peer-owned and is not duplicated as a new outbound request here.

### SPEC-2026-07-20-05 — uppercase `\P` is excluded by kernel pattern admission

- **Status:** accepted
- **Local revision:** introducing commit
- **Supersedes:** [`SPEC-2026-07-20-03`](#spec-2026-07-20-03--patterns-use-java-admission-and-java-runtime-semantics)
- **a12-dmkits basis revision:** `7dc0a52fba5ffc2d90fdfef76cc8ac94e1d8dc4d`
- **Kernel behavior:** 30.8.1
- **Canonical clauses:** [`06-strings-and-enumerations.md` Pattern admission and execution](../spec/06-strings-and-enumerations.md#pattern-admission-and-execution) and [`SEMANTICS-MAP.md` §9](../spec/SEMANTICS-MAP.md#9-drilling-into-the-authoritative-sources)
- **Delta:** Narrow only the admitted pattern set recorded by the predecessor: a direct typed/full-kernel model rejects uppercase `\P{L}` with `MVK_INVALID_PATTERN` even though uppercase `P` is absent from the source-visible `PatternUtils` blacklist. The blacklist remains exact source evidence but is not an exhaustive total-admission grammar. Java whole-value runtime semantics and the explicit TypeScript strategy split are unchanged.
- **Basis:** a12-dmkits IF164 records both the literal source blacklist and the direct real-kernel rejection, and explicitly classifies the interpreter's JVM/Node uppercase-`\P` primitive support as defensive rather than admission evidence.
- **Requested a12-dmkits reconciliation:** None. The peer already owns the correction and its defensive runtime support; no new hidden grammar or broader exclusion is inferred.
- **Compatibility:** Consumers must remove uppercase `\P` from any advertised kernel-admitted set while preserving the predecessor's Java-runtime and target-split account. A narrower implementation may continue to fail closed outside its declared pattern fragment.
- **Acceptance:** The exact basis revision was reviewed; its durable findings distinguish source-visible blacklist evidence, direct full-kernel admission evidence, and defensive peer support without treating one as another.
- **a12-dmkits revision:** `7dc0a52fba5ffc2d90fdfef76cc8ac94e1d8dc4d`
- **Disposition:** accepted — this successor corrects only the predecessor's uppercase-`\P` admission overclaim; the remainder of `SPEC-2026-07-20-03` stays valid.

### SPEC-2026-07-20-06 — constructed-Date validity complements only at truth projection

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `883e0e22f87e22e3a7ff4529fd41ab87f331de8f`
- **Kernel behavior:** 30.8.1
- **Canonical clause:** [`05-dates-and-time.md` §3 and checklist](../spec/05-dates-and-time.md#3-constructing-dates-and-checking-validity)
- **Delta:** Replace the mathematically imprecise claim that `Valid(Date(...))` and `Invalid(Date(...))` are not complements. Their truth projections are exact strong-Kleene complements across real, unreal, incomplete, and formally unavailable constructions. The non-derivability is at the full verdict level: incomplete and unreal both make `Valid` not fire, while `Invalid` must recover OMISSION for incomplete and VALUE for unreal; malformed makes both UNKNOWN. A reason-bearing construction result is therefore required even though the truth table complements.
- **Basis:** kernel `RuntimeController.constructDatumHelper`, `dateGueltig`, and `dateUngueltig` at revision `cb66e51fa7ab90b650698f861bf670754e2e1e66` establish the four classifications and directional verdicts; a12-dmkits `DateConstructionDiffTest`, `DateValidityLawsTest`, and its `DateStatus` evaluator at the basis revision already implement the same classification-to-verdict table. The local Lean capsule takes concrete calendar reality as a separate input and proves truth complementation, both fired-polarity characterizations, and the nearest non-law: `Valid(incomplete) = Valid(unreal)` while `Invalid(incomplete) ≠ Invalid(unreal)`. Exact model-zone/cutover calendar resolution is a separate semantic issue and is not folded into this entry.
- **Requested a12-dmkits reconciliation:** Correct only prose and comments that call the predicates non-complements because an unspecified component fires `Invalid` but not `Valid`. State strong-Kleene truth complementation separately from full-verdict/polarity recovery and preserve the already-correct four-way evaluator and focused kernel differentials. Do not add a general negation operator or change runtime behavior merely to produce a source diff.
- **Compatibility:** Formal precision for existing 30.8.1 behavior. Evaluators and public condition syntax remain unchanged; a proof, refactoring, or implementer guide that derives the full `Invalid` verdict from the `Valid` verdict must change.
- **Acceptance:** a12-dmkits canonical prose distinguishes truth projection from full verdict, retains malformed UNKNOWN/UNKNOWN and incomplete-versus-unreal polarity, existing Date-construction controls remain green, and the handback supplies the exact reviewed revision plus per-surface disposition.
- **a12-dmkits revision:** pending
- **Disposition:** pending

### SPEC-2026-07-20-07 — constructed-Date reality uses the model-zone legacy hybrid calendar

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `883e0e22f87e22e3a7ff4529fd41ab87f331de8f`
- **Kernel behavior:** 30.8.1
- **Canonical clause:** [`05-dates-and-time.md` §3 and checklist](../spec/05-dates-and-time.md#3-constructing-dates-and-checking-validity)
- **Delta:** Specify that `Date(...)` calendar reality is decided by a non-lenient legacy `GregorianCalendar` in `modelConfig.timeZone`, not by a zone-free proleptic-Gregorian predicate. The default hybrid cutover admits UTC 1500-02-29 on its Julian side, while the `Pacific/Apia` discontinuity rejects the skipped local date 2011-12-30. This constructor rule remains separate from the later 1583-10-16 stored/computed-value floor.
- **Basis:** kernel `RuntimeController.constructDatum` delegates to `DateUtil.createDate(..., timeZone)` at revision `cb66e51fa7ab90b650698f861bf670754e2e1e66`; `constructDatumHelper` then accumulates not-given/nonrelevant provenance. `createDate` uses a cleared, non-lenient `GregorianCalendar` with the supplied zone. The two separators were independently reproduced through that JDK mechanism during Lean review, but not yet through a retained full-kernel differential; the zone database is a runtime input not identified by kernel 30.8.1 alone. At the basis revision, a12-dmkits `ExprEval.analyzeDate` delegates to the zone-free proleptic `DateMath.isRealDate`, so its current agreement on ordinary modern dates does not close this domain.
- **Requested a12-dmkits reconciliation:** Confirm both separators against the real kernel's normative Groovy-dynamic route, retain generated-static-Java co-evidence where supported, and correct the clean-room interpreter at the construction-reality locus. First audit every other consumer of the shared proleptic date helper: do not globally replace stored-date, arithmetic, range, or timezone semantics merely to fix `Date(...)`. Record the exact supported calendar/zone domain and fail closed for any deliberately unsupported zone rather than silently using the proleptic predicate.
- **Compatibility:** This can change `Valid`/`Invalid`, extractors, and any operation consuming a constructed Date for historical or zone-skipped triples. Ordinary modern UTC/GMT dates are expected to remain unchanged. A runtime without the configured model zone cannot claim general `Date(...)` parity.
- **Acceptance:** Focused kernel differentials lock both named separators and neighboring controls; the interpreter construction path uses the model zone and pinned hybrid-cutover behavior or explicitly rejects an accurately declared narrower domain; unrelated date consumers retain their separately justified semantics; and the handback supplies the exact reviewed revision plus per-surface disposition.
- **a12-dmkits revision:** pending
- **Disposition:** pending

### SPEC-2026-07-20-08 — DifferenceInDays counts model-zone calendar steps

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `0f797f17826380ce84b4279cc63a882f9d770717`
- **Kernel behavior:** 30.8.1
- **Canonical clause:** [`05-dates-and-time.md` §9 and checklist](../spec/05-dates-and-time.md#9-datetime-rides-the-date-format-definition--but-the-operand-gates-are-per-operator-)
- **Delta:** Replace the “Δ wall-seconds / 86 400, truncated toward zero” formula with the actual general rule. The kernel orders the model-zone legacy `Calendar` operands, makes a `yearDifference × 365` lower-bound `Calendar.DAY_OF_MONTH` jump, advances by single days until the next landing passes the later operand, and restores authored sign. Existing time-of-day, mixed Date/DateTime, reverse-sign, and named Berlin controls remain valid, but the formula also diverges inside Berlin around a special-hour landing: 2024-03-30T02:30 to 2024-03-31T01:45 counts one calendar step although the wall-label difference is only 23 h 15 m. Across a whole-date discontinuity, `Pacific/Apia` 2011-12-29T12:00 to 2011-12-31T12:00 is likewise one calendar step, not two.
- **Basis:** kernel `BedingungsOperatorHelper.getDatumsDiff` and `getDifferenzInTagen` at revision `cb66e51fa7ab90b650698f861bf670754e2e1e66` own the model-zone `GregorianCalendar` conversion, signed operand ordering, the whole-year lower-bound jump, and subsequent single-day additions. Independent review reproduced both separating legacy-calendar mechanisms: the Berlin day addition lands at 01:30 before the 01:45 endpoint, and one `Pacific/Apia` `Calendar.DAY_OF_MONTH` addition from non-leniently parsed 2011-12-29T12:00 lands on 2011-12-31T12:00. Retained full-kernel differentials for those separators are still required. At the basis revision, a12-dmkits prose, `WallDayArithmeticDiffTest`, and `ExprEval` call this behavior zone-independent and compute a proleptic wall-second quotient. Its deliberate zone domain rejects Apia but includes Berlin, so the partial-gap separator is a reachable interpreter divergence.
- **Requested a12-dmkits reconciliation:** Confirm both the Berlin partial-gap separator and the Apia skipped-date separator, with neighboring controls, through the real kernel's Groovy-dynamic route and generated-static-Java co-evidence. Correct canonical prose and interpreter comments to describe calendar-step semantics, then correct `DifferenceInDays` at its own operation locus for the supported Berlin domain. Keep the existing fail-closed gate for other unsupported zones unless a deliberately broader implementation is justified; if broader support is claimed, implement or supply the legacy calendar-step rule rather than the wall-coordinate shortcut. Do not globally rewrite sub-day differences, Date construction, `AddDays`, or unrelated date consumers.
- **Compatibility:** UTC and the currently maintained Berlin controls remain unchanged, but additional Berlin gap-adjacent inputs can change `DifferenceInDays` values and consuming verdicts. A general interpreter or analyzer that accepts a legal model zone with a whole-date discontinuity has the same risk. A profile-restricted implementation must reject unsupported zones before evaluation.
- **Acceptance:** Both kernel routes lock the Berlin partial-gap and Apia skipped-date separators plus neighboring controls; canonical a12-dmkits prose no longer calls the general rule zone-independent wall-second division; the interpreter implements calendar-step semantics for its supported Berlin domain and continues to reject unsupported zones; unrelated temporal operations remain separately justified; and the handback supplies the exact reviewed revision plus per-surface disposition.
- **a12-dmkits revision:** pending
- **Disposition:** pending

### SPEC-2026-07-20-09 — `FirstFilledValue` observes only filters before termination

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `3696df4e38ae6f13fb97c2bddfcdf2cc730c4869`
- **Kernel behavior:** 30.8.1
- **Canonical clause:** [`10-validation-and-polarity.md` §§4 and 4.1](../spec/10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing)
- **Delta:** Qualify the broad statement that `Having` escalates a consumed aggregate. Multi-operand `FirstFilledValue` encounters each slot's filter immediately before scanning that slot and terminates at the first present or formally unavailable value; a filter on any later, unvisited slot therefore cannot affect the result or its polarity.
- **Basis:** kernel `RuntimeController.combineFeldListe` invokes the filter marker for the current operand before adding its values and returns as soon as `FirstValueCombiner` is no longer changeable; `FirstValueCombiner` makes present and formally unavailable prefixes terminal. Maintained a12-dmkits `FirstFilledValueLawsTest`, `FirstFilledValueInvalidTailDiffTest`, `FirstFilledValueDiffTest`, `FirstFilledValueKindDiffTest`, and `HavingStarComparisonPolarityDiffTest` establish prefix termination, suffix invisibility, and encountered-filter escalation, while the source order closes their composition.
- **Requested a12-dmkits reconciliation:** Make the filter-position qualification durable in the owning `FirstFilledValue` prose and add one focused control only if no existing test directly distinguishes an unvisited later filtered slot from an encountered filtered slot. Preserve the current implementation if it already follows the ordered source mechanism; do not introduce a global aggregate-level filter flag.
- **Compatibility:** A flat implementation that ORs filter presence across every authored operand can misclassify a firing as OMISSION even though an earlier terminal operand makes the later filtered slot unreachable. The one-operand Lean capsule is unaffected because its sole filter is necessarily encountered.
- **Acceptance:** a12-dmkits documentation states the positional encounter rule; a focused source or differential control distinguishes an encountered filter from an unreachable later filter; the clean-room interpreter retains per-slot order or otherwise proves equivalent behavior; and the handback supplies the exact reviewed revision plus per-surface disposition.
- **a12-dmkits revision:** pending
- **Disposition:** pending
