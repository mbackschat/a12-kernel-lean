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

### SPEC-2026-07-19-08 — every arithmetic node uses precision-50 `HALF_UP`

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `2ceee778cbcbd16a63e456fb662d3b61a13c99a8`
- **Kernel behavior:** 30.8.1
- **Canonical clause:** [`04-numbers-and-decimals.md` §5](../spec/04-numbers-and-decimals.md#5-internal-precision--the-constants-that-must-match-exactly)
- **Delta:** Correct the former claim that `+` and `−` stay exact. The kernel applies one precision-50 decimal `MathContext`, default `HALF_UP`, independently to every `+`, `−`, `×`, `÷`, and `^` node. Before evaluation/code generation, it performs one order-sensitive post-order pass: each original multiplication pulls only immediate root-division operands, keeps ordinary factors first in their existing order, appends extracted numerators and denominators in division encounter order, left-folds multi-factor products, and never revisits newly created products. Authored fold order is therefore not always evaluated fold order, but the mechanism is not global or fixed-point normalization.
- **Basis:** kernel `VkBigDecimal` constructs one `MathContext(50)` and passes it to `add`, `subtract`, `multiply`, `divide`, and `pow`; `DivisionTransformer`, parse-tree traversal, and composite code generation establish the exact one-pass/order/left-fold mechanism at kernel revision `cb66e51fa7ab90b650698f861bf670754e2e1e66`. In particular, `a * {b / c}` and `{b / c} * a` both become `{a * b} / c`, while a newly created product containing a nested extracted division is not revisited. The formerly cited `[q] / 3 * 3` rounding example is not a scale-19 pre-round discriminator because this rewrite makes it exact; three separately braced thirds joined by addition are the corrected discriminator. a12-dmkits' JVM `Dec` and `KERNEL-FINDINGS.md` currently cap only multiplication/division/power, while `ArithmeticDiffTest` has a genuine 52-to-50-digit multiplication separator but no above-50 addition/subtraction or division-rewrite separator.
- **Requested a12-dmkits reconciliation:** Apply the precision boundary to JVM addition and subtraction as well as the existing operations; reconcile the common contract, JS gap/account, interpreter findings, kernel semantics, catalog/operator guidance, staged implementation guidance, and any evaluator optimization that assumes exact `+`/`−`. Determine one clean-room ordered single-pass lowering mechanism for division-bearing multiplication rather than accumulating expression-shape patches or flattening factors into an unordered/global fraction. Preserve braces through the authoring checks even though they do not block the later rewrite. Replace the superseded `[q] / 3 * 3` staging example wherever it appears. Add focused kernel differentials that separate rounded `+` and `−` from exact arithmetic, direct authored-tree evaluation from the one-pass lowered tree, one pass from a fixed point, and the real three-thirds scale-19 pre-round from direct flooring.
- **Compatibility:** This changes a12-dmkits results for legal expressions whose addition or subtraction produces more than 50 significant digits and may change division-bearing products whose authored and one-pass rewritten trees round differently. Classify JVM, JS, public interpreter, serialization, and dmtool-release consequences explicitly; do not describe the correction as documentation-only.
- **Acceptance:** Both kernel strategies and the JVM interpreter agree on focused above-50 `+`/`−` witnesses, order-sensitive one-pass division-rewrite witnesses, a nested no-second-pass witness, and the corrected three-thirds pre-round witness; all five operations use the same precision/rounding contract at each evaluated node; JS either conforms or remains an explicit fail-closed/nonconforming capability; prose and operator metadata contain neither “`+`/`−` stay exact” nor global/fixed-point normalization claims. The handback supplies the exact reviewed revision and per-surface disposition.
- **a12-dmkits revision:** pending
- **Disposition:** pending

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
- **Kernel behavior:** 30.8.1
- **Canonical clauses:** [`04-numbers-and-decimals.md` §3](../spec/04-numbers-and-decimals.md#3-arithmetic-domain-failures-are-consumer-sensitive) and [`§5`](../spec/04-numbers-and-decimals.md#5-internal-precision--the-constants-that-must-match-exactly)
- **Delta:** Specify the numeric mechanism behind admitted powers. Positive power follows the OpenJDK 21 X3.274 numeric-value algorithm, rounding binary-exponentiation intermediates at precision `50 + decimalDigits(exponent) + 1` before the final precision-50 round. Negative power is kernel-specific: it first rounds `1 / base` at precision 50, then applies the positive algorithm. Exact rational power plus one final round and reciprocal-after-positive-power are both observably different.
- **Basis:** kernel `VkBigDecimal.power` and `getKehrwert` at revision `cb66e51fa7ab90b650698f861bf670754e2e1e66`, together with the OpenJDK 21 `BigDecimal.pow(int, MathContext)` X3.274 contract. The positive separator `0.473471768303411 ^ 7` ends in `…3319` under staged power but `…3318` under exact-power/final-round. The negative separator `3 ^ -3` ends in `…7036` under the kernel's reciprocal-first order but `…7037` under a final reciprocal. a12-dmkits calls Java's positive primitive correctly, but its JVM negative path currently takes the reciprocal after positive power; existing `4 ^ -1` coverage cannot distinguish the orders, and no committed power test crosses the 50-significant-digit boundary.
- **Requested a12-dmkits reconciliation:** Fix the JVM numeric mechanism at its shared power locus so negative exponents use the kernel's reciprocal-first order; correct any exact/bit-for-bit correspondence claim; add positive staged-precision and negative reciprocal-order differentials against both kernel strategies plus `±1000`, `±1001`, `0^0`, `0^-1`, and fractional-exponent controls. Keep the JS limitation explicit until that implementation matches the same mechanism. Do not use the peer interpreter as the oracle.
- **Compatibility:** Legal negative powers can change in the last retained digit; nested arithmetic and scale-19 comparisons can amplify the difference into a visible verdict. Classify JVM, JS, public interpreter, serialization, and dmtool-release consequences. Positive behavior should remain unchanged if it already delegates to Java `BigDecimal.pow(MathContext)`.
- **Acceptance:** Both kernel strategies and the JVM interpreter agree on discriminating positive and negative precision cases and the named known-value domain-edge matrix; the implementation performs reciprocal-first staging structurally rather than special-casing examples; prose makes the OpenJDK 21 algorithm and external-evidence boundary explicit; the handback supplies the exact reviewed revision and per-surface disposition.
- **a12-dmkits revision:** pending
- **Disposition:** pending

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

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `2ceee778cbcbd16a63e456fb662d3b61a13c99a8`
- **Kernel behavior:** 30.8.1
- **Canonical clauses:** [`04-numbers-and-decimals.md` §§4–5 and checklist](../spec/04-numbers-and-decimals.md#4-other-numeric-constraints), [`09-computations.md` §6 and checklist](../spec/09-computations.md#6-the-implicit-validation-rule-precisely), and [`10-validation-and-polarity.md` §4 and checklist](../spec/10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing)
- **Delta:** Correct tolerance truth from rounding the completed difference to independently normalizing both operands before subtraction: `|R₁₉(a) − R₁₉(b)| > N` for the fixed `N ∈ {1,2,5,10}`, with a closed exact boundary. Correct the former equality-like polarity claim: tolerance reuses directional `!=` polarity, so only movement of the normalized smaller side upward or larger side downward can type a firing OMISSION. Tolerance accepts numeric `BaseYear`, bypasses the ordinary exact-comparison scale-agreement gate, and an implicit computation-validation alternative preserves its declared `toleranceRangeOp` instead of always using strict `!=`.
- **Basis:** kernel `BedingungsOperatorHelper` independently scale-19-normalizes both operands, applies the strict four-band predicate, and routes all four tolerance operators through its directional inequality polarity helper at revision `cb66e51fa7ab90b650698f861bf670754e2e1e66`; the parser's tolerance branch establishes number-like typing and scale-gate bypass, and the computation-alternative generator preserves the optional tolerance operator. The audited a12-dmkits implementation instead rounds after subtraction in `evalTolerance`, uses `Polarity.anyMove`, and drops `toleranceRangeOp` under recorded gap IG96. Its current signed-field tolerance differentials cannot separate either the normalization-order defect or the directional-polarity defect.
- **Requested a12-dmkits reconciliation:** Fix the shared tolerance evaluator to normalize both operands before subtraction and reuse the existing ordered-inequality fillability mechanism rather than `anyMove`. Complete IG96 by carrying a closed tolerance enum through loading and implicit-rule synthesis. Add focused existing-harness controls for the independent-rounding separator `ε = 49 / 10²¹`, `a = 1 + ε`, `b = −ε`, range 1; unsigned empty `0` versus `−2` VALUE and versus `+2` OMISSION; the signed and swapped controls; every fixed strict boundary; malformed and empty-row suppression; mixed declared scales and numeric `BaseYear` authoring; and implicit-computation inside/at/outside-band behavior. Cover both kernel strategies and JVM/JS where the existing facilities support them; do not create a new capture framework.
- **Compatibility:** This is a behavioral correction to the a12-dmkits interpreter for legal tolerance rules and implicit computation validation. The four public syntax tokens and kernel behavior version do not change. The local Lean capsule now covers the parser-independent checked same-group Number-expression leaf, including authored checks, scale-gate bypass, one-pass lowering, full-row gating, formal/domain projection, directional polarity, and fixed thresholds; concrete syntax, `BaseYear`, implicit computation lowering, and portable tolerance evidence remain explicit later work.
- **Acceptance:** a12-dmkits has one source of truth for operand normalization and directional tolerance polarity; the separating matrix agrees with both kernel strategies; `toleranceRangeOp` survives the implicit-validation path; affected docs and capability claims are corrected; and the handback supplies the exact reviewed revision plus per-surface disposition.
- **a12-dmkits revision:** pending
- **Disposition:** pending

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

- **Status:** pending
- **Local revision:** introducing commit
- **a12-dmkits basis revision:** `a00bfc0861396b82409d51ae1c474347f37ca032`
- **Kernel behavior:** 30.8.1
- **Canonical clauses:** [`09-computations.md` §4 and checklist](../spec/09-computations.md#4-the-stored-form--a-computed-value-lands-as-a-string-in-the-targets-shape) and the [`SEMANTICS-MAP.md` glossary](../spec/SEMANTICS-MAP.md#7-glossary)
- **Delta:** Correct the former single-path summary. Every computed Number is pre-rounded to scale 19 `HALF_UP`. When its stripped natural scale fits the target maximum, rendering pads to `max(naturalScale, minFractionalDigits)` with no length cap, so an over-15-digit result is retained in full and target-rejected. A legal no-fit result requires `MVK_INVALID_COMPARE_DEC_PLACES` suppression, uses the separate 16-significant-digit length-bounded renderer where the integer part permits that bound, and is invalid unconditionally. Stored-form equality is decimal-scale-sensitive.
- **Basis:** kernel `CalculationController.handleBerechnetenWert(VkBigDecimal, id)`, `FormatDefinitionZahl`, `BigDecimalUtils.toStringWertLaengenBeschraenkt`, the computation scale-warning gate, and the scale-sensitive change path `DocumentComputationResultImpl` → `FieldInstanceImpl.fieldValuesEqual` at revision `cb66e51fa7ab90b650698f861bf670754e2e1e66`. a12-dmkits already records and implements the two store branches in `KERNEL-FINDINGS.md` IF82/IF92, `ComputedNumberStore.kt`, and `ComputationEngine.kt`; its focused scale, overflow, target-error, delta-granularity, and exact-application differentials provide clean-room triangulation but remain outside this repository's retained evidence.
- **Requested a12-dmkits reconciliation:** Correct the known stale single-path Number paragraph in `docs/KERNEL-SEMANTICS.md`, then verify that canonical and consumer-facing prose retain the fit/no-fit distinction, warning-suppression precondition, uncapped fit attempt, and scale-sensitive stored equality. Preserve `ComputedNumberStore.kt`, its comments, and IF82/IF92 controls where they already satisfy this account; return an already-satisfied disposition rather than creating churn. Division-domain invalidity and dependent poison remain solely the separate open correction in `SPEC-2026-07-19-12`.
- **Compatibility:** This corrects the language-neutral specification and known stale peer prose without changing the already-correct a12-dmkits fit/no-fit implementation. A consumer that modeled one universal “round to target scale” path or compared only numeric `Rat`/value equality would change behavior. The local Lean fragment implements only the ordinary fit path plus universal digit and signedness checks; it fails closed on the warning-suppressed no-fit surface and leaves other Number constraints outside its current claim.
- **Acceptance:** a12-dmkits has one source of truth for both render branches and the warning-suppression gate; `docs/KERNEL-SEMANTICS.md` no longer presents one universal target-scale rounding path; existing focused multi-route controls remain green; and the handback supplies the exact reviewed revision plus per-surface disposition.
- **a12-dmkits revision:** pending
- **Disposition:** pending
