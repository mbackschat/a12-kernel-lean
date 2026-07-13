# Authoritative sources & how to drill

The working map from `spec/` prose down to ground truth. [`../spec/`](../spec/) is the *self-contained prose helper* (its intro deliberately promises you need no other repo to *understand* the semantics); **this doc is the drill hub** that connects each `spec/` area to the authoritative sources when you need to *verify* or go deeper. Authority order: **[`../../a12-kernel`](../../a12-kernel) (the engine — ground truth) → [`../spec/`](../spec/) → [a12-dmkits (local `a12-rulekit/` checkout)](../../a12-rulekit) (peer clean-room + verified knowledge)**. Everything here is pinned to kernel **30.8.1**. Read to learn behaviour; never link, call, or transcribe the engine (see [`../CLAUDE.md`](../CLAUDE.md)).

**The drill chain**, per semantic area (`§n` = the shared 14-section taxonomy): our `spec/NN-*.md` (understand) → a12-dmkits `KERNEL-SEMANTICS.md §n` (the canonical rule) → `KERNEL-FINDINGS.md §n` (edge cases + the oracle that established each) → the catalog `semantics` facet if one exists (machine-readable + runnable probes) → the `corpus/` family if one exists (replayable `expected` signatures) → the `interpreter` `commonTest` classes (portable property/unit tests to mirror as Lean theorems) → if you need the mechanism, the kernel runtime class. a12-dmkits' own [`docs/SEMANTICS-MAP.md`](../../a12-rulekit/docs/SEMANTICS-MAP.md) is the **guard-checked hub** for the middle of that chain — follow it for the exhaustive per-`§n` test list rather than duplicating it here.

---

## `../../a12-kernel` — the engine (ground truth)

A codegen + runtime: the DSL compiles to Java/TS/Groovy that **calls runtime helper classes**, so the evaluation semantics live in the helpers, not the generated code.

**Where the semantics are** — `kernel-rt/kernel-core-runtime/src/main/java/com/mgmtp/a12/kernel/core/rt/_30_8/internal/`:

- `core/BedingungsOperatorHelper.java` — operator evaluation: numeric/date/string comparison, date arithmetic (`addiereJahre`/`addiereMonate` with Feb-28 / leap corrections), date difference, date-part extraction.
- `core/ValidierungsErgebnis.java` — the **3-valued truth model**: `TRUE_WF` (value error), `TRUE_AF` (omission error), `FALSE_OR_UNKNOWN`, with `combineUND`/`combineODER` (the Kleene AND/OR tables).
- `core/{Number,Date,FirstValue}Combiner.java` — aggregation over iteration + the empty→0 machinery.
- `util/VkBigDecimal.java` — decimals: `DEFAULT_SCALE=19`, `MathContext(50)`, div-by-zero→`INVALID_NUMBER`, `kannGroesser/KleinerWerden` (fillability seeds), empty sentinels.
- `util/DreiWertBool.java` (three-valued boolean), `util/DateUtil.java` (`clearTime` = Now/Today truncation).
- `core/{MainValidatorController,CalculationController,CalculationCommand}.java` — validation + computation orchestration; caches under `core/`.
- Iteration and correlated `Having`: [`IterationState.java`](../../a12-kernel/kernel-rt/kernel-core-runtime/src/main/java/com/mgmtp/a12/kernel/core/rt/_30_8/internal/util/IterationState.java) carries the captured outer rule state, [`EbenenIterator.java`](../../a12-kernel/kernel-rt/kernel-core-runtime/src/main/java/com/mgmtp/a12/kernel/core/rt/_30_8/internal/util/EbenenIterator.java) evaluates the filter for each candidate with that capture attached, and [`RtInternalIdentifier.java`](../../a12-kernel/kernel-rt/kernel-core-runtime/src/main/java/com/mgmtp/a12/kernel/core/rt/_30_8/internal/util/RtInternalIdentifier.java) resolves an outer-marked reference against the capture rather than the candidate. The surrounding iteration machinery is `util/{EntityIterator,KontextIterator,EbenenIterator}.java`; [`RuntimeController.java`](../../a12-kernel/kernel-rt/kernel-core-runtime/src/main/java/com/mgmtp/a12/kernel/core/rt/_30_8/internal/core/RuntimeController.java) owns Number reads and `CurrentRepetition`.

TS mirror (identical, German-named files): `kernel-rt/kernel-core-runtime-ts/src/main/js/internal/`. String↔typed conversion (date formats, decimal parsing, partially-known dates): `kernel-conversion-java/.../a12internal/util/`.

**Codegen (names every operator, emits calls — not semantics):** `kernel-tool/kernel-core-codegen-condition/.../generator/backingbeans/{conditions,fieldoperations}/` + `internal/utils/RuntimeMethodNameFactory.java`. For the narrow filter boundary, [`CodeGenFilterCondition.st`](../../a12-kernel/kernel-tool/kernel-core-codegen-condition/src/main/resources/internal/templates/validation/java/conditionsDir/CodeGenFilterCondition.st), [`CodeGenCondition.java`](../../a12-kernel/kernel-tool/kernel-core-codegen-condition/src/main/java/com/mgmtp/a12/kernel/core/codegen/internal/generator/backingbeans/conditions/CodeGenCondition.java), and [`ConditionSuffix.st`](../../a12-kernel/kernel-tool/kernel-core-codegen-condition/src/main/resources/internal/templates/validation/java/conditionsDir/ConditionSuffix.st) show that a generated `Having` predicate keeps only a known true condition result. **Parser/grammar:** `kernel-tool/kernel-core-parser` (ANTLR `.g4` + bilingual `LexerTerminals_{en,de}.java`). **Model/document API:** `kernel-md/*`.

**Docs:** [`documentation/_merged/kernel-ba.md`](../../a12-kernel/documentation/_merged/kernel-ba.md) — the definitive evaluation-behaviour spec (**read first**); [`documentation/_merged/kernel-dev.md`](../../a12-kernel/documentation/_merged/kernel-dev.md) — custom conditions/types, Document API; [`ANALYSIS.md`](../../a12-kernel/ANALYSIS.md) — architecture; [`KERNEL-GRAMMAR.md`](../../a12-kernel/KERNEL-GRAMMAR.md), [`KERNEL-USE.md`](../../a12-kernel/KERNEL-USE.md).

**Drill path for one operator:** kernel-ba.md section → keyword table (`LexerTerminals_*`) → backing-bean `getRuntimeName()` → the runtime helper method above.

---

## a12-dmkits — peer clean-room engine + verified knowledge (`../../a12-rulekit/` checkout)

### `interpreter/` — a peer clean-room KMP evaluator (the closest reference)

Pure `interpreter/src/commonMain/kotlin/…/dm/interpreter/`; only the `Dec` decimal is platform-specific. The `eval/` package is what maps most directly to Lean:

- `eval/ThreeValued.kt` — `Kleene` and/or/not tables. `eval/Operators.kt` — enum-keyed operator registry (`PredicateOp`/`ConstantOp`/`FunctionOp`) + `quantifierFires`.
- `eval/Polarity.kt` + `eval/PolarityWalk.kt` — VALUE/OMISSION fillability (`Fill(canGrow,canShrink)`) and the typed truth+polarity walk.
- `eval/ValCompare.kt` (scale-19 vs full-precision compare), `eval/ArithFill.kt`, `eval/Aggregates.kt`, `eval/DateMath.kt`.
- `eval/Poison.kt` + `eval/OverlayContext.kt` + `ComputationEngine.kt` — compute cascade + poison-on-read. `eval/FormalError.kt` — the invalidity sources.
- `ast/Ast.kt` — `Cond`/`Expr`/`Tri`/`Val` + `emptyValue(kind)`. `model/` — `EvalClock`, `CustomCondition`, `LegalCharset`. `Document.kt`/`EvalContext.kt` — the data-access seam. Entry point: `DmInterpreter.kt`.

The module's layering — (1) data-access → (2) **pure operator semantics** (`Kleene`, `Polarity`, `ArithFill`, `Aggregates`, `ValCompare`, `DateMath`, `quantifierFires`) → (3) tree-walk strategy — means **layer (2) is the direct analogue of our Lean core**. Its rules: [`interpreter/CLAUDE.md`](../../a12-rulekit/interpreter/CLAUDE.md) (exact-match both kernel strategies; clean-room/EUPL).

### `adapter/` — the kernel-as-oracle differential (JVM, kernel-linked)

- `adapter/src/test/java/…/laws/RuntimeLaws.java` — **the oracle**: builds a model, injects a rule, runs the real kernel over a document, reports fired `code|type|pointer`.
- `adapter/src/test/kotlin/…/laws/*DiffTest.kt` — ~180 interpreter↔kernel differentials, one semantic case each; canonical pattern in `InterpreterDiffTest.kt`.
- `adapter/src/test/kotlin/…/perf/InterpreterKernelFuzzTest.kt` — tri-engine fuzz (interpreter vs kernel-groovy-dynamic vs kernel-java-static); `laws/FuzzDiagnostics.kt` shrinks divergences.
- `adapter/src/test/kotlin/…/laws/{CorpusEngines,CorpusReplay}.kt` — the corpus reference runner.

How it works: the kernel is a **black box**; the same document is materialized into every engine and outcomes are compared as signature multisets. For one observed case, empirical kernel correspondence for the a12-dmkits interpreter or this project means agreement with that oracle at the explicitly retained projection. It does not define internal Lean correctness or establish universal kernel equivalence.

### The doc set (indexed by the hub)

The guard-checked hub is [`docs/SEMANTICS-MAP.md`](../../a12-rulekit/docs/SEMANTICS-MAP.md) — open it to jump to any `§n`'s prose, findings, facet, corpus, and lock tests. Canonical prose: [`docs/KERNEL-SEMANTICS.md`](../../a12-rulekit/docs/KERNEL-SEMANTICS.md) (the 14 `§n`). Evidence: [`docs/KERNEL-FINDINGS.md`](../../a12-rulekit/docs/KERNEL-FINDINGS.md). **Kernel-side hub** (classifies the engine's `rt.internal.core` classes): [`docs/RT-SEMANTICS-LEDGER.md`](../../a12-rulekit/docs/RT-SEMANTICS-LEDGER.md). Also: [`INTERPRETER-SPEC.md`](../../a12-rulekit/docs/INTERPRETER-SPEC.md)/[`-ARCHITECTURE.md`](../../a12-rulekit/docs/INTERPRETER-ARCHITECTURE.md)/[`-FINDINGS.md`](../../a12-rulekit/docs/INTERPRETER-FINDINGS.md), [`CONFORMANCE-CORPUS-SPEC.md`](../../a12-rulekit/docs/CONFORMANCE-CORPUS-SPEC.md), [`MVK-LEDGER.md`](../../a12-rulekit/docs/MVK-LEDGER.md), [`GRAMMAR-LEDGER.md`](../../a12-rulekit/docs/GRAMMAR-LEDGER.md), [`KERNEL-INTEGRATION-NOTES.md`](../../a12-rulekit/docs/KERNEL-INTEGRATION-NOTES.md), [`TESTING-SPEC.md`](../../a12-rulekit/docs/TESTING-SPEC.md).

### `corpus/` and the catalog

- [`corpus/`](../../a12-rulekit/corpus/) — portable replay vectors: `case.schema.json` (`modelRef` + `placements` + `op` + `expected` signature), `models/*.json` (bare DM-JSON), `cases/{comparison,clock,compute,fuzz,partial}/`. **Caveat: thin** — the committed cases cover only 5 of the 14 areas (see the table). Full differential coverage lives in `adapter/laws` (kernel-linked, not portable).
- [`rulekit/src/main/resources/catalog/operators.json`](../../a12-rulekit/rulekit/src/main/resources/catalog/operators.json) — 110 operators; `emptyOperandDefaults` (the per-kind empty matrix); `semantics` facets (`emptyOperand`/`aggregateIdentity`/`boundary`/`iterationRange`/`polarity`) with runnable kernel probes; `gotchas`.

---

## The `§n` drill-down index

The per-`§n` map — which a12-dmkits source, catalog facet, corpus family, and kernel class carries each area — lives in [`../spec/SEMANTICS-MAP.md`](../spec/SEMANTICS-MAP.md) §9, kept inside the spec map so it doubles as a live index from the prose into ground truth. For the exhaustive per-`§n` lock-test list, follow a12-dmkits' guard-checked [`SEMANTICS-MAP.md`](../../a12-rulekit/docs/SEMANTICS-MAP.md) (it re-derives from the live surface, so it never rots).

## What the coverage tells us

- **Machine-readable facts exist for only 5 areas** (§2, §5, §6, §9, §12). For those, lean on the catalog `semantics` facets + their runnable probes; for the other nine, ground truth is prose + findings + tests + the kernel class.
- **The sibling replayable corpus covers only 5 areas** (§5, §6, §9, §11, §12) and is thin. It is useful kernel-derived source evidence, not a live dependency or substitute oracle for this repository; the broader focused differentials live in `adapter/laws` (JVM, kernel-linked, not portable to Lean). Expanding local coverage means externally capturing the relevant case, retaining a portable own-repository observation, and adding only the typed projection needed by the Lean capsule.
- **The hardest, test-densest areas are §6, §9, §11, §12** — the same ones our [`spec/SEMANTICS-MAP.md`](../spec/SEMANTICS-MAP.md) rates ★★★★★. Encoding risk and proof payoff concentrate there.
- **The `interpreter` `commonTest` property tests are the Kotlin analogues of our target theorems** — `KleeneMonotonicityPropertyTest`, `DeterminismPropertyTest`, `RowPermutationPropertyTest`, `AggregateIdentityPropertyTest`. Mirror them as Lean theorems and cross-check.
