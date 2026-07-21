# 13 — The Lean encoding guide

This consolidates the per-file `Lean modelling note` callouts into encoding guidance. It names representation choices, the traps that make plausible implementations diverge, the dependency spine within a semantic capsule, and the evidence/proof gate for each slice. Read the deep dives for behavioral rationale. Global sequencing, interleaving, and the active work item belong to [`../docs/PROJECT-DESIGN.md`](../docs/PROJECT-DESIGN.md) and [`../docs/PLAN.md`](../docs/PLAN.md), not this guide.

The stance is semantics-first and executable-first, but proofs are not an optional afterthought. Each capsule produces a small executable reference meaning, exact theorem obligations for the supported fragment, checked non-laws, and an honest evidence status. Matching retained observations are replayed when available; related external evidence may be batched later while the capsule remains `external evidence pending`. [`../docs/LEAN-FORMALIZATION.md`](../docs/LEAN-FORMALIZATION.md) defines the project-wide claim boundaries and required proof spine; [`../docs/ARCHITECTURE.md`](../docs/ARCHITECTURE.md) owns the concrete representation decisions.

---

## 1. The semantic foundations

The current foundations already live in [`../A12Kernel/Core.lean`](../A12Kernel/Core.lean), [`../A12Kernel/Cell.lean`](../A12Kernel/Cell.lean), and [`../A12Kernel/Document.lean`](../A12Kernel/Document.lean). Extend those types rather than reviving the older single-level sketches that this guide superseded.

The essential boundaries are:

- `Value` represents semantic values. Numbers use exact `Rat`; a field's scale is static `NumField` data, while stored-form rendering is separate.
- `K` represents strong-Kleene truth. The object language has no generic negation operation.
- `Verdict` represents `notFired`, `fired Polarity`, and `unknown`; it does not discard the invalid/suppressed outcome.
- `CheckedCell` records raw placement, an optional parsed value, and formal findings before a phase reads it. An absent cell and a present-empty cell both lack a parsed value but remain different placements. Base `formalCheck` contributes ordinary local findings; generated and structural passes may add later annotations to the same representation.
- `observeCell` will map the same `CheckedCell` to `CellObservation.empty`, `.value`, `.unknown`, or `.poison` according to validation/computation phase. Both absent and present-empty map to `.empty` without erasing their checked placement; operator-specific empty substitution happens after this boundary.
- `Document` represents instantiated rows independently of raw cell values, because an instantiated blank row is semantically observable.
- `Env` binds enclosing repeatable levels to rows; `World` supplies clocks and other otherwise ambient inputs.
- Surface rules remain extrinsic. A checked elaborator should reject illegal paths/types/scales/scopes or return a `WellFormed` core rule; successful host elaboration of an AST constructor is not that guarantee.

The conceptual public flow is:

```lean
def elaborate   : SurfaceRule → Model → Except ElabError CoreRule
def eval        : Model → World → Document → Env → CoreCondition → Verdict
def computeOne  : Model → World → Document → Env → CoreComputation → ComputeOutcome
def apply       : Document → List (CellAddr × ComputeOutcome) → Document
def validate    : Model → World → Document → ValidationResult
```

These signatures are design targets, not declarations already present. Keep computation outcome-producing rather than document-mutating so compute → apply → validate remains explicit and read-driven poison cannot leak into unrelated instances.

---

## 2. The ten encoding traps

Each trap reflects observed A12 behavior that a reasonable-looking implementation can silently lose.

1. **Collapsing the cell boundary into `Option Value`.** Absent and present-empty placements can supply the same empty observation, while malformed, validation-unknown, and computation-poison remain different states. Preserve raw placement independently of parsed value through the two-level `CheckedCell → observeCell Phase → CellObservation` model, and route every finding through that common checked-cell boundary. Keep base `formalCheck` limited to ordinary local checks; generated and structural findings are staged annotations, not hidden operator behavior. ([§1](01-data-model.md#2-document--an-instance-of-the-tree), [§3](02-logic-and-formal-errors.md))
2. **One universal meaning for empty.** Empty meaning depends on kind and consuming operator: Number may substitute `0`, Confirm may substitute `False`, comparisons may not evaluate String/Date, concat uses `""`, and several aggregates skip empties. Preserve whether a value was actually given alongside any substituted value. ([§2](03-empty-and-required.md))
3. **Scale as a runtime numeric attribute.** Scale is static and gates equality/inequality through `scaleOf` (`+` → max, `*` → sum, `/` and `^` → unknown). Do not attach declared scale to the runtime rational. ([§5](04-numbers-and-decimals.md))
4. **Forgetting directional fillability and polarity.** VALUE/OMISSION depends on how legal fills can move the expression, not only on current truth. Design its propagation together with each operator and fold it into `Verdict` without losing `unknown`. ([§12](10-validation-and-polarity.md))
5. **Eager computation reads.** Poison is read-driven. `And`, `Or`, conditionals, and scans stop early, so an unread malformed cell must not poison. Make evaluation order explicit and genuinely short-circuiting. ([§11](09-computations.md))
6. **Conflating the two computation clears.** A precondition clear cascades as empty after computed inputs are pre-stripped; an invalidity clear poisons when read. Both mechanisms must remain distinct. ([§11](09-computations.md))
7. **Deriving iteration scope from placement.** Scope comes from referenced repeatable fields, never from the syntax node's tree position; empty scope means evaluate once. ([§9](07-repetition-and-iteration.md))
8. **Binding `*` like `$`.** Fix environment levels strictly above the first `*`, reopen the starred level and descendants, and let same-group star range over all rows. Only `$` correlates. ([§9](07-repetition-and-iteration.md))
9. **Treating semantic-index no-match as unknown.** No match reads empty, so numeric-zero and field-not-filled conditions can fire. It is not formal invalidity. ([§10](08-paths-and-references.md))
10. **Inferring row existence from filled cells.** Substitution is gated by content-bearing instances, `AllFieldsFilled` uses the declared range, and `AtLeastOneFieldFilled` uses instantiated rows. `Document.instantiatedRows` must remain independent of cell contents. ([§2](03-empty-and-required.md), [§1](02-logic-and-formal-errors.md))

---

## 3. Dependency spine within a capsule

Build each claimed semantic path bottom-up through the layers it actually needs. The numbered list is a dependency and risk guide, not a global instruction to complete one entire domain before work may rotate to another. Reuse completed layers, follow the controlled spiral, and close one active proof-bearing capsule or bounded risk spike at a time.

1. **Scalars and literals.** Complete `Value`, explicit numeric rescaling (19 / `HALF_UP` / 50-digit intermediate context), calendar conventions, the string/date literal typer, and UTF-16 code-unit String length. Lock the rounding table, the three-independently-divided-thirds `RoundDown` pre-round case from §5, and the decomposed-combining length witness. ([§5](04-numbers-and-decimals.md), [§6](05-dates-and-time.md), [§7](06-strings-and-enumerations.md))
2. **Formal checking and phase observation.** Define `FieldPolicy`, an explicit `RawCell` placement shape, base `formalCheck`, checked-cell annotation, and `observeCell`; retain absent versus present-empty even though both observations are empty, keep ordinary local findings in the base pass, and route later generated/structural findings through the same checked-cell boundary. Make raw empty String ingestion and CRLF→LF normalization explicit ingestion-stage facts after the raw-text line-break gate and before normalized pattern/domain/length checks, without rewriting the document. Prove the placement and phase laws, including that computation ignores a validation-scoped `.required` annotation. ([§1](01-data-model.md#2-document--an-instance-of-the-tree), [§3](02-logic-and-formal-errors.md), [§4](03-empty-and-required.md))
3. **Flat condition semantics.** Add comparisons, per-kind empty handling, negative predicates, presence/fill predicates, and the exact strong-Kleene `And`/`Or` verdict tables. Because value-wins `Or` may upgrade an OMISSION-fired branch, do not infer a validation read trace from truth short-circuiting; add phase-specific trace semantics only when an observable distinction or focused probe justifies it. Define the strong-Kleene information order before proving monotonicity: unknown may refine to true or false, while definite results remain stable. ([§1](02-logic-and-formal-errors.md), [§2](03-empty-and-required.md))
4. **Checked elaboration and generated rules.** Introduce `WellFormed` core rules and explicit rejection; implement required/index generation and staged checked-cell annotations. Required validation must evaluate the generated mandatory rule on base checked cells, retain its hit/message, and only on a hit annotate the empty target with `.required` for authored rules; this order prevents the mandatory rule's `FieldNotFilled` from suppressing itself. Reject every raw-type String value window and desugar its sole admitted strict whole-condition `Length` declaration to metadata with no runtime rule. Prove the accepted elaborations and desugarings preserve meaning. ([§4](03-empty-and-required.md), [§7](06-strings-and-enumerations.md))
5. **Iteration environment.** Implement referenced-field scope, context enumeration, star binding, `Having`/`$` correlation, parallel-iteration outer join, and the two-phase uniqueness cache. Specify the declarative context set before optimizing enumeration. ([§9](07-repetition-and-iteration.md))
6. **Paths.** Implement the exact two-tier bare-name resolution (declaring group, then flag-gated model-wide unique field short name), explicit `..` and named ancestors, semantic index with no-match-as-empty, and the `..` plus `*` rejection; make successful resolution part of `WellFormed`. Never add an implicit ancestor walk. ([§10](08-paths-and-references.md))
7. **Directional fillability and polarity.** Define `FillExtends`, sign-aware seeds, propagation through arithmetic, functions, aggregates, counts, dates, concat, and `Having`, and the per-comparison-direction consumer dispatch including the normalized-side `!=` arm. Prove only the one-sided result supported by the explicit fill relation. The portable [`empty-polarity` family](../../a12-rulekit/corpus/cases/empty-polarity/) supplies focused replay for the empty-Number and polarity witnesses. ([§12](10-validation-and-polarity.md))
8. **Computation.** Add VALUE/CLEARED/ERRORED outcomes, precondition empty cascade, poison-on-read, stored-form render, the final-empty String root-store gate before the reduced formal check, delta reporting, the placement-sensitive apply table including ERRORED-never-creates, and implicit validation-rule elaboration. Prove read-footprint noninterference before adding caches and state application laws over absent/present-empty/present-value target placement. ([§11](09-computations.md))
9. **Partial validation.** Define relevant-set agreement, out-of-set unknown, global auto-add, starred-aggregate gating, and phantom rows; state the one-sided theorem over that exact relation. ([§12](10-validation-and-polarity.md))
10. **Interpolation and custom conditions.** Keep rendering pure over post-fire resolved display-policy inputs, distinct from normalized evaluation reads, and model custom operations as explicit oracles. Exclude them from locality/monotonicity results unless their contracts provide the required footprint and stability laws. ([§13/§14](11-messages-and-custom.md))

Every capsule has the same internal exit gate:

- the smallest total executable definition for the clause;
- focused examples for ordinary, boundary, empty, malformed, and order-sensitive behavior as applicable;
- direct replay of every currently available matching portable corpus case and retained external kernel observation, with unavailable correspondence recorded as `external evidence pending` for later family calibration;
- an updated `§n` coverage entry with version, provenance, support status, and outcome domain;
- the proof-spine obligation introduced by the stage, with exact assumptions and root-axiom review;
- a checked counterexample to the nearest attractive false generalization;
- focused elaboration and a green whole-project build.

---

## 4. Regression, conformance, and theorem guards

Examples and tests anchor concrete behavior; theorems establish universal consequences of the Lean definitions; differential evidence anchors primitive choices to the kernel. Do not use any one of these as a label for the other two.

Use four distinct evidence roles. The kernel's Groovy-dynamic runtime service is the normative behavioral observation anchor. Generated static-Java is required co-evidence for detecting and characterizing strategy splits; when both routes accept the same legal input but disagree, record the split and do not let static-Java override Groovy-dynamic. [`../../a12-rulekit/adapter`](../../a12-rulekit/adapter) is the external kernel harness and result-export boundary for focused probes; it remains outside this repository's trusted or shipped dependency graph. [`../../a12-rulekit/corpus`](../../a12-rulekit/corpus) is the portable replay format consumed here. [`../../a12-rulekit/interpreter`](../../a12-rulekit/interpreter) is a valuable independent clean-room peer for triangulation and finding divergences, but agreement with it is not kernel evidence and it never resolves a disagreement against the kernel anchor.

The first engine-backed conformance witnesses should be:

1. empty Number participates as fillable zero in a comparison, including the directional unsigned/signed `!=` cases from the portable `empty-polarity` family;
2. empty Boolean remains not evaluable while empty Confirm behaves as false;
3. a VALUE-fired `Or` remains fired rather than becoming suppressed by a malformed sibling; make no validation-read-trace claim without a focused kernel probe;
4. fired `And` with a malformed sibling becomes unknown;
5. semantic-index no-match reads empty rather than unknown;
6. required-empty produces its validation-scoped formal finding but not computation poison;
7. a malformed computation input beyond a short-circuit or scan stop does not poison;
8. precondition clear and invalidity poison cascade differently;
9. same-group and cross-subtree star binding use their distinct context sets;
10. scale-19 pre-rounding is observable in the documented numeric boundary case; its legal witness uses arithmetic, so whole-rule replay waits for the arithmetic-expression fragment rather than inventing a scale-20 field.

Useful sampled regression properties include determinism under an injected `World`, computation-delta projection, star-binding small cases, intended poison order sensitivity, `No` versus `NotAll` asymmetry, and the constructed-Date boundary where `Valid`/`Invalid` complement at truth projection but one full verdict does not determine the other. Sampled property tests remain valuable even after related theorems exist because they exercise executable integration and produce small counterexamples.

The universal theorem catalog and its required scopes live in [`../docs/LEAN-FORMALIZATION.md`](../docs/LEAN-FORMALIZATION.md). In particular, do not write “prove monotonicity” without first defining the information/fill relation and excluding or constraining counting quantifiers, row creation, custom oracles, and order-sensitive computations.

Follow Cedar's mechanical coverage lesson: when the proof hierarchy grows, maintain one trusted theorem root that recursively imports every trusted proof module and make a coverage/hygiene check part of CI. `lake build` alone is not sufficient because Lean accepts `sorry`.

---

## 5. Clean-room boundary

The kernel's Groovy-dynamic runtime service is the behavioral oracle, not a dependency or transcription source; generated static-Java remains co-evidence and a strategy-split detector. Learn the mechanism from the specifications, findings, source inspection, and focused external probes; write original Lean; then lock it with own-domain examples, portable corpus replay, and externally exported kernel differential evidence. The a12-dmkits adapter in the `a12-rulekit/` checkout may host the kernel-facing probe outside this repository; this repository consumes the resulting portable evidence and never links, calls, or ships that harness or the kernel. Never translate kernel expressions line by line. [`../CLAUDE.md`](../CLAUDE.md) is the authoritative licensing and clean-room rule.

---

## 6. Summary

The semantic center is a total, pure evaluator over phase-aware cell observations, explicit document rows, an iteration environment, and an injected world. Validation yields a `Verdict` that retains unknown and polarity; computation yields explicit per-cell outcomes with order-sensitive, read-driven poison; elaboration separates legal surface rules from a smaller well-formed core; application and orchestration remain outside individual semantic clauses. The difficulty is not merely implementing every operator. It is preserving the interacting distinctions, connecting each primitive choice to evidence, proving the consequences that matter, and retaining checked boundaries where stronger claims fail.
