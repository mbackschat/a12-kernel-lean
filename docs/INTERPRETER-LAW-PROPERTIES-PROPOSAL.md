# Lean-proved laws as interpreter properties

> **Status:** temporary upstream proposal, item IV-P8 of the [interpreter verification checklist](PLAN.md#interpreter-verification-checklist), carried to a12-dmkits by the owner under the [upstream engagement rule](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md#upstream-engagement-rule). Once a12-dmkits' handback is accepted, its durable facts move into their owners and this file is deleted.

## Request

The owner, as a12-dmkits' owner, asks a12-dmkits to check four laws that this repository proves in Lean as properties of a12-dmkits' interpreter, and to show for each one that it catches a seeded defect. Two non-laws are added as controls on the scenarios. The properties, scenarios and tests are a12-dmkits'; this repository supplies the laws, their exact hypotheses and the checks below.

Work starts from a12-dmkits `03ea6e3c6e68f18f057df1b58de35eaddc0f116c` on `feature/q2`, or a successor. The interpreter is the `:interpreter` module through `DmInterpreter`'s calls `validate`, `validatePart` and `compute`, on the JVM and on JS, as the existing property pack in `interpreter/src/commonTest/.../property/` runs.

The scenarios are curated models in the style of `PropertySupport`'s `flat`, `singleRep` and `nested`, with documents drawn from deterministic seeds. The existing scenarios do not contain the rules and documents each law and control needs, so new curated ones are expected; no model generator is requested. The first failing sample suffices as a counterexample; no shrinker is requested.

A passing property is evidence over its samples, not a proof that the interpreter satisfies the law. A law's kernel correspondence is the Lean account's; this request does not re-measure the kernel.

## What a12-dmkits already checks

The property pack sweeps lazy and eager polarity, Kleene monotonicity, row permutation, empty-row append (IF53, IF54, IF46), aggregate identities, the indexed join against the scan, index identity across stages (`IndexIdentityStagePropertyTest`), determinism, rule independence and unavailable-cell tallies. The `adapter` law and differential tests pin examples of several laws below against the kernel, and `PartialValidationFuzzDiffTest` sweeps documents and relevant sets against the kernel, but none checks these laws. Control N2 overlaps `EmptyRowAppendPropertyTest`'s IF54 case on a flat field instead of a phantom row; no law here repeats an existing property.

## Laws

Each law names its Lean theorems in `A12Kernel/Proofs/` at this repository's revision that carries this file, states its hypotheses, and says what to observe, what the scenarios must produce and which seeded defect must turn it red. "Fires" means the rule's message is present; "type" is `MsgType.VALUE` or `MsgType.OMISSION`.

### Shared fragment for P1, P2 and P3

The Lean theorems quantify over the flat condition fragment only. A scenario for these laws has a nonrepeatable model with no computations and no required, unique or index fields. Its rules have no `Having` and no `CustomCondition`, each rule's error field is a field its condition reads, and each condition is an `And`/`Or` tree of these leaves, with exactly these operators, field on the left and literal on the right as the Lean constructors take them:

- a Number field compared with a Number literal by `==`, `!=`, `<`, `<=`, `>`, `>=` or a tolerance operator;
- a String field's length compared with a literal by `<`, `<=`, `>` or `>=`;
- a Boolean, String or Enumeration field compared with a literal, or a Confirm field tested, by `==` or `!=`;
- two Boolean, text or DateRange fields compared by `==` or `!=`;
- two fields of the same temporal family (Date with Date, DateTime with DateTime, Time with Time) compared by an ordering or equality operator;
- text or Enumeration fields, or Number fields against integer literals or Number fields, under one of the five `…ValueIncludedInValueList` operators;
- `FieldFilled` or `FieldNotFilled`.

Excluded: arithmetic, Number field-against-field comparisons, functions other than the String length, fill-list quantifiers such as `NoFieldFilled`, DateRange against a literal, and temporal literals, `Now` and `Today`. The temporal exclusion is a hypothesis of the theorems, not a scenario convenience: the flat projection they quantify over reads an unresolvable temporal label as unknown, while the kernel fails the whole rule when such a label is reached (spec/10, "A runtime failure fails the rule, not the validation").

Messages are keyed by `rulePath` and pointer, and each law compares only the messages whose `rulePath` is a scenario rule; the format messages malformed cells produce are expected. For every law, the interpreter is constructed with a fixed `clock: EvalClock`, since the theorems hold the world equal between the two documents or runs.

### P1 — partial firing persists into full validation

- **Theorem:** `partialRule_fired_implies_fullWithContent_fired_of_agreesOn` (`PartialValidation.lean`).
- **Law:** if a rule fires under `validatePart(D, R)` and its error field is in `R`, then it fires under `validate(D')` for every document `D'` that agrees with `D` on the fields in `R` and on the global fields, and in which the error field's root instance has content. Its type may differ.
- **Hypotheses:** the shared fragment; `R` a set of field pointers only, never a group, since a relevant group makes its descendants relevant. `validatePart` counts global fields as relevant (IF37), so the agreement covers `R` together with every global field. "Has content" means at least one well-formed filled cell under the error field's root group; a malformed-only root is not used.
- **Observe:** each `(rulePath, pointer)` of a scenario rule in `validatePart(D, R)` whose error field is in `R` appears in `validate(D')`.
- **Scenarios:** documents `D`, relevant sets `R`, and completions `D'` that change only cells outside `R` and outside the global fields, to empty, filled and malformed values, with `D'`'s root keeping content.
- **Seeded defect:** partial validation reads cells outside `R` as their stored values instead of treating them as unknown.

### P2 — a partial result depends only on the relevant fields

- **Theorem:** `partialSelected_agreesOn` (`PartialValidation.lean`).
- **Law:** `validatePart(D, R)` and `validatePart(D', R)` report the same scenario-rule messages whenever `D` and `D'` agree on the fields in `R` and on the global fields.
- **Hypotheses, scenarios and seeded defect:** those of P1, except that `D'` need not have content.
- **Observe:** the two lists of scenario-rule messages as multisets of `rulePath`, type and pointer.

### P3 — rule metadata does not change firing

- **Theorem:** `flatRule_metadata_doesNotChangeVerdict` (`ValidationRule.lean`), stated for full validation. Under `validatePart` no theorem states it; it holds by construction, since `FlatCondition.evalPartial` (`Semantics/PartialValidation.lean`) takes no code, severity or text.
- **Law:** changing a rule's code, severity or message text changes neither whether it fires nor its type.
- **Hypotheses:** the shared fragment; the error field is not changed; the changed texts contain no `$` character, since the Lean rule takes its text as already resolved while the interpreter renders parameters.
- **Observe:** for each scenario rule, its fired pointers and types before and after the change, under `validate` and under `validatePart` with the relevant sets of P1.
- **Scenarios:** the rules of the scenarios with their codes, severities and texts changed, WARNING and INFO among the severities, including a rule that fires changed to WARNING.
- **Seeded defect:** rules of severity WARNING are skipped.

### P4 — absolute requiredness does not change computation

- **Theorems:** `applyAbsoluteRequired_preserves_computation`, `withRequiredFinding_preserves_computation` and `requiredFinding_empty_phase_split` (`Required.lean`).
- **Law:** `compute(D)` is the same whether a field is declared absolutely required or not: a required empty cell is unknown to validation but an ordinary empty value to computation.
- **Hypotheses:** a nonrepeatable model with no index fields; absolute requiredness only, toggled on fields the computations read and never on a computation's target, since the theorems cover reads; parent-relative requiredness is not covered.
- **Observe:** the computed outcomes, and that `validate` reports the requiredness message on the empty cell.
- **Scenarios:** computations that read fields toggled between required and not required, over empty, filled and malformed cells, including a computation whose outcome differs between an empty operand and a poisoned one, such as arithmetic over the field beside a filled operand.
- **Seeded defect:** a required empty cell poisons the computation that reads it.

## Non-laws as scenario controls

Each control is reached when a test asserts its witness pair on a sample the law's scenarios produce. Scenarios that never reach it are too weak for the laws it serves.

- **N1, for P1 and P2, witnessed on P1's samples, whose documents P2's scenarios share.** Partial non-firing does not imply full non-firing: a rule silent under `validatePart(D, R)` can fire under `validate(D')` once a masked cell is filled. For example, `FieldFilled(A) And [B] > 5` with error field `A`, `A` filled and in `R`, and `B` outside `R`: partial validation is silent because `B` is unknown, and a completion with `B` = 6 fires ([LEAN-FINDINGS LF66](LEAN-FINDINGS.md#lf66--partial-value-list-relevance-is-per-cell-and-per-star-extent-while-only-firing-is-completion-stable): only firing is completion-stable).
- **N2, for P1.** Partial validation does not require root content: a relevant cell is evaluated even when the root instance has no content, where `validate` does not evaluate it (IF54). The witness pair is a document `D` with no valued placement and `R` holding the error field, where the rule fires under `validatePart(D, R)` and stays silent under `validate(D)`; for example `[Price] < 10` with error field `Price`. This is why P1 requires `D'` to have content.

## Observation, not a request

`DmInterpreter.validatePart`'s KDoc says that with the whole document relevant it equals `validate`. Three cases contradict it: N2 above; a rule with `Having`, which partial validation skips for every relevant set (`partialFilteredRule_skipped`, and a12-dmkits' own `PartialValidationFilterSkipDiffTest`); and a rule whose error field is a group, which a12-dmkits' partial plan also skips (`skippedInPartial` in `ModelStaticPlans.kt`). The sentence appears too broad; this repository did not run the interpreter to confirm it.

## Not requested

- **The computed Number target's self-validation typing** (`ComputationSelfValidation.lean`) and **a computed target's stored value never being read** (`RepeatableNumberPlan.lean`, `ScalarComputationRun.lean`). Their hypotheses, which keep computed fields out of operand groups, fix the decided gate and make a stripped stored target observable, are not settled enough for a property; a later request may add them.
- **Validity follows ERROR severity alone** (`flatRuleMessage_invalidates_iff_error`). `DmInterpreter`'s `ValidationOutcome` carries no validity verdict; the only one is `ValidationReport.noErrorOccurred` with its severity projection, reached through the public `io.github.mbackschat.a12.dm.interpreter.Interpreter`, which the pack does not use.
- **Negation exclusivity and exhaustiveness.** a12-dmkits' complement, `ConditionPolarity.complement`, lives in the JVM-only `rulekit` module and declines quantifiers, custom conditions and tolerance comparisons; the multiplatform `:interpreter` pack does not depend on it. A later request may add them.
- Re-measuring the kernel; repeatable and nested shapes beyond each law's hypotheses; a model generator or a shrinker.

## Acceptance

1. Each of P1–P4 runs as a property over a12-dmkits' deterministic samples on the JVM and on JS and passes at the handback revision.
2. Each seeded defect, applied in a scratch change that is not committed, turns its property red; the handback records the red run.
3. N1 and N2 are each reached on P1's samples.
4. The existing property pack and `:interpreter:check` still pass.

## Handback

Return the following:
- the revision;
- the test names per law and control;
- the sample counts;
- the red runs of the seeded defects;
- any law that fails, with its first failing model and document, as an observation for this repository rather than a fix;
- any hypothesis that the interpreter's public calls cannot express.
