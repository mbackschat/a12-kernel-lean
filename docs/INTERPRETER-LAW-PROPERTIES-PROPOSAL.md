# Lean-proved laws as interpreter properties

> **Status:** temporary upstream proposal, item IV-P8 of the [interpreter verification checklist](PLAN.md#interpreter-verification-checklist), carried to a12-dmkits by the owner under the [upstream engagement rule](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md#upstream-engagement-rule). Once a12-dmkits' handback is accepted, its durable facts move into their owners and this file is deleted.

## Request

The owner, as a12-dmkits' owner, asks a12-dmkits to check six laws that this repository proves in Lean as properties of a12-dmkits' interpreter, over generated models and documents, and to show for each one that it catches a seeded defect. Two non-laws are added as controls on the generators. The properties, generators and tests are a12-dmkits'; this repository supplies the laws, their exact hypotheses and the checks below.

Work starts from a12-dmkits `03ea6e3c6e68f18f057df1b58de35eaddc0f116c` on `feature/q2`, or a successor. The interpreter is the `:interpreter` module through its public calls `validate`, `validatePart` and `compute` (`DmInterpreter`), on the JVM and on JS, as the existing property pack in `interpreter/src/commonTest/.../property/` runs.

A passing property is evidence over its samples, not a proof that the interpreter satisfies the law. A law's kernel correspondence is the Lean account's; this request does not re-measure the kernel.

## What a12-dmkits already checks

The property pack sweeps lazy and eager polarity, Kleene monotonicity, row permutation, empty-row append (IF53, IF54, IF46), aggregate identities, the indexed join against the scan, determinism, rule independence and unavailable-cell tallies. The `adapter` law and differential tests pin examples of several laws below against the kernel, but none sweeps them. Nothing here repeats an existing property.

## Laws

Each law names its Lean theorems in `A12Kernel/Proofs/` at this repository's revision that carries this file, states its hypotheses, and says what to observe, what the generator must produce and which seeded defect must turn it red. "Fires" means the rule's message is present; "type" is `VALUE_ERROR` or `OMISSION_ERROR`.

### P1 — partial firing persists into full validation

- **Theorem:** `partialRule_fired_implies_fullWithContent_fired_of_agreesOn` (`PartialValidation.lean`).
- **Law:** if a rule fires under `validatePart(D, R)` and its error field is in `R`, then it fires under `validate(D')` for every document `D'` that agrees with `D` on the fields in `R` and whose root instance has content. Its type may differ.
- **Hypotheses:** a nonrepeatable model; rules without `Having`, without `CustomCondition` and without repeatable reads; `R` a set of fields of that model, global fields counted as relevant (IF37).
- **Observe:** each `(code, pointer)` of `validatePart(D, R)` whose error field is in `R` appears in `validate(D')`.
- **Generator:** documents `D`, relevant sets `R`, and completions `D'` that change only cells outside `R`, to empty, filled and malformed values.
- **Seeded defect:** partial validation reads cells outside `R` as their stored values instead of treating them as unknown.

### P2 — a partial result depends only on the relevant fields

- **Theorem:** `partialSelected_agreesOn` (`PartialValidation.lean`).
- **Law:** `validatePart(D, R)` and `validatePart(D', R)` report the same messages whenever `D` and `D'` agree on the fields in `R`.
- **Hypotheses, generator and seeded defect:** those of P1.
- **Observe:** the two message lists as multisets of code, type and pointer.

### P3 — the computed Number target's self-validation message

- **Theorems:** `computedNumberSelfValidation_notFired_iff`, `_closed_value`, `_below_omission_iff`, `_above_value` and `starredChannels_separate_at_capacity` (`ComputationSelfValidation.lean`).
- **Law:** a computed Number target whose stored value differs from its computed value carries its implicit message, and one whose stored value is equal, under the normalized comparison, carries none. A stored value above the computed one types the message VALUE. A stored value below types it OMISSION exactly when some operand can still grow, otherwise VALUE.
- **Hypotheses:** the operands are of the measured kinds only: a count over a fixed group (closed once the group has content), a count over a starred group (open below its declared capacity), and a value read inside starred rows (open below capacity, or while a row cell is empty). A starred group at capacity with an empty row closes its count and leaves the value read open.
- **Observe:** the implicit message's presence and type under `validate`.
- **Generator:** one Number computation over `NumberOfFilledGroups` of a fixed group, `NumberOfFilledGroups` of a starred group and `Sum` over the starred rows; stored target values equal to, above and below the computed value, equal ones in another spelling such as `5.0`; starred groups below and at capacity, with empty and filled rows.
- **Seeded defect:** a stored value below the computed one types OMISSION whatever the operands' headroom.

### P4 — a computed target's stored value is never read

- **Theorems:** `repeatableNumberPlan_read_pending` and `repeatableNumberPlan_read_completed` (`RepeatableNumberPlan.lean`) for repeatable Number plans, and `scalarComputationRun_documentFor_find_listed` (`ScalarComputationRun.lean`) for scalar runs, where a pending target is absent from the document a later step reads. No single theorem states the end-to-end law; the property is their consequence inside Lean.
- **Law:** every computed outcome of `compute(D)` is unchanged when the stored values of computed targets change. A computed target that a later computation reads contributes its own completed outcome, or a clean empty value before it is computed.
- **Hypotheses:** acyclic computations, which the interpreter admits; the change projection (VALUE against unchanged) is not compared, because it legitimately reads the stored value.
- **Observe:** the computed outcome per target: value, cleared or errored.
- **Generator:** producer and consumer chains of Number computations, and arbitrary stored values in the targets, malformed ones included.
- **Seeded defect:** a computation reads the stored value of a target that has not been computed yet.

### P5 — rule metadata does not change firing

- **Theorems:** `flatRule_metadata_doesNotChangeVerdict` and `flatRuleMessage_invalidates_iff_error` (`ValidationRule.lean`).
- **Law:** changing a rule's code, severity or message text changes neither whether it fires nor its type; a fired message makes the outcome invalid exactly when its severity is ERROR.
- **Hypotheses:** the hypotheses of P1, without the relevant set; the error field is not changed.
- **Observe:** for each rule, its fired pointers and types, before and after the change; the outcome's validity.
- **Generator:** the rules of the generated models with their codes, severities and texts changed.
- **Seeded defect:** a fired WARNING makes the outcome invalid.

### P6 — absolute requiredness does not change computation

- **Theorems:** `applyAbsoluteRequired_preserves_computation`, `withRequiredFinding_preserves_computation` and `requiredFinding_empty_phase_split` (`Required.lean`).
- **Law:** `compute(D)` is the same whether a field is declared absolutely required or not: a required empty cell is unknown to validation but an ordinary empty value to computation.
- **Hypotheses:** absolute requiredness only; parent-relative requiredness is not covered.
- **Observe:** the computed outcomes, and that `validate` reports the requiredness message on the empty cell.
- **Generator:** models whose computations read fields toggled between required and not required, over empty, filled and malformed cells.
- **Seeded defect:** a required empty cell poisons the computation that reads it.

## Non-laws as generator controls

Each generator must reach the witness below at least once over its samples; a generator that never does is too weak for the law it serves.

- **N1, for P1 and P2.** Partial non-firing does not imply full non-firing: a rule silent under `validatePart(D, R)` can fire under `validate(D')` once a masked cell is filled, for example `[B] > 5` on a relevant error field with `B` outside `R` ([LEAN-FINDINGS LF66](LEAN-FINDINGS.md#lf66--partial-value-list-relevance-is-per-cell-and-per-star-extent-while-only-firing-is-completion-stable): only firing is completion-stable).
- **N2, for P1 and P2.** A rule containing `Having` is skipped by partial validation for every relevant set (`partialFilteredRule_skipped`), so `validatePart` with every field relevant need not equal `validate`.

## Observation, not a request

`DmInterpreter.validatePart`'s KDoc says that with the whole document relevant it equals `validate`. N2 and a12-dmkits' own `PartialValidationFilterSkipDiffTest` say a `Having` rule is skipped there. The sentence appears too broad; this repository did not run the interpreter to confirm it.

## Not requested

- Other Lean laws the inventory found, among them negation exclusivity and exhaustiveness, which would need a rule negator a12-dmkits does not have; a later request may add them.
- Re-measuring the kernel; repeatable and nested shapes beyond each law's hypotheses.

## Acceptance

1. Each of P1–P6 runs as a property over a12-dmkits' deterministic samples on the JVM and on JS and passes at the handback revision.
2. Each seeded defect, applied in a scratch change that is not committed, turns its property red; the handback records the red run.
3. N1 and N2 are each reached by the generators of P1 and P2.
4. The existing property pack and `:interpreter:check` still pass.

## Handback

Return the following:
- the revision;
- the test names per law and control;
- the sample counts;
- the red runs of the seeded defects;
- any law that fails, with its smallest failing model and document, as an observation for this repository rather than a fix;
- any hypothesis that the interpreter's public calls cannot express.
