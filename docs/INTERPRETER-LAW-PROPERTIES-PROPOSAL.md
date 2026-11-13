# Lean-proved laws as interpreter properties

> **Status:** temporary upstream proposal, item IV-P8 of the [interpreter verification checklist](PLAN.md#interpreter-verification-checklist), carried to a12-dmkits by the owner under the [upstream engagement rule](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md#upstream-engagement-rule). Once a12-dmkits' handback is accepted, its durable facts move into their owners and this file is deleted.

## Request

The owner, as a12-dmkits' owner, asks a12-dmkits to check six laws that this repository proves in Lean as properties of a12-dmkits' interpreter, and to show for each one that it catches a seeded defect. Two non-laws are added as controls on the generators. The properties, generators and tests are a12-dmkits'; this repository supplies the laws, their exact hypotheses and the checks below.

Work starts from a12-dmkits `03ea6e3c6e68f18f057df1b58de35eaddc0f116c` on `feature/q2`, or a successor. The interpreter is the `:interpreter` module through its public calls `validate`, `validatePart` and `compute` (`DmInterpreter`), on the JVM and on JS, as the existing property pack in `interpreter/src/commonTest/.../property/` runs.

"Generated" means what the existing pack does: curated model scenarios in the style of `PropertySupport`'s `flat`, `singleRep` and `nested`, with documents drawn from its deterministic seeds. No model generator is requested. The first failing sample suffices as a counterexample; no shrinker is requested.

A passing property is evidence over its samples, not a proof that the interpreter satisfies the law. A law's kernel correspondence is the Lean account's; this request does not re-measure the kernel.

## What a12-dmkits already checks

The property pack sweeps lazy and eager polarity, Kleene monotonicity, row permutation, empty-row append (IF53, IF54, IF46), aggregate identities, the indexed join against the scan, index identity across stages (`IndexIdentityStagePropertyTest`), determinism, rule independence and unavailable-cell tallies. The `adapter` law and differential tests pin examples of several laws below against the kernel, but none sweeps them. Nothing here repeats an existing property.

## Laws

Each law names its Lean theorems in `A12Kernel/Proofs/` at this repository's revision that carries this file, states its hypotheses, and says what to observe, what the scenarios must produce and which seeded defect must turn it red. "Fires" means the rule's message is present; "type" is `MsgType.VALUE` or `MsgType.OMISSION`.

### Shared fragment for P1, P2 and P5

The Lean theorems quantify over the flat condition fragment only. A scenario rule for these laws is a rule on a nonrepeatable model, without `Having` and without `CustomCondition`, whose condition is an `And`/`Or` tree of these leaves:

- a field compared with a literal;
- two Boolean, text, DateRange or temporal fields compared with each other;
- a field tested against a value list;
- `FieldFilled` or `FieldNotFilled`.

Excluded: arithmetic, Number field-against-field comparisons, functions, fill-list quantifiers, and the implicit formal, requiredness and uniqueness rules. The evaluation clock and every other world input are fixed per sample, since the theorems hold the world equal between the two documents.

### P1 — partial firing persists into full validation

- **Theorem:** `partialRule_fired_implies_fullWithContent_fired_of_agreesOn` (`PartialValidation.lean`).
- **Law:** if a rule fires under `validatePart(D, R)` and its error field is in `R`, then it fires under `validate(D')` for every document `D'` that agrees with `D` on the fields in `R` and on the global fields, and whose root instance has content. Its type may differ.
- **Hypotheses:** the shared fragment; `R` a set of fields of that model. `validatePart` counts global fields as relevant (IF37), so the agreement covers `R` together with every global field.
- **Observe:** each `(code, pointer)` of `validatePart(D, R)` whose error field is in `R` appears in `validate(D')`.
- **Scenarios:** documents `D`, relevant sets `R`, and completions `D'` that change only cells outside `R` and outside the global fields, to empty, filled and malformed values, with `D'`'s root keeping content.
- **Seeded defect:** partial validation reads cells outside `R` as their stored values instead of treating them as unknown.

### P2 — a partial result depends only on the relevant fields

- **Theorem:** `partialSelected_agreesOn` (`PartialValidation.lean`).
- **Law:** `validatePart(D, R)` and `validatePart(D', R)` report the same messages whenever `D` and `D'` agree on the fields in `R` and on the global fields.
- **Hypotheses, scenarios and seeded defect:** those of P1, except that `D'` need not have content.
- **Observe:** the two message lists as multisets of code, type and pointer.

### P3 — the computed Number target's self-validation message

- **Theorems:** `computedNumberSelfValidation_notFired_iff`, `_closed_value`, `_below_omission_iff`, `_above_value`, `computedNumberSelfValidationIfDecided_unknown_iff` and `starredChannels_separate_at_capacity` (`ComputationSelfValidation.lean`).
- **Law:** where the generated rule is decided, a computed Number target whose stored value differs from its computed value under the normalized comparison carries its implicit message, and one whose stored value is equal carries none. When the computed value is above the stored one, the message types VALUE. When the computed value is below the stored one, it types OMISSION exactly when some operand can still grow, otherwise VALUE.
- **Hypotheses:**
  - The rule is decided: the stored target is filled, and no operand group is empty or holds only malformed content.
  - One alternative, no tolerance band, `Exact` rounding, and no row beyond the declared capacity.
  - The operands combine with `+` only, so each operand's growth moves the computed value up.
  - The operands are of these measured kinds: `NumberOfFilledGroups` over two fixed groups, or over a fixed group beside a starred group (closed once the fixed groups have content; a single fixed group is refused with `MVK_PARAMSIZE_INVALIDGN`); `NumberOfFilledGroups` over a starred group (open below its declared capacity); and `Sum` of an unsigned Number field read inside starred rows (open below capacity, or while a row cell is empty). A starred group at capacity with an empty row closes its count and leaves the value read open.
  - A stored value equal to the computed one in another spelling, such as `5.0` for `5`, needs a target scale of at least one.
- **Observe:** the implicit message's presence and type under `validate`.
- **Scenarios:** Number computations over the operand kinds above; stored target values equal to, above and below the computed value, and equal ones in another spelling; starred groups below and at capacity, with empty and filled rows.
- **Seeded defect:** a computed value below the stored one types OMISSION whatever the operands' headroom.

### P4 — a computed target's stored value is never read

- **Theorems:** `repeatableNumberPlan_read_pending` and `repeatableNumberPlan_read_completed` (`RepeatableNumberPlan.lean`) for repeatable Number plans, and `scalarComputationRun_documentFor_find_listed` (`ScalarComputationRun.lean`) for scalar runs, where a pending target is absent from the document a later step reads. No single theorem states the end-to-end law; the property is their consequence inside Lean.
- **Law:** every computed outcome of `compute(D)` is unchanged when the stored values of computed targets change. A computed target that a later computation reads contributes its own completed outcome, or a clean empty value before it is computed.
- **Hypotheses:** acyclic computations, which the interpreter admits; only the values of target cells change, never which cells or rows are placed, since a placement changes group content; the change projection (VALUE against unchanged) is not compared, because it legitimately reads the stored value.
- **Observe:** the computed outcome per target: value, cleared or errored.
- **Scenarios:** producer and consumer chains of Number computations, arbitrary stored values in the targets, malformed ones included, and at least one consumer that reads group content beside a computed target, such as `NoGroupFilled` or `NumberOfFilledFields` over the target's group.
- **Seeded defect:** group-content consumers see a computed target's stored value: the interpreter skips its step that strips computed target cells before group content is judged (IF332). The content consumer in the scenarios is what makes this defect observable.

### P5 — rule metadata does not change firing

- **Theorems:** `flatRule_metadata_doesNotChangeVerdict` and `flatRuleMessage_invalidates_iff_error` (`ValidationRule.lean`).
- **Law:** changing a rule's code, severity or message text changes neither whether it fires nor its type, and a fired message makes the outcome invalid exactly when its severity is ERROR.
- **Hypotheses:** the shared fragment; the error field is not changed.
- **Observe:** for each rule, its fired pointers and types before and after the change. Validity is observed through `Interpreter.validateFull` or `Interpreter.validatePart` and `ValidationReport.noErrorOccurred`, on a scenario where this rule is the only one that fires, so that a flip of `noErrorOccurred` is caused by this rule's severity.
- **Scenarios:** the rules of the scenarios with their codes, severities and texts changed.
- **Seeded defects:** a fired WARNING makes the outcome invalid; rules of severity WARNING are skipped. The first tests the validity half, the second the firing half.

### P6 — absolute requiredness does not change computation

- **Theorems:** `applyAbsoluteRequired_preserves_computation`, `withRequiredFinding_preserves_computation` and `requiredFinding_empty_phase_split` (`Required.lean`).
- **Law:** `compute(D)` is the same whether a field is declared absolutely required or not: a required empty cell is unknown to validation but an ordinary empty value to computation.
- **Hypotheses:** a nonrepeatable model; absolute requiredness only; parent-relative requiredness is not covered.
- **Observe:** the computed outcomes, and that `validate` reports the requiredness message on the empty cell.
- **Scenarios:** computations that read fields toggled between required and not required, over empty, filled and malformed cells.
- **Seeded defect:** a required empty cell poisons the computation that reads it.

## Non-laws as scenario controls

Each control must be reached at least once by the scenarios of the laws it serves; scenarios that never reach it are too weak for those laws.

- **N1, for P1 and P2.** Partial non-firing does not imply full non-firing: a rule silent under `validatePart(D, R)` can fire under `validate(D')` once a masked cell is filled. For example, `FieldFilled(A) And [B] > 5` with error field `A`, `A` filled and in `R`, and `B` outside `R`: partial validation is silent because `B` is unknown, and a completion with `B` = 6 fires ([LEAN-FINDINGS LF66](LEAN-FINDINGS.md#lf66--partial-value-list-relevance-is-per-cell-and-per-star-extent-while-only-firing-is-completion-stable): only firing is completion-stable).
- **N2, for P1.** Partial validation does not require root content: with every field relevant, `validatePart` evaluates a relevant cell even when the root instance has no content, where `validate` does not (IF54). For example, `[Price] < 10` with error field `Price` on a document with no filled cell fires under `validatePart(D, all)` and stays silent under `validate(D)`. This is why P1 requires `D'` to have content.

## Observation, not a request

`DmInterpreter.validatePart`'s KDoc says that with the whole document relevant it equals `validate`. Two cases contradict it: N2 above, and a rule with `Having`, which partial validation skips for every relevant set (`partialFilteredRule_skipped`, and a12-dmkits' own `PartialValidationFilterSkipDiffTest`). The sentence appears too broad; this repository did not run the interpreter to confirm it.

## Not requested

- Other Lean laws the inventory found, among them negation exclusivity and exhaustiveness, which would need a rule negator a12-dmkits does not have; a later request may add them.
- Re-measuring the kernel; repeatable and nested shapes beyond each law's hypotheses; a model generator or a shrinker.

## Acceptance

1. Each of P1–P6 runs as a property over a12-dmkits' deterministic samples on the JVM and on JS and passes at the handback revision.
2. Each seeded defect, applied in a scratch change that is not committed, turns its property red; the handback records the red run.
3. N1 is reached by the scenarios of P1 and P2, and N2 by those of P1.
4. The existing property pack and `:interpreter:check` still pass.

## Handback

Return the following:
- the revision;
- the test names per law and control;
- the sample counts;
- the red runs of the seeded defects;
- any law that fails, with its first failing model and document, as an observation for this repository rather than a fix;
- any hypothesis that the interpreter's public calls cannot express.
