# Q2-P10 field fillability in a12-dmkits' contradiction detection

> **Status:** temporary upstream proposal, item Q2-P10 of the [Q2 preparation checklist](PLAN.md#q2-preparation-checklist), carried to a12-dmkits by the owner under the [upstream engagement rule](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md#upstream-engagement-rule) after Q2-P9's terminal handback. Once a12-dmkits accepts it, its durable facts move into a12-dmkits' owners and this file is deleted.

## Request

The owner, as a12-dmkits' owner, adds **field fillability** to contradiction detection: for one field of a model, whether an accepted document fills it, and when none does, a contradiction explanation of why. SME's Rule Contradictions report such fields beside whole-model conflicts, by a12-dmkits' SME comparison of 2026-11-12, which this repository has not re-read.

The question is the test data generator's, asked of a rewritten model: profile `test-data-v1`, kernel 31.3.1, DM 29.8.0, both acceptance relations, the encoder, solver protocol, interpreter replay, model check and contradiction search are those a12-dmkits hands back for Q2-P9 at the revision the hand-off task names, unchanged in meaning: `model generate-test-data` and contradiction detection without a field keep their semantics and result bytes.

The code and the roadmap are a12-dmkits'; this repository supplies the contract and checks the handback.

## The contract, by pointer

| Item | Owner of the statement | Executable check |
|---|---|---|
| The question and its goal rule | [Q2-P10 `question`](PLAN.md#q2-preparation-checklist) | goal models in [`FillabilityControlLocks.lean`](../A12Kernel/Reference/Dm/FillabilityControlLocks.lean) |
| Why the goal model answers it | [Q2-P10 `reading`](PLAN.md#q2-preparation-checklist) | — |
| Which entities are asked | [Q2-P10 `entities`](PLAN.md#q2-preparation-checklist) | — |
| The explanation of a field no document fills | [Q2-P10 `explanation`](PLAN.md#q2-preparation-checklist), [Q2-P9](PLAN.md#q2-preparation-checklist) | `explanations` in [`ExplainedUnsatControlLocks.lean`](../A12Kernel/Reference/Dm/ExplainedUnsatControlLocks.lean) |
| What a result names | [Q2-P10 `result`](PLAN.md#q2-preparation-checklist) | — |
| Separating controls | [Q2-P10 `controls`](PLAN.md#q2-preparation-checklist), [controls checkpoint](sources/kernel-31-calibration-probes.md#src-q2p10-fillability-controls) | [`FillabilityControlLocks.lean`](../A12Kernel/Reference/Dm/FillabilityControlLocks.lean) |

In short: for a field `E` and one relation, the goal model is the model plus one ERROR goal rule firing when `E` is not filled, `FieldNotFilled(E)` outside repeatable groups and `NumberOfFilledFields(G*/E) == 0` for `E` in a repeatable group `G`. The generator's answer for the goal model answers whether an accepted document fills `E`. When it is `solverReportedUnsatWithinBounds`, a Q2-P9 contradiction explanation of the goal model says why, the goal rule fixed and never a member. The goal rule sits in the root group holding `E` and reports on `E`. Groups and fields in a repeatable root group are not asked. The pointers decide where this summary is shorter.

## Responsibilities

- **a12-dmkits** writes the goal model, renders the goal rule in the model's condition language with a name, code and texts no model element already uses, and runs the generator on it unchanged. When the generator's admission refuses the goal model, that refusal is the goal model's result, and the result still carries the model's own answer.
- **The model's own answer** is the generator's result for the model under the same relation, row bounds and limits as the goal model; a12-dmkits may compute it once and reuse it for every field it asks of that model and relation.
- **The explanation** follows Q2-P9's responsibilities, admission screen, final verification and no-set rule on the goal model, whose removable constraints are the model's own; where Q2-P9 names the model and its own answer, read the goal model and its answer. Each removal witness fills `E`, since every final model keeps the goal rule.
- **This repository** owns the semantics in `spec/` and the contract in Q2-P10, and answers a semantic disagreement through its normal route. It writes no a12-dmkits code.

## Public surface

Recommended, a12-dmkits deciding: an option of `model detect-contradictions` naming one field by its element path, repeatable for several fields. Without it the operation answers the whole model as today. A group path given as a field is a usage error, not a result. Asking every field of a model is a12-dmkits' choice to offer; each field costs at least one generator run.

## Versioned bytes of a result

Per field: its element path, the goal rule as written, the model's own generator result, and the goal model's generator result. On `verifiedSat` that result's witness fills the field. On `solverReportedUnsatWithinBounds` the result also holds a Q2-P9 contradiction explanation of the goal model, or the reason none was produced. The goal rule appears only as the result's goal rule, never among the constraints admission fixed. The result names its own contract revision, the a12-kernel-lean revision the hand-off task pins, in a field of its own; an embedded contradiction explanation and generator result keep the contract revisions they name today. The byte layout is a12-dmkits'.

## Acceptance gates

1. **Controls.** For each retained control model, [`FForbidden.json`](../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FForbidden.json), [`FRequired.json`](../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRequired.json) and [`FRowBound.json`](../evidence/kernel-31.3.1/captures/q2p10-controls-2026-11-12/FRowBound.json), under both relations: the model's own answer is `verifiedSat`; `A` of `FForbidden` is filled by no document, explained by `AForbidden`; `C` of `FForbidden` is filled; `A` of `FRequired` is filled by no document, explained by `ABTrue`, `ABFalse` and the required role of `B`; `X` of `FRowBound` is filled by no document, explained by `XLow` and the `maxValue` of `X`; `Y` of `FRowBound` is filled.
2. **Witness agreement.** Every witness of gate 1, each model's own, a filled field's and each removal witness, is accepted by the interpreter's replay and, through the existing `:adapter:kernelProbe` route, by kernel 31.3.1 on its own model, goal model or reduced goal model, both strategies agreeing.
3. **Seeded mutations.** One mutant at each named seam is killed by a control answer: the goal rule left out, so the field is answered by the model's own answer, killed by `A` of `FForbidden`; a goal for a row field that asks whether a row of its group exists, such as `NoGroupFilled(Rows*)`, killed by `X` of `FRowBound`, a kill that follows from the captured acceptance of an empty row and spec/07 §5.1, no goal model of it being measured or locked; the count written unstarred, exactly `NumberOfFilledFields(Rows/Y) == 0`, which kernel 31.3.1 refuses at the model check with `MVK_PARAMSIZE_INVALIDN` since its only operand is one unstarred field, killed by `Y` of `FRowBound`, whose expected `verifiedSat` becomes that refusal; and the goal rule counted among the removable constraints, killed by the explanation of `A` of `FForbidden`.

## Handback

The committed a12-dmkits revision and the one command that runs gates 1 to 3, together with the test data generator's gates 1 to 4 and Q2-P9's gates 1 to 3 still passing at that revision; a moved mutation anchor may be updated if its named seam is still killed. Per control, field and relation: the answer, the witness or explanation with its removal witnesses. The mutation kill table. Any semantic disagreement as an a12-dmkits finding with its kernel measurement, which this repository records as inbound provenance rather than as another outbound entry.

## Excluded

Groups as entities; fields in a repeatable root group; listing every explanation of a field or a smallest one; certified UNSAT; Q1 condition reachability; computations.
