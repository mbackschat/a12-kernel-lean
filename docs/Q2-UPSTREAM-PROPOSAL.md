# Q2 test data generator in a12-dmkits

> **Status:** temporary upstream proposal, item Q2-P7 of the [Q2 preparation checklist](PLAN.md#q2-preparation-checklist), carried to a12-dmkits by the owner under the [upstream engagement rule](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md#upstream-engagement-rule). Once a12-dmkits accepts it, its durable facts move into a12-dmkits' owners and this file is deleted.

## Request

The owner, as a12-dmkits' owner, adopts a **test data generator**: SMT-grade generation of documents the model accepts, which a12-dmkits' feature gaps call accepted-sample generation. That adoption is the reopen condition of Q2 in a12-dmkits' [FEATURE-GAPS](../../a12-rulekit/docs/FEATURE-GAPS.md#4-deferred--out-of-scope--wont-build), read at a12-dmkits `44e45be6e` and unchanged at `0db083976`. The question is **∃ document. Accepted(model, document)** under the profile `test-data-v1`, for kernel 31.3.1 and DM 29.8.0. The code, the solver dependency and the roadmap are a12-dmkits'; this repository supplies the contract and checks the handback.

## The contract, by pointer

Each item is closed in this repository with its acceptance evidence; the pointers are the contract, and nothing here restates them.

| Item | Owner of the statement | Executable check |
|---|---|---|
| Profile: what is admitted and what fails closed by name | [Q2-P1](PLAN.md#q2-preparation-checklist) | — |
| Sample form: the Document JSON a witness is written in | [Q2-P1](PLAN.md#q2-preparation-checklist) | [`SampleFormCompletenessLocks.lean`](../A12Kernel/Reference/Dm/SampleFormCompletenessLocks.lean) |
| Verdict of each admitted leaf over absent, empty, not-check-relevant and filled cells, content gate and traversal | [spec/14](../spec/14-operator-reference.md) columns V, N, B and T with [spec/02 §B.2](../spec/02-logic-and-formal-errors.md#b2-the-three-cell-states--the-third-one-is-not-empty) and [spec/03 §A.4](../spec/03-empty-and-required.md#a4-the-row-gate--where-the-substitutions-stop) | [`LeafStateLocks.lean`](../A12Kernel/Reference/Dm/LeafStateLocks.lean) |
| Admitted set of each field kind | [spec/04 §4.8](../spec/04-numbers-and-decimals.md#48-the-formal-check-of-a-stored-value), [spec/06](../spec/06-strings-and-enumerations.md#stored-value-checking-and-normalization), [spec/02 §A.3](../spec/02-logic-and-formal-errors.md#a3-boolean-is-a-three-state-field-type-distinct-from-three-valued-logic) | [`FormalDomainLocks.lean`](../A12Kernel/Reference/Dm/FormalDomainLocks.lean), and for retained Number text [`NumberLengthLocks.lean`](../A12Kernel/Reference/Dm/NumberLengthLocks.lean) |
| Message-free and error-free acceptance | [spec/10 §2](../spec/10-validation-and-polarity.md#2-severity-is-metadata) | [`SampleAcceptance.lean`](../A12Kernel/Reference/Dm/SampleAcceptance.lean) |
| Bounded repetition and the rule iteration domain | [spec/07 §1.3](../spec/07-repetition-and-iteration.md#13-evaluation-domains), [spec/01 §2.3](../spec/01-data-model.md#23-reading-a-document-from-json) | [`LeafStateLocks.lean`](../A12Kernel/Reference/Dm/LeafStateLocks.lean) |
| Separating controls | [Q2-P6](PLAN.md#q2-preparation-checklist), [controls checkpoint](sources/kernel-31-calibration-probes.md#src-accepted-sample-controls) | [`AcceptedSampleControlLocks.lean`](../A12Kernel/Reference/Dm/AcceptedSampleControlLocks.lean) |

The two corrections this contract carried outbound, the severity channel and the Number admitted set, are reconciled: a12-dmkits' interpreter at `8b290c30b` agrees on their rows (KF684 and KF681, [reviewed handback](sources/inbound-handbacks.md#src-inbound-2026-11-10)), so no ledger entry is open against this contract.

## Responsibilities

- **a12-dmkits** encodes a model inside the profile, runs the solver, and reports one of the eight result labels of the U03 kit's [encoding rules](IMPLEMENTER-KIT-SMT.md#encoding-rules); this contract borrows the labels, not that kit's replay through Lean. A model is inside the profile when the 31.3.1 model check admits it, the a12-dmkits interpreter evaluates its rules, and it carries none of Q2-P1's exclusions; Q2-P1's in-profile count is Lean's measurement, not a gate. a12-dmkits refuses any other model as `unsupported`, naming an excluded feature it found or the model check's refusal. It replays every SAT witness through its interpreter, at a revision it names together with the tests that check that interpreter's catalog against kernel 31.3.1, and reports `replayRejected` when the replay disagrees.
- **The encoding ranges over the rule iteration domain**, not over the document's rows. A rule visits every declared slot up to a declared product of 5, and above it coordinate 1 plus every coordinate any group occupies, so an UNSAT label cites, per repeatable group, the row bound it searched ([Q2-P5](PLAN.md#q2-preparation-checklist)). A bound below the declared repeatability is allowed, since a root admits up to 999,999,999 rows, and makes the label UNSAT within that bound only.
- **This repository** owns the semantics in `spec/` and answers a semantic disagreement through its normal route. It writes no a12-dmkits code.

## Versioned bytes of a result

Each result names the profile `test-data-v1`, kernel `31.3.1`, DM `29.8.0`, the a12-dmkits revision and the interpreter revision, which may coincide, the solver and its version, the acceptance relation as `strictNoMessages` or `errorFree` ([Q2-P4](PLAN.md#q2-preparation-checklist)), and the label. A SAT result adds the witness in [Q2-P1](PLAN.md#q2-preparation-checklist)'s sample form and the interpreter's message set for it. An UNSAT result adds the row bounds it searched. The byte layout is a12-dmkits'.

## Acceptance gates

1. **Controls.** On the retained [control models](../evidence/kernel-31.3.1/captures/q2-controls-2026-11-08/MANIFEST.sha256), the labels follow their recorded acceptance, SAT being `verifiedSat` and UNSAT `solverReportedUnsatWithinBounds`:
   - `QUnsat_DM` is UNSAT under both relations.
   - `QSat_DM` is SAT under both relations.
   - `QWarn_DM` is SAT under error-free acceptance and UNSAT under message-free acceptance.
2. **Witness agreement.** No result over the controls and the gate 3 fixtures is `replayRejected`. The control witnesses are also run on kernel 31.3.1 through the existing `:adapter:kernelProbe` route and accepted there: both strategies agree, with no message under message-free acceptance and no `ERROR` message under error-free acceptance, as [`AcceptedSampleControlLocks.lean`](../A12Kernel/Reference/Dm/AcceptedSampleControlLocks.lean) reads the Kernel's rows.
3. **Seeded mutations.** One mutant of the encoder at each named seam is killed: a settled SAT answer of a control or fixture turns UNSAT, or a settled UNSAT answer turns SAT and replay rejects the witness. A SAT answer is settled by a witness the interpreter's replay accepts. The seams are: a substitution for an empty read where the operator's [column N](../spec/14-operator-reference.md#empty-read) assigns none; a WARNING rule counted as an error; an instantiated-only scan where the domain is declared, whose kill fixture [`LeafStateLocks.lean`](../A12Kernel/Reference/Dm/LeafStateLocks.lean) locks in both iteration regimes (a rule every slot fails, beside an absolute-required field); and a dropped conjunct of a field kind's admitted set. Collapsing a leaf's UNKNOWN to not-fired is no seam: no composed rule observes it ([spec/02 §A.1](../spec/02-logic-and-formal-errors.md#a1-connectives-are-two-valued-parentheses-are-mandatory), proved as [`evalVerdict_collapseUnknown`](../A12Kernel/Proofs/ConditionTree.lean)), so its mutant cannot be killed.
4. **Fail-closed profile.** Each model feature Q2-P1 excludes has one fixture, a model the 31.3.1 model check admits, refused as `unsupported` under that feature's name; a12-dmkits fixes the name tokens and maps them to Q2-P1's list in the handback. An excluded feature for which no admitted model is known is listed there with the model check's refusal instead. Partial validation and the world are not model features: the generator offers full validation in a fixed world only.

## Compatibility and retirement

Existing dmtool commands keep their contracts, and `model seed` stays a best-effort candidate generator. Choosing and distributing the solver is a12-dmkits' decision; its FEATURE-GAPS entry already names a Z3 subprocess as the least-bad route. When a12-dmkits accepts the request, its Q2 entry becomes live work there, and this file is deleted.

## Excluded

Computations join a later profile ([Q2-P8](PLAN.md#q2-preparation-checklist)), together with Q3's computation-table statement. Condition reachability (Q1) and computation-table partition (Q3) are separate questions. Verifying the interpreter against this theory follows this hand-off as a separate application.

## Handback

The committed a12-dmkits revision and the command that runs gates 1 to 4. Per control: its label and witness. The mutation kill table. The interpreter revision whose catalog is verified against kernel 31.3.1. Any semantic disagreement as an a12-dmkits finding with its kernel measurement, which this repository records as inbound provenance rather than as another outbound entry.
