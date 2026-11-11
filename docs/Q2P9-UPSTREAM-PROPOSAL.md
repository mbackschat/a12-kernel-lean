# Q2-P9 explained UNSAT in a12-dmkits' test data generator

> **Status:** temporary upstream proposal, item Q2-P9 of the [Q2 preparation checklist](PLAN.md#q2-preparation-checklist), carried to a12-dmkits by the owner under the [upstream engagement rule](SEMANTIC-CAPSULE-PIPELINE-PROPOSAL.md#upstream-engagement-rule). Once a12-dmkits accepts it, its durable facts move into a12-dmkits' owners and this file is deleted.

## Request

The owner, as a12-dmkits' owner, adds **contradiction detection** to the test data generator: when the generator answers `solverReportedUnsatWithinBounds`, it can also name an explanation, a set of the model's own constraints that conflict. SME's Rule Contradiction Detection does the same from SME's own generator, by a12-dmkits' reading of SME 12.5.2 recorded in its feature gaps at `802b930fe0ab1edec13d7b1f19437dfa0cd3069f`, whose contradiction-analysis family that SME feature inspired.

This is that generator's question asked from its UNSAT side, not a new analysis: profile `test-data-v1`, kernel 31.3.1, DM 29.8.0, both acceptance relations, the encoder, solver protocol, interpreter replay and model check are the test data generator's as handed back at a12-dmkits `166530750a756574558f396b1b7097733b6b0c44`, unchanged in meaning: `model generate-test-data` keeps its semantics and result bytes. Their code may change, for instance to guard each removable constraint with an assumption literal and solve with `check-sat-assuming`; an interpreter fix re-pins the catalog check against kernel 31.3.1 and is reported.

The code and the roadmap are a12-dmkits'; this repository supplies the contract and checks the handback.

## The contract, by pointer

| Item | Owner of the statement | Executable check |
|---|---|---|
| Removable constraints and what removing one writes | [Q2-P9 `constraints`](PLAN.md#q2-preparation-checklist) | `remove` in [`ExplainedUnsatControlLocks.lean`](../A12Kernel/Reference/Dm/ExplainedUnsatControlLocks.lean) |
| Admission of a reduced model | [Q2-P9 `admission`](PLAN.md#q2-preparation-checklist) | — |
| What an explanation is | [Q2-P9 `explanation`](PLAN.md#q2-preparation-checklist) | `explanations` in the same module |
| Row bounds of an explanation | [Q2-P9 `bounds`](PLAN.md#q2-preparation-checklist) | — |
| What a result names, and when it names no set | [Q2-P9 `result`](PLAN.md#q2-preparation-checklist) | — |
| Separating controls | [Q2-P9 `controls`](PLAN.md#q2-preparation-checklist), [controls checkpoint](sources/kernel-31-calibration-probes.md#src-q2p9-explained-unsat-controls) | [`ExplainedUnsatControlLocks.lean`](../A12Kernel/Reference/Dm/ExplainedUnsatControlLocks.lean) |

In short: the removable constraints are a model's authored rules, each field's absolute-required role, and each declared Number `minValue`, `maxValue`, `minLength` or `maxLength` and String `minLength` or `maxLength`; removing one leaves its rule element, `requirednessConfig` or bound member out. An explanation `S` is a set of them such that the model keeping only `S` is `solverReportedUnsatWithinBounds`, and the model keeping `S` without any one member is `verifiedSat`. The pointers decide where this summary is shorter.

## Responsibilities

- **a12-dmkits** computes an explanation for a model it answered `solverReportedUnsatWithinBounds` under one relation. The search method is its own; an unsat core over one assumption per removable constraint, shrunk by removing one member at a time, is one route. Every reduced model it solves passes the whole admission it applies to its input. It screens each removable constraint up front by removing it alone from the input model; one whose removal admission refuses joins the fixed part. Each member's reported witness is accepted by the interpreter's replay on that member's final reduced model, `S` without it, whether re-solved there or found earlier and replayed there; a set is reported only when all of them are.
- **No set is reported unverified.** When a solver answer during the search is neither SAT nor UNSAT, a replay rejects a witness or the model check refuses a reduced model, the result names no set and says which of the three occurred.
- **This repository** owns the semantics in `spec/` and the contract in Q2-P9, and answers a semantic disagreement through its normal route. It writes no a12-dmkits code.

## Public surface

Recommended, a12-dmkits deciding: a verb of its own beside `model generate-test-data`, opt-in, since it asks why nothing is accepted rather than for a sample and costs a solver call, a replay and a model check per member it tries. Its result embeds the generator's UNSAT result unchanged.

## Versioned bytes of a result

The test data generator's result for the same model and relation, and in addition either the explanation or the reason none was produced. The explanation lists each member by its kind, `rule`, `required` or `bound`, and its element path in the expanded model, a bound also naming its member, so a bound a type definition declares is one constraint per field; for each member the witness its removal admitted; the kinds this profile keeps fixed; and every constraint admission fixed, by identity. It names its own contract revision, the one this proposal is handed off at. A model the generator does not answer `solverReportedUnsatWithinBounds` gets the generator's result alone. The row bounds are the generator's UNSAT bounds, and an explanation found below a group's declared repeatability conflicts only within them. A result names an explanation, never the explanation. The byte layout is a12-dmkits'.

## Acceptance gates

1. **Controls.** For each of the four retained control models, [`XUnrelated.json`](../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XUnrelated.json), [`XDisjoint.json`](../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XDisjoint.json), [`XRequired.json`](../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XRequired.json) and [`XBound.json`](../evidence/kernel-31.3.1/captures/q2p9-controls-2026-11-11/XBound.json), under both relations, the explanation is one of those the lock lists: the three `A` rules; either trio; the required role of `A` with both rules; and `NLow`, `maxValue` of `N` and the required role of `N`.
2. **Witness agreement.** Every removal witness of the controls is accepted by the interpreter's replay and, through the existing `:adapter:kernelProbe` route, by kernel 31.3.1 on the reduced model, both strategies agreeing; most of these reduced models are not among the retained single-removal captures, since `S` without a member also lacks every constraint outside `S`, with no message under message-free acceptance and no `ERROR` message under error-free acceptance.
3. **Seeded mutations.** One mutant at each named seam is killed by a control answer: the required role left out of the removable kinds, killed by `XRequired`; the bounds left out, killed by `XBound`; and every removable constraint reported as the explanation, killed by `XUnrelated`, whose removable constraints include `[B] == True`.

## Handback

The committed a12-dmkits revision and the one command that runs gates 1 to 3. Per control and relation: the explanation and its removal witnesses. The mutation kill table. Any semantic disagreement as an a12-dmkits finding with its kernel measurement, which this repository records as inbound provenance rather than as another outbound entry.

## Excluded

Other removable kinds, such as fraction digits, Enumeration values or repeatabilities, which stay fixed; listing every explanation of a model or a smallest one; certified UNSAT; Q1 condition reachability; computations.
