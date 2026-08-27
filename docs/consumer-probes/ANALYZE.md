# Analyze consumer lab

- `status`: designed
- `contract`: a checked artifact produces facts, witnesses, or explicit insufficient information under a named query and bound.
- `authority`: the proof-bearing [presence contradiction analyzer](../../A12Kernel/Elaboration/Flat/PresenceContradiction.lean), its [never-fires theorem](../../A12Kernel/Proofs/FlatPresenceContradiction.lean), and checked flat-condition evaluation.
- `solver`: installed Z3 CLI through canonical SMT-LIB; solver output is never semantic authority.

## First probe

Encode bounded presence reachability for two exact flat conjunctions. The same-field `FieldFilled(A) And FieldNotFilled(A)` query should be solver-UNSAT and the different-field `FieldFilled(A) And FieldNotFilled(B)` query should be SAT. Decode the SAT assignment into an A12 presence witness and replay it through Lean.

Lean acceptance separates the two result directions. Replayed SAT is a verified witness. Raw Z3 UNSAT is only `solverReportedUnsatWithinBounds` unless the existing Lean contradiction certificate independently closes that exact shape. Wrong accounts are authored-error polarity reversal, absence/formal collapse, different-field aliasing, and presenting raw UNSAT as certified.

## Lab record

| Run | Status | Current result |
|---|---|---|
| `analyze-smt-presence-01` | designed | Awaiting SMT-LIB consumer, SAT replay, and UNSAT classification. |
