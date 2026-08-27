# Analyze consumer lab

- `status`: green for bounded presence reachability; amber for bounded computation-cycle analysis
- `contract`: a checked artifact produces facts, witnesses, or explicit insufficient information under a named query and bound.
- `authority`: the proof-bearing [presence contradiction analyzer](../../A12Kernel/Elaboration/Flat/PresenceContradiction.lean), its [never-fires theorem](../../A12Kernel/Proofs/FlatPresenceContradiction.lean), and checked flat-condition evaluation.
- `solver`: installed Z3 CLI through canonical SMT-LIB; solver output is never semantic authority.

## First probe

Encode bounded presence reachability for two exact flat conjunctions. The same-field `FieldFilled(A) And FieldNotFilled(A)` query should be solver-UNSAT and the different-field `FieldFilled(A) And FieldNotFilled(B)` query should be SAT. Decode the SAT assignment into an A12 presence witness and replay it through Lean.

Lean acceptance separates the two result directions. Replayed SAT is a verified witness. Raw Z3 UNSAT is only `solverReportedUnsatWithinBounds` unless the existing Lean contradiction certificate independently closes that exact shape. Wrong accounts are authored-error polarity reversal, absence/formal collapse, different-field aliasing, and presenting raw UNSAT as certified.

## Computation-cycle probe

Analyze a disposable language-neutral computation artifact as a target-field dependency graph. Detect a direct two-target cycle and an indirect three-target cycle, recover a dependency order for an acyclic chain even when its supplied order is reversed, and keep `CurrentRepetition(group)` structural rather than expanding it into dependencies on computed descendants. Every cycle path must carry its computation rule and read-site labels; every accepted acyclic order must satisfy all extracted edges.

This remains an Analyze probe rather than another consumer category or a public graph surface. It covers computation value dependencies only. Validation rules read a document snapshot and emit messages, so mutual validation references are not computation feedback cycles. Wrong accounts are pair-only detection, supplied-order rejection in place of cycle analysis, structural-group expansion, omitted precondition reads, and unchecked cycle paths.

## Lab record

| Run | Status | Current result |
|---|---|---|
| `analyze-smt-presence-01` | green | Z3 5.1.0 reported UNSAT for the exact same-field conjunction and SAT with `A = filled`, `B = empty` for the different-field conjunction. Root replay verified the SAT witness through checked Lean evaluation; the existing exact-shape theorem independently certifies that the same-field condition never fires, while raw solver UNSAT remains only `solverReportedUnsatWithinBounds`. All four wrong accounts separated. The disposable consumer used 53 nonblank executable lines, no repository dependency, no semantic guesses, and about 0.03 seconds of solver time. |
| `analyze-computation-cycle-01` | amber | A cold standard-library consumer extracted labeled value dependencies, reported `A → B → A` and `A → C → B → A`, and recovered `Input, B, A` plus `Base, First, Second` for the two acyclic controls. An independently implemented guard re-extracted every edge and checked both cycle paths and topological orders. Pair-only detection, supplied-order rejection, `CurrentRepetition` descendant expansion, and omitted precondition reads were all killed. The probe took 5 minutes, used 357 nonblank executable/test lines, and added no dependency. It remains amber because current Lean owns family-specific dependency projections and supplied-order plan certificates, not a general graph reconstruction that can certify this artifact's extracted edge set; no Kernel correspondence, public graph, or new consumer category is claimed. |
