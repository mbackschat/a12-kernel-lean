# Synthesize consumer lab

- `status`: designed
- `contract`: a bounded semantic goal produces a document, rule, repair, or counterexample that Lean can validate; completeness and optimality are separate claims.
- `authority`: checked flat-condition evaluation over the same presence fragment used by the proof-bearing analyzer.
- `solver`: installed Z3 CLI may search, but the decoded witness must replay through Lean.

## First probe

Synthesize a minimal two-field presence assignment that makes `FieldFilled(A) And FieldNotFilled(B)` fire. Decode the solver model into the bounded checked-document projection and replay it through Lean. Ask the same consumer for a witness to the same-field contradiction and require `no witness within the exact finite domain`, not an unqualified impossibility claim.

Wrong accounts are returning a raw solver model, using a formally invalid value to suppress evaluation, claiming minimality from the first model, and translating rule firing as document acceptance.

## Lab record

| Run | Status | Current result |
|---|---|---|
| `synthesize-presence-witness-01` | designed | Awaiting isolated witness generator and Lean replay. |
