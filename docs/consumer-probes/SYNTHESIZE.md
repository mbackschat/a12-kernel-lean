# Synthesize consumer lab

- `status`: green
- `contract`: a bounded semantic goal produces a document, rule, repair, or counterexample that Lean can validate; completeness and optimality are separate claims.
- `authority`: checked flat-condition evaluation over the same presence fragment used by the proof-bearing analyzer.
- `solver`: installed Z3 CLI may search, but the decoded witness must replay through Lean.

## First probe

Synthesize a minimal two-field presence assignment that makes `FieldFilled(A) And FieldNotFilled(B)` fire. Decode the solver model into the bounded checked-document projection and replay it through Lean. Ask the same consumer for a witness to the same-field contradiction and require `no witness within the exact finite domain`, not an unqualified impossibility claim.

Wrong accounts are returning a raw solver model, using a formally invalid value to suppress evaluation, claiming minimality from the first model, and translating rule firing as document acceptance.

## Lab record

| Run | Status | Current result |
|---|---|---|
| `synthesize-presence-witness-01` | green | A cold Z3 consumer synthesized and decoded `A = filled`, `B = empty` in the exact two-state domain, labeled the error condition as firing, and classified the same-field UNSAT result only as no witness within that domain. A disposable Lean replay accepted the different-field witness as `.fired .omission`; the existing universal theorem independently excludes every firing polarity for the exact same-field condition. Wrong-account guards rejected reversed rule polarity, a third formal-invalid state, minimality language, and an undecoded raw model. The consumer used 43 nonblank implementation lines plus 18 test lines, Z3 5.1.0, and no repository dependency or semantic guess. |
