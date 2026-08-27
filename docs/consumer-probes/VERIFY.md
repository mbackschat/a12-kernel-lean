# Verify consumer lab

- `status`: designed
- `contract`: an artifact plus an independently stated claim produces a checked certificate, replayed counterexample, or explicit inconclusive result.
- `authority`: the dependent [presence contradiction witness](../../A12Kernel/Elaboration/Flat/PresenceContradiction.lean) and its [universal never-fires theorem](../../A12Kernel/Proofs/FlatPresenceContradiction.lean).

## First probe

Have an independent consumer emit a minimal certificate containing the claimed field, operand order, and exact root shape for a same-field presence contradiction. A temporary Lean checker reconstructs the dependent witness and accepts only the exact certified shape. A different-field and an `Or` claim must produce counterexamples or rejection rather than a false proof.

This probe tests certificate checking, not output equality. Wrong accounts are trusting a Boolean analyzer flag, accepting a field-name collision without checked identity, generalizing `And` to `Or`, and treating an SMT UNSAT response as a Lean proof.

## Lab record

| Run | Status | Current result |
|---|---|---|
| `verify-presence-certificate-01` | designed | Awaiting isolated certificate producer and temporary Lean checker. |
