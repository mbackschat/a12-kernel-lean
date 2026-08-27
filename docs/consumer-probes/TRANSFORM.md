# Transform consumer lab

- `status`: designed
- `contract`: a checked A12 artifact becomes another checked A12 artifact under an explicitly named observation relation and preconditions.
- `authority`: [addressed numeric-operation consumer laws](../../A12Kernel/Proofs/AddressedNumericOperationConsumer.lean), especially universal identity preservation of Analyze, Execute, and rich result views.
- `handover`: the [bounded numeric-operation capability](../implementation/numeric-and-temporal.md#cap-addressed-numeric-operation-consumer) and its explicit rule that fingerprint difference is not semantic inequivalence.

## First probe

Implement the exact identity Transform over one checked addressed numeric operation and validate its structural fingerprint. Then reject a tempting nonidentity rewrite that changes operation parameters while retaining source and target fields. The point is to experience the difference between producing a plausible rewrite and carrying a preservation relation.

Lean acceptance is universal identity preservation from the existing theorems plus one checked parameter-change counterexample. Wrong accounts are dependency-only identity, derived-scale-only identity, fingerprint equality as general equivalence, and finite example agreement as a universal preservation claim.

## Lab record

| Run | Status | Current result |
|---|---|---|
| `transform-numeric-identity-01` | designed | Awaiting isolated implementation and Lean reconciliation. |
