# Compile consumer lab

- `status`: green
- `contract`: a checked A12 artifact becomes an executable specialized plan or target program under a named refinement relation.
- `authority`: the shared checked condition-tree evaluator and its [three-valued control-flow capability](../IMPLEMENTATION-MAP.md#cap-shared-condition-tree-control-flow).
- `handover`: the logic/formal-error and computation-order clauses plus a finite admitted source condition.

## First probe

Compile one bounded source-first conjunction over the finite `value`, `empty`, and `formal` observation domain into a standalone specialized decision function. Exhaustively compare every admitted input pair against the Lean-owned truth, poison, and read-order projection.

The finite domain makes exhaustive refinement meaningful for this exact plan. It does not prove a general compiler. Wrong accounts are ordinary Boolean collapse, eager right evaluation, formal-to-false conversion, and reordered reads.

## Lab record

| Run | Status | Current result |
|---|---|---|
| `compile-finite-condition-01` | green | A cold standard-library consumer compiled `FieldFilled(A) And FieldFilled(B)` into a 75-line specialized plan and exhaustively classified all nine `filled`/`empty`/`formal` pairs with exact result, first poison field, and read trace. Boolean collapse, eager right reads, formal-to-false conversion, and operand reversal were all killed. A disposable Lean refinement check proved the compiled result equals the shared computation-condition evaluator for every finite input and checked the complete trace table. Implementation plus tests totaled 117 nonblank lines; no dependency or semantic guess was added. This is refinement of one finite plan, not a general compiler claim. |
