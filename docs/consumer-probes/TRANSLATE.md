# Translate consumer lab

- `status`: green
- `contract`: one admitted source decision becomes either a checked target representation, an exact rejection, or an explicit approximation/refusal under a stated preservation direction.
- `authority`: the [computed-target diagnostic consumer](../../A12Kernel/Conformance/ComputationTargetDiagnosticConsumer.lean) and family-owned static diagnostic projections.
- `handover`: numeric and String computation clauses, the measured diagnostic boundary, and typed unsupported outcomes.

## First probe

Translate bounded Number and String computed-target authoring attempts into `accepted`, exact Kernel diagnostic code, or typed local refusal. The consumer must preserve the distinction between decimal-scale rejection and calculated-field self-reference, including suppression exposing the later self-reference, while never inventing an external code for an unmapped refusal.

Lean acceptance is equality of the closed translated decision, not evaluator output. Wrong accounts are mapping every refusal, collapsing unmapped refusal into acceptance, choosing self-reference before the measured scale gate, and treating suppression as admission.

<a id="task-non-operation"></a>
## `Non<Operation>` lowering probe

Given a condition text in the `Non<Operation>` extension, written in English, produce the Kernel-language text it lowers to, or refuse it naming the predicate whose twin does not exist. The handover is the [negation use case](../USE-CASES.md#cross-category-use-case-negation), the [rule-negation capability record](../implementation/validation-messages-and-custom.md#cap-rule-negation), and the [concrete syntax](../../spec/12-concrete-syntax.md); the consumer receives no Lean source, no Kernel, and no expected output.

The fixture is the 20 inputs below. Lean acceptance parses each answer with `parseText`, requires the tree to equal the Lean `lowerNon` result over `parseNonText` up to parentheses that change no grouping and regrouping within one connective, and requires each refusal to name the predicate Lean refuses. The probe is green when all 20 agree and every wrong account below is killed by at least one named input.

| id | input |
|---|---|
| `X01` | `NonFieldFilled(A)` |
| `X02` | `NonFieldFilled(A) And [B] > 1` |
| `X03` | `NonAllFieldsFilled(A, B, C) Or NonGroupFilled(G)` |
| `X04` | `NonFieldsNotCollectivelyFilled(A, B) Or FieldFilled(C)` |
| `X05` | `FieldFilled(X) And (NonFieldFilled(A) Or NonGroupsNotCollectivelyFilled(G, H))` |
| `X06` | `NonMoreThanOneFieldFilled(A, B, C) And FieldFilled(D)` |
| `X07` | `NonNotExactlyOneFieldFilled(A, B)` |
| `X08` | `NonNoFieldFilled(Rows*/R)` |
| `X09` | `NonAtLeastOneFieldValueIncludedInValueList(A, B In "x", "y")` |
| `X10` | `NonFieldValueIncludedInValueList(Kind, "AB", "CD")` |
| `X11` | `NonValid(Date(D, M, Y))` |
| `X12` | `NonInvalid(Date(D, M, Y)) And [D] > 3` |
| `X13` | `NonValid(Iban, "IBAN")` |
| `X14` | `NonFieldValuesNotUnique(A, B)` |
| `X15` | `NonDateRangesOverlap(P1, P2) Or FieldFilled(A)` |
| `X16` | `[NonFieldFilled] == 1` |
| `X17` | `NumberOfFilledFields(NonFieldFilled, B) == 1` |
| `X18` | `NonGroupFilled(Address) And [Amount] <= 0` |
| `X19` | `FieldNotFilled(A) Or [B] != "x"` |
| `X20` | `NonNotAllGroupsFilled(G, H)` |

Wrong accounts and the inputs that kill them: a twin negating its surrounding conjunction or disjunction instead of itself (`X02`, `X06`, `X18`); a compound complement left unparenthesized where it would mix `And` and `Or` (`X05`); a twin invented for a predicate without a complement (`X13` to `X15`); `NonValid(Field, "Type")` lowered to `Invalid` (`X13`); a double negative such as `NonNoFieldFilled` or `NonNotAllGroupsFilled` lowered to anything but the positive predicate (`X08`, `X20`); a `Non`-prefixed name that is not a call read as a twin (`X16`, `X17`); a condition without twins changed (`X19`).

Excluded: German spellings, for the reason the [rule negation probe](TRANSFORM.md#task-rule-negation) gives; static legality; messages, polarity and evaluation; Kernel correspondence beyond what the capability record cites.

## Lab record

| Run | Status | Current result |
|---|---|---|
| `translate-target-diagnostic-01` | green | A cold standard-library consumer translated all eight bounded Number and String attempts in 128 seconds. It preserved scale rejection before self-reference, suppression exposing the later self-reference, two accepted controls, exact mapped direct/range String codes, and typed local refusals for Number `Abs(target)` and String concatenation without inventing external diagnostics. All four wrong accounts were killed. The closed matrix then matched the Lean diagnostic consumer exactly. The disposable implementation and tests used 170 nonblank lines, no external dependency, and no semantic or external-code guess. |
