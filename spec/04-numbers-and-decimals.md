# 04 — Numbers and decimals (§5)

The number type is exact decimal (think `BigDecimal`, never binary floating point), and its two hard parts are:

1. **Scale** — a Number field's declared maximum count of fractional digits — is a *static* property that **gates `==`/`!=` at parse time**, and expression scales are *derived*.
2. **Internal precision** — every comparison rescales to a fixed high precision, and arithmetic runs under a fixed large `MathContext`. Get these constants right or fold-order differences show up as off-by-one-ulp divergences.

Empty-number behaviour (`0` substitution, its exceptions in aggregates) is in [§2](03-empty-and-required.md); this file is about *filled* numbers.

---

## 1. Scale gates `==` / `!=` (checked at parse time)

By default `==` and `!=` are **not permitted** between two numbers whose declared maximum decimal places differ. The rule is **rejected when parsed**, based on the *model-declared* scales — not the runtime values.

```
[Product] == [Factor1] * [Factor2]                       -- REJECTED if scales differ
[Product] == RoundAccounting([Factor1] * [Factor2], 3)   -- permitted (rounding fixes the scale)
```

Multiplication grows scale (two 3-decimal factors ⇒ a 6-decimal product), which is what makes the first form fail. A documented exact-comparison rewrite that dodges the gate: `[F] <= [G] And [G] <= [F]`.

**Four verified boundaries of the gate:**

- A numeric literal is **not globally scale-exempt**. A fractional literal contributes its authored fractional length, while an integer literal is stripped of trailing zeros and can therefore contribute a negative scale. Every literal also carries a separate “multiplicative constant” capability: on `==`/`!=`, the side with the smaller scale may be padded to the larger scale only when that smaller-scale expression carries the capability. Consequently, a scale-2 field may be compared with literal `0`, but a scale-0 field may not be compared with literal `0.00` unless the warning is suppressed.
- **Ordering** (`<`, `<=`, `>`, `>=`) is scale-exempt, even field-vs-field.
- An expression's **derived** scale is what the gate sees. `+`/`−` take the max input scale; `×` adds them; `÷` derives an *unknown* scale (shown as `?`). Power is normally unknown, but a scale-0 base raised to a syntactically simple nonnegative constant exponent derives scale 0. The exponent itself must have a statically known scale no greater than 0; a fractional-scale or unknown-scale exponent is rejected during authoring with `MVK_INVALID_NUMBER_FOR_EXP`. This is a legal-model boundary, not a quiet runtime power result. An `==`/`!=` involving an unknown-scale result is rejected until a rounding gives it a known scale.
- **Strings** compare field-vs-field with `==`/`!=` only; string *ordering* draws `MVK_INVALID_TYPE_FOR_COMPARISON`.

**The one waivable diagnostic.** Beginning a rule condition with `@SuppressWarning(MVK_INVALID_COMPARE_DEC_PLACES)` allows an `==`/`!=` across differing scales (e.g. comparing a checksum). This is the **only** suppressible code — naming any other raises `MVK_INVALID_SUPPRESSED_WARNING`.

> **Lean modelling note.** A complete checked expression needs a static summary containing at least a known signed decimal scale or unknown plus the multiplicative-constant capability; `Option Nat` and “literal means exempt” are insufficient. Fields contribute their declared nonnegative scale without the capability. Literals contribute their authored/stripped scale with the capability. Multiplication adds known scales and OR-propagates the capability, while addition/subtraction take the maximum known scale and preserve the capability only when both sides carry it. The `==`/`!=` well-formedness check is a parse-time predicate over that summary, entirely separate from evaluation.

---

## 2. Rounding

Three rounding families, each with a value-construct variant taking a Number field. Both forms accept an optional `DecimalPlaces` argument: `RoundAccounting([F], n)` and `RoundAccountingValue(F, n)` have the same arithmetic, `n` is an integer **0..14 inclusive**, and omission is exactly `0` decimal places.

- **`RoundDown` / `RoundDownValue`** — target-scale `FLOOR`, toward **−∞**.
- **`RoundUp` / `RoundUpValue`** — target-scale `CEILING`, toward **+∞**.
- **`RoundAccounting` / `RoundAccountingValue`** — to the **nearest**; on an equidistant tie, **away from zero**. ⚠ This is **not** banker's rounding: `RoundAccounting(2.5) = 3`, `RoundAccounting(-2.5) = -3` (banker's would give `2` and `-2`).

The directional bounds apply to the scale-19 `HALF_UP` pre-rounded value consumed by the target-scale step, not necessarily to the raw higher-precision input. A raw value just below `1` can pre-round to `1` and then remain `1` under `RoundDown(..., 0)`.

Worked values (no `DecimalPlaces` argument):

| input | `RoundDown` | `RoundUp` | `RoundAccounting` |
|---|---|---|---|
| `-1.5` | `-2` | `-1` | `-2` |
| `1.777` | `1` | `2` | `2` |
| `-1.777` | `-2` | `-1` | `-2` |
| `2/3` | `0` | `1` | `1` |
| `1.5` | `1` | `2` | `2` |

⚠ For negatives, "down"/"up" follow the **number line**, not magnitude: `RoundUp(-1.777) = -1` (toward zero), `RoundDown(-1.777) = -2` (away).

> **Lean modelling note.** In `Mathlib`/`Std` terms these are: `RoundDown` = `Int.floor`-ward (toward `-∞`) = `RoundingMode.FLOOR`; `RoundUp` = `Int.ceil`-ward = `CEILING`; `RoundAccounting` = `HALF_UP` in the "half away from zero" reading (Java's `RoundingMode.HALF_UP`), **not** `HALF_EVEN`. Name the mode explicitly in the type so the tie rule can't drift.

---

## 3. Arithmetic domain failures are consumer-sensitive

- **Division by zero** produces no numeric value. A validation comparison containing it evaluates to **not-fired** — never an authored error fire.
- **Power** produces no numeric value for some otherwise authorable inputs: `0` to a negative power and an integral exponent outside the inclusive `−1000..1000` range. A validation rule containing one of those runtime domain failures may simply **not fire** — indistinguishable from a satisfied condition unless tested explicitly. The endpoints `−1000` and `1000` are admitted, `−1001` and `1001` fail quietly, and `0 ^ 0 = 1`. A non-integral exponent is not another legal runtime case: the exponent-scale authoring gate rejects it before evaluation.

Power has two precision stages that are observable and must not be replaced with exact rational exponentiation followed by one final round. A positive exponent uses the OpenJDK 21 X3.274 `BigDecimal.pow` numeric-value algorithm: binary exponentiation rounds its intermediate squares and accumulator multiplications at working precision `50 + decimalDigits(exponent) + 1`, then rounds the result to precision 50. For a negative exponent the kernel does **not** use Java's negative-exponent branch: it first computes `1 / base` at precision 50, then applies the same positive-power algorithm to that already-rounded reciprocal. For example, `3 ^ -3` ends in `…7036` under the kernel's reciprocal-first order, while taking the precision-50 reciprocal of `3 ^ 3` ends in `…7037`.

⚠ Division and runtime-invalid integral power are silent only at the **validation-comparison consumer**. A numeric computation must preserve either domain failure through the expression and target boundary. The shared invalid sentinel survives legal numeric `Abs`, `Min`, `Max`, and `RoundAccounting` wrappers rather than becoming an ordinary empty value. For legal shapes such as `RoundAccounting([x] / 0, 2)`, `RoundAccounting(0 ^ -1, 2)`, or `RoundAccounting(2 ^ 1001, 2)`, the Number target is marked invalid with `berechnungsWertFehler`, and a later computation that reads that target is itself poisoned. A fresh target has no computed-value result and a stale target is reported CLEARED, but that delta shape does not make the target cleanly empty. A date-valued consumer is different: `AddDays(StartDate, RoundAccounting([x] / 0, 2))` cannot obtain a day amount and therefore yields a valueless Date, clears a stale date target, and does not attach `berechnungsWertFehler` to that Date target. This is a consuming-operation projection of the same invalid numeric operand, not global erasure of the numeric failure.

> **Lean modelling note.** Arithmetic evaluation is a *partial* operation surfaced as a total result type: `_ / 0`, `0 ^ (neg)`, and out-of-range integral exponents return a domain-failure result rather than Lean's junk rational value. A generic unchecked evaluator may defensively return the same result for a fractional exponent, but checked authoring must reject that shape first and must not present the defensive branch as legal kernel runtime behavior. A validation comparison maps a reached domain failure to not-fired; the checked numeric-computation consumer maps both zero division and runtime-invalid integral power to an invalid numeric target whose dependent reads poison. Date-shift projection is a separate consumer. Do not erase these distinctions into a globally clean `Option.none`.

---

## 4. Other numeric constraints

- **Numeric operand-list `Min`/`Max` admits at most one Number constant.** The list is nonempty, and the constant must be a direct list member rather than a grouped or nested expression. A second constant is rejected during authoring. This restriction belongs to operand-list extrema, not the separately defined `MinValue`/`MaxValue` aggregates.
- **At most one division per plain-arithmetic calculation region** without grouping braces: write `{ [G] / [F] } / 2`. A multiplication/division region counts its own division plus the open contributions of both operands; a count above one is illegal. Addition, subtraction, power, and `{ … }` validate their children as fresh regions and contribute zero to the enclosing region. This is a static legality boundary only: braces around a divided factor do not make that factor opaque to the later evaluation-tree rewrite.
- **An ungrouped power may not be the direct left operand of another power.** Since the concrete grammar is left-associative, this rejects the parser-reachable `a ^ b ^ c`; `{a ^ b} ^ c`, `a ^ {b ^ c}`, and separate powers joined by multiplication are legal. A generic structured tree can represent an ungrouped direct-right power that the parser cannot produce; grammar-shape validation remains a separate precondition and the kernel's check must not be strengthened into a symmetric rule.
- **Rendering must preserve the structured tree even at equal precedence.** A right child with the same arithmetic precedence needs braces even for `+` and `×`: render `a + {b + c}` and `a * {b * c}`, because precision-50 rounding makes those trees observably different from the left-associated parses. The same structural rule retains right-nested subtraction/division, while nested powers need their authored left/right grouping preserved. Braces reset the static authoring walk at the documented boundary; they do not hide the enclosed subtree from runtime lowering or per-node rounding.
- Input numbers may have at most **15 digits** (checked before each validation); internal arithmetic uses higher precision.
- A Number field's scale is **always bounded** — there is *no* unbounded-scale decimal. A model that omits `maxFractionalDigits` gets scale **`0`**, never unbounded, never rejected.
- **Numeric `BaseYear` is the configured model year as a fixed, non-expandable scale-0 source.** A model without a Base Year rejects the source during authoring. Outside an explicitly date-typed source position, `BaseYear` is number-like throughout plain arithmetic and Number computation expressions; evaluating it reads no document field. It is not an authored numeric literal: combining it with a wider-scale literal or expression must preserve the non-expandable side when deriving result-scale admission.
- **Tolerance comparisons** exist only at fixed thresholds — `DiffersWithToleranceRange1 / 2 / 5 / 10` — and fire when the independently normalized operands are **strictly outside** the tolerance: `|R₁₉(a) − R₁₉(b)| > N`, where `R₁₉` is scale-19 `HALF_UP`. A normalized difference of *exactly* `N` does **not** fire. Normalizing the already-subtracted difference is not equivalent. An empty numeric operand reads `0` ([§2](03-empty-and-required.md)); polarity follows the directional `!=` rule after normalization: OMISSION exactly when the currently smaller side can grow or the larger side can shrink toward the closed band ([§12](10-validation-and-polarity.md)). Tolerance accepts number-like operands, including `BaseYear` in its numeric role, and deliberately bypasses the ordinary `==`/`!=` maximum-fractional-digit agreement gate.

> **Operation-wrapper boundary.** The compositional region account above is exact for parser-reachable plain arithmetic. Kernel source shows that the legacy checker descends through operation-valued function wrappers, while a nested grouping/addition/subtraction/power reset aborts the enclosing walk rather than returning a local contribution. Wrapper behavior is therefore ordered and non-compositional; it has no focused portable observation. A clean-room checker must fail closed for that larger surface instead of assuming functions are uniformly transparent or uniformly reset regions until the behavior is characterized.

---

## 5. Internal precision — the constants that must match exactly

These fixed constants decide the last-digit behaviour; a reimplementation must use the same ones or diverge on edge inputs.

- **Every comparison** (ordering, equality, tolerance) rescales **both** operands to **scale 19, `HALF_UP`** before comparing. `Min`/`Max` *selection* stays full-precision (it does not rescale).
- **Every arithmetic node** — `+`, `−`, `×`, `÷`, and the final result of `^` — rounds to a **50-significant-digit `MathContext`, `HALF_UP`**. Addition and subtraction are therefore not universally exact: an intermediate 51-digit result can lose its least significant digit before the enclosing operation runs. The boundary is reachable through high-scale intermediates and is what makes `÷` terminate at all. Power additionally has the working-precision intermediate rounds described in §3; “one precision-50 round after exact exponentiation” is not equivalent.
- **Number `Sum` is an encounter-ordered left fold from zero.** Every reached present value is added under the same 50-significant-digit `HALF_UP` context, including the first value's addition to zero. Reassociation, reordering, an exact rational total followed by one final round, and a parallel reduction are therefore not semantics-preserving in general.
- The evaluated tree is not always the authored tree. Before code generation, the kernel performs exactly one order-sensitive post-order rewrite pass over the original tree. At each multiplication, after its children have been rewritten, only immediate operands whose root is division are collected. Existing non-division operands keep their order and come first; extracted numerators follow in division encounter order, and extracted denominators keep that encounter order. Singleton sides are unwrapped, while multi-factor products are evaluated as left folds. Newly created product nodes are not revisited, so this is neither global algebraic normalization nor a fixed-point rewrite. Thus `a * {b / c}` and `{b / c} * a` both become `{a * b} / c`; left-associated `a * {b / c} * {d / e}` becomes `{{a * b} * d} / {c * e}`; and `x * {{a / b} / c}` becomes `{x * {a / b}} / c` and stops. Because every resulting node rounds independently, an evaluator must execute this exact lowering rather than assume direct authored-tree fold order or flatten factors into an unordered fraction.
- A **scale-19 `HALF_UP` pre-round precedes every target-scale rounding.** A separating consequence is `RoundDown({[q] / 3} + {[q] / 3} + {[q] / 3}, 0) == [q]` for scale-0 `q = 1`: the three independently rounded thirds sum to `1 − 10⁻⁵⁰`; addition prevents the division rewrite from combining them; the scale-19 pre-round produces `1` before the floor to zero places. Flooring the raw sum directly would produce `0`. In contrast, `[q] / 3 * 3` is not a pre-round discriminator because the preceding one-pass division rewrite makes that product exact first.

> **Lean modelling note.** Two viable value representations:
> - **exact rational (`ℚ`)** for arithmetic, with explicit rounding applied at exactly the points above (comparison → scale 19 HALF_UP; every lowered arithmetic node → 50 significant digits HALF_UP; before a target rounding → scale 19 HALF_UP). Significant-digit rounding needs a signed target scale derived from the result's decimal magnitude; fixed scale 50 is not equivalent. Cleanest for *proving* things, but you must not forget the operation-local rounds or the exact one-pass division rewrite — they are semantically load-bearing, not hygiene.
> - **a `BigDecimal` model** (unscaled integer + scale) mirroring the engine directly. Easier to match ulp-for-ulp, harder to reason about.
> Whichever you pick, make the three magic constants (**19**, `HALF_UP`, **50-digit**) named definitions, and property-test the pre-round example above — it is the canonical "did you get the rescale order right" check.

---

## Checklist for §5

- [ ] Scale is a **static** signed-or-unknown attribute paired with multiplicative-constant capability; `+`→max, `*`→sum, `/`→unknown, and the narrow scale-0/simple-nonnegative-power case→0. A power exponent with fractional or unknown derived scale is authoring-rejected with `MVK_INVALID_NUMBER_FOR_EXP`. The `==`/`!=` gate is parse-time and asymmetrically pads only a capable smaller-scale side; ordering alone is scale-exempt.
- [ ] `MVK_INVALID_COMPARE_DEC_PLACES` is the only suppressible diagnostic.
- [ ] Three rounding modes with `RoundAccounting` = **half away from zero** (not banker's); down/up follow the number line after the scale-19 pre-round.
- [ ] Both expression and `…Value` forms accept `DecimalPlaces` **0..14**; omission means exactly `0`.
- [ ] Division-by-zero and runtime-invalid integral power inputs are **total domain failures** in validation: comparison → not-fired. Fractional/unknown-scale exponents are rejected before runtime. Either numeric domain failure survives legal numeric wrappers and reaches a Number target as invalid/formal error plus dependent poison, while a Date shift with the same invalid amount yields a valueless Date. `±1000` and `0^0` are admitted; `±1001` and `0^-1` fail quietly. Positive power follows the staged X3.274 working-precision algorithm; negative power rounds the reciprocal to precision 50 before positive exponentiation.
- [ ] Scale is always bounded (missing `maxFractionalDigits` ⇒ `0`); ≤15 input digits.
- [ ] Numeric operand-list `Min`/`Max` is nonempty and admits at most one direct Number constant; reject a second constant or a grouped/nested constant.
- [ ] Plain arithmetic enforces at most one division per unbraced multiplication/division region and rejects only a direct-left ungrouped nested power; grouping/addition/subtraction/power reset division contribution. Rendering preserves a same-precedence right child with braces, including `+` and `×`, because per-node rounding makes association observable. Treat operation-valued wrappers as unclosed rather than extrapolating a compositional rule.
- [ ] Tolerance uses the fixed 1/2/5/10 thresholds only; independently normalize both operands to scale 19 before testing the **strictly outside** (`> N`) boundary; type a firing with directional `!=` polarity; do not impose the ordinary `==`/`!=` scale-agreement gate.
- [ ] Precision constants and order: comparison rescale **scale 19 HALF_UP**, every lowered arithmetic node **50 significant digits HALF_UP**, Number `Sum` as an encounter-ordered left fold applying that context at every present term, the exact order-sensitive single post-order division rewrite before evaluation (never a global/fixed-point normalization), and a scale-19 HALF_UP **pre-round** before any target rounding.
