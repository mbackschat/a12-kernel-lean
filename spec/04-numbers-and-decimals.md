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
- An expression's **derived** scale is what the gate sees. `+`/`−` take the max input scale; `×` adds them; `÷` derives an *unknown* scale (shown as `?`). Power is normally unknown, but a scale-0 base raised to a syntactically simple nonnegative constant exponent derives scale 0. The exponent itself must have a statically known scale no greater than 0. An `==`/`!=` involving an unknown-scale result is rejected until a rounding gives it a known scale.
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
- **Power** produces no numeric value for some inputs (`0` to a negative power; a non-integral exponent; an exponent outside ±1000), so a validation rule containing it may simply **not fire** — indistinguishable from a satisfied condition unless tested explicitly. The endpoints `−1000` and `1000` are admitted, and `0 ^ 0 = 1`.

Power has two precision stages that are observable and must not be replaced with exact rational exponentiation followed by one final round. A positive exponent uses the OpenJDK 21 X3.274 `BigDecimal.pow` numeric-value algorithm: binary exponentiation rounds its intermediate squares and accumulator multiplications at working precision `50 + decimalDigits(exponent) + 1`, then rounds the result to precision 50. For a negative exponent the kernel does **not** use Java's negative-exponent branch: it first computes `1 / base` at precision 50, then applies the same positive-power algorithm to that already-rounded reciprocal. For example, `3 ^ -3` ends in `…7036` under the kernel's reciprocal-first order, while taking the precision-50 reciprocal of `3 ^ 3` ends in `…7037`.

⚠ Division's domain failure is silent only at the **validation-comparison consumer**. A computation must preserve it through the expression and target boundary. For the legal `RoundAccounting([x] / 0, 2)` shape, rounding preserves the invalid result, the target is marked invalid with `berechnungsWertFehler`, and a later computation that reads that target is itself poisoned. A fresh target has no computed-value result and a stale target is reported CLEARED, but that delta shape does not make the target cleanly empty. The computation projection of invalid power inputs remains to be audited separately.

> **Lean modelling note.** Arithmetic evaluation is a *partial* operation surfaced as a total result type: `_ / 0`, `0 ^ (neg)`, and out-of-range exponents return a domain-failure result rather than Lean's junk rational value. A validation comparison maps that result to not-fired; the checked division-computation consumer maps zero division to an invalid target whose dependent reads poison. Do not erase the distinction into a globally clean `Option.none`, and do not infer the unchecked power-computation projection from the shared pure result.

---

## 4. Other numeric constraints

- **At most one division per calculation region** without grouping braces: write `{ [G] / [F] } / 2`. Addition/subtraction, power, and `{ … }` establish separate regions for this check. Powers cannot be nested without braces.
- Input numbers may have at most **15 digits** (checked before each validation); internal arithmetic uses higher precision.
- A Number field's scale is **always bounded** — there is *no* unbounded-scale decimal. A model that omits `maxFractionalDigits` gets scale **`0`**, never unbounded, never rejected.
- **Tolerance comparisons** exist only at fixed thresholds — `DiffersWithToleranceRange1 / 2 / 5 / 10` — and fire when the difference is **strictly outside** the tolerance: `|a − b| > N`. A difference of *exactly* `N` does **not** fire. An empty numeric operand reads `0` ([§2](03-empty-and-required.md)); a fired tolerance comparison types like `==` (either operand's fill can close the band → OMISSION; [§12](10-validation-and-polarity.md)).

---

## 5. Internal precision — the constants that must match exactly

These fixed constants decide the last-digit behaviour; a reimplementation must use the same ones or diverge on edge inputs.

- **Every comparison** (ordering, equality, tolerance) rescales **both** operands to **scale 19, `HALF_UP`** before comparing. `Min`/`Max` *selection* stays full-precision (it does not rescale).
- **Every arithmetic node** — `+`, `−`, `×`, `÷`, and the final result of `^` — rounds to a **50-significant-digit `MathContext`, `HALF_UP`**. Addition and subtraction are therefore not universally exact: an intermediate 51-digit result can lose its least significant digit before the enclosing operation runs. The boundary is reachable through high-scale intermediates and is what makes `÷` terminate at all. Power additionally has the working-precision intermediate rounds described in §3; “one precision-50 round after exact exponentiation” is not equivalent.
- The evaluated tree is not always the authored tree. Before code generation, multiplication containing divided factors is normalized by collecting numerators and denominators: `a * {b / c}` becomes `{a * b} / c`, and `a * {b / c} * {d / e}` becomes `{a * b * d} / {c * e}`. Because every resulting node rounds independently, an evaluator must lower through this normalization rather than assume direct authored-AST fold order.
- A **scale-19 `HALF_UP` pre-round precedes every target-scale rounding.** Worked consequence: `RoundDown([q] / 3 * 3, 0) == [q]` fires for `q = 1`, because the internal `0.999…9` pre-rounds to `1.000…` *before* the floor to 0 places yields `1`.

> **Lean modelling note.** Two viable value representations:
> - **exact rational (`ℚ`)** for arithmetic, with explicit rounding applied at exactly the points above (comparison → scale 19 HALF_UP; every lowered arithmetic node → 50 significant digits HALF_UP; before a target rounding → scale 19 HALF_UP). Significant-digit rounding needs a signed target scale derived from the result's decimal magnitude; fixed scale 50 is not equivalent. Cleanest for *proving* things, but you must not forget the operation-local rounds or the division normalization — they are semantically load-bearing, not hygiene.
> - **a `BigDecimal` model** (unscaled integer + scale) mirroring the engine directly. Easier to match ulp-for-ulp, harder to reason about.
> Whichever you pick, make the three magic constants (**19**, `HALF_UP`, **50-digit**) named definitions, and property-test the pre-round example above — it is the canonical "did you get the rescale order right" check.

---

## Checklist for §5

- [ ] Scale is a **static** signed-or-unknown attribute paired with multiplicative-constant capability; `+`→max, `*`→sum, `/`→unknown, and the narrow scale-0/simple-nonnegative-power case→0. The `==`/`!=` gate is parse-time and asymmetrically pads only a capable smaller-scale side; ordering alone is scale-exempt.
- [ ] `MVK_INVALID_COMPARE_DEC_PLACES` is the only suppressible diagnostic.
- [ ] Three rounding modes with `RoundAccounting` = **half away from zero** (not banker's); down/up follow the number line after the scale-19 pre-round.
- [ ] Both expression and `…Value` forms accept `DecimalPlaces` **0..14**; omission means exactly `0`.
- [ ] Division-by-zero and invalid power inputs are **total domain failures** in validation: comparison → not-fired. Division-by-zero computation → invalid/formal error and dependent poison; invalid-power computation projection remains pending. `±1000` and `0^0` are admitted. Positive power follows the staged X3.274 working-precision algorithm; negative power rounds the reciprocal to precision 50 before positive exponentiation.
- [ ] Scale is always bounded (missing `maxFractionalDigits` ⇒ `0`); ≤15 input digits.
- [ ] Tolerance is **strictly outside** (`> N`); the fixed 1/2/5/10 thresholds only.
- [ ] Precision constants and order: comparison rescale **scale 19 HALF_UP**, every lowered arithmetic node **50 significant digits HALF_UP**, division-bearing multiplication normalization before evaluation, and a scale-19 HALF_UP **pre-round** before any target rounding.
