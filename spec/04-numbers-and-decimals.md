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

- It applies to **field/expression operands only** — a numeric **literal is scale-exempt** (`== 0`, `== 0.00`, `<= 0.000` are all accepted against any scale). So scale-explicit literals are a rendering nicety, not a correctness requirement.
- **Ordering** (`<`, `<=`, `>`, `>=`) is scale-exempt, even field-vs-field.
- An expression's **derived** scale is what the gate sees. `+`/`−` take the max input scale; `×` adds them; `÷` and `^` derive an *unknown* scale (shown as `?`), so an `==`/`!=` involving them is rejected until you wrap in a rounding.
- **Strings** compare field-vs-field with `==`/`!=` only; string *ordering* draws `MVK_INVALID_TYPE_FOR_COMPARISON`.

**The one waivable diagnostic.** Beginning a rule condition with `@SuppressWarning(MVK_INVALID_COMPARE_DEC_PLACES)` allows an `==`/`!=` across differing scales (e.g. comparing a checksum). This is the **only** suppressible code — naming any other raises `MVK_INVALID_SUPPRESSED_WARNING`.

> **Lean modelling note.** Model scale as a *static, derivable* attribute of an expression, computed by a `scaleOf : Ast → Option Nat` pass (literals → `none`/exempt; field → its declared scale; `a+b` → `max`; `a*b` → sum; `a/b`, `a^b` → `none`-as-unknown). The `==`/`!=` well-formedness check is then a *parse-time* predicate over `scaleOf`, entirely separate from evaluation. This cleanly reflects that the gate never looks at runtime values.

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

## 3. Division by zero and power edge cases evaluate *quietly*

- **Division by zero** is not executed; the comparison containing it evaluates to **`false`** — never an error, never a fire.
- **Power** is not evaluated for some inputs (`0` to a negative power; an exponent outside ±1000), so a rule containing it may simply **not fire** — indistinguishable from a satisfied condition unless tested explicitly.

⚠ Both are *silent*. A reimplementation must make these total (return "not evaluated" / `false`), never throw. A test that only checks the happy path will miss that `[x]/0 > 5` quietly does not fire.

> **Lean modelling note.** Arithmetic evaluation is a *partial* operation surfaced as total: `arith : Ast → Env → Doc → Option Decimal`, where `_ / 0`, `0 ^ (neg)`, and out-of-range exponents return `none`, and a comparison over a `none` operand yields *not-fired*. Do not use Lean's junk-value `x / 0 = 0` — the semantics is "the whole comparison does not fire", which is different from "the quotient is 0".

---

## 4. Other numeric constraints

- **At most one division per calculation** without grouping braces: write `{ [G] / [F] } / 2`. Powers cannot be nested without brackets.
- Input numbers may have at most **15 digits** (checked before each validation); internal arithmetic uses higher precision.
- A Number field's scale is **always bounded** — there is *no* unbounded-scale decimal. A model that omits `maxFractionalDigits` gets scale **`0`**, never unbounded, never rejected.
- **Tolerance comparisons** exist only at fixed thresholds — `DiffersWithToleranceRange1 / 2 / 5 / 10` — and fire when the difference is **strictly outside** the tolerance: `|a − b| > N`. A difference of *exactly* `N` does **not** fire. An empty numeric operand reads `0` ([§2](03-empty-and-required.md)); a fired tolerance comparison types like `==` (either operand's fill can close the band → OMISSION; [§12](10-validation-and-polarity.md)).

---

## 5. Internal precision — the constants that must match exactly

These fixed constants decide the last-digit behaviour; a reimplementation must use the same ones or diverge on edge inputs.

- **Every comparison** (ordering, equality, tolerance) rescales **both** operands to **scale 19, `HALF_UP`** before comparing. `Min`/`Max` *selection* stays full-precision (it does not rescale).
- **Arithmetic** `×` / `÷` / `^` rounds to a **50-digit `MathContext`** (`+` / `−` stay exact). This is reachable through high-scale multiplication and is what makes `÷` terminate at all (a non-terminating decimal is cut to 50 significant digits).
- A **scale-19 `HALF_UP` pre-round precedes every target-scale rounding.** Worked consequence: `RoundDown([q] / 3 * 3, 0) == [q]` fires for `q = 1`, because the internal `0.999…9` pre-rounds to `1.000…` *before* the floor to 0 places yields `1`.

> **Lean modelling note.** Two viable value representations:
> - **exact rational (`ℚ`)** for arithmetic, with an explicit `rescale : ℚ → (scale : Nat) → RoundingMode → ℚ` applied at exactly the points above (comparison → scale 19 HALF_UP; arithmetic result → 50 significant digits; before a target rounding → scale 19 HALF_UP). Cleanest for *proving* things, but you must not forget the rescales — they are semantically load-bearing, not hygiene.
> - **a `BigDecimal` model** (unscaled integer + scale) mirroring the engine directly. Easier to match ulp-for-ulp, harder to reason about.
> Whichever you pick, make the three magic constants (**19**, `HALF_UP`, **50-digit**) named definitions, and property-test the pre-round example above — it is the canonical "did you get the rescale order right" check.

---

## Checklist for §5

- [ ] Scale is a **static** attribute; `scaleOf` derives expression scale (`+`→max, `*`→sum, `/`,`^`→unknown); `==`/`!=` gate is **parse-time**, literal- and ordering-exempt.
- [ ] `MVK_INVALID_COMPARE_DEC_PLACES` is the only suppressible diagnostic.
- [ ] Three rounding modes with `RoundAccounting` = **half away from zero** (not banker's); down/up follow the number line after the scale-19 pre-round.
- [ ] Both expression and `…Value` forms accept `DecimalPlaces` **0..14**; omission means exactly `0`.
- [ ] Division-by-zero and out-of-range power are **total**: comparison → `false`/not-fired, never an error.
- [ ] Scale is always bounded (missing `maxFractionalDigits` ⇒ `0`); ≤15 input digits.
- [ ] Tolerance is **strictly outside** (`> N`); the fixed 1/2/5/10 thresholds only.
- [ ] Precision constants: comparison rescale **scale 19 HALF_UP**, arithmetic **50-digit MathContext**, a scale-19 HALF_UP **pre-round** before any target rounding.
