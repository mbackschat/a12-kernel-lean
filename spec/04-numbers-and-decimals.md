# 04 — Numbers and decimals (§5)

The number type is exact decimal (think `BigDecimal`, never binary floating point). Its two hard parts are:

1. **Scale** — a Number field's declared maximum count of fractional digits — is a *static* property: every number-valued expression derives a static scale, and that scale **gates `==`/`!=` at parse time** (§1).
2. **Internal precision** — every comparison rescales to a fixed high precision, and arithmetic runs under a fixed large `MathContext` (§5).

Empty-number behaviour (`0` substitution, its exceptions in aggregates) is in [§2](03-empty-and-required.md); this chapter is about *filled* numbers. How a Number operand's fill directions type a fired message is [§12 §4](10-validation-and-polarity.md#4-the-directional-fill-machinery-behind-the-typing)'s; [the operator reference](14-operator-reference.md) assigns each operator its classes.

## Stored decimal identity and runtime read text depend on the storage regime

**An in-memory Number cell has one of two storage regimes, selected by the actual stored value representation rather than by the field declaration or the consumer, and every evaluation channel reads the one text that regime selects.** A **decimal-valued** placement retains its exact coefficient and scale, so `250.00` and `250` have the same amount but different source identities. A **String-valued** placement is read verbatim.

**The decimal-valued regime derives one formal-read text before evaluation** by stripping fractional trailing zeros, flooring the resulting scale at the declaration's `minFractionalDigits`, rescaling exactly, and rendering in plain notation:

```
readScale = max(value.stripTrailingZeros().scale, minFractionalDigits)
readText  = value.setScale(readScale).toPlainString()
```

Thus a decimal-valued `250.00` in a scale-0 field is read as `250`, the same decimal amount in a field with `minFractionalDigits = 2` is read as `250.00`, and a negative-scale value such as `1E+5` is read as plain `100000`. This evaluation text does not replace the exact decimal identity retained by the document.

**The String-valued regime reads the stored text verbatim**, so the same stored text can receive different formal results by regime: on a `maxFractionalDigits = 0` field, String-valued `250.00` fails with `zahlHatDezimalTrenner` while decimal-valued `250.00` is read as `250` and is clean; on a `minFractionalDigits = 2` field, String-valued `250` fails with `zahlOhneDezimalTrenner` while decimal-valued `250` is read as `250.00` and is clean. Two placements belong to this regime and remain verbatim rather than being silently normalized or dropped: a Number placement whose leading zeros are retained under `leadingZerosAllowed`, and a present nonempty value that failed conversion.

**Every evaluation channel consumes the selected text.** The ordinary formal checker and `FieldValueAsString` see exactly the same text. Number `minLength` and `maxLength` count every character of it, a sign and decimal separator included: decimal-valued `250.00` with `maxFractionalDigits = 2` is read as the three-character `250` and violates `minLength = 4`, while decimal-valued `250` with `minFractionalDigits = 2` is read as the six-character `250.00` and violates `maxLength = 5`. Number semantic-index lookup and uniqueness are numeric relations that normalize their own keys rather than compare this text literally. A Number field has no `pattern` property: a model that supplies one is rejected rather than opening a regex channel over this text.

### Document ingestion

**How the typed JSON document reader turns a native decimal number into node text, and which unquoted values it reads,** is [data model §2.3](01-data-model.md#23-reading-a-document-from-json)'s.

**Quoted text reaching a Number destination is converted by the host's exact decimal grammar, not by the formal-read grammar of §4.8:** an optional `+` or `-`, decimal digits with an optional fraction, and an optional exponent.

- **Digits** are any BMP code unit the host classifies as a decimal digit, so Arabic-Indic `٣.٥` and fullwidth `５` convert to `3.5` and `5`, and `1.5e1` and `0e5` convert.
- **A plus** converts: `+5` converts to `5`, so its plus never reaches the formal checks.
- **Text outside that grammar**, such as `+1,5` or `abc`, keeps its exact text.
- **A leading zero on a `leadingZerosAllowed` field** keeps its exact text even when it would convert. A leading zero is an optional single sign, then `0`, then any character other than `.`. So `007`, `-00`, `+007`, `0e5` and `00e1` are retained there, while `0.5` and `0` convert.
- **The scale** — written fractional digits less the exponent — must fit a 32-bit signed integer, so `1e2147483649` and `1e-2147483648` keep their text and report `zahlHatUngueltigeZeichen`. Inside that range an extreme scale can fault validation as a whole rather than produce a formal finding: `1e2147483648` faults with an arithmetic underflow. Measured: scales of magnitude up to 100,000 (`1e±100000`, and native `1e100000`) convert and report their digit count, `stelligkeitZuLang`; where between 100,000 and the 32-bit bound the fault begins is unmeasured.

Formal codes are locale-independent across `en_US` and `de_DE`.

> **Non-normative implementation note.** Keep the storage regime, exact decimal coefficient/scale, regime-selected formal-read text, and computed-target rendering as distinct facts. Exact decimal identity is needed for scale-sensitive change equality; the formal-read projection is needed by every stored-input evaluation channel; computed target application follows the separate scale-19 rule in [§11 §4.3](09-computations.md#43-number-string-enumeration-and-custom-targets). A single text or unconditional re-rendering cannot preserve both input regimes.

Sources: [source route](../docs/sources/cross-layer-routes.md#src-number-wire-ingestion), [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), [Number ingress checkpoint](../docs/sources/domain-ingestion-probes.md#src-number-ingress-k16).

---

## 1. Scale gates `==` / `!=` (checked at parse time)

**Every number-valued expression carries a static summary: a known signed decimal scale or *unknown*, plus a multiplicative-constant capability. `==` and `!=` compare the two sides' summaries when the rule is parsed, from the model-declared scales and never from runtime values.** The summary is entirely separate from evaluation.

### 1.1 Static scale and the multiplicative-constant capability

**Each number-valued operator derives its result's summary from its operands' summaries by one scale class and one capability class; [column R of the operator reference](14-operator-reference.md#static-scale) assigns each operator its two classes.** A field or operation without the capability is *non-expandable*: under `==`/`!=` it is never padded to a larger scale (§1.2).

| Scale class | Static scale of the result |
|---|---|
| `declared` | a Number field's declared `maxFractionalDigits`, `0` when it is omitted; a `−1` maximum gives an unknown static scale, although its stored values resolve to a fixed count at runtime (§4.7) |
| `authored` | a fractional literal's written fractional digit count; an integer literal's scale after stripping trailing zeros, which can be negative (`100` has scale −2) |
| `integral` | known scale 0 |
| `maximum` | the largest operand scale; unknown when any operand's is unknown |
| `scale sum` | the sum of the operand scales; unknown when either is unknown |
| `unknown` | unknown |
| `power` | 0 when the base has known scale 0 and the exponent is an ungrouped nonnegative numeric literal; unknown otherwise (§1.3) |
| `places` | the authored decimal places, `0` when omitted (§2) |
| `child` | the child's scale |
| `domain` | `0` for a String source; for an Enumeration source the largest number of fractional digits in the selected token domain (§4.5) |

| Capability class | The result carries the capability when |
|---|---|
| `capable` | always |
| `none` | never: the result is non-expandable |
| `every operand` | every operand carries it |
| `either operand` | at least one operand carries it |
| `n/a` | — an unknown-scale result's capability takes part in no gate, since §1.2 refuses an unknown scale whatever the capability |

So two 3-decimal factors make a 6-decimal product; `[A] * 100` over a scale-2 `A` derives scale 0 and stays capable, so it is admitted at declared scales 0, 2 and 4; `Min([A] * 100, [C])` beside a scale-2 field `C` derives scale 2 without the capability; and `[A] * [B]` and `Min([A], [C])` over fields require exact equality.

**Measured scope.** The `declared` and `authored` scales and their capabilities are measured under the gate, as are `scale sum` with `either operand` on `*`, the `maximum` scale on `+` and `-`, `maximum` with `every operand` on operand-list `Min` and the `maximum` scale on operand-list `Max`, `unknown` on `/`, `power`, the `places` scale, the `child` scale of `Abs`, the `domain` scale 0 of a String-source `FieldValueAsNumber` (at a scale-0 target), and the non-expandable `integral` result of `BaseYear` and `RangeAsNumber`; [§6 §2.1](05-dates-and-time.md#21-what-the-operations-produce) records the extractions' and differences' scope. The unknown `declared` scale of a `−1` maximum is measured on fields declaring minimum 2. Such a field is refused `MVK_INVALID_COMPARE_DEC_PLACES` at `==` against itself, at `==` against a second such field and at `!=` against a scale-2 field. It is refused the same way as a computation's source into a scale-2 target and as the target of a scale-2 source, and it is refused `MVK_INVALID_NUMBER_FOR_EXP` as an exponent. Ordering it against a scale-2 field and `RoundAccounting(…, 2)` of it into a scale-2 target are admitted. The same refusal holds for a `−1` maximum beside minimum 0 at `== 1` and against `BaseYear`, on a repeatable row's own fields, inside a `Having` filter, across a `$`-correlated read and a key-joined pair, under `MaxValue`, `Sum`, operand-list `Min` and `FirstFilledValue`, and into a repeatable target from a field copy, a constant, a `Length` or a `NumberOfFilledGroups` count; ordering stays admitted on the row, `Having`, correlated, joined, `MaxValue` and `BaseYear` carriers, and `errorCodesToSuppress` admits a row copy of it. A `−1` minimum beside a maximum of 2 reads `declared` 2. The `none` capability of rounding is measured on `RoundAccounting`: `[P4] == RoundAccounting([P2] * 1, 2)` over scale-4 `P4` is refused while `[P2] == RoundAccounting([P4] * 1, 2)` is admitted; `[P4] == RoundAccountingValue(P2, 2)` is refused as well. `Sum(Rows*/F) == 1.00` and `MaxValue(Rows*/F) == 1.00` over a scale-2 `F` are admitted. Unmeasured: the `every operand` capability of `+` and `-`, the `none` capability of `RoundDown` and `RoundUp`, a `−1` maximum with no declared minimum, `power` for a braced, `-0` or `BaseYear` exponent, the Enumeration-source `domain` scale, the `none` capability of `Sum`, and the `maximum` scale and `none` capability of `MinValue` and `MaxValue`, whose operands are the contributing fields' declared scales.

### 1.2 The equality scale gate and its waiver

**`==` and `!=` admit two equal known scales. Otherwise the side with the smaller known scale is padded to the larger one only when that smaller-scale side carries the capability; a pair with an unknown scale, or whose smaller side is non-expandable, is refused `MVK_INVALID_COMPARE_DEC_PLACES`.** A scale-2 field may therefore be compared with literal `0`, but a scale-0 field may not be compared with literal `0.00` unless the code is waived.

```
[Product] == [Factor1] * [Factor2]                       -- REJECTED if scales differ
[Product] == RoundAccounting([Factor1] * [Factor2], 3)   -- permitted (rounding fixes the scale)
```

A documented exact-comparison rewrite that dodges the gate: `[F] <= [G] And [G] <= [F]`.

- **Ordering** (`<`, `<=`, `>`, `>=`) and the **tolerance comparisons** (§4.6) are scale-exempt, even field-vs-field, and stay exempt inside a `Having` filter, where the waiver below therefore changes nothing for them.
- **Ordering requires orderable operands** ([§6 §1](05-dates-and-time.md#cross-kind-comparison-classes)), so Strings compare field-vs-field with `==`/`!=` only, and String ordering draws `MVK_INVALID_TYPE_FOR_COMPARISON`.
- **A computed target** is admitted by the same predicate, per alternative ([§11 §1.3](09-computations.md#13-the-scale-gate)).

**`MVK_INVALID_COMPARE_DEC_PLACES` is the only waivable diagnostic.** A rule condition beginning with `@SuppressWarning(MVK_INVALID_COMPARE_DEC_PLACES)` allows an `==`/`!=` across differing or unknown scales (e.g. comparing a checksum). Naming any other single name raises `MVK_INVALID_SUPPRESSED_WARNING`, while text that is not one name falls to the lexer or parser first ([concrete syntax §4](12-concrete-syntax.md#4-directives-and-the-special-entities)). A computation waives it through its own `errorCodesToSuppress` property, whose only accepted member this is, and that waiver makes an unknown-scale expression a legal computed source: `[F] ^ [F]` and `[F] ^ Sum(G*/F)` are admitted into a scale-0 target with it and refused without it, and the same waiver admits `[F] / 2`, so it serves every unknown-scale operator.

**The waiver covers the whole text, its `Having` filters included.** A filter comparison meets the same `==`/`!=` gate as the enclosing condition, so `Sum(Rows*/N Having [Rows/N] == 1.5) > 0` over a scale-0 `N` draws `MVK_INVALID_COMPARE_DEC_PLACES` bare and is admitted behind the preamble. Measured members: a filter's literal, field-pair and arithmetic sides, under `Sum`, `NumberOfFilledFields`, `FirstFilledValue` and `NumberOfValueInFields`, and in a computation through `errorCodesToSuppress`. A waived comparison still compares exactly: a scale-0 field never equals `1.5` and always differs from it.

### 1.3 Power scale and the exponent gate

**A power derives scale 0 only when its base has known scale 0 and its exponent is an ungrouped nonnegative numeric literal, a signed literal counting as one literal; every other power derives unknown scale, and no power carries the capability.** The derived scale is never the base's: a scale-2 base under a literal exponent, compared `==` with a scale-2 literal, is refused `MVK_INVALID_COMPARE_DEC_PLACES`, while `[Rate] * [Rate] == 100.00` is admitted on the same model. A negative literal exponent also derives unknown scale and is refused at `==` the same way. Measured: literal, field, grouped-expression and aggregate exponents; a braced literal exponent such as `{2}`, `-0` and a `BaseYear` exponent are unmeasured, and by this rule `{2}` and `BaseYear` derive unknown scale and `-0` derives scale 0.

**The exponent must have a known scale of at most 0; a fractional-scale or unknown-scale exponent is refused during authoring with `MVK_INVALID_NUMBER_FOR_EXP`.** Measured admitted: an integer literal, a negative integer literal, a scale-0 field, compound whole-scale exponents (`{b + c}`, `{b * c}`, `{2 + 3}`), an aggregate over scale-0 fields (`[F] ^ Sum(G*/F)`, which passes the exponent gate and only makes the derived scale unknown; while over a field of scale 2, `[Qty] ^ Sum(Lines*/D2)`, the aggregate is refused `MVK_INVALID_NUMBER_FOR_EXP`), and a braced literal power `[N] ^ {2 ^ 2}`. Measured refused: a fractional literal, a scale-2 field, a field with a `−1` maximum, a division, and a power with a field exponent, so `a ^ {b ^ c}` over fields is refused here although it passes the nesting rule of §4.2. The base is unrestricted in shape: a grouped arithmetic expression and an aggregate are both legal bases.

### 1.4 The constant-pair gate

**A comparison first asks whether both operands are constants; such a pair is refused `MVK_INVALID_COMPARE_TO_CONST` unless the left operand has a temporal result type and exactly one operand is an ungrouped `Today` or `Now`.** The gate precedes the pattern-slot and tolerance-kind gates as well as every ordinary comparison check; passing it still requires the operator's remaining checks.

- **A constant is an immediate written-out literal or `Today`/`Now`.** A sign belongs to the literal, so `1 > 0` and `-1 > 0` are refused. A literal under any operation stops being immediate and one non-immediate side is enough: `1 + 2 > 0` and `1 > 1 + 2` are admitted.
- **Braces preserve constantness** but remove the bare-clock exception: a grouped literal stays a constant, and a grouped `Today` or `Now` counts as a constant that is not an ungrouped clock. The temporal consequences and their witnesses are [§6's](05-dates-and-time.md#comparison-entry-and-grouping).
- **An operand that reads no cell is not thereby a constant.** `BaseYear`, a Base-Year date part such as `YearFromDate(BaseYear)`, and `CurrentRepetition(group)` each clear the gate against a bare literal, and `BaseYear` clears it against `YearFromDate(BaseYear)`. The gate asks what was written, not what is read.
- **`CurrentRepetition` clears it only where it is bound.** `CurrentRepetition(G) > 1` clears the gate only in a rule that binds the coordinate — one whose scope is `G` or a level below it. Written in a rule at an enclosing group, the identical comparison reports `MVK_NO_WILDCARD`, the binding gate of [§9 §3.2](07-repetition-and-iteration.md#32-correlation--and-currentrepetition).
- **Other gates answer first at some sites.** Wrapping a literal in a value function is a different refusal: `Abs(1)` draws the operand-list `MVK_NO_CONST` before this gate is reached. A parenthesised literal, `(1) > 0`, does not parse at this site (`MVK_UNEXPECTED_TOKEN`).

> **Non-normative implementation note.** Carry the summary as `{ scale : known signed integer or unknown, capable : Bool }`; `Option Nat` and "literal means exempt" are insufficient. Run the `==`/`!=` check as a parse-time predicate over the two summaries, separate from evaluation.

Sources: [String integer-source scale](../docs/sources/computation-placement-and-constant-probes.md#src-string-integer-source-scale-suppression), [comparison constant gate](../docs/sources/static-admission-and-class-probes.md#src-comparison-constant-gate-immediacy), [comparison entry gates](../docs/sources/static-admission-and-class-probes.md#src-comparison-entry-gates), [power derived scale](../docs/sources/computation-placement-and-constant-probes.md#src-power-derived-scale-and-operand-shapes), [arithmetic shape gates](../docs/sources/static-admission-and-class-probes.md#src-arithmetic-shape-gates), [node gates](../docs/sources/computation-placement-and-constant-probes.md#src-number-operation-node-gates), [addressed numeric binary computation](../docs/sources/evaluation-and-application-routes.md#src-addressed-numeric-binary), [repeatable numeric wrappers and extrema](../docs/sources/evaluation-and-application-routes.md#src-repeatable-numeric-wrappers-extrema), [repeatable String application](../docs/sources/evaluation-and-application-routes.md#src-repeatable-string-application), [extremum call boundary](../docs/sources/evaluation-and-application-routes.md#src-numeric-extremum-call-boundary), [fieldless numeric computation](../docs/sources/evaluation-and-application-routes.md#src-fieldless-numeric-computation), [Having scale-warning suppression](../docs/sources/having-filter-probes.md#src-having-scale-warning-suppression), [inbound 2026-09-21 corrections](../docs/sources/inbound-handbacks.md#inbound-2026-09-21-corrections), [inbound 2026-10-27](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-27), [unknown-scale and root-index batch](../docs/sources/static-admission-and-class-probes.md#src-unknown-scale-and-root-index).

---

## 2. Rounding

**Three rounding modes, each with an operation form and a field form taking a Number field; both forms accept an optional `DecimalPlaces` argument and have the same arithmetic.** `n` is an integer **0..14 inclusive**, and omission is exactly `0` decimal places. `AbsValue(F)` is likewise the field form of `Abs([F])`.

| Operation form | Field form | Target-scale mode |
|---|---|---|
| `RoundDown` | `RoundDownValue` | `FLOOR`, toward **−∞** |
| `RoundUp` | `RoundUpValue` | `CEILING`, toward **+∞** |
| `RoundAccounting` | `RoundAccountingValue` | to the **nearest**; on an equidistant tie, **away from zero** |

⚠ `RoundAccounting` is **not** banker's rounding: `RoundAccounting(2.5) = 3`, `RoundAccounting(-2.5) = -3` (banker's would give `2` and `-2`).

⚠ For negatives, "down"/"up" follow the **number line**, not magnitude: `RoundUp(-1.777) = -1` (toward zero), `RoundDown(-1.777) = -2` (away).

**The directional bounds apply to the scale-19 `HALF_UP` pre-rounded value consumed by the target-scale step (§5), not necessarily to the raw higher-precision input.** A raw value just below `1` can pre-round to `1` and then remain `1` under `RoundDown(..., 0)`.

Worked values (no `DecimalPlaces` argument):

| input | `RoundDown` | `RoundUp` | `RoundAccounting` |
|---|---|---|---|
| `-1.5` | `-2` | `-1` | `-2` |
| `1.777` | `1` | `2` | `2` |
| `-1.777` | `-2` | `-1` | `-2` |
| `2/3` | `0` | `1` | `1` |
| `1.5` | `1` | `2` | `2` |

**Places admission has two refusal stages after the operand checks.** Once the decimal digit token reaches this stage, its exact nonnegative value is read as a signed 64-bit integer. Values from 15 through `2^63 − 1` report `MVK_INVALID_DIGIT_FOR_ROUNDING`; `2^63` and larger instead report `MVK_INTERNAL_ERROR` from the failed integer read. Leading zeros do not turn an otherwise admitted value into overflow. Both forms and all three modes share this distinction. An immediate literal operation operand or a wrong-type String operand still reports its earlier `MVK_NO_CONST` or `MVK_NO_NUMBER`, even beside an overflowing places argument. Measured on the validation-rule carrier, statically; the computation carrier and runtime rounding are not measured by these rows.

> **Non-normative implementation note.** `RoundDown` is Java's `RoundingMode.FLOOR`, `RoundUp` is `CEILING`, and `RoundAccounting` is `HALF_UP` in its "half away from zero" reading, **not** `HALF_EVEN`. Name the mode explicitly in the type so the tie rule cannot drift.

Sources: [rounding argument](../docs/sources/static-admission-and-class-probes.md#src-rounding-argument), [numeric field forms](../docs/sources/evaluation-and-application-routes.md#src-numeric-field-forms).

---

## 3. Arithmetic domain failures are consumer-sensitive

**Division by zero and a runtime-invalid power produce no numeric value; what that means depends on the consuming construct.**

- **Division by zero** produces no numeric value.
- **Power** produces no numeric value for `0` to a negative power and for an integral exponent outside the inclusive `−1000..1000` range. The endpoints `−1000` and `1000` are admitted, `−1001` and `1001` fail quietly, and `0 ^ 0 = 1`. A non-integral exponent is not another runtime case: the exponent-scale authoring gate (§1.3) rejects it before evaluation.

**At the validation-comparison consumer the failure is silent.** A validation comparison containing a reached domain failure evaluates to **not-fired** — never an authored error fire — so it is indistinguishable from a satisfied condition unless tested explicitly.

⚠ **Division and runtime-invalid integral power are silent only at the validation-comparison consumer.** A numeric computation preserves either domain failure through the expression and the target boundary: the invalid result survives legal numeric `Abs`, `Min`, `Max` and `RoundAccounting` wrappers rather than becoming an ordinary empty value, so legal shapes such as `RoundAccounting([x] / 0, 2)`, `RoundAccounting(0 ^ -1, 2)` and `RoundAccounting(2 ^ 1001, 2)` mark a Number target invalid with `berechnungsWertFehler`, and a later computation that reads that target is poisoned. [§11 §3.2](09-computations.md#32-an-invalidity-clear-poisons) owns that target projection and its change-delta shape; a Date-valued consumer instead yields a valueless Date and attaches no `berechnungsWertFehler` ([§6 §2](05-dates-and-time.md#2-addition-and-difference-are-asymmetric-and-calendar-corrected)).

**Power has two precision stages, and they are observable:** replacing them with exact rational exponentiation followed by one final round changes last digits.

- **A positive exponent `n`** runs binary exponentiation over `n`'s bits from the most significant set bit down. The accumulator starts at `1`; at each bit it is squared, then multiplied by the base when the bit is set. Each squaring and each multiplication is rounded `HALF_UP` to the working precision of `50 + d + 1` significant digits, `d` being `n`'s decimal digit count, and the final accumulator is rounded `HALF_UP` to precision 50. This is the OpenJDK 21 X3.274 `BigDecimal.pow` algorithm.
- **A negative exponent** first computes `1 / base` at precision 50, `HALF_UP`, then applies the positive algorithm to that already-rounded reciprocal with the exponent's magnitude. For example, `3 ^ -3` ends in `…7036` under this reciprocal-first order, while taking the precision-50 reciprocal of `3 ^ 3` ends in `…7037`.

> **Non-normative implementation note.** Surface arithmetic as a *partial* operation with a total result type: `_ / 0`, `0 ^ (neg)` and out-of-range integral exponents return a domain-failure result rather than a junk rational value. A generic unchecked evaluator may defensively return the same result for a fractional exponent, but checked authoring rejects that shape first and the defensive branch is not legal runtime behavior. Do not erase the consumer distinctions into a globally clean `Option.none`.

Sources: [addressed numeric binary computation](../docs/sources/evaluation-and-application-routes.md#src-addressed-numeric-binary).

---

## 4. Other numeric constraints

This section holds the static legality of number-valued operations (§4.1–§4.6), the declared digit quantities and fractional pair (§4.7), and the formal check of a stored value (§4.8).

### 4.1 Arithmetic operand kinds

**`*`, `/`, `-` and `^` each demand a Number of both operands and refuse anything else `MVK_NO_NUMBER_FOR_CALC`; `+` demands neither, admitting two Numbers or two string-like operands and refusing every other pair `MVK_NO_STRING_OR_NUMBER_FOR_ADD`.** String-like means String, a Custom declaration and a predefined type; an Enumeration is string-like under [§7's](06-strings-and-enumerations.md#string-concatenation) display restriction. A Date, a DateRange, a Boolean and a Confirm are neither numeric nor string-like, so they fail both of `+`'s arms. Measured over all seven declared kinds against each of the four numeric operators. An inner operation's **result** type is what the outer operator judges. String concatenation is [§7's](06-strings-and-enumerations.md#string-concatenation).

Sources: [inbound 2026-09-21 corrections](../docs/sources/inbound-handbacks.md#inbound-2026-09-21-corrections), [node gates](../docs/sources/computation-placement-and-constant-probes.md#src-number-operation-node-gates).

### 4.2 Division and power shape

**The division limit (`MVK_TOO_MANY_DIV_FOR_CALC`) is one walk.** The check runs at every arithmetic operator (`+`, `-`, `*`, `/`) and every power, and at no other node: a value-function call, a wrapper and a brace are never themselves checked. At its node it walks that node's subtree in authored order with one "division seen" mark:

- a division sets the mark, and a division met while the mark is set is refused;
- a multiplication or division continues the walk into its left operand, then its right;
- the walk passes through `Abs`, rounding (measured on `RoundDown`) and every operand of an operand-list `Min`/`Max` call, so their operands share the walk;
- a brace, an addition or subtraction, or a power is walked afresh, operand by operand, each starting without the mark, and then **ends the whole walk**, so nothing the walk had not yet reached is counted.

Each node is checked at its own close, so every operand of a call is still checked at its own nodes.

**Without value functions the walk is a region rule.** A multiplication/division region holds at most one division without grouping braces; addition, subtraction, power and `{ … }` start fresh regions. So `a / b / c` and `a / b * c / d` are refused, while `a / b + c / d`, `a / b - c / d`, `{a / b} * {c / d}`, `a / {b / c}`, a division inside a power's operand, and `{ [G] / [F] } / 2` are admitted. The limit is static legality only: braces around a divided factor do not make that factor opaque to the evaluation-tree rewrite of §5.

**With value functions the walk is not compositional.** `Max([a] / [b], [b] / [a])` passes at the root, under a wrapper and inside another call, while `[a] + Max([a] / [b], [b] / [a])` and `[a] * Max(…)` are refused. `[a] / Max({[b]}, [b] / [a])` passes while `[a] / Max([b] / [a], {[b]})` is refused. `[a] + [a] + Max([a] / [b], [b] / [a])` passes, its left addition ending the walk before the call, while `Max([a] / [b], [b] / [a]) + [a] + [a]` is refused. `Max([a] / [b] / [a], [b])` is refused at its own inner node.

**An ungrouped power may not be the direct left operand of another power (`MVK_TOO_MANY_POW_FOR_CALC`).** Powers associate to the left, so this refuses `a ^ b ^ c`; `{a ^ b} ^ c`, `a ^ {b ^ c}` and separate powers joined by multiplication pass this rule, `a ^ {b ^ c}` still meeting the exponent gate of §1.3. The rule is checked at every power node, inside a value function's operands included, while each value-function node separates an outer direct-left-power relation. A structured tree can represent an ungrouped direct-right power that the parser cannot produce; grammar-shape validation is a separate precondition, and the rule is not symmetric.

**Gate order.** Each checked node asks its gates as it closes, left subtree before right and both before their parent: first its operands' typing (§4.1), including a power's exponent scale (§1.3), then the division walk, then the direct-left-power rule. The first failing node decides the class. So `[a] ^ 2 ^ [b]` with a fractional-scale `[b]` draws the exponent class rather than the nesting one, `2 ^ Max([a] / [b], [b] / [a])` the exponent class rather than the division one, and `[a] / [b] / [a] + [s]` with a String `[s]` the division class, its inner division node closing before the addition is typed. The kind check pre-empts the division walk and the nesting rule at the node it types: a text operand in a two-division chain such as `[a] / [s] / [b]` draws `MVK_NO_NUMBER_FOR_CALC`, and a power asks its operands' kinds before its exponent's scale, so a non-numeric exponent (`[a] ^ 2 ^ [s]`) draws `MVK_NO_NUMBER_FOR_CALC` and never `MVK_INVALID_NUMBER_FOR_EXP`. Every such gate answers ahead of the target's scale rule. This does not make every value function legal at every arithmetic position; the child's own authoring grammar and static type remain decisive.

**Rendering preserves the structured tree even at equal precedence.** A right child with the same arithmetic precedence needs braces even for `+` and `*`: render `a + {b + c}` and `a * {b * c}`, because precision-50 rounding makes those trees observably different from the left-associated parses. The same rule retains right-nested subtraction and division, and nested powers keep their authored grouping. Braces reset the static walk at the documented boundary; they do not hide the enclosed subtree from runtime lowering or per-node rounding (§5).

Sources: [arithmetic shape gates](../docs/sources/static-admission-and-class-probes.md#src-arithmetic-shape-gates), [node gates](../docs/sources/computation-placement-and-constant-probes.md#src-number-operation-node-gates), [division walk](../docs/sources/computation-placement-and-constant-probes.md#src-number-operation-division-walk).

### 4.3 Operand-list `Min` and `Max`

**Numeric operand-list `Min`/`Max` is a nonempty ordered list of complete number-like operations with at most one constant per call; a second refuses the call `MVK_TOO_MANY_CONST_FOR_CALC_OP`.** A constant here is an immediate or braced numeric literal: braces do not hide a literal from the call's budget. A literal inside arithmetic, another value function or a nested `Min`/`Max` call is not a constant of the outer list, and every nested call checks its own budget: `Min(Min([A], 1), 2)` and `Min([A] * 1.5, [C], 2)` are admitted, while the flattened `Min([A], 1, 2)` is refused, and `Max(a, b, 2)` is admitted while `Max(a, 1, 2)` is refused. Call boundaries are therefore authored structure and must not be flattened. A literal-only call such as `Min(1.25)` is admitted.

- **The leader must be sortable.** A lone operand of a non-sortable kind draws `MVK_NOT_SORTABLE`: measured on `Max` and `Min` over a String, and on `Max` over a Boolean, a Confirm, an Enumeration (labelled or not), a DateRange and a braced String concatenation. An operand naming nothing answers first, `MVK_INVALID_ENTITY`. Temporal operands are [§6's](05-dates-and-time.md#the-temporal-pair-gate).
- **Static result:** [column R](14-operator-reference.md#static-scale) assigns its class (§1.1).
- **Runtime** evaluates the operands and combines them from left to right in authored order; selection stays full-precision (§5). How an empty operand is read is [§2's](03-empty-and-required.md), and the fill directions are [§12 §4's](10-validation-and-polarity.md#propagation-through-arithmetic-and-the-value-functions).
- A completed call may appear wherever an ordinary number-like operation is admitted, including inside surrounding arithmetic or an operation-form wrapper. This restriction belongs to operand-list extrema, not to the separately defined `MinValue`/`MaxValue` aggregates.

Sources: [arithmetic shape gates](../docs/sources/static-admission-and-class-probes.md#src-arithmetic-shape-gates), [extremum call boundary](../docs/sources/evaluation-and-application-routes.md#src-numeric-extremum-call-boundary), [fieldless numeric computation](../docs/sources/evaluation-and-application-routes.md#src-fieldless-numeric-computation), [node gates](../docs/sources/computation-placement-and-constant-probes.md#src-number-operation-node-gates).

### 4.4 Operation-form wrappers

**The operation-form `RoundDown`, `RoundUp`, `RoundAccounting` and `Abs` wrappers admit any already-checked number-like child except an immediate numeric literal, braced or not.** The admitted children include another wrapper, an independently admitted operand-list `Min`/`Max`, numeric `BaseYear` direct or braced, a direct `FieldValueAsNumber(...)` or `RangeAsNumber(...)`, a numeric field-list aggregate, a Date/Time/DateTime numeric component extraction, a numeric component extracted from direct or range-selected `BaseYear`, and a Date-only month or year difference. Each nested wrapper enforces the literal check on its own child; a larger legal subtree is not rejected merely because it contains constants elsewhere. Numeric `BaseYear` is a number-like operation rather than a literal, so both its direct and braced forms are admitted. A wrapper may be the root or an ordinary operand inside larger arithmetic. An aggregate may sit inside a wrapper or an extremum — `Abs(Sum(G*/F))` and `Min(Sum(G*/F), [X])` are admitted, and `Abs` nests at least three deep — while an aggregate's own operand list takes no expression ([§9 §3.4](07-repetition-and-iteration.md#34-aggregation-consumes-an-ordered-stream)).

- **Evaluation.** Nested wrappers evaluate from the innermost outward in authored order. Rounding maps its complete child's exact result through the ordinary rounding of §2; `Abs` takes the magnitude of the completed child, after an aggregate's ordered fold or an extremum's selection, not per operand.
- **Static result.** [Column R](14-operator-reference.md#static-scale) assigns each wrapper's class (§1.1).
- **Fill directions.** Each wrapper transforms its complete child's directions by [§12 §4's propagation table](10-validation-and-polarity.md#propagation-through-arithmetic-and-the-value-functions).
- **Computation** produces the corresponding staged amount, maps clean missing through scalar sources and all-empty aggregates to the ordinary numeric zero, and preserves an arithmetic domain failure or an exact formal cause through every wrapper.

Sources: [aggregate operand list](../docs/sources/computation-placement-and-constant-probes.md#src-aggregate-operand-list-takes-paths-only), [repeatable numeric wrappers and extrema](../docs/sources/evaluation-and-application-routes.md#src-repeatable-numeric-wrappers-extrema).

### 4.5 Number-valued sources

**Numeric `BaseYear` is the configured model year as a Number source; its static class is [column R's](14-operator-reference.md#static-scale).** A model without a Base Year rejects the source during authoring. Outside an explicitly date-typed source position, `BaseYear` is number-like throughout plain arithmetic and Number computation expressions; evaluating it reads no document field. It is not an authored numeric literal, so combining it with a wider-scale literal or expression never pads its side when the result's scale admission is derived.

**`RangeAsNumber(field, start, end)` is a Number source over one value-validating String-like field without category or wildcard access; its static class is column R's.**

- **Admission** resolves the field shape first, then requires `1 ≤ start ≤ end`, then admits the String value kind.
- **Selection.** The bounds are 1-based and inclusive over the evaluation-normalized String's UTF-16 code units.
- **Value.** A missing source, an end beyond the String, an empty selection, or a selection containing anything other than one nonempty ASCII digit run yields the actual Number `0`; a valid digit run yields its nonnegative integer value. Formal unavailability remains unavailable rather than becoming zero. An operand addressing one row's cell ([§9 §1.10](07-repetition-and-iteration.md#110-field-operations-in-the-guard)) keeps its checked interval and the missing-versus-fallback distinction.
- **Fill directions** are [§12 §4's leaf seeds](10-validation-and-polarity.md#leaf-seeds): the missing-source zero is grow-only, a filled source's zero is fixed. Computation retains the same amount but erases validation fillability before the ordinary Number target path.

**`FieldValueAsNumber(field)` converts one statically numeric String or ordinary closed Enumeration projection into a Number source, of static class `domain` (§1.1).**

- **A String source** must retain value validation, the exact pattern `[0-9]+`, and a written maximum length no greater than 15, an out-of-range `0` or signed count included, while `−1` declares none ([data model §1](01-data-model.md#1-model--a-typed-tree)).
- **An Enumeration source** may use its stored values or one named category, and every token in the selected projection must be an ordinary parsable decimal with at most 15 digits after removing a leading minus and decimal point. That decimal grammar admits an optional leading `-`, at most one `.`, at least one digit, and no trailing `.`, and rejects `+`, exponent notation, whitespace and comma syntax. Its digit predicate is the host's UTF-16 `Character.isDigit(char)`, not ASCII alone: non-ASCII BMP decimal digits such as Arabic-Indic and fullwidth digits are admitted, while a supplementary-plane decimal code point is rejected because its surrogate code units are tested separately. A supplementary token is refused earlier by the BMP-only supported-character declaration gate, so the conversion-stage boundary rests on source reading and has no legal-model witness known.
- **Refused during authoring** rather than assigned a runtime fallback: a table-backed Enumeration, wildcard or repeatable access, and a selected domain containing any non-convertible token.
- **Runtime** first applies the selected stored or category projection and then parses that exact token. A missing source yields the real Number `0`; a filled source yields its exact decimal; formal unavailability remains unavailable. The fill directions are [§12 §4's leaf seeds](10-validation-and-polarity.md#leaf-seeds). An operand addressing one row's cell keeps the checked projection and the domain-derived scale before the conversion. Checked computation erases only fillability and sends the same amount or poison through ordinary numeric arithmetic, generated validation and Number target checking.

**`NumberOfValueInFields(constant In entities...)` counts the filled selected fields equal to the typed constant and returns a Number of the static class column R names.**

- **Admission.** The constant is Number, String, `True` or `False`; the expanded entity list must contain matching Number, value-validating String/Enumeration, Boolean/Confirm-for-`True`, or Boolean-for-`False` fields respectively, with the Enumeration/category-domain and shared Boolean-label checks performed statically. The Boolean kind gate reads every declaration in a group expansion: `True` admits a mixed Boolean/Confirm expansion, while `False` refuses that same expansion and admits the Boolean-only control. Duplicate direct references and group/descendant overlap are rejected; a sole plain field is insufficient, while a group or wildcard may expand to multiple fields.
- **Identity.** Number equality uses the ordinary scale-19 boundary (§5), while the textual families use exact evaluated or stored projection identity.
- **Availability.** An empty cell never substitutes a value, so an empty Number does not match `0`. The first reached formal unavailability suppresses the result. A malformed Boolean retains `feldJaNeinFalsch`, while a malformed Confirm retains the yes-only `feldJaFalsch`.
- **Movement.** The count's headroom and its filter effect are [§12 §4's](10-validation-and-polarity.md#counts-and-headroom) (`count headroom` and `match shrink` in [the operator reference](14-operator-reference.md#having-filter-effect)). Computation retains the same count and reached-read ordering while erasing validation-only movement at the enclosing computation-result projection.
- **Group operands** expand to their fields ([§2](03-empty-and-required.md#the-count-family)). Measured on a fixed nonrepeatable group with exactly two direct declarations: the Boolean-followed-by-Confirm `True` form and the two-Boolean `False` form return `2`, `1` and `0` for two matches, one match and empty input in checked computation, and malformed reached content suppresses the computed count and clears its target; under full validation the Boolean-followed-by-Confirm count is fixed once every declaration is filled. Enumeration/category groups, nested or recursive fixed groups, wider fixed-group arity, other declaration kind or order sequences, legacy raw-document execution and the internal classification order are unmeasured.
- **Capacity.** Rows beyond declared repeatability are outside the operand's domain ([§9 §4.3](07-repetition-and-iteration.md#43-capacity-rows-beyond-the-declared-repeatability)).

Sources: [String integer-source scale](../docs/sources/computation-placement-and-constant-probes.md#src-string-integer-source-scale-suppression), [filtered starred-field capacity](../docs/sources/group-and-iteration-probes.md#src-filtered-starred-field-capacity).

### 4.6 Tolerance comparisons

**Tolerance comparisons exist only at the fixed thresholds of `DiffersWithToleranceRange1`, `2`, `5` and `10`, and fire when the independently normalized operands are strictly outside the tolerance: `|R₁₉(a) − R₁₉(b)| > N`, where `R₁₉` is scale-19 `HALF_UP`.** A normalized difference of exactly `N` does **not** fire. Normalizing the already-subtracted difference is not equivalent. An empty numeric operand reads `0` ([§2](03-empty-and-required.md)). A firing is typed by the directional tolerance arm of [§12 §4's comparison dispatch](10-validation-and-polarity.md#the-comparison-dispatch). Tolerance accepts number-like operands, including `BaseYear` in its numeric role; its scale exemption is §1.2's.

Sources: [tolerance family calibration](../docs/sources/computation-placement-and-constant-probes.md#src-tolerance-family-calibration).

### 4.7 Declared digit quantities and the fractional pair

**Nine distinct quantities count digits, on five different axes. Name the one you mean.** The last two are the declaration's own axis, distinct from the stored-value cascade (§4.8) and from the literal spelling of [concrete syntax §2](12-concrete-syntax.md#2-literals).

| name | value | what it constrains | refused as |
|---|---|---|---|
| `fieldScaleCap` | **14** | the largest declarable `maxFractionalDigits`, and `minFractionalDigits` alike | a codeless refusal stating the bound, and **one** refusal even when both keys breach |
| `fieldScaleOrdering` | refuses exactly `max ≥ 0 ∧ min > max` | the declared fractional interval, where an **absent** member reads as `0` and a **negative** maximum takes the pair out of the comparison | `MVK_FRACT_DIGITS_INVALID` |
| `enteredValueTotalDigits` | **15** | an entered **value**, integer **plus** fractional digits, on **every** number field | `stelligkeitZuLang` |
| `amountIntegerCap` | **15 − scale** | an entered value's integer part, **amount trait only** | `zahlZuvieleVorkommastellen` |
| `literalFracDigits` | **≤ the field's scale** | an authored comparison **literal**, by the scale gate of §1.2, and **waivable** | `MVK_INVALID_COMPARE_DEC_PLACES` |
| `literalTotalDigits` | **ungated** | an authored literal's total length; 16 and 19 digits measured admitted | — |
| `shortestLiftingDecimal` | **17** | *not a gate* — an IEEE-754 property of the conversion chain ([§9 §1.9](07-repetition-and-iteration.md#19-converting-the-comparison-constant)) | — |
| `declarationDigitBudget` | **15** | the **declaration's** own integer places plus its fractional part | `MVK_ARITY_TOO_BIG`; a `maxIntegerDigits` above 15 instead draws a **codeless** verdict, beside which the model is still built and judged ([data model §1](01-data-model.md#1-model--a-typed-tree)) |
| `declarationLengthThreshold` | **`15 + sign + fractional part`** | the declared `minLength`/`maxLength` of a Number field | `MVK_MAX_LENGTH_TOO_BIG` / `MVK_MIN_LENGTH_TOO_BIG`, and `MVK_MAX_LENGTH_TOO_SMALL` below the declared minimum scale |

**`−1` is the declaration's suppression sentinel, not a value.**

- **The ordering row is not `0 ≤ min ≤ max`.** `minFractionalDigits: −1` beside `maxFractionalDigits: 2`, a bare `maxFractionalDigits: −1`, and `minFractionalDigits: 1` beside `maxFractionalDigits: −1` are each **admitted**: `−1` takes the pair out of the comparison instead of being compared as a number. Bounding both endpoints below at `0`, or comparing the members as declared, refuses three models the Kernel takes.
- **The `≤ 14` cap applies to a declared minimum as well as a declared maximum.** Whether a minimum above 14 is reachable beside a negative maximum is unmeasured.
- **The sentinel is what makes "missing" expressible.** An absent member reads as `0` (§1.1) and counts as declared, so `MVK_FRACT_DIGITS_MISSING` needs **both** members written `−1`, and a body declaring neither is admitted. So a declaration carrying `minFractionalDigits: 2` with the maximum omitted is refused `MVK_FRACT_DIGITS_INVALID`, while omitting *both* members is admitted.
- **A suppressed fractional member counts nothing in the two declaration thresholds**: with both at `−1` a `maxLength` of 17 is refused exactly as it is on a body with no fractional part.
- `enteredValueTotalDigits` is a **value** bound, never a literal-length gate: `== 9223372036854775808` carries nineteen digits and is admitted.
- `literalFracDigits` is **at most**, not equality: on a scale-14 field `== 0.5` and `== 0.4` both pass it. A comparison in a rule whose every read iterates additionally classifies the literal by its converted integer form, which refuses `== 0.4` ([§9 §1.8–§1.9](07-repetition-and-iteration.md#19-converting-the-comparison-constant)).

**At runtime the `−1` sentinel resolves into an ordinary fractional pair, with one exception.**

- A `−1` minimum beside a positive maximum reads as minimum `0`.
- A `−1` maximum fixes the count at the minimum `n ≥ 0`, an absent minimum reading as `0`: `minFractionalDigits: 2` beside `maxFractionalDigits: −1` validates stored text as a fixed two-place field, and a bare `maxFractionalDigits: −1` as an integer field. The static scale gate does not read this resolved pair: a `−1` maximum's static scale is unknown (§1.1).
- **The exception** is a `−1` minimum beside a zero maximum, written or absent: stored text then meets neither the separator test nor the fractional-count test, so `1.555` and `-1.5` are valid there while the remaining cascade arms still apply.
- A computation into any of these fields fits its result to the resolved pair; statically a target with a `−1` maximum has unknown scale, so a scale-2 source into it is refused `MVK_INVALID_COMPARE_DEC_PLACES` (§1.2); for the exception that is zero places, read from source and measured only with an integer result.

**A declared `minValue` or `maxValue` reaches the value check as printed text, not as the authored decimal.** Code generation converts the authored bound to its nearest binary64 double and prints that double. When both fractional members are the same `n ≥ 0`, it prints exactly `n` places, rounding the double's shortest decimal half up; otherwise it prints the shortest decimal that reads back to the double, in plain notation without trailing zeros. The stored value is compared with the printed value, so on a fixed two-place field `maxValue: 5.555` admits `5.56` and `0.125` admits `0.13`, on a fixed zero-place field `12.5` admits `13`, and `minValue: 1.00000000000000001` becomes `1`. The printed text is also what the model's own check of the declaration reads ([data model §1.2](01-data-model.md#12-model-consistency-rules)).

Sources: [inbound 2026-09-21 corrections](../docs/sources/inbound-handbacks.md#inbound-2026-09-21-corrections) (the first seven rows measured at a12-dmkits `ee2f5d84`, the last two the peer's), [Number literal leaf grid](../docs/sources/having-filter-probes.md#src-having-number-leaf-grid), [declaration bounds checkpoint](../docs/sources/domain-ingestion-probes.md#src-number-declaration-bounds-k17), [inbound 2026-10-27](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-27).

### 4.8 The formal check of a stored value

**A value's formal checks are an ordered cascade over the regime-selected formal-read text, and the reported refusal is the first one that fails — never the set of all that do.**

**The formal-read grammar.** The cascade first asks two lexical questions of the text:

1. **The plus-signed shape** — a `+`, one or more ASCII digits, and optionally a `.` followed by one or more ASCII digits — reports `zahlMitPlus`.
2. **Otherwise the text must be** an optional `-`, one or more ASCII digits, and optionally a `.` followed by one or more ASCII digits; anything else, an exponent or a plus in another shape included, is unreadable and reports `zahlHatUngueltigeZeichen`.

Measured: the plus shape on kept text (witnesses below) and kept `0e5` and `00e1` reporting the unreadable class. The ASCII-only digit class and the refusal of an empty integer or fraction part are unmeasured. The document-validation route reads this grammar with no presentation information: the decimal separator is `.`, it supplies no optional decimal places (measured by the missing-separator witness below), and this account assumes it supplies no grouping separator, which is unmeasured. The checks can also read caller-supplied presentation information — a grouping separator that is validated and removed first, and a decimal separator and optional decimal places that pad a missing fraction — whose defaults supply none of them. The display-to-internal conversion of user-entered text is a separate host entry point.

**The cascade order:**

| # | Check | Code |
|---|---|---|
| 1 | a plus-signed number | `zahlMitPlus` |
| 2 | unreadable text | `zahlHatUngueltigeZeichen` |
| 3 | the 15-digit total | `stelligkeitZuLang` |
| 4 | a minus on a zero magnitude where zero is allowed and the field is signed | `zahlNullEnthaeltVorzeichen` |
| 5 | a minus on a positives-only field | `zahlMitVorzeichen` |
| 6 | a separator where no fractional place is declared | `zahlHatDezimalTrenner` |
| 7 | a missing separator where fractional places are required | `zahlOhneDezimalTrenner` |
| 8 | the declared fractional-digit range | `zahlFalscheAnzahlNachkommastellen` |
| 9 | the integer-digit cap | `zahlZuvieleVorkommastellen` |
| 10 | a disallowed zero | `zahlIstNull` |
| 11 | a disallowed leading zero | `zahlHatFuehrendeNullen` |
| 12 | the minimum, then the maximum rendered length | `zahlZuKurz`, `zahlZuLang` |
| 13 | the minimum, then the maximum value | `zahlZuKlein`, `zahlZuGross` |

- **The positives-only step has one exception:** a negative zero on an unsigned, zero-forbidding amount field reports `zahlIstNull`, while `-5.00` there keeps the sign class.
- **The integer-digit cap is consulted before both value bounds**, so a value that overflows the cap and the maximum together reports the cap.
- **The 15-digit total outranks every declaration-specific test**, so it reports even on a field whose narrower cap the value also breaches.

**The lexical checks are reached only by a String-valued placement.** A decimal-valued placement's formal-read text never carries a plus, a signed zero, a leading zero or a missing required separator, so the plus, signed-zero and missing-separator refusals arise from text the conversion kept: a retained leading zero (`+007` and `+00.00` report the plus class, `-00` the signed-zero class, and `007` beside two required places the missing-separator class). Kept leading-zero text exists only where leading zeros are allowed, and text outside the conversion grammar fails as unreadable first, so the leading-zero refusal has no document-route witness known; a String-valued placement written directly reaches it.

**The surfaced error code and the rendered error text are chosen on independent axes.** The code is a function of the failing check **alone**. The text additionally depends on the number's *art* — plain, money-with-cents, or money-without-cents — so one code stands behind up to three texts, and the internal message keys are a finer partition than the codes a consumer can observe; codes derived from message keys report distinctions the Kernel does not surface. The money-with-cents text is selected at **exactly two** declared minimum fractional places; one or three places renders money-without-cents text even though the field type is named for cents. Within an art the key also reads the declared sign and, on a plain Number, the fractional shape: unreadable text, a missing separator and a wrong fractional count share one key per art, split on a plain Number into integer-only, variable-range and fixed-scale variants (the last also by sign) and on a money Number by sign; a separator on a money-without-cents field joins that shared key; a plus on an unsigned field selects the sign key; and a disallowed zero selects the plain zero key on every art. Measured: the code axis, the money-place split, and on unsigned declarations a minus selecting each art's sign key, unreadable text selecting the without-sign variants and an excess integer count selecting its key; the other sign splits and the plus key on an unsigned field rest on source reading.

Sources: [Number ingress checkpoint](../docs/sources/domain-ingestion-probes.md#src-number-ingress-k16), [inbound 2026-09-08](../docs/sources/inbound-handbacks.md#inbound-2026-09-08), [cascade code axis](../docs/sources/evaluation-and-application-routes.md#src-number-formal-cascade-code-axis-and-load-canonicalisation), [formal keys 2026-10-24](../docs/sources/domain-ingestion-probes.md#src-k22-formal-keys-wider).

---

## 5. Internal precision — the constants that must match exactly

**Three fixed constants decide the last-digit behaviour — scale 19, `HALF_UP` and a 50-significant-digit `MathContext` — and internal arithmetic uses higher precision than any static gate of §4.** A reimplementation must use the same ones, at the same points, or diverge on edge inputs.

- **Every comparison** (ordering, equality, tolerance) rescales **both** operands to **scale 19, `HALF_UP`** before comparing. `Min`/`Max` *selection* stays full-precision (it does not rescale).
- **Every arithmetic node** — `+`, `−`, `×`, `÷`, and the final result of `^` — rounds to a **50-significant-digit `MathContext`, `HALF_UP`**. Addition and subtraction are therefore not universally exact: an intermediate 51-digit result can lose its least significant digit before the enclosing operation runs. The boundary is reachable through high-scale intermediates and is what makes `÷` terminate at all. Power additionally has the working-precision intermediate rounds of §3; "one precision-50 round after exact exponentiation" is not equivalent.
- **Number `Sum` is an encounter-ordered left fold from zero.** Every reached present value is added under the same 50-significant-digit `HALF_UP` context, including the first value's addition to zero. Reassociation, reordering, an exact rational total followed by one final round, and a parallel reduction are therefore not semantics-preserving in general.
- **The evaluated tree is not always the authored tree.** Before code generation, exactly one order-sensitive post-order rewrite pass runs over the original tree. At each multiplication, after its children have been rewritten, only immediate operands whose root is division are collected. Existing non-division operands keep their order and come first; extracted numerators follow in division encounter order, and extracted denominators keep that encounter order. Singleton sides are unwrapped, while multi-factor products are evaluated as left folds. Newly created product nodes are not revisited, so this is neither global algebraic normalization nor a fixed-point rewrite. Thus `a * {b / c}` and `{b / c} * a` both become `{a * b} / c`; left-associated `a * {b / c} * {d / e}` becomes `{{a * b} * d} / {c * e}`; and `x * {{a / b} / c}` becomes `{x * {a / b}} / c` and stops. Because every resulting node rounds independently, an evaluator must execute this exact lowering rather than assume direct authored-tree fold order or flatten factors into an unordered fraction.
- **A scale-19 `HALF_UP` pre-round precedes every target-scale rounding.** A separating consequence is `RoundDown({[q] / 3} + {[q] / 3} + {[q] / 3}, 0) == [q]` for scale-0 `q = 1`: the three independently rounded thirds sum to `1 − 10⁻⁵⁰`; addition prevents the division rewrite from combining them; the scale-19 pre-round produces `1` before the floor to zero places. Flooring the raw sum directly would produce `0`. In contrast, `[q] / 3 * 3` is not a pre-round discriminator because the preceding one-pass division rewrite makes that product exact first.

> **Non-normative implementation note.** Two viable value representations:
> - **exact rational (`ℚ`)** for arithmetic, with explicit rounding applied at exactly the points above (comparison → scale 19 HALF_UP; every lowered arithmetic node → 50 significant digits HALF_UP; before a target rounding → scale 19 HALF_UP). Significant-digit rounding needs a signed target scale derived from the result's decimal magnitude; fixed scale 50 is not equivalent. Cleanest for *proving* things, but the operation-local rounds and the exact one-pass division rewrite are semantically load-bearing, not hygiene.
> - **a `BigDecimal` model** (unscaled integer + scale) mirroring the engine directly. Easier to match ulp-for-ulp, harder to reason about.
> Whichever you pick, make the three constants (**19**, `HALF_UP`, **50-digit**) named definitions, and property-test the pre-round example above.

Sources: [addressed numeric binary computation](../docs/sources/evaluation-and-application-routes.md#src-addressed-numeric-binary).

---

## Checklist for §5

- [ ] Stored Number input retains its decimal-valued or String-valued regime. Decimal-valued input derives the strip-and-minimum-scale formal-read text; String-valued input, kept leading-zero text and failed conversions included, is read verbatim. Every evaluation channel, including `FieldValueAsString`, consumes that selected text; `minLength`/`maxLength` count all its characters; Number has no pattern property.
- [ ] Quoted document text converts by the host decimal grammar (BMP decimal digits, optional sign and exponent, 32-bit scale), except kept leading-zero text on a `leadingZerosAllowed` field; unquoted values must be JSON numbers.
- [ ] Every number-valued expression carries a static signed-or-unknown scale and a multiplicative-constant capability by the §1.1 scale and capability classes, read per operator from [column R](14-operator-reference.md#static-scale); a power's scale and the exponent gate follow §1.3.
- [ ] The `==`/`!=` gate is parse-time and pads only a capable smaller-scale side; ordering and tolerance are scale-exempt; `MVK_INVALID_COMPARE_DEC_PLACES` is the only waivable diagnostic, by preamble or `errorCodesToSuppress`, and the waiver reaches `Having` filters.
- [ ] An exponent needs a known scale ≤ 0, else `MVK_INVALID_NUMBER_FOR_EXP`.
- [ ] Two constants in one comparison draw `MVK_INVALID_COMPARE_TO_CONST` unless the left is temporal and exactly one is an ungrouped `Today`/`Now`; braces preserve constantness; any operation, `BaseYear`, a Base-Year part and a bound `CurrentRepetition` are not constants.
- [ ] Three rounding modes with `RoundAccounting` = **half away from zero** (not banker's); down/up follow the number line after the scale-19 pre-round; both forms accept `DecimalPlaces` **0..14**, omission meaning exactly `0`; 15 through `2^63 − 1` draw `MVK_INVALID_DIGIT_FOR_ROUNDING` and `2^63` up `MVK_INTERNAL_ERROR`.
- [ ] Division by zero and runtime-invalid integral power (`0^-1`, `±1001`; `±1000` and `0^0` admitted) are not-fired at a validation comparison and poison a Number computation through legal wrappers; positive power follows the staged binary algorithm at working precision `50 + d + 1`, negative power rounds the reciprocal to precision 50 first.
- [ ] `*`, `/`, `-` and `^` need two Numbers (`MVK_NO_NUMBER_FOR_CALC`); `+` needs two Numbers or two string-like operands (`MVK_NO_STRING_OR_NUMBER_FOR_ADD`).
- [ ] The division walk runs at every operator and power and at no call, wrapper or brace, passes through every reached value-function operand, and ends at the first brace, addition, subtraction or power; a direct-left ungrouped power draws `MVK_TOO_MANY_POW_FOR_CALC`; each node asks typing (with the exponent's scale), then the division walk, then the nesting rule. Rendering braces a same-precedence right child.
- [ ] Operand-list `Min`/`Max` is nonempty, admits at most one immediate or braced literal per call (`MVK_TOO_MANY_CONST_FOR_CALC_OP`), budgets each nested call separately, and needs a sortable leader (`MVK_NOT_SORTABLE`).
- [ ] Operation-form rounding/`Abs` admit an already-checked number-like child but refuse an immediate or braced literal at each wrapper boundary; they apply to the completed child.
- [ ] `RangeAsNumber`, `FieldValueAsNumber` and `NumberOfValueInFields` follow §4.5's admission, value and availability rules.
- [ ] Tolerance uses the fixed 1/2/5/10 thresholds only, normalizes both operands to scale 19, and fires only **strictly outside** (`> N`).
- [ ] The nine digit quantities are distinguished by name; `fieldScaleOrdering` refuses exactly `max ≥ 0 ∧ min > max`; `−1` is a sentinel that resolves at runtime into an ordinary pair except a `−1` minimum beside a zero maximum; declared bounds are checked as printed doubles.
- [ ] The formal cascade reports its first failing check in the §4.8 order over the formal-read grammar; the code depends on the check alone and the text also on the art.
- [ ] Precision constants and order: comparison rescale **scale 19 HALF_UP**, every lowered arithmetic node **50 significant digits HALF_UP**, Number `Sum` as an encounter-ordered left fold applying that context at every present term, the exact order-sensitive single post-order division rewrite before evaluation, and a scale-19 HALF_UP **pre-round** before any target rounding.
