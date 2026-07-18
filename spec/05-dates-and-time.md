# 05 — Dates and time (§6)

Dates carry more surprises than any other scalar type. The recurring theme: a date is **not** a canonical instant — it is a value in a *declared format*, with a *precision*, sometimes deliberately imprecise (fragments), and its arithmetic is **asymmetric** (add ≠ inverse of difference) and **calendar-corrected**. And a string literal that *looks* like a date silently *is* one.

Empty-date behaviour (not-evaluated in comparisons; `0` in the extractors/differences; dropped/`no value` in aggregates) is in [§2](03-empty-and-required.md).

---

## 1. Constant format and the string/date literal ambiguity ⚠

Date constants are written **`DD.MM.YYYY`** (day first) regardless of locale; the decimal separator is always `.`. A **string literal that matches the date format is interpreted as a date constant**, which is why it cannot be used in string concatenation:

```
"30.11." + [YearString]        -- invalid: "30.11." is read as a date
"30." + "11." + [YearString]   -- valid: the pieces don't match the date format
```

The literal is typed **by its own syntax, not by context**:

- `[StringField] == "15.06.2024"` is **rejected** (string field vs a date constant).
- a `dd.MM.yyyy` literal compares **chronologically** to a DATE field *whatever the field's stored format*, and rides in argument position: `DifferenceInDays(OrderDate, "01.01.2022")`.
- **inside a value list**, a date-looking entry stays a plain **string**.
- an **ISO-format literal** `"2022-01-01"` is lexed as a **string**, never a date.
- the **omitted-year form** `"13.07."` (trailing dot) injects the model's **Base Year** (a reference year, *not* a floor); a model without a Base Year **rejects** it.

> **Lean modelling note.** Resolve the ambiguity in the **lexer/typer**, not the evaluator: a literal token is classified as `dateConst` iff it matches `DD.MM.YYYY` (or the omitted-year shape), else `strConst`, with ISO shapes always `strConst`. Downstream evaluation then never has to "guess" a literal's kind. This mirrors the engine: the literal is typed by syntax.

---

## 2. Addition and difference are asymmetric and calendar-corrected

`DifferenceInMonths` / `DifferenceInYears` return the **largest whole number of months/years that can be added to the first date without passing the second** — a *floor*, not a calendar count:

```
DifferenceInMonths("31.01.2010", "30.03.2010")   -- returns 1, not 2
```

And addition is not the inverse of difference:

- **`AddYears`** maps the last day of February to the last day of February: `AddYears("28.02.2023", 1) = 29.02.2024`. More precisely it *corrects into* a leap year: `28.02.1999 + 1 year = 29.02.2000` (not the plain `28.02.2000`).
- **`AddMonths`** preserves the *day number* and **clamps** end-of-month overflow to the shorter month's last day, never carrying into the next month: `AddMonths("28.02.2011", 12) = 28.02.2012`; `31.01.2008 + 1 month = 29.02.2008`.
- The two therefore **disagree across a leap-year boundary** — a naive age check built on them is wrong around leap days. **Fractional offsets are truncated, not rounded.**

**Sub-day arithmetic** reduces to integer **seconds since epoch**:

- `AddHours` / `AddMinutes` / `AddSeconds` carry across the day boundary.
- `DifferenceIn{Hours,Minutes,Seconds}(a, b) = (epoch(b) − epoch(a)) / unit`, **truncated toward zero** — a reverse difference of −5 h 30 m is **`-5`**, not `-6`. Argument order is `b − a` (same as `DifferenceInDays`).

> **Lean modelling note.** Implement these as **total** functions on a proleptic-Gregorian calendar model. `AddMonths`/`AddYears` need the explicit end-of-month clamp and the Feb-into-leap-year correction as *code*, not as a library default — most date libraries pick one convention and the kernel mixes them (day-preserving with clamp for months; last-of-February-preserving for years). The sub-day family is cleanest as `Int` epoch-seconds with truncating integer division (`Int.tdiv`, toward zero — **not** `Int.fdiv`).

---

## 3. Constructing dates, and checking validity

`Date(Day, Month, Year)` builds a date from numeric parts (also: a 2-argument form supplying the year from the Base Year, and a 4-argument century form). `Time(...)` and `DateTime(...)` construct the corresponding values. A constructed date is **invalid** if any referenced part is unfilled, or the parts don't form a real calendar date (`Date(31, 11, 2000)` — November has 30 days; or 30 February).

```
Invalid(Date(Day, Month, Year))   -- fires on 31.11, 30.02, an unfilled part, …
```

**`Valid` and `Invalid` are *not* complements**, and the construction has a defined non-value:

- An **unreal `Date(...)` is non-evaluable** — it does *not* roll over and does *not* keep an out-of-range value, so an extractor over it yields nothing.
- `Valid(Date(...))` = all parts present ∧ well-formed ∧ the date is real → fired **VALUE**.
- `Invalid(Date(...))` = parts well-formed ∧ (not real ∨ some part empty). Its polarity is **directional**: an empty fillable part → **OMISSION**, a present-but-unreal date → **VALUE**. It even fires on an **all-empty** row.
- A **malformed** part suppresses **both** predicates (each goes UNKNOWN; the formal error fires instead) — they are complementary only when no part is malformed.
- To fire `Invalid` **only** on a complete-but-impossible date, prefix `AllFieldsFilled(...)`.

`Valid(Field, "CustomTypeName")` is the other form: it runs the project's registered validator for that custom type against the field.

> **Lean modelling note.** Model a constructed date as `Option CalDate` where `none` is the *non-evaluable* unreal/incomplete date — but note `Valid`/`Invalid` are **not** `isSome`/`isNone`: they split the `none` case by *why* (empty part → OMISSION-flavoured, unreal → VALUE-flavoured) and both go UNKNOWN under a malformed part. Encode `Valid`/`Invalid` as two separate predicates reading the construction's *reason*, not as `p`/`¬p`.

---

## 4. The Gregorian floor

**Dates before 16 October 1583 are invalid — as stored or computed *values*.** The floor is always-on and exact:

- strict *before*: `1583-10-15` errors, `1583-10-16` is valid;
- a day-optional value completes its omitted day to `01` **before** the check;
- a **stored** value below it is the formal error `datumFalsch` (suppressing referencing rules, [§3](02-logic-and-formal-errors.md)); a **computed** one is **ERRORED**; a date **range** floors its *start* the same way.
- It is distinct from the *opt-in* "younger than 1900" additional check.

⚠ The floor is **not** a runtime criterion for the `Date(...)` **construction**: `Invalid(Date(1,1,1500))` does **not** fire (in 30.8.1). The floor gates *values*, not the constructor's reality test.

Also: **a date value is stored and formal-checked in its field's declared `format`, not a canonical wire format** — the same calendar date is well-formed in one field and `datumFormatFalsch` in another. A consumer must read each field's `format` to parse its dates.

---

## 5. Time zones and the sub-day difference

`DifferenceInHours/Minutes/Seconds` is **absolute-instant subtraction** — `floor(|instant₂ − instant₁| / unit)`, sign from operand order — computed **identically** by the runtime and by every code-generation target (they all call the one runtime helper; no target inlines its own arithmetic).

Across a **daylight-saving transition** the result depends on the model's configured **`timeZone`** (the DM-JSON key `content.modelConfig.timeZone`; the capitalized `TimeZone` is the *internal* metamodel key code generation copies it into; **default `UTC`**, only other *documented* value `Europe/Berlin` — the code whitelists nothing: unknown ids silently collapse to GMT), applied at *parse time* — **not** on the code-gen target language:

- Under **`UTC`**, the wall-clock gap equals the instant gap.
- Under **`Europe/Berlin`**, two datetimes straddling a transition differ by their *physical* elapsed time: `2024-03-31T01:30:00 → 03:30:00` is `DifferenceInHours = 1` (the skipped 02:00 hour), and `2024-10-27T01:30:00 → 03:30:00` is `3` (the repeated hour).

**The zone applies to every DATE and DATE_TIME parse** — a plain date is midnight in the model zone — through a zone-set, **non-lenient** formatter. That non-lenience gives the two DST edge hours exact, probe-verified laws (kernel 30.8.1):

- **The spring-forward gap is a FORMAL error.** A stored wall time that does not exist (`2024-03-31T02:30:00` under Berlin) draws `datumFormatFalsch` — the non-lenient round-trip rejects it — and suppresses a referencing rule exactly like any malformed value. It is **not** rolled forward.
- **The fall-back ambiguous hour parses as STANDARD time** (CET): `01:30 → 02:30` on `2024-10-27` is `DifferenceInMinutes = 120`, and two stored `02:30` values are instant-equal.
- **Datetime comparison is instant-based too** (`==`/ordering compare the parsed instants), and a **chained `Add{Hours,Minutes,Seconds}` result keeps its exact instant**: `AddHours(01:30 CEST, 1)` lands on the *daylight* side of the ambiguous hour, so it is **not** equal to the equal-looking stored `"02:30:00"` (which re-parses standard) — the pair is 60 real minutes apart. A rendering-based re-parse loses this; the arithmetic is instant-in, instant-out.
- **`AddDays` landings in a special hour never overshoot the direction of travel** (all four combinations probed): a **forward** add resolves the landing with the DAYLIGHT (earlier) instant — a gap landing renders `01:30` CET — and a **backward** add with the STANDARD (later) instant.

> **Lean modelling note.** Carry the time zone in the model (§1 of [`01-data-model.md`](01-data-model.md)). A `UTC`-only implementation matches every `UTC` model and diverges from a `Europe/Berlin` model *only* across DST transitions — an acceptable staged first cut if you record it as a known gap. The faithful version needs the two-zone conversion at datetime construction *plus the edge-hour laws above* (gap ⇒ formal error at the value gate; ambiguous ⇒ standard; instant-space arithmetic so chains keep identity; the no-overshoot day-add landing). The Berlin offset rule to encode is the **current EU rule** (CEST between the last Sundays of March and October, transitions at 01:00Z, in force since 1996) — pre-1996 values follow older tz-database rules only the engine knows; record that boundary explicitly. The peer clean-room encoding (a12-dmkits interpreter, IF128) implements exactly this and is differentially locked (`DstTimeZoneDiffTest`, `WallDayArithmeticDiffTest`, JVM+JS `ModelTimeZoneTest`).

---

## 6. Date fragments and fragment ranges

A **DateFragment** is a deliberately imprecise date (format `MM`, `yyyy`, `yyyy-MM`, `MM-dd`).

- Fragments are **comparable only if both formats include the year or both omit it** (or globally via the Base Year). A missing component defaults to `01`.
- At evaluation a fragment **completes to the earliest concrete date** — missing month → `01`, missing day → `01`, missing year → the declared Base Year — and then compares, shifts, or extracts **as a plain date**. The fragment format decides which `Add*` apply.

A **fragment-format date range** completes its two endpoints **asymmetrically**:

- the **start** to the interval's *earliest* date, the **end** to its *latest* (missing month → `12`, missing day → the month's last day, leap-aware).
- So a `yyyy` range `2024/2025` denotes `2024-01-01 .. 2025-12-31`.

**Day-optional dates** (a `DateType` with `datePrecision: DAY_OPTIONAL`) omit the day as a literal `00` in the day position — `00.06.2024` is the *only* well-formed omission shape. Such a value is not a single concrete date; `ValueAsDate(field, FirstDay|LastDay)` resolves it (day `01` / the month's last day; a full value resolves to itself). `ValueAsDate` is valid **only** as a direct comparison operand.

> **Lean modelling note.** Model a fragment as `(present-components, format)` and give it a single `completeEarliest : Fragment → CalDate` plus, for ranges, a `completeLatest`. Keep completion a *pure* function separate from comparison, so a fragment "becomes a date" at exactly one place. The start/end asymmetry for ranges is the subtle bit — two different completion functions, chosen by endpoint position.

---

## 7. The point-in-time and reference sources

- `Today` ignores the time of day — more precisely, it truncates the validation instant to midnight **in the model zone** (a zone-set calendar), so under `Europe/Berlin` the day boundary is Berlin midnight, not UTC midnight. `Now` is the raw validation instant. `Now` is **not recommended with `==`** and is **forbidden in computations** (a time-dependent computed value would immediately disagree with itself; [§11](09-computations.md)). `Now` compares only to an operand whose format carries a *time* component — against a plain date field the rejection fires at **code generation**, not at the parse/consistency check.
- **`BaseYear` is polymorphic by the other operand:** against a **date** it is the base-year *start* (`2020-01-01`); against a **number** it is the year *number* (`2020`); as a range source, `StartOfDateRange(BaseYear)` / `EndOfDateRange(BaseYear)` are `01.01` / `31.12` of the reference year. It is *model config*, not the clock; **VALUE** polarity.

> **Lean modelling note.** Inject the clock (`Today`/`Now`) as an explicit parameter — a `PointInTime` in the evaluation environment — never a global read. This keeps `eval`/`compute` pure and deterministic (essential for reproducible property tests and for the "compute is a function" stance of [`01-data-model.md`](01-data-model.md)). `BaseYear` is model config, resolved by the *other operand's kind* — a small dispatch, not a clock read.

---

## 8. Date ranges and overlap

Date ranges support only `==` / `!=` (**no ordering**), and `DateRange(...)` **cannot be nested** inside other constructs. Overlap tests treat endpoints as **inclusive (closed intervals)**.

The two overlap predicates differ in **shape** ⚠:

- **`DateRangesOverlap(op0, op1, …)`** is **any-pair** among *all* operands' kept, filled ranges (one growing set): a list-internal pair fires even when a scalar operand is disjoint, and a same-cell self-pair via scalar + star fires on every filled row.
- **`AtLeastOneDateRangeOverlaps(scalar In list…)`** is genuinely **scalar-vs-list**: two list cells overlapping *each other* do **not** fire.

For both: intervals are **closed** (back-to-back periods sharing a boundary day overlap); an **inverted** range (start after end) **never** overlaps; empty/malformed cells are **skipped**.

---

## 9. DateTime rides the date-format definition — but the operand gates are PER-OPERATOR ⚠

The date **extractors** (`DayFromDate`, …) accept a DateTime operand and see its **DATE part** (times ignored). Beyond the extractors, the earlier blanket claims ("differences see the date part; arithmetic is rejected") are **wrong per-operator** — probe-corrected (kernel 30.8.1, 2026-07-18):

- **`DifferenceInDays` accepts DateTime operands and is TIME-OF-DAY AWARE**: the count of whole **wall-clock** days (Δ wall-seconds / 86 400, truncated toward zero) — `23:00 → 01:00` next day is **0** days, *not* the date-part 1; a DST-shortened 23-real-hour Berlin day still counts as **1** wall day (wall basis, not instants). **Mixed `(datetime, date)` pairs are legal** — the date reads as midnight.
- **`DifferenceIn{Months,Years}` REJECT a DateTime operand** at code generation (`MVK_WRONG_DATE_FORMAT_FOR_OP`) — date-only.
- **`AddDays` accepts a DateTime operand and is TIME-PRESERVING** (`15T22:00 + 1 = 16T22:00`); a special-hour landing follows the no-overshoot rule (§5). **`AddMonths` / `AddYears` REJECT a DateTime operand** at code generation.
- **`DifferenceIn{Hours,Minutes,Seconds}` REJECT a plain DATE operand** — DateTime-only, mirror-image of the months/years gate.

---

## Checklist for §6

- [ ] Literal kind (`dateConst` vs `strConst`) resolved at **lex/type** time by shape; ISO always a string; omitted-year needs a Base Year.
- [ ] `AddMonths` (day-preserving + end-of-month clamp) vs `AddYears` (last-of-Feb-preserving, corrects into leap years) — **different** conventions; fractional offsets truncated.
- [ ] Sub-day diffs = epoch-seconds `/ unit`, **truncated toward zero**, order `b − a`.
- [ ] `Valid`/`Invalid(Date(...))` are **not** complements; unreal date = non-evaluable; malformed part suppresses both; `Invalid` directional polarity; fires on all-empty.
- [ ] **Gregorian floor** at 1583-10-16 on *values* (stored → `datumFalsch`, computed → ERRORED), day-optional completes day first; **not** applied to the `Date(...)` constructor's reality test.
- [ ] Dates stored/checked in the field's **declared format**.
- [ ] Sub-day differences AND datetime comparison honour the model **time zone** (UTC default, Europe/Berlin) across DST — instant-based, with chained `Add*` keeping instant identity; clock injected, not read globally.
- [ ] Berlin edge hours: a spring-gap wall time is `datumFormatFalsch` (formal error, suppresses); the ambiguous fall-back hour parses as **standard** time; `AddDays` special-hour landings never overshoot the travel direction.
- [ ] Per-operator DateTime gates: `DifferenceInDays`/`AddDays` accept DateTime (time-aware wall-day count / time-preserving add); `DifferenceIn{Months,Years}`/`AddMonths`/`AddYears` reject it; `DifferenceIn{Hours,Minutes,Seconds}` reject a plain DATE.
- [ ] Fragment completion: earliest for a value/start, latest for a range end (leap-aware); day-optional `00`; `ValueAsDate` only as a direct comparison operand.
- [ ] Ranges: `==`/`!=` only, no nesting, closed intervals; `DateRangesOverlap` (any-pair, growing set) vs `AtLeastOneDateRangeOverlaps` (scalar-vs-list); inverted never overlaps.
