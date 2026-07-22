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

The calendar basis of the operand is observable, and no one calendar implementation applies to every temporal consumer. A real value produced by `Date(...)` retains the constructor's model-zone legacy hybrid-calendar identity through legal `AddDays`/`AddMonths`/`AddYears` and `DifferenceInDays`/`DifferenceInMonths`/`DifferenceInYears` consumers. Stored values, fragments, ranges, and each other operation remain governed by their separately stated clauses; this constructed-value rule does not classify them globally. A constructed-Date month/year shift whose nominal field-preserving landing lies in the missing `1582-10-05..14` cutover labels normalizes forward by ten civil labels. Thus `1582-09-10 + 1 month = 1582-10-20`, `1581-10-10 + 1 year = 1582-10-20`, and from `1582-09-10` the constructed dates 15 October and 20 October are respectively zero and one whole month away. From `1581-10-10`, 15 October 1582 is zero whole years/11 whole months away, while 20 October is one year/12 months away. The `AddYears` February-28 correction itself uses Gregorian leap status even on the Julian side: `1499-02-28 + 1 year = 1500-02-28`, although `Date(29, 2, 1500)` is constructible there.

A date shift whose numeric amount is a domain-invalid expression has no amount to apply. For example, `AddDays(StartDate, RoundAccounting([x] / 0, 2))` yields a valueless Date and clears a stale Date target; it does not attach the numeric `berechnungsWertFehler` to that Date target. This is a Date-consumer projection of the invalid numeric operand, distinct from assigning the same expression to a Number target.

**Sub-day arithmetic** operates on exact integer **milliseconds since epoch**. Stored and constructed Date/Time/DateTime syntax has whole-second precision, but `Now` retains the injected validation clock's millisecond identity:

- `AddHours` / `AddMinutes` / `AddSeconds` carry across the day boundary.
- `DifferenceIn{Hours,Minutes,Seconds}(a, b) = (epochMillis(b) − epochMillis(a)) / unitMillis`, **truncated toward zero** — a reverse difference of −5 h 30 m is **`-5`**, not `-6`, and a `999 ms` residual is `0` seconds. Argument order is `b − a` (same as `DifferenceInDays`).

> **Lean modelling note.** Do not erase the operand's calendar basis. A proleptic-Gregorian total function is suitable only for a narrowed consumer/domain whose own clause or proof establishes that equivalence; a constructed-Date consumer needs a supplied legacy-calendar operation or a proof-backed supported profile. `AddMonths`/`AddYears` need the explicit end-of-month clamp and the Feb-into-leap-year correction as *code*, not as an assumed library default. The sub-day family is cleanest after resolution as `Int` epoch-milliseconds with truncating integer division (`Int.tdiv`, toward zero — **not** `Int.fdiv`).

---

## 3. Constructing dates, and checking validity

`Date(Day, Month, Year)` builds a date from numeric parts (also: a 2-argument form supplying the year from the Base Year, and a 4-argument century form). `Time(...)` and `DateTime(...)` construct the corresponding values. A constructed date is **invalid** if any referenced part is unfilled, or the parts don't form a real calendar date (`Date(31, 11, 2000)` — November has 30 days; or 30 February).

```
Invalid(Date(Day, Month, Year))   -- fires on 31.11, 30.02, an unfilled part, …
```

**The truth projections of `Valid` and `Invalid` are strong-Kleene complements, but one full verdict does not determine the other**, because the construction has reason-bearing non-values:

- An **unreal `Date(...)` carries no date value** — it does *not* roll over and does *not* keep an out-of-range label. Its direct numeric date/time extractors and date differences nevertheless produce the actual Number **`0`** with fixed/present provenance. An incomplete construction also produces `0`, but retains not-given/fillable provenance; a fired comparison can therefore be VALUE for unreal input and OMISSION for incomplete input even though the numeric amounts agree. A malformed/formally unavailable construction projects to UNKNOWN instead, never to zero.
- `Valid(Date(...))` = all parts present ∧ well-formed ∧ the date is real → fired **VALUE**.
- `Invalid(Date(...))` = parts well-formed ∧ (not real ∨ some part empty). Its polarity is **directional**: an empty fillable part → **OMISSION**, a present-but-unreal date → **VALUE**. It even fires on an **all-empty** row.
- A **malformed** part suppresses **both** predicates (each goes UNKNOWN; the formal error fires instead). This is the UNKNOWN/UNKNOWN arm of strong-Kleene complementation, not ordinary Boolean false.
- The decisive non-law is at the full verdict/polarity level: incomplete and unreal constructions both make `Valid` not fire, but `Invalid` must recover **OMISSION** for incomplete and **VALUE** for unreal.
- To fire `Invalid` **only** on a complete-but-impossible date, prefix `AllFieldsFilled(...)`.

The constructor's **calendar-reality test is model-zone-sensitive and uses the legacy hybrid calendar**, not an abstract proleptic-Gregorian `LocalDate`. Kernel 30.8.1 creates a non-lenient `GregorianCalendar` in `modelConfig.timeZone`; the default cutover uses Julian rules before the Gregorian transition, and a zone discontinuity can remove a complete local date. Consequently, UTC `Date(29, 2, 1500)` is real under the Julian side of that calendar, while `Date(30, 12, 2011)` is unreal in `Pacific/Apia` because that local date was skipped. This is separate from the later 1583-10-16 stored/computed-value floor. The zone database is a runtime input not identified by the kernel behavior version alone. A portable implementation must reproduce the pinned legacy calendar, zone, and zone-data behavior or fail closed outside its explicitly supported calendar domain; substituting a zone-free proleptic-Gregorian predicate is not equivalent.

The reason and calendar basis compose through legal temporal producers rather than being rediscovered at each leaf:

- A Date- or DateTime-valued operation carries either a concrete value with its calendar/instant identity or a no-value reason. Incomplete/not-given, present-but-unreal, and non-relevant/malformed provenance must remain distinguishable; non-relevant dominates when a `DateTime(date, time)` combines it with a check-relevant no-value.
- `DateFromDateTime`, `TimeFromDateTime`, and legal `Add*` descendants preserve the source no-value reason. Real `Date(...)` descendants preserve the legacy-calendar identity described in §2.
- Numeric component extractors and date differences map incomplete/not-given and present-but-unreal operands to the same amount `0`, but retain fillable versus fixed provenance respectively; they map a non-relevant operand to UNKNOWN.
- The direct date-component family is `DayFromDate`, `MonthFromDate`, `QuarterFromDate`, and `YearFromDate`. For a real source, the quarter is `((month - 1) / 3) + 1` with integer division; the numeric-zero projection of an incomplete or unreal source remains `0` for Quarter just as it does for the direct components.
- Direct date `Min`/`Max` skips check-relevant valueless operands when another concrete value exists; a non-relevant operand propagates non-relevance. This consumer admission does not widen the grammar: a result such as `YearFromDate(Min(...))` remains authoring-rejected where the extractor requires a narrower source form.
- Operand-list `Min`/`Max` and field-list/star `MinValue`/`MaxValue` also admit homogeneous TIME operands or homogeneous full-component DATETIME operands whose declared formats expose comparable component sets. Time selection compares each decoded time-of-day coordinate; DateTime selection compares each resolved physical instant, not its rendered wall label. In both families, check-relevant valueless operands are skipped, an all-empty selection has no value, any reached non-relevant operand propagates non-relevance, and an empty, omitted-tail, or encountered-filter source retains symmetric missing provenance on a selected value. A seconds-level Time difference therefore remains ordered even when a shorter display omits it, and an exact selected DateTime instant remains distinct from an equal-looking stored value on the other side of a model-zone overlap.

Temporal format admission deliberately has two strengths. A direct comparison requires matching year presence unless the Base Year supplies `YEAR`, and requires both formats to contain some date component or neither; only `==` and `!=` additionally require both formats to agree on whether they contain any time component. It does not require identical component sets: ordering admits `yyyy-MM` against `yyyy-MM-dd`, Date against DateTime, and `HH:mm` against `HH:mm:ss`, while equality rejects only the Date/DateTime pair among those examples. Temporal operand-list and field-list extrema are stricter: after optional Base Year supplementation their complete six-component sets must be identical, and a DATETIME extremum requires all year/month/day/hour/minute/second components.

`Valid(Field, "CustomTypeName")` is the other form: it runs the project's registered validator for that custom type against the field.

> **Lean modelling note.** A bare `Option CalDate` is insufficient: its `none` would collapse incomplete, unreal, and non-relevant constructions even though validity, numeric polarity, and later temporal composition distinguish them. Use a reason-bearing result such as `real (calendarBasis, CalDate) | incomplete | unreal | unknown`, define the two validity verdict projections separately, and give each consuming operation an explicit projection. Their truth projections complement under strong Kleene; `Invalid` is not a unary function of the full `Valid` verdict.

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

`DifferenceInHours/Minutes/Seconds` is **absolute-instant subtraction** — `floor(|instant₂ − instant₁| / unit)`, sign from operand order — under the normative Groovy-dynamic behavioral anchor. Generated static-Java is required co-evidence and agrees on the exercised historical cases. No identical-behavior claim is made for the TypeScript/luxon target: a legal strategy split is recorded and never overrides Groovy-dynamic.

The model's configured **`timeZone`** is the DM-JSON key `content.modelConfig.timeZone`; the capitalized `TimeZone` is the *internal* metamodel key code generation copies it into. Absent means `UTC`. An explicit id is model-legal exactly when it is the literal `GMT` or `java.util.TimeZone.getTimeZone(id).getID() != "GMT"`. Known IANA ids, `GMT±HH:MM`, `UTC`, `Zulu`, and `Etc/UTC` are legal. An empty, unknown, or misspelled id that silently collapses to `GMT` is rejected with `MVK_INVALID_TIME_ZONE`.

The normative kernel path applies that id at parse time through legacy `java.util.TimeZone` plus non-lenient `SimpleDateFormat`, not `java.time`. A plain DATE is midnight in the model zone. Across a daylight-saving transition:

- Under **`UTC`**, the wall-clock gap equals the instant gap.
- Under **`Europe/Berlin`**, two datetimes straddling a transition differ by their *physical* elapsed time: `2024-03-31T01:30:00 → 03:30:00` is `DifferenceInHours = 1` (the skipped 02:00 hour), and `2024-10-27T01:30:00 → 03:30:00` is `3` (the repeated hour).

That non-lenient zone-set parse gives every historical transition the following laws:

- **Every gap is a FORMAL error.** A stored wall time that does not exist (`2024-03-31T02:30:00` under Berlin) draws `datumFormatFalsch` — the non-lenient round-trip rejects it — and suppresses a referencing rule exactly like any malformed value. It is **not** rolled forward.
- **Every overlap selects the smaller/after offset.** In an ordinary modern CEST→CET overlap that is CET: `01:30 → 02:30` on `2024-10-27` is `DifferenceInMinutes = 120`, and two stored `02:30` values are instant-equal. In a historical CEMT→CEST overlap the same general rule selects CEST, not CET.
- **Datetime comparison is instant-based too** (`==`/ordering compare the parsed instants), and a **chained `Add{Hours,Minutes,Seconds}` result keeps its exact instant**: `AddHours(01:30 CEST, 1)` lands on the *daylight* side of the ambiguous hour, so it is **not** equal to the equal-looking stored `"02:30:00"` (which re-parses standard) — the pair is 60 real minutes apart. A rendering-based re-parse loses this; the arithmetic is instant-in, instant-out.
- **`AddDays` landings in a special hour never overshoot the direction of travel**: a forward add selects the earlier consistent instant and a backward add the later one. “Daylight” versus “standard” is only an explanatory label for an ordinary modern two-offset transition; the ordering rule also covers CEMT. In the modern spring-gap control, a forward landing renders `01:30` CET.

### 5.1 Versioned `Europe/Berlin` legacy profile

The normative profile `europe-berlin-java-util-timezone-jdk21-tzdb2026a-v1` records the legacy `java.util.TimeZone` observations on JDK 21.0.11 with tzdb 2026a. Before the first entry, the offset is flat CET `+3600`; unlike `java.time`, this path does not expose pre-1893 LMT `+3208`. At each listed UTC instant, `offset after` takes effect. The table contains all 62 legacy transitions through 1997, including CEMT `+10800` in the 1945 and 1947 double-summer periods.

| UTC transition instant | Offset after (seconds) |
|---|---:|
| `1916-04-30T22:00:00Z` | 7200 |
| `1916-09-30T23:00:00Z` | 3600 |
| `1917-04-16T01:00:00Z` | 7200 |
| `1917-09-17T01:00:00Z` | 3600 |
| `1918-04-15T01:00:00Z` | 7200 |
| `1918-09-16T01:00:00Z` | 3600 |
| `1940-04-01T01:00:00Z` | 7200 |
| `1942-11-02T01:00:00Z` | 3600 |
| `1943-03-29T01:00:00Z` | 7200 |
| `1943-10-04T01:00:00Z` | 3600 |
| `1944-04-03T01:00:00Z` | 7200 |
| `1944-10-02T01:00:00Z` | 3600 |
| `1945-04-02T01:00:00Z` | 7200 |
| `1945-05-24T00:00:00Z` | 10800 |
| `1945-09-24T00:00:00Z` | 7200 |
| `1945-11-18T01:00:00Z` | 3600 |
| `1946-04-14T01:00:00Z` | 7200 |
| `1946-10-07T01:00:00Z` | 3600 |
| `1947-04-06T02:00:00Z` | 7200 |
| `1947-05-11T01:00:00Z` | 10800 |
| `1947-06-29T00:00:00Z` | 7200 |
| `1947-10-05T01:00:00Z` | 3600 |
| `1948-04-18T01:00:00Z` | 7200 |
| `1948-10-03T01:00:00Z` | 3600 |
| `1949-04-10T01:00:00Z` | 7200 |
| `1949-10-02T01:00:00Z` | 3600 |
| `1980-04-06T01:00:00Z` | 7200 |
| `1980-09-28T01:00:00Z` | 3600 |
| `1981-03-29T01:00:00Z` | 7200 |
| `1981-09-27T01:00:00Z` | 3600 |
| `1982-03-28T01:00:00Z` | 7200 |
| `1982-09-26T01:00:00Z` | 3600 |
| `1983-03-27T01:00:00Z` | 7200 |
| `1983-09-25T01:00:00Z` | 3600 |
| `1984-03-25T01:00:00Z` | 7200 |
| `1984-09-30T01:00:00Z` | 3600 |
| `1985-03-31T01:00:00Z` | 7200 |
| `1985-09-29T01:00:00Z` | 3600 |
| `1986-03-30T01:00:00Z` | 7200 |
| `1986-09-28T01:00:00Z` | 3600 |
| `1987-03-29T01:00:00Z` | 7200 |
| `1987-09-27T01:00:00Z` | 3600 |
| `1988-03-27T01:00:00Z` | 7200 |
| `1988-09-25T01:00:00Z` | 3600 |
| `1989-03-26T01:00:00Z` | 7200 |
| `1989-09-24T01:00:00Z` | 3600 |
| `1990-03-25T01:00:00Z` | 7200 |
| `1990-09-30T01:00:00Z` | 3600 |
| `1991-03-31T01:00:00Z` | 7200 |
| `1991-09-29T01:00:00Z` | 3600 |
| `1992-03-29T01:00:00Z` | 7200 |
| `1992-09-27T01:00:00Z` | 3600 |
| `1993-03-28T01:00:00Z` | 7200 |
| `1993-09-26T01:00:00Z` | 3600 |
| `1994-03-27T01:00:00Z` | 7200 |
| `1994-09-25T01:00:00Z` | 3600 |
| `1995-03-26T01:00:00Z` | 7200 |
| `1995-09-24T01:00:00Z` | 3600 |
| `1996-03-31T01:00:00Z` | 7200 |
| `1996-10-27T01:00:00Z` | 3600 |
| `1997-03-30T01:00:00Z` | 7200 |
| `1997-10-26T01:00:00Z` | 3600 |

After the final entry, retain its `+3600` offset through the end of 1997. Beginning with 1998, apply the recurring EU rule: offset `+7200` from the last Sunday of March at `01:00Z` inclusive until the last Sunday of October at `01:00Z` exclusive, otherwise `+3600`. The rule has held continuously since 1996; the explicit 1996 and 1997 entries make the table-to-recurrence boundary non-overlapping. For 1980–1995, the table records the historically different last-Sunday-of-September end.

The a12-dmkits pinned profile carries the same 62 entries. `BerlinHistoricalTzTest` compares the production table with an independent JDK 21.0.11/tzdb2026a 62-pair vector on JVM and Node, checks immediately before, at, and after every transition, every gap/overlap class, the pre-first and post-last regimes, and seeded epoch, offset, missing, extra, and reorder mutation classes. `BerlinTransitionOracleDiffTest` reuses prepared Groovy-dynamic and generated-static-Java engines and checks immediately before, at, and after all 62 transitions against that independent vector. This certifies the pinned profile; it does not claim equivalence to every future JDK/tzdb release.

> **Lean modelling note.** Carry the model's accepted time-zone id in the model and resolve it through a versioned zone-rule oracle/profile supplied by `World` (§4 of [`01-data-model.md`](01-data-model.md)). A staged consumer may support a smaller named set only by rejecting every other legal id before evaluation. A faithful `Europe/Berlin` implementation uses the versioned table and recurrence above, rejects gaps, selects the smaller/after overlap offset, keeps instant identity through sub-day arithmetic, and implements the no-overshoot wall-day landing. The current fixed 2024 overlap slice must be replaced when that general resolver lands, not retained as a parallel legacy mechanism.

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

- `Today` ignores the time of day — more precisely, it truncates the validation instant to midnight **in the model zone** (a zone-set calendar), so under `Europe/Berlin` the day boundary is Berlin midnight, not UTC midnight. `Now` is the raw validation instant, including any millisecond remainder supplied through `currentDateForTest` or sampled from the wall clock; it is not rounded to authored DateTime precision before comparison or difference. `Now` is **not recommended with `==`** and is **forbidden in computations** (a time-dependent computed value would immediately disagree with itself; [§11](09-computations.md)). `Now` compares only to an operand whose format carries a *time* component — against a plain date field the rejection fires at **code generation**, not at the parse/consistency check.
- **`BaseYear` is polymorphic by the other operand:** against a **date** it is the base-year *start* (`2020-01-01`); against a **number** it is the year *number* (`2020`); as a range source, `StartOfDateRange(BaseYear)` / `EndOfDateRange(BaseYear)` are `01.01` / `31.12` of the reference year. It is *model config*, not the clock; **VALUE** polarity.

> **Lean modelling note.** Inject the clock (`Today`/`Now`) as an explicit parameter — a `PointInTime` in the evaluation environment — never a global read. This keeps `eval`/`compute` pure and deterministic (essential for reproducible property tests and for the "compute is a function" stance of [`01-data-model.md`](01-data-model.md)). `BaseYear` is model config, resolved by the *other operand's kind* — a small dispatch, not a clock read.

---

## 8. Date ranges and overlap

Date ranges support only `==` / `!=` (**no ordering**), and `DateRange(...)` **cannot be nested** inside other constructs. Overlap tests treat endpoints as **inclusive (closed intervals)**.

The two overlap predicates differ in **shape** ⚠:

- **`DateRangesOverlap(op0, op1, …)`** is **any-pair** among *all* operands' kept, filled ranges (one growing set): a list-internal pair fires even when a scalar operand is disjoint, and a same-cell self-pair via scalar + star fires on every filled row.
- **`AtLeastOneDateRangeOverlaps(scalar In list…)`** is genuinely **scalar-vs-list**: two list cells overlapping *each other* do **not** fire.

For both: intervals are **closed** (back-to-back periods sharing a boundary day overlap); an **inverted** range (start after end) **never** overlaps; empty or formally unavailable cells are **skipped**.

Their firing polarity is scan- and operand-shape-sensitive:

- `DateRangesOverlap` fires **OMISSION** exactly when the scan has processed a kept, filled range from a filter-bearing operand at or before the first overlapping pair; otherwise it fires **VALUE**. A filtered operand with no kept, filled range does not taint a later firing.
- `AtLeastOneDateRangeOverlaps` fires **OMISSION** exactly when the list operand containing the matched range carries a filter; otherwise it fires **VALUE**. An earlier filtered but disjoint list operand does not taint a later unfiltered match.

For `AtLeastOneDateRangeOverlaps`, an empty, malformed, or formally unavailable scalar collapses directly to no fire; overlaps internal to the list cannot rescue it. Stored inverted ranges are normally rejected by their field's formal check and therefore skipped, while the resolved interval relation independently returns false if an inverted pair reaches it.

---

## 9. DateTime rides the date-format definition — but the operand gates are PER-OPERATOR ⚠

The date **extractors** (`DayFromDate`, …) accept a DateTime operand and see its **DATE part** (times ignored). The time extractors (`HoursFromTime`, `MinutesFromTime`, `SecondsFromTime`) likewise accept either Time or DateTime and see only the **TIME part** (the DateTime date is ignored). Beyond the extractors, the earlier blanket claims ("differences see the date part; arithmetic is rejected") are **wrong per-operator** — probe-corrected (kernel 30.8.1, 2026-07-18):

- **`DifferenceInDays` accepts DateTime operands and is TIME-OF-DAY AWARE**, but its general rule is a signed **model-zone calendar-step count**, not unconditional subtraction on zone-free wall labels. The kernel orders the resolved legacy `Calendar` values, makes a `yearDifference × 365` lower-bound jump with `Calendar.DAY_OF_MONTH`, advances by single calendar days until the next landing passes the later operand, and then restores authored argument order (`b − a`). The familiar wall-seconds quotient happens to agree with the maintained controls: `23:00 → 01:00` next day is **0**, not the date-part 1, while the equal-wall-time Berlin `2024-03-30T12:00 → 2024-03-31T12:00` is **1** despite only 23 elapsed instant hours. It is not a generally equivalent formula, even within Berlin: `2024-03-30T02:30 → 2024-03-31T01:45` counts **1** because one calendar-day addition lands at `01:30` before the second operand, whereas Δ wall-label seconds is only 23 h 15 m and would truncate to 0. Across a whole-date discontinuity the distinction is sharper: in `Pacific/Apia`, `2011-12-29T12:00 → 2011-12-31T12:00` is one zone-calendar day because a single `DAY_OF_MONTH` step skips 30 December, whereas a proleptic wall-label coordinate would incorrectly return two. **Mixed `(datetime, date)` pairs are legal** — the date reads as midnight in the model zone.
- **`DifferenceIn{Months,Years}` REJECT a DateTime operand** at code generation (`MVK_WRONG_DATE_FORMAT_FOR_OP`) — date-only.
- **`AddDays` accepts a DateTime operand and is TIME-PRESERVING** (`15T22:00 + 1 = 16T22:00`); a special-hour landing follows the no-overshoot rule (§5). **`AddMonths` / `AddYears` REJECT a DateTime operand** at code generation.
- **`DifferenceIn{Hours,Minutes,Seconds}` REJECT a plain DATE operand** — DateTime-only, mirror-image of the months/years gate.

---

## Checklist for §6

- [ ] Literal kind (`dateConst` vs `strConst`) resolved at **lex/type** time by shape; ISO always a string; omitted-year needs a Base Year.
- [ ] `AddMonths` (day-preserving + end-of-month clamp) vs `AddYears` (last-of-Feb-preserving, corrects into leap years) — **different** conventions; fractional offsets truncated. Preserve a constructed Date's legacy hybrid-calendar identity through legal month/year addition and difference rather than erasing it into a separately modeled ordinary-date function.
- [ ] Sub-day diffs = epoch-seconds `/ unit`, **truncated toward zero**, order `b − a`.
- [ ] `DifferenceInDays` = signed legacy model-zone `Calendar.DAY_OF_MONTH` stepping, time-of-day aware; Δ wall-seconds `/ 86 400` is not generally equivalent around special-hour landings or skipped whole dates.
- [ ] `Valid`/`Invalid(Date(...))` have strong-Kleene-complementary truth but distinct full verdict projections; malformed makes both UNKNOWN; `Invalid` distinguishes unreal VALUE from incomplete OMISSION and fires on all-empty. Direct numeric extractors/differences project both unreal and incomplete to amount `0`, but retain fixed versus fillable provenance; malformed/non-relevant projects to UNKNOWN.
- [ ] `Date(...)` reality uses non-lenient legacy `GregorianCalendar` in the model zone: hybrid cutover and zone-skipped local dates matter; a zone-free proleptic replacement is not equivalent. Preserve both calendar identity and no-value reason through legal `DateTime`, extraction, shift, difference, and direct date `Min`/`Max` composition.
- [ ] **Gregorian floor** at 1583-10-16 on *values* (stored → `datumFalsch`, computed → ERRORED), day-optional completes day first; **not** applied to the `Date(...)` constructor's reality test.
- [ ] Dates stored/checked in the field's **declared format**.
- [ ] Time-zone admission follows the legacy recognized-id rule: absent ⇒ UTC; literal GMT or an id that does not collapse to GMT is legal; collapsed empty/unknown/typo ids draw `MVK_INVALID_TIME_ZONE`.
- [ ] Zone resolution uses a versioned legacy `java.util.TimeZone` profile; the Berlin account is flat CET before 1916, uses the 62-transition table through 1997, then the recurring EU rule.
- [ ] Sub-day differences and datetime comparison are instant-based; every historical gap draws `datumFormatFalsch`, every overlap selects the smaller/after offset, chained sub-day `Add*` keeps instant identity, and wall-day landings never overshoot the travel direction.
- [ ] Per-operator DateTime gates: `DifferenceInDays`/`AddDays` accept DateTime (time-aware model-zone calendar-day count / time-preserving add); `DifferenceIn{Months,Years}`/`AddMonths`/`AddYears` reject it; `DifferenceIn{Hours,Minutes,Seconds}` reject a plain DATE.
- [ ] Fragment completion: earliest for a value/start, latest for a range end (leap-aware); day-optional `00`; `ValueAsDate` only as a direct comparison operand.
- [ ] Ranges: `==`/`!=` only, no nesting, closed intervals; `DateRangesOverlap` (any-pair, growing set) vs `AtLeastOneDateRangeOverlaps` (scalar-vs-list); inverted never overlaps.
