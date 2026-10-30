# 05 — Dates and time (§6)

A temporal value is not a canonical instant. It is a value **in a declared format**, which fixes its component set; it is resolved on the **legacy hybrid calendar in the model zone**; and where it has no value it carries a **reason** — incomplete, unreal, non-relevant or formally unavailable — that later consumers keep apart. Some values are deliberately imprecise (component-omitting formats, fragments, partially known dates). Temporal arithmetic is asymmetric — a shift is not the inverse of a difference — and calendar-corrected, and a String literal shaped like a date is a date.

Empty-date behaviour — not evaluated in comparisons, the fillable `0` of the extractors and differences, dropped or `no value` in aggregates — is [§2](03-empty-and-required.md#a2-where-an-operator-overrides-its-kinds-default)'s. Which operator takes which class of the operand gates this chapter defines is column D of [the operator reference](14-operator-reference.md#temporal-operand-gate).

---

## Declared formats and stored temporal text

### The format vocabulary

**A temporal declaration admits one format vocabulary whatever its kind.** DATE, TIME and DATE_TIME declare a `format`, and DATE_FRAGMENT declares its format under its own `formatOfFragment` key; all four admit the same strings and persist each exactly as declared.

| Group | Admitted formats |
|---|---|
| complete date | `yyyy-MM-dd`, `dd.MM.yyyy`, `yyyyMMdd` |
| year-bearing, component-omitting | `yyyy`, `yyyy-MM`, `yyyyMM` |
| yearless, component-omitting | `MM`, `MM-dd`, `MMdd`, `ddMM`, `dd.MM.` |
| clock | `HH:mm:ss` |
| date-time | `yyyy-MM-dd'T'HH:mm:ss` |

Measured scope: the table is closed over 135 candidates built by joining components (the twelve formats other than `dd.MM.` admitted on DATE, TIME and DATE_TIME alike, the other 123 refused on all) and over 1,223 that also vary a trailing separator (`dd.MM.` the one further string); DATE_FRAGMENT answers the same way. `QQQ` is measured refused on all four kinds as well; the table claims nothing else.

- **Admission is per string, not compositional.** `ddMM` is admitted where `dd.MM` is refused, and `yyyyMMdd` where `ddMMyyyy` is refused. `dd.MM.` is admitted on DATE, TIME and DATE_TIME and as a `formatOfFragment`, while `dd.MM` without the closing dot is refused on all of them: a trailing separator is part of the string.
- **Natural-looking strings can be refused.** `HH:mm` is refused on a TIME, a DATE and a DATE_TIME declaration alike, beside an admitted `HH:mm:ss`, so every admitted time-bearing format carries all three clock components. The day-first `dd.MM.yyyy'T'HH:mm:ss` is refused on every kind, although DateTime-valued expressions — `Now`, the `DateTime(...)` constructor and a date-time constant — use that shape. A refused candidate draws one codeless model-level notification on a DATE, TIME, DATE_TIME or DATE_FRAGMENT field the variant filter keeps, whether the field declares the format or uses a type definition that does; a deleted field and a type definition no kept field uses draw nothing.
- **A default is not a restriction.** TIME defaults to `HH:mm:ss` and DATE_TIME to `yyyy-MM-dd'T'HH:mm:ss`, yet `yyyy-MM-dd` and `dd.MM.yyyy` on TIME, `HH:mm:ss` on DATE and DATE_TIME, the fragment format `MM` on TIME and the date-time format on DATE are all admitted.
- **A declaration without a format takes its kind's default.** A DATE, TIME or DATE_TIME declaration with an empty type payload is legal and behaves throughout as if it declared its kind's default: the format-less DATE carries the complete-date component set, admitted beside `yyyy-MM-dd` and refused beside `yyyy-MM` with `MVK_DATEFORMATS_NOT_COMPATIBLE`, and the format-less TIME and DATE_TIME carry the full clock and the full stamp. The resolution reads the kind, so a format-less DATE beside a format-less DATE_TIME is refused incompatible. The resolved string compares equal to the default spelling: `FieldValuesNotUnique`'s format-string gate admits a format-less DATE beside a declared `yyyy-MM-dd` field and refuses that field beside a `dd.MM.yyyy` one. Measured scope: the resolved literal itself is not exhibited; the rows pin its component set and its equality class at the gates measured.

A component-omitting value denotes an interval or a yearless position, not a point: `yyyy` a whole calendar year, `yyyy-MM` and `yyyyMM` a whole month, `MM` a yearless month, and `MM-dd`, `MMdd`, `ddMM` and `dd.MM.` a yearless month and day. The DateRange `(format, separator)` allowlist is a separate domain ([§8.1](#81-declaration-and-stored-text)); it stays at eight pairs and admits no trailing-separator format with any separator.

Sources: [format-less declaration](../docs/sources/static-admission-and-class-probes.md#src-temporal-declaration-without-a-format), [inbound 2026-10-29](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-29), [inbound 2026-09-21](../docs/sources/inbound-handbacks.md#inbound-2026-09-21-corrections), [operation granularity separability](../docs/sources/temporal-and-message-probes.md#src-temporal-operation-granularity-separability).

### The format decides, never the kind

**Every temporal gate and reader asks the declared format's component set — after a declared Base Year supplies a missing year where that gate allows it — and never the declared kind.** Each owner records its carrier's measured scope.

| Carrier | What the format decides | Owner |
|---|---|---|
| declaration | the vocabulary | [above](#the-format-vocabulary) |
| stored text | which parse applies, and which finding a misfit draws | below and [stored temporal text](#stored-temporal-text) |
| comparison | the cell's value family and the pair gate | [§1](#the-temporal-pair-gate) |
| computed target | admission and the stored rendering | below and [§11 §4.1](09-computations.md#41-temporal-constants) |
| extractor, shift and difference operands | the unit gates | [§9](#9-datetime-rides-the-date-format-definition--but-the-operand-gates-are-per-operator-) |
| `Date(...)` and `Time(...)` components | the positional gates | [§3.1](#31-date), [§3.2](#32-time-and-the-clock-anchor) |
| `DateRange` endpoints | the endpoint gate | [§8.4](#84-construction-and-equality) |
| formal message keys | the component reading | [§4.2](#42-message-keys-of-a-stored-date-refusal) |

So a temporal cell's value family — admission, store and comparison — is its format's. An implementation keying a cell's admitted payload on the declared kind marks as formally invalid a cell the Kernel stores and compares, a wrong value rather than a wrong diagnostic; a consumer must not infer a component set from a field's kind.

- **Stored text is parsed by the declared format, and the kind supplies no fallback.** A DATE declared `HH:mm:ss` holding `12:30:00` is a clock reading and counts as one value with a TIME holding the same reading, while a valid *date* text stored in that field draws `datumFormatFalsch` and leaves the cell formally invalid. Symmetrically, a TIME and a DATE_TIME each declared `yyyy-MM-dd` count as one value with a DATE declared the same, and a clock text in the TIME-declared date field draws that same date-format cause, so the finding names the format the parser applied and not the kind. A formally invalid cross-kind operand suppresses a computation's outcome, neither clearing nor erroring it.
- **Comparison reads the format's family.** A DATE whose format is `HH:mm:ss` compares with a TIME field and is refused against a `yyyy-MM-dd` DATE, while a TIME whose format is `yyyy-MM-dd` does the opposite. The DATE_TIME family is measured separately: a DATE declared `yyyy-MM-dd'T'HH:mm:ss` compares with a DATE_TIME and is refused against a DATE, a DATE_TIME declared `yyyy-MM-dd` does the opposite, and the two ordinary fields refuse each other as the control.
- **A computed target is admitted by its whole format and stores by it.** A computed `Time(...)` is admitted into a DATE-declared `HH:mm:ss` field and refused into a DATE-declared `dd.MM.yyyy` one; a computed `Date(...)` is admitted into a TIME-declared `dd.MM.yyyy` field and refused into both clock-formatted targets; a computed `DateTime(...)` is admitted into DATE- and TIME-declared fields carrying the date-time format and refused otherwise. Every refusal is `MVK_INVALID_COMPARE_TO_DATE`. The whole format is compared: a date-time target refuses a computed Time. An admitted cross-kind target stores by its format: a DATE declared `HH:mm:ss` stores `12:30:00` and a TIME declared `yyyy-MM-dd` stores `2024-03-05`, each beside its same-kind control, and the DATE_TIME carrier, whose format holds both component sets, is measured too.
- **Neither decision depends on the carrier that produced the value**: admission is the ordinary comparison gate over the two result formats, and every computed temporal stores through the target's format, so constructed, shifted, first-filled and addressed carriers behave as a constant does.

Sources: [computed target reads the format](../docs/sources/computation-placement-and-constant-probes.md#src-computed-temporal-target-reads-the-format-not-the-kind), [DateTime carrier](../docs/sources/computation-placement-and-constant-probes.md#src-datetime-carrier-stores-by-its-format), [carrier invariance](../docs/sources/computation-placement-and-constant-probes.md#src-computed-target-gate-is-carrier-invariant), [value family](../docs/sources/computation-placement-and-constant-probes.md#src-temporal-value-family-is-the-formats-not-the-kinds), [DATE_TIME family](../docs/sources/inbound-handbacks.md#inbound-2026-09-05d), [operand family](../docs/sources/computation-placement-and-constant-probes.md#src-temporal-operand-family-is-the-formats-not-the-kinds).

### Stored temporal text

**Stored Date, Time, DateTime and DateRange text is converted non-leniently against the field's declared format.** A noncanonical spelling — `2024-3-5` or `20240305` for a `yyyy-MM-dd` declaration, `14:5:0` for `HH:mm:ss`, `1.1.2024-31.12.2024` for a fixed-width range — does not normalize: conversion fails, the physical placement and exact text remain, and formal checking makes the cell not check-relevant ([§3 B.2](02-logic-and-formal-errors.md#b2-the-three-cell-states--the-third-one-is-not-empty)). The digits are ASCII only, unlike a Number's: a `yyyy` year stored as Arabic-Indic or fullwidth digits does not convert, so `Date("01", "01", Built) == Date("01", "01", "1963")` fires for a stored `1963` alone. Empty stored text is present and value-free on every format. One calendar date can be well-formed in one field and `datumFormatFalsch` in another, so a consumer parses each field by its own `format`.

**Every stored temporal failure draws one of the two Date formal codes.** `datumFormatFalsch` is the format error: text the format does not parse, or whose present components are no real date. `datumFalsch` is the date error: a real date in a refused position ([§4](#4-the-gregorian-floor)), or a partially known Date's refused omission pattern ([§6.2](#62-partially-known-dates)). There is no Time- or DateTime-specific code; the kind selects nothing.

- `HH:mm:ss` maps width and component-range failures to the format error and has no date-error branch. Hour 24 is not an end-of-day spelling: `24:00:00` is refused exactly as `25:00:00` is, while `00:00:00` and `23:59:59` are admitted, so the hour runs from 0 through 23.
- At a complete Date or DateTime format a real value before `1583-10-16` draws the date error, while an unreal component draws the format error before the floor is asked: `yyyyMMdd` admits `15831016`, draws the date error on `15831015` and the format error on `00000615` and `20240231`. The date-time format's literal `'T'` is mandatory.
- A wall time the model zone skips draws the format error ([§5](#5-time-zones-and-the-sub-day-difference)).

Measured scope: the twelve formats of the 135-candidate universe with their discriminating values on all three kinds, and the component-omitting formats, `dd.MM.` included, the clock and the date-time format in the formal-key runs of [§4.2](#42-message-keys-of-a-stored-date-refusal). An unmeasured text inside a measured format is not covered.

**Formal checking first completes a component-omitting format**, then applies the position checks of [§4](#4-the-gregorian-floor) to the completed date:

| Format | Completion for the formal check |
|---|---|
| `yyyy`, `yyyy-MM`, `yyyyMM` | a missing month becomes January and a missing day the first |
| `MM-dd`, `MMdd`, `ddMM`, `dd.MM.` | the model Base Year, `2000` when none is declared |
| `MM` | the parser's default year `1970`, whatever the Base Year; day the first |

So `yyyy` holding `1583`, `yyyy-MM` holding `1583-10` and `MM-dd` holding `01-01` under Base Year 1583 draw `datumFalsch`, while `MM` holding `01` stays admitted under that Base Year. Measured on these discriminators.

**Separators and component order are exact.** `yyyy-MM` refuses `202006` and `yyyyMM` refuses `2020-06`; `MMdd` refuses `06-15` and reads `0611` as month 6, day 11, while `ddMM` refuses `15-06` and reads `0611` as day 6, month 11. A parse or calendar-reality failure draws the format error.

**The stored yearless day bound follows the declared Base Year.** With none declared, no year decides leapness and the bound is the month's greatest possible day, February 29: `04-31` and compact `3104` are refused, while `04-30`, `02-29`, compact `0229` and day-first compact `2902` are admitted. This is the yearless bound the DateRange overlap uses ([§8.6](#86-overlap-evaluation)). With a Base Year declared the bound is the month's length in that year, so `02-29` is admitted under Base Year 2024 and is `datumFormatFalsch` at the cell under Base Year 2023, on models differing in nothing else; the leapness of the declared year decides. Consequently every admitted yearless stored value can be completed in its model's Base Year. The literal's calendar check ignores the Base Year ([§1](#1-constant-format-and-the-stringdate-literal-ambiguity-)), so under a leap Base Year a stored `02-29` is admitted while the literal `"29.02."` is refused.

Sources: [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), [calendar expression family](../docs/sources/temporal-runtime-fold-probes.md#src-calendar-expression-family), [yearless day bound](../docs/sources/temporal-constant-and-base-year-probes.md#src-yearless-day-bound-reads-the-base-year), [inbound 2026-09-21](../docs/sources/inbound-handbacks.md#inbound-2026-09-21-corrections), [formal keys, wider](../docs/sources/domain-ingestion-probes.md#src-k22-formal-keys-wider).

### Where a yearless value gets its year

**Each carrier completes a missing year by its own rule; no carrier's year transfers to another.**

| Carrier | Year used | Owner |
|---|---|---|
| formal check of a stored day-and-month value | the Base Year, `2000` when none is declared | [above](#stored-temporal-text) |
| formal check of a stored `MM` value | `1970`, never the Base Year | [above](#stored-temporal-text) |
| stored yearless day bound | the Base Year's length of February; February 29 when none is declared | [above](#stored-temporal-text) |
| message-key reading of a stored day-and-month value | the Base Year, `2000` when none is declared | [§4.2](#42-message-keys-of-a-stored-date-refusal) |
| message-key reading of a partially known Date | an unknown year reads as `2000`, an unknown month or day as `01` | [§4.2](#42-message-keys-of-a-stored-date-refusal) |
| a yearless value or constant read for calculation | the declared Base Year; with none, a default anchor that is a leap year, measured as 2000 for a stored `MM-dd` field's day shift and as one year for both operands of `DifferenceInDays` | [§1](#the-omitted-year-constant-and-the-base-year) |
| a component-omitting DATE operand of a direct date comparison | the declared Base Year, an `MM` operand's included | [§1](#the-temporal-pair-gate) |
| a component-omitting Date argument of `DateTime(date, time)` | its own year; for a yearless source the declared Base Year, not separated from the clock year, and refused in a rule condition without one; a missing month or day completes to the first | [§3.3](#33-datetimedate-time-and-the-datetime-projections) |
| a yearless field copied into a year-bearing Date target | the declared Base Year, a month-only source completing its day to the first; with none the copy is refused | [§11 §4](09-computations.md#4-the-stored-form--a-computed-value-lands-as-a-string-in-the-targets-shape) |
| calendar check of an omitted-year literal | a common year, never the Base Year | [§1](#1-constant-format-and-the-stringdate-literal-ambiguity-) |
| a computed component-omitting target's check | the stored value's formal completion, after rendering | [§3.1](#31-date) |
| DateRange day-and-month endpoints | the Base Year, `2000` when none is declared; interpreted wrapping pairs move one endpoint a year | [§8.2](#82-the-two-stage-runtime-reading) |
| DateRange month-only formal position checks | neither the completed year nor the Base Year | [§8.2](#82-the-two-stage-runtime-reading) |
| partially known Date, earliest completion | its own known year; an unknown year is non-relevant | [§6.2](#62-partially-known-dates) |

---

## 1. Constant format and the string/date literal ambiguity ⚠

**A quoted literal's kind is fixed by its own content before any context reads it, independently of locale.** The decimal separator is always `.`. The classification is closed:

| Content | Kind | Examples of the kind | Not the kind |
|---|---|---|---|
| `DD.MM.YYYY`: two-digit day and month, four-digit year, `.` separators, ASCII digits, naming a real date of the legacy hybrid calendar | date constant | `"05.03.2024"`, `"29.02.2024"`, `"30.04.2024"`, `"29.02.1500"`, `"04.10.1582"` | `"5.3.2024"`; `"29.02.2023"`, `"31.04.2024"`, `"29.02.1700"`, `"05.10.1582"` through `"14.10.1582"`; a shape holding an Arabic-Indic digit |
| `DD.MM.` with the closing dot, naming a real day and month of a common year | omitted-year date constant | `"30.04."`, `"13.07."`, `"05.03."` | `"13.07"`, `"05.03"`, `"03.2024"`; `"31.04."`, `"00.01."`, `"13.13."`, `"29.02."` |
| exactly eight ASCII characters `HH:mm:ss`, two digits per component, a real clock from `00:00:00` to `23:59:59` | clock constant | `"12:30:00"` | `"12:30"`, other separators, non-ASCII digits, a trailing space, hour 24, minute or second 60 |
| a date constant, a literal `T` and a clock constant, concatenated | date-time constant | `"05.03.2024T12:30:00"`, the measured admitted spelling | `"2024-03-05T12:30:00"`, the space-separated form |
| any other content | String | `"abc"`, the ISO-shaped `"2022-01-01"` | — |

- **The calendar is the legacy hybrid one**, Julian before the October 1582 cutover: 29 February 1500 and 4 October 1582 exist, the cutover labels 5 through 14 October 1582 and 29 February 1700 do not. A constant before the cutover is a Julian instant, so `DifferenceInDays("04.10.1582", Inception)` counts no skipped label.
- **The omitted-year check uses a common year and never consults the Base Year**: `"29.02."` is refused even under Base Year 2024, so a model may compute across a February 29 that no literal names ([below](#the-omitted-year-constant-and-the-base-year)).
- **Inside a value list** a date-shaped entry stays a String; no other context that changes the classification is known.
- **A literal that fails every temporal shape is a String, and the class it draws is its consumer's**: opposite a text field it is admitted; opposite a Date it is refused as a text is, `MVK_INVALID_COMPARE_TO_DATE` under `==` and `MVK_INVALID_TYPE_FOR_COMPARISON` under `>` (`"29.02.2023"`); at a temporal computation target `MVK_INVALID_COMPARE_TO_DATE` ([§11 §4.1](09-computations.md#41-temporal-constants)); as a temporal-operation operand `MVK_INVALID_DATE_STRING`, which names the literal ([§9](#9-datetime-rides-the-date-format-definition--but-the-operand-gates-are-per-operator-)). The omitted-year calendar refusal reaches these same consumer classes. Neither code is the classification's own signature.
- **A clock constant's shape is checked statically.** Opposite a Time field every non-clock shape in the table draws `MVK_INVALID_COMPARE_TO_DATE` rather than reaching evaluation. In the pattern slot `"12:30"` is an ordinary String and admitted. Assigned to a Time target it is refused; its class follows the constant ladder of [§11 §1.4](09-computations.md#14-wrong-kind-constants-and-field-sources), whose temporal-target rung is `MVK_INVALID_COMPARE_TO_DATE`, while the measured row recorded only the refusal.
- **An admitted clock constant is a wall clock.** Generated evaluation carries it on 1970-01-01 in the model zone, but Time comparison and `DateTime(date, time)` observe only its decoded hour, minute and second.

Typing by content has these consequences:

```
"30.11." + [YearString]        -- invalid: "30.11." is a date constant
"30." + "11." + [YearString]   -- valid: no piece matches a temporal shape
```

- `[StringField] == "15.06.2024"` is refused: a String field against a date constant.
- A `dd.MM.yyyy` literal compares chronologically with a DATE field whatever the field's stored format, and rides in argument position: `DifferenceInDays(OrderDate, "01.01.2022")`.
- `Today` and `Now` are typed as [§7](#7-the-point-in-time-and-reference-sources) states, and a date-time constant is a date-time, so the clock matters under `==` only: opposite a Date, `== Now` and `==` the date-time constant draw `MVK_INVALID_COMPARE_TO_DATE` while `>` the date-time constant is admitted, and `[Stamped] == Today` and a Time `== Now` draw the date class. A computation's constant is typed the same way ([§11 §4.1](09-computations.md#41-temporal-constants)).

Sources: [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), [inbound 2026-09-26d constant typing](../docs/sources/inbound-handbacks.md#inbound-2026-09-26d-constant-typing), [constant family gate](../docs/sources/temporal-constant-and-base-year-probes.md#src-constant-literal-family-gate), [literal composition](../docs/sources/temporal-constant-and-base-year-probes.md#src-temporal-constant-literal-composition), [yearless anchor](../docs/sources/temporal-constant-and-base-year-probes.md#src-yearless-anchor-is-the-base-year), a12-dmkits [KF78](../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf78) and ledger `SPEC-2026-07-27-06` for the clock shape.

> **Non-normative implementation note.** Classify literals in the lexer or typer, not the evaluator.

### The omitted-year constant and the Base Year

**An omitted-year constant takes the model's Base Year — a reference year, not a floor — wherever a year is needed, and a default leap-year anchor when none is declared.** A missing Base Year therefore costs these two measured things; no third is known:

- **Year agreement.** The constant is refused where it meets a year-bearing counterpart: a year-bearing computation target or comparison operand draws `MVK_INVALID_COMPARE_TO_DATE`, and a year-bearing operand beside it in a temporal operation draws `MVK_DATE_WITH_AND_WITHOUT_YEAR` ([§9](#9-datetime-rides-the-date-format-definition--but-the-operand-gates-are-per-operator-)).
- **Year-requiring units.** A unit or extractor that steps or reads the year — `AddYears`, `DifferenceInYears`, `YearFromDate` — needs the year component and refuses a yearless operand with `MVK_WRONG_DATE_FORMAT_FOR_OP` unless a Base Year supplies it ([§9](#9-datetime-rides-the-date-format-definition--but-the-operand-gates-are-per-operator-)).

An all-yearless operation of a unit that needs no year is admitted with no Base Year and resolved against the default anchor, which is a leap year: `DifferenceInDays("28.02.", "01.03.")` is 2 there. With a Base Year declared the anchor is exactly that year: the same difference is 2 under Base Year 2024 and 1 under 2023, and a stored yearless `MM-dd` field is anchored identically. A day shift of a stored yearless `MM-dd` field with no Base Year starts from the year 2000 on the legacy hybrid calendar of [§2.7](#27-calendar-basis): `02-28` shifted by 1, 36890, 73049 and `0 - 36160` days stores `02-29`, `02-28`, `02-28` and `02-27`, `06-15` by `0 - 160000` and `0 - 200000` days stores the Julian labels `05-13` and `11-06`, and of the years 1600 to 8999 only 2000 reproduces these together with the other measured stored values. **The shifted value keeps the year it reaches**, while the stored value it meets is read in the anchor year, so on that stored source `AddDays(MD, 1) == [N]` holds for `02-28` beside `02-29` and `12-30` beside `12-31` but not for `12-31` beside `01-01`, with no Base Year and likewise under Base Year 2001. Both operands of a measured `DifferenceInDays` complete in one anchor year: `DifferenceInDays("31.12.", "01.01.")` is `-365` with no Base Year and `-364` under 2001, and `DifferenceInDays("01.01.", MD)` over a stored `12-31` is 365 and 364. A yearless constant shifted back across 1582 lands where every leap year from 1904 to 2020 lands, so the constants' anchor year has no witness beyond that span as of a12-dmkits `08b0d6499`. Measured under `==` on the stored source and under `DifferenceInDays`; a shifted constant's comparison, `MM` sources, `AddMonths`, ordering comparisons and extrema over a year-crossing shift are unmeasured.

Sources: [yearless anchor](../docs/sources/temporal-constant-and-base-year-probes.md#src-yearless-anchor-is-the-base-year), [yearless shift anchor](../docs/sources/temporal-constant-and-base-year-probes.md#src-yearless-shift-anchor), [Base-Year conditioning](../docs/sources/computation-placement-and-constant-probes.md#src-difference-gate-base-year-conditioning).

### Comparison entry and grouping

**A comparison first meets the constant-pair gate of [§5 §1.4](04-numbers-and-decimals.md#14-the-constant-pair-gate), and braces preserve constantness.** Its temporal consequences:

- **Grouping is observable at authoring.** `Today == Today` is refused, `{Today} == Today` and `Today == {Today}` are admitted, and `{Today} == {Today}` is refused again; `Now` has the same distinction. A bare `Today` against `"05.03.2024"` is admitted in either order, grouping that `Today` makes the pair fail the constant gate, and grouping the literal leaves its admission unchanged.
- **Depth beyond the first brace changes nothing**, because the gate counts ungrouped clocks rather than reading a nesting level: `{{Today}} == Today` is admitted as `{Today} == Today` is, and `{{Today}} < 1` is refused as `{Today} < 1` is. Which way a group moves the verdict turns on the partner: against a Number constant a group never admits — it converts the date-kind refusal into the constant one — while against another clock it always admits, at either depth.
- **The left temporal-type requirement makes the gate directional.** `Today < 1` clears it and is refused later with `MVK_INVALID_COMPARE_TO_DATE`, while `1 < Today` is refused with `MVK_INVALID_COMPARE_TO_CONST`. The later kind gate ([below](#cross-kind-comparison-classes)) is not directional: `[Due] < 1`, `1 < [Due]`, `[Due] < [Amount]` and `[Amount] < [Due]` each draw `MVK_INVALID_COMPARE_TO_DATE`. So removing braces or swapping operands does not preserve legality or diagnostics.

Sources: [comparison entry gates](../docs/sources/static-admission-and-class-probes.md#src-comparison-entry-gates), [ordering date class](../docs/sources/static-admission-and-class-probes.md#src-ordering-date-class-reads-the-pair).

### Cross-kind comparison classes

**Two operands of different kinds draw one class, chosen by an ordered walk over the pair; a checker judging each side alone reports two classes where the Kernel reports one.**

**Equality (`==`, `!=`) between two fields asks its kind arms in a fixed order, and the first to refuse draws the class.** Each arm claims its kind on either side:

| Order | Arm claims the pair when one side is | Class |
|---|---|---|
| 1 | a Confirm field | `MVK_INVALID_COMPARE_TO_YES` |
| 2 | a Boolean field | `MVK_INVALID_COMPARE_TO_YESNO` |
| 3 | a temporal value (Date, Time, DateTime, fragment) against a non-temporal one | `MVK_INVALID_COMPARE_TO_DATE` |
| 4 | a DateRange | `MVK_INVALID_COMPARE_TO_DATE_RANGE` |
| 5 | a text, Enumeration or Number arm | that arm's class |

So a Confirm against a Date, a DateRange or an Enumeration draws `MVK_INVALID_COMPARE_TO_YES`, a Boolean against a Date, a String or a Number `MVK_INVALID_COMPARE_TO_YESNO`, a Date against a DateRange, an Enumeration or a Number `MVK_INVALID_COMPARE_TO_DATE`, and a DateRange against a String, an Enumeration or a Number `MVK_INVALID_COMPARE_TO_DATE_RANGE`. A Confirm against a fragment, a Time or a Custom field draws `MVK_INVALID_COMPARE_TO_YES`, and a Boolean against a Time or a Custom field `MVK_INVALID_COMPARE_TO_YESNO`. Two temporal operands pass to [the temporal pair gate](#the-temporal-pair-gate). The non-temporal arms after the fourth, and the same walk at a computation's generated comparison, are [§11 §1.4](09-computations.md#14-wrong-kind-constants-and-field-sources)'s.

**Ordering (`<`, `<=`, `>`, `>=`) asks two questions of the pair, in order.** First both operands must be orderable — a Number or a temporal value (Date, Time, DateTime, fragment) — and otherwise `MVK_INVALID_TYPE_FOR_COMPARISON` is drawn whichever side fails; String, Enumeration, Boolean, Confirm, DateRange and Custom are not orderable, a Custom declaration carrying the String kind here. Then a temporal operand against a Number draws `MVK_INVALID_COMPARE_TO_DATE`, in either order. Measured members: a fragment, a Time and a Date ordered against text and a Custom field ordered against a Number draw the first class; a numeric ordering collapses String, Enumeration, Boolean, Confirm and DateRange into it; a Date field against a Number field in both orders and against a numeric literal on either side draws the second. A tolerance operator has its own class: a DateTime against a Number and a Custom field against a Number draw `MVK_INVALID_TYPE_FOR_TOLERANCE_OP`. A fragment, a Time and a DateTime each order against their own kind.

**A constant is typed before the walk and meets the arms from arm 3 on as a field of its kind would; arms 1 and 2 claim only a Confirm or Boolean field.** The Boolean arm answers before the date arm, and the date arm before an Enumeration's domain is asked: `[Paid] == "05.03.2024"` draws `MVK_INVALID_COMPARE_TO_YESNO`, while `[Tier] == "05.03.2024"` and `[Tier] == Now` draw `MVK_INVALID_COMPARE_TO_DATE`. A date or clock constant opposite a text draws `MVK_INVALID_COMPARE_TO_DATE`, and so does a date constant ordered against a Number, both sides being orderable. Opposite a DATE_RANGE a date constant lands on the date arm, `MVK_INVALID_COMPARE_TO_DATE`, and a Number, Boolean or text constant on the range arm, `MVK_INVALID_COMPARE_TO_DATE_RANGE`. A date fragment meets the same component test as a Date: `[FiscalYear] == "05.03.2024"` and `[Season] == "05.03."` are admitted, while `[FiscalYear] == 2024` draws `MVK_INVALID_COMPARE_TO_DATE`, a number being no date constant.

**`BaseYear` meets the `==` walk as a Number opposite every kind but a Date**, which takes it as the date-typed source of [§7](#7-the-point-in-time-and-reference-sources), in either position, while its range endpoints meet the walk as a date. Opposite a String `[Note] == BaseYear` draws `MVK_INVALID_COMPARE_TO_ENUM_OR_STRING`, as an Enumeration does, labelled or not; opposite a DATE_RANGE `MVK_INVALID_COMPARE_TO_DATE_RANGE`; opposite a Time or a DateTime `MVK_INVALID_COMPARE_TO_DATE`; and opposite a scale-2 Number `MVK_INVALID_COMPARE_DEC_PLACES`; a Date and a scale-0 Number are admitted. `StartOfDateRange(BaseYear)` and `EndOfDateRange(BaseYear)` draw `MVK_INVALID_COMPARE_TO_DATE` opposite a String, a Number, a DATE_RANGE, a Time or an Enumeration.

Sources: [inbound 2026-09-25e arm order](../docs/sources/inbound-handbacks.md#inbound-2026-09-25e-comparison-arm-order), [inbound 2026-09-25e base type](../docs/sources/inbound-handbacks.md#inbound-2026-09-25e-value-list-base-type), [inbound 2026-09-26d constant typing](../docs/sources/inbound-handbacks.md#inbound-2026-09-26d-constant-typing), [condition class projection](../docs/sources/diagnostic-class-vocabulary-and-sweeps.md#src-condition-class-projection), [ordering date class](../docs/sources/static-admission-and-class-probes.md#src-ordering-date-class-reads-the-pair).

### The temporal pair gate

**Two temporal operands of a direct comparison are admitted by three questions of their formats, after a declared Base Year supplies a missing year:** both carry a year or neither does; both carry some date component or neither does; and, under `==` and `!=` only, both carry some time component or neither does. The gate does not compare component sets. Ordering therefore admits `yyyy-MM` against `yyyy-MM-dd` and Date against DateTime, and a `yyyy` operand compares with a `yyyy-MM` one and with a complete date; equality refuses the Date/DateTime pair. A yearless operand against a year-bearing one is refused `MVK_INVALID_COMPARE_TO_DATE` unless the model declares a Base Year. Equality is the measured operator throughout, so a pair equality refuses may still be ordered. As a total function it also admits `HH:mm` against `HH:mm:ss` under ordering, a pair no admitted declaration reaches ([above](#the-format-vocabulary)).

**Two date-only operands of a direct comparison compare as two dates, each completed by its own component set**, the completion [§6.1](#61-fragments) states for a fragment, here on component-omitting DATE declarations: a missing month or day becomes `01` and a missing year the declared Base Year, an `MM` operand's included ([its carrier row](#where-a-yearless-value-gets-its-year)), and the completed dates then compare, so the shorter set does not narrow the comparison to the components both carry. So under Base Year 2023, `yyyy-MM` `2023-06` is before `MM-dd` `06-11`, `yyyy` `2023` before `yyyy-MM` `2023-06`, `MM` `06` before `06-11` and `07` neither equal to it nor before it, and `yyyy-MM` `2024-06` after `06-11`, while in a row holding `2023-01`, `01-01`, `01` and `2023` every measured pair is equal. Measured under `==`, `<` and `>` on the spellings `yyyy`, `yyyy-MM`, `MM`, `MM-dd` and `yyyy-MM-dd` under one Base Year; other operators, DATE_FRAGMENT declarations, compact and dotted spellings, partial precision, time-bearing operands, yearless pairs without a Base Year and the computation arm are unmeasured here.

**The temporal extrema are stricter.** Operand-list `Min`/`Max` and field-list `MinValue`/`MaxValue` over temporal operands require identical complete component sets after Base-Year supplementation, and a DATETIME extremum requires all six components, year through second.

Sources: [fragment pair comparison](../docs/sources/temporal-constant-and-base-year-probes.md#src-fragment-pair-comparison), [operation granularity separability](../docs/sources/temporal-and-message-probes.md#src-temporal-operation-granularity-separability), [value family](../docs/sources/computation-placement-and-constant-probes.md#src-temporal-value-family-is-the-formats-not-the-kinds).

---

## 2. Addition and difference are asymmetric and calendar-corrected

### 2.1 What the operations produce

**Every numeric extraction and every difference is a non-expandable scale-0 Number operation.** This covers Day, Month, Quarter and Year extraction and Hour, Minute and Second extraction — from a field, from a derived operand, from a range endpoint ([§8.3](#83-bound-extraction)) or from direct or range-selected `BaseYear` — and the differences in all six units. *Non-expandable* means it lacks the multiplicative-constant capability of [§5 §1](04-numbers-and-decimals.md#1-scale-gates----checked-at-parse-time), so `==` and `!=` never pad it: assigned to a fractional Number target it is refused `MVK_INVALID_COMPARE_DEC_PLACES`, the one waivable code. Operation-form `RoundDown`, `RoundUp`, `RoundAccounting` and `Abs` accept these results directly. Direct numeric `BaseYear` is admitted beneath them likewise, being a number-like reference operation rather than an authored numeric literal. Measured scope: the extractors, the month and year differences and the range-endpoint component; the day and sub-day differences' scale class is unmeasured.

- **Over an empty operand they yield symmetric fillable zero**, in validation and in computation alike: an empty Date contributes numeric zero to a computation rather than leaving it unevaluated. Under rounding both movement directions survive, while `Abs(0)` keeps only possible magnitude growth. Direct and derived Base-Year values are fixed. Formal unavailability stays UNKNOWN in validation and poison in computation, through either wrapper.
- **A filled operand yields a fixed component or difference.** An unreal or incomplete constructed operand yields the amount `0` with its own provenance ([§3.5](#35-reasons-and-their-composition)).

**A shift yields a temporal value carrying its source's component set**: `AddDays` over a DateTime keeps the clock (`15T22:00 + 1 = 16T22:00`), and an extractor over a shift is admitted exactly where the source's set carries its component ([§9](#9-datetime-rides-the-date-format-definition--but-the-operand-gates-are-per-operator-)).

Sources: [recursive temporal expression](../docs/sources/temporal-and-message-probes.md#src-recursive-temporal-numeric-expression), [parallel numeric operations](../docs/sources/computation-scheduling-probes.md#src-parallel-numeric-operations), [calendar expression family](../docs/sources/temporal-runtime-fold-probes.md#src-calendar-expression-family).

### 2.2 Shift amounts

**All six shifts convert their amount the same way.** `AddDays`, `AddMonths`, `AddYears`, `AddHours`, `AddMinutes` and `AddSeconds` admit an ordinary signed Number operation, truncate its reached decimal toward zero — not rounded — and keep the low signed 32 bits, like Java `BigDecimal.intValue()`. Overflow wraps; it is neither range-rejected nor saturated: `4294967303` (`2^32 + 7`) shifts by `7` and `4294967296` by `0`. A sub-day shift narrows before multiplying by its unit.

The amount is evaluated by the ordinary numeric-expression semantics, authored order and directional missing provenance included:

- **An empty direct Number-field amount supplies numeric zero with missing provenance.** With a source value present, the shift keeps the same concrete value marked not-given, so a true downstream comparison fires OMISSION rather than VALUE. An empty Number field plus `1` supplies the concrete amount `1`, marked not-given.
- **A domain-invalid amount has no amount to apply** and yields a valueless Date: `AddDays(StartDate, RoundAccounting([x] / 0, 2))` clears a stale Date target and does not attach the numeric `berechnungsWertFehler` to it. Payload absence does not itself introduce missingness: with a present source and the fixed invalid amount `1/0`, a numeric extractor over the shift yields fixed zero and a true comparison is VALUE; with an empty source it yields fillable zero and OMISSION.

**The shift evaluates its Date or DateTime source before its amount.** In computation a formally unavailable source stops before the amount. In validation the amount is still reached, and a runtime failure there can produce the authored rule's VALUE error despite the earlier unavailable source. A cause-free empty source reaches the amount in both phases.

Sources: [recursive temporal expression](../docs/sources/temporal-and-message-probes.md#src-recursive-temporal-numeric-expression), [calendar expression family](../docs/sources/temporal-runtime-fold-probes.md#src-calendar-expression-family).

### 2.3 Month and year shifts

**`AddYears` and `AddMonths` follow different end-of-month conventions:**

- **`AddYears` maps the last day of February to the last day of February**, correcting *into* a leap year: `AddYears("28.02.2023", 1) = 29.02.2024`, and `28.02.1999 + 1 year = 29.02.2000`, not the plain `28.02.2000`.
- **`AddMonths` preserves the day number and clamps** an end-of-month overflow to the shorter month's last day, never carrying into the next month: `AddMonths("28.02.2011", 12) = 28.02.2012`; `31.01.2008 + 1 month = 29.02.2008`.

The two therefore disagree across a leap-year boundary, so an age check built on either is wrong around leap days. Calendar field mutation preserves the source's millisecond, except that the leap-to-nonleap February-28 correction clears the entire clock.

Sources: [calendar expression family](../docs/sources/temporal-runtime-fold-probes.md#src-calendar-expression-family).

### 2.4 Completed-period differences

**`DifferenceInMonths` and `DifferenceInYears` order their endpoints, compute the largest nonnegative whole number of months or years that can be added to the earlier date without passing the later one, and then apply the sign of `second − first`.** A reverse fractional result truncates toward zero:

```
DifferenceInMonths("31.01.2010", "30.03.2010")   -- 1, not 2
```

Sources: [calendar expression family](../docs/sources/temporal-runtime-fold-probes.md#src-calendar-expression-family).

### 2.5 Day differences

**`DifferenceInDays(a, b)` is a signed model-zone calendar-step count, aware of the time of day.** It orders the two resolved legacy-calendar values, qualifies a whole-year candidate through the corrected year mutation `AddYears` uses, jumps by `yearDifference × 365` days with a day-of-month mutation, then advances one calendar day at a time until the next landing would pass the later operand, and finally restores the authored order (`b − a`). The year qualification uses the sign-independent later, post-gap year landing of [§2.7](#27-calendar-basis); every lower-bound or residual day landing assumes the offset of the instant it starts from and keeps the millisecond ([§5](#5-time-zones-and-the-sub-day-difference)). A DateTime operand is admitted, and a mixed `(datetime, date)` pair is legal, the date reading as midnight in the model zone.

| Operands | Result | Why |
|---|---|---|
| `23:00 → 01:00` next day | 0 | time-of-day aware, not the date parts' 1 |
| Berlin `2024-03-30T12:00 → 2024-03-31T12:00` | 1 | despite only 23 elapsed instant hours |
| Berlin `2024-03-30T02:30 → 2024-03-31T01:45` | 1 | one calendar-day step lands at `01:30` before the second operand; wall-label seconds (23 h 15 m) would truncate to 0 |
| Berlin `2023-04-01T02:30 → 2024-04-05T02:30` | 369 | each step starts from its source offset; a direction-selected landing gives 370 |
| Berlin `2003-03-31T02:30 → 2024-03-31T03:00` | 7670 | compute-time year qualification; direction-selected gap qualification gives 7671 |
| `Pacific/Apia` `2011-12-29T12:00 → 2011-12-31T12:00` | 1 | one day-of-month step skips the missing 30 December; a proleptic wall-label coordinate gives 2 |

The wall-seconds quotient `Δ wall-label seconds / 86 400` agrees with the first two rows but is not generally equivalent, even within Berlin: it fails around special-hour landings and skipped whole dates.

Sources: [calendar expression family](../docs/sources/temporal-runtime-fold-probes.md#src-calendar-expression-family), [temporal difference gates](../docs/sources/computation-placement-and-constant-probes.md#src-temporal-difference-gates-read-the-format).

### 2.6 Sub-day arithmetic

**Sub-day arithmetic works on exact integer milliseconds since the epoch.** Stored and constructed Date, Time and DateTime syntax has whole-second precision, but `Now` keeps the injected validation clock's millisecond ([§7](#7-the-point-in-time-and-reference-sources)).

- **`AddHours`, `AddMinutes` and `AddSeconds`** need a date-bearing operand whose format carries the selected time component ([§9](#9-datetime-rides-the-date-format-definition--but-the-operand-gates-are-per-operator-)); they keep the DateTime format and carry across the day boundary, and their result keeps its exact instant ([§5](#5-time-zones-and-the-sub-day-difference)). A Time-only operand is refused; `TimeFromDateTime(AddHours(…))` yields a Time.
- **`DifferenceInHours`, `DifferenceInMinutes` and `DifferenceInSeconds`** subtract absolute instants: `(epochMillis(b) − epochMillis(a)) / unitMillis`, truncated toward zero, which is the floor of the absolute difference with the sign of the operand order. A reverse difference of −5 h 30 m is `-5`, not `-6`, and a `999 ms` residual is `0` seconds. The order is `b − a`, as for `DifferenceInDays`. Measured on the Groovy-dynamic strategy, with the generated static Java strategy agreeing on the exercised historical cases; no identical-behaviour claim is made for a TypeScript/luxon target.

Sources: [calendar expression family](../docs/sources/temporal-runtime-fold-probes.md#src-calendar-expression-family), [temporal difference gates](../docs/sources/computation-placement-and-constant-probes.md#src-temporal-difference-gates-read-the-format).

### 2.7 Calendar basis

**No single calendar implementation serves every temporal consumer; the operand's calendar basis is observable.** A real value produced by `Date(...)` keeps the constructor's model-zone legacy hybrid-calendar identity ([§3.4](#34-calendar-reality)) through the legal `AddDays`, `AddMonths` and `AddYears` and the `DifferenceInDays`, `DifferenceInMonths` and `DifferenceInYears` consumers. The calendar of a shift or completed-period difference whose source is a stored value, a fragment or a range and whose landing falls before the 1582 cutover is not stated.

- **A constructed-Date month or year shift whose nominal field-preserving landing lies in the missing `1582-10-05..14` labels moves forward by ten civil labels.** So `1582-09-10 + 1 month = 1582-10-20` and `1581-10-10 + 1 year = 1582-10-20`. From `1582-09-10`, the constructed 15 October and 20 October are zero and one whole month away; from `1581-10-10`, 15 October 1582 is zero whole years and 11 whole months away, and 20 October one year and 12 months.
- **The `AddYears` February-28 correction uses Gregorian leap status even on the Julian side**: `1499-02-28 + 1 year = 1500-02-28`, although a `Date(...)` whose Year component is a field holding 1500 constructs 29 February 1500.
- **A constructed-Date shift keeps the exact model-zone instant its particular calendar mutation selects, so equal decoded labels do not imply equal results.** Direct Date comparison resolves both operands to exact instants: a constructed or shifted Date supplies its retained instant, an ordinary stored Date one derived by the ordinary model-zone parse. A day landing follows [§5](#5-time-zones-and-the-sub-day-difference)'s source-offset re-fit: under `Europe/Berlin`, `AddDays(Date("30", "9", "1916"), 1)` carries CEST and lands at `1916-09-30T22:00:00Z`, while `AddDays(Date("1", "3", "1916"), 214)` carries CET into the same label and lands at `1916-09-30T23:00:00Z`, equal to a fresh `Date("1", "10", "1916")`. At that repeated midnight `AddDays(Date("30", "9", "1916"), 1) == Date("1", "10", "1916")` is false, while the corresponding one-month and one-year comparisons are true.
- **`AddMonths` and `AddYears` resolve at compute time, independently of the amount's sign**: both signed month routes from 1 September and 1 November 1916, and both signed year routes from 1 October 1915 and 1917, into 1 October 1916 select the later CET instant. A nominal month or year landing in a gap moves to its post-gap label.

The year components in these examples are fields: a quoted Year constant is bounded to 1800–2199 ([§3.1](#31-date)). Every other operation follows its own clause.

Sources: [calendar expression family](../docs/sources/temporal-runtime-fold-probes.md#src-calendar-expression-family), [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21).

> **Non-normative implementation note.** Keep the operand's calendar basis; use a proleptic-Gregorian function only where a narrowed domain proves it equivalent. Write the `AddMonths` clamp and the `AddYears` February correction as code rather than trusting a library default, and the sub-day family as integer epoch milliseconds with truncating division.

### 2.8 Reading operands

**A difference reads its first temporal operand before its second, from one complete environment.** In computation a formally unavailable first operand stops before the second; in validation the second is still reached before the numeric result is classified, so a runtime failure there fails the rule. A cause-free empty or unreal first result does not stop the second operand. The order holds when the difference is nested in a `Having` filter. Measured for `DifferenceInDays` in both phases; the other units are unmeasured.

- Either missing operand maps to symmetric fillable zero; formal unavailability stays UNKNOWN in validation and poisons in computation; a structural addressing failure is a fault, not UNKNOWN.
- A temporal extraction over a repeated row reads that row's decoded value: an empty source yields symmetric fillable zero, a filled one a fixed component, and a formally unavailable one UNKNOWN in validation.
- `DifferenceInDays` reads each operand's decoded local label and its already-resolved exact instant under the model-zone profile; the sub-day differences read the exact instants and the selected unit ([§2.6](#26-sub-day-arithmetic)).

Sources: [recursive difference effects](../docs/sources/temporal-runtime-fold-probes.md#src-recursive-difference-effects), [temporal difference gates](../docs/sources/computation-placement-and-constant-probes.md#src-temporal-difference-gates-read-the-format).

### 2.9 Operand shapes

**A shifted operand is admitted in a difference, and an extremum is not.** `DifferenceInDays(AddDays(Due, 1), Day)`, `DifferenceInMonths(AddYears(Due, 1), Due)`, `DifferenceInYears(Due, Today)` and `DifferenceInHours(AddHours(Stamp, 1), Stamp2)` are admitted, the first also as a computation's operation. `Max(Rows*/RDay)` or `Min(Due, Day)` as a difference's or a direct extractor's operand, and an extremum inside a shift there, draw `MVK_UNEXPECTED_TOKEN`; a starred `Rows*/RDay` operand draws `MVK_NO_WILDCARDS_ALLOWED`; and `DifferenceInMinutes(Clock, AddMinutes(Clock2, 5))` over Time fields draws `MVK_INVALID_TIME`. A function operand takes a bare reference: `DifferenceInDays([/G/F], …)` draws `MVK_UNEXPECTED_TOKEN`. Each slot's class is the operator reference's column S, and the component gates are [§9](#9-datetime-rides-the-date-format-definition--but-the-operand-gates-are-per-operator-)'s.

Sources: [K22 static batch 5](../docs/sources/group-count-topology.md#src-k22-static-s5), [yearless anchor](../docs/sources/temporal-constant-and-base-year-probes.md#src-yearless-anchor-is-the-base-year).

---

## 3. Constructing dates, and checking validity

### 3.1 `Date(...)`

**`Date(Day, Month, Year)` builds a date from numeric parts.** `Date(Day, Month)` takes the year from the Base Year, and `Date(Day, Month, Century, ShortYear)` forms it as `Century × 100 + ShortYear`. Each explicit component is a field, its matching direct Date extractor (three-part form only), or a quoted decimal string constant, and the forms may be mixed across positions. A bare numeric token is not a component literal: it is read as an entity name and refused `MVK_INVALID_ENTITY`. The constructed date is **invalid** when a referenced part is unfilled or the parts form no real calendar date: `Date("31", "11", "2000")` (November has 30 days), or 30 February.

**Each position admits these component forms**; every other form is refused at that position:

| Position | Quoted constant | Number field | String field | Temporal field | Extractor |
|---|---|---|---|---|---|
| Day | any width, `1 ≤ v < 32` | stored width 2, or maximum 31 | maximum length 2 | — | `DayFromDate` |
| Month | any width, `1 ≤ v < 13` | stored width 2, or maximum 12 | maximum length 2 | — | `MonthFromDate` |
| Year (complete) | exactly 4 code units, `1800 ≤ v < 2200` | stored width 4, or any maximum from 1000 through 9999 | maximum length 4 | declared exactly `yyyy` | `YearFromDate` |
| Century | exactly 2 code units, `18 ≤ v < 22` | stored width 2, or any maximum from 10 through 99 | maximum length 2 | — | — |
| Short-Year | exactly 2 code units, `0 ≤ v < 100` | stored width 2, or exactly 99 | maximum length 2 | — | — |

- **A quoted constant**, after quote removal, must be a nonempty sequence of UTF-16 code units each accepted by the host decimal-digit predicate, and is then parsed as an integer. Day and Month have no width restriction, so leading zeroes of any length are legal. A supplementary-plane digit occupies surrogate code units and fails this character-wise gate.
- **A Number field** must have an effective maximum of zero fractional digits (an omitted maximum passes), admit only nonnegative values by its sign policy or an explicit minimum, and carry either the complete stored-length bound of the table or its positional maximum. `maxIntegerDigits` is not the stored-length alternative.
- **A String field** must have a maximum length equal to the positional width and either be an extensible enumeration or use exactly one of `[0-9]+`, `[0-9]*`, `\d+`, `\d*`, `[0-9]{width}` or `\d{width}`; regex-equivalent spellings are refused.
- **A temporal field declared exactly `yyyy`** is admitted at the complete-Year position on DATE, TIME and DATE_TIME alike, and refused at Day, Month and both split-year positions; every other declared format is refused at Year. The position and the format each decide; the kind decides nothing.
- **An extractor operand** uses the ordinary nonliteral Date-expression grammar, not only a direct field, and must resolve to a value whose declared format carries the selected component after optional Base-Year supplementation. The kind is not read: a TIME- or DATE_TIME-declared field formatted as a complete date is admitted at Day, Month and Year alike, while any clock-formatted field is refused `MVK_WRONG_DATE_FORMAT_FOR_OP`. A direct temporal literal inside the extractor is refused, with the literal-entry diagnostic of [§3.3](#temporal-extractor-operands). The extractor's source is evaluated before its component is passed on, so an empty source keeps the construction incomplete while formal unavailability stays exact. The four-part form refuses an extractor in either split-year position.

**Conversion and range.** An admitted String or `yyyy` field is converted from its stored text as a Number. An empty component keeps the construction incomplete, formal unavailability stays exact, and a present out-of-range component reaches the constructor's reality check rather than being clamped. The four-part form evaluates Day, Month, Century, then Short-Year, and requires the narrowed Century to be nonzero: a present zero Century makes the Date unreal even beside a positive Short-Year. A fixed Short-Year zero is present, while an unfilled field or extractor result keeps the construction incomplete.

**The extensible-String alternative** is a client-interface capability of a String declaration, distinct from an Enumeration declaration, and the DM-JSON model format does not expose that flag. Its width requirement stays exact, but it need not carry a digit pattern, so the conversion cannot assume unsigned integer text: it accepts the Java decimal spellings — a leading sign, a leading or trailing decimal point, an exponent, BMP decimal digits — after normalizing a comma to a dot, then truncates toward zero and keeps the low signed 32 bits. So `+1` contributes 1, `.5` contributes 0, `2e3` contributes 2000 and `3e9` contributes −1294967296; the declared width still bounds which tokens reach a position. A nonnumeric token that passed the String's formal checks raises a runtime conversion failure rather than producing an empty component or an unreal date. Unmeasured.

**A fully present Date must also resolve to a strict host-calendar instant within signed 64-bit milliseconds.** A year beyond that range is unreal, not a conversion failure, and there is no four-digit runtime year ceiling: an extensible Year `2e8` can construct a real date whose spelling then fails the target's formal format, while `3e8` and `2e9` construct unreal dates. Unmeasured.

**Arguments are evaluated in authored order.** In validation an earlier formally unavailable component does not stop later conversion, so a later nonnumeric extensible String still fails the rule; computation stops at formal poison. A cause-free non-relevant extractor component does not stop a Date computation from reading later components, so a later formal poison still wins; with no later failure, construction keeps the non-relevance, and an enclosing `Min` does not substitute its concrete fallback. With no argument raising, formal unavailability and missing-component provenance keep their ordinary constructor meaning. Boolean short-circuiting still decides whether the constructor is reached at all ([§12 §3.1](10-validation-and-polarity.md#31-truth-testing-and-message-classification)).

**A computed component-omitting target is checked after rendering.** The target format may discard the expression's year, so the target check uses the stored value's format-specific completion ([stored temporal text](#stored-temporal-text)). Under Base Year 1583 a month-and-day shift reaching January 1584 still renders `01-01` and is refused after completion back into 1583, while the month-only target stays admitted. A literal `"29.02.2024"` assigned to `MM-dd` under Base Year 2023 keeps an errored `02-29` attempt and poisons its dependent; under Base Year 2024 the same assignment succeeds. Year and year-month targets refuse five-digit attempted years as format failures. Arithmetic itself keeps the intermediate calendar result, below-floor dates included, so returning it to the storage range before assignment succeeds.

Sources: [construction route](../docs/sources/temporal-and-message-probes.md#src-temporal-construction-route), [operand family](../docs/sources/computation-placement-and-constant-probes.md#src-temporal-operand-family-is-the-formats-not-the-kinds), [recursive Date components](../docs/sources/temporal-runtime-fold-probes.md#src-recursive-date-components), [calendar expression family](../docs/sources/temporal-runtime-fold-probes.md#src-calendar-expression-family), [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21).

### 3.2 `Time(...)` and the clock anchor

**`Time()` through `Time(Hour, Minute, Second)` supply a leading prefix of zero to three components, and every omitted trailing component is the fixed value zero**: `Time()` is midnight and `Time("10", "30")` is `10:30:00`. It is the one call measured whose whole argument list may be empty ([concrete syntax §3.1](12-concrete-syntax.md#31-which-class-a-refused-text-draws)). Each authored component is statically restricted to its matching field, extractor or in-range decimal-digit string constant before runtime conversion, and the forms may be mixed across positions:

- **A Number field** must have an effective maximum of zero fractional digits (an omitted maximum passes), admit only nonnegative values by its sign policy or an explicit minimum, and carry either maximum stored length 2 or the exact positional maximum, 23 for Hour and 59 for Minute or Second; `maxIntegerDigits = 2` is not the stored-length alternative. Under the maximum-length-2 profile with no minimum, `5` produces the component `05`, while stored `"05"` is refused `zahlHatFuehrendeNullen` and clears the target; adding a minimum stored length of 2 also refuses `5`, so that profile represents no valid single-digit component.
- **A String field** must have maximum length 2 and either be an extensible enumeration or use one of `[0-9]+`, `[0-9]*`, `\d+`, `\d*`, `[0-9]{2}` or `\d{2}`; unlike a Number, this carrier accepts and converts `"05"`.
- **An extractor** must be `HoursFromTime`, `MinutesFromTime` or `SecondsFromTime` at the matching position. Its operand is the ordinary nonliteral temporal-expression grammar: any statically admitted Time- or DateTime-bearing expression whose format carries the selected component, while a direct temporal literal inside the extractor is refused. The nested source is evaluated before the extractor call.

At runtime an empty extractor source reaches the constructor as numeric zero with missing provenance and still makes the constructed Time incomplete, while a present temporal expression that yields no value reaches it as fixed numeric zero; formal unavailability stays exact. A formally unavailable or non-relevant supplied component dominates missingness, a missing supplied component produces an incomplete, not-given no-value, and a fully present but impossible clock produces a distinct present, unreal no-value.

**A present Time carries the date anchor 1970-01-01.** A present clock field, a `Time(...)` value and a `TimeFromDateTime(...)` result all do. Where a Base Year admits `YearFromDate` over these Time-valued expressions ([§9.2](#92-the-component-classes)), its result is **1970** whatever Base Year is configured: the exemption opens the component gate and does not replace the anchor. Missing, unreal and formally unavailable sources keep the ordinary numeric-extractor rules. Measured for the clock field and both constructed-Time forms.

Sources: [inbound 2026-09-26o](../docs/sources/inbound-handbacks.md#inbound-2026-09-26o-production-close), [inbound 2026-10-09 extensions](../docs/sources/inbound-handbacks.md#inbound-2026-10-09-extensions), [operand family](../docs/sources/computation-placement-and-constant-probes.md#src-temporal-operand-family-is-the-formats-not-the-kinds); Kernel source read: the component checker, Time construction and runtime projection.

### 3.3 `DateTime(date, time)` and the DateTime projections

**`DateTime(date, time)` evaluates its Date argument before its Time argument** and resolves a real combined wall label in the model zone. In computation, poison aborts before later arguments; clean absence and cause-free non-relevance do not. After both operands are reached, non-relevance takes precedence over an ordinary no-value, and the Time side's reasons are kept. **A component-omitting Date argument completes to its earliest day.** `yyyy` completes to January 1 and `yyyy-MM` to the first of its month, with or without a Base Year. A yearless `MM-dd` or `MM` argument is refused `MVK_WRONG_DATE_FORMAT_FOR_OP` without a Base Year, measured in a rule condition, and otherwise completes in the Base Year, `MM` to the first: under Base Year 2024, `2024`, `2024-03`, `03` and `03-31` with `12:30:00` store `2024-01-01T12:30:00`, `2024-03-01T12:30:00`, `2024-03-01T12:30:00` and `2024-03-31T12:30:00`. The completed label then resolves as any other, so `03-31` with `02:30:00` is a Berlin spring-gap label and clears cleanly. This is the earliest completion of [§6.1](#61-fragments). Where it is measured the Base Year equals the clock year and the year of the document's other Dates, so a yearless argument's year is not separated from the clock's. The Time argument admits a clock-formatted operand of any declared kind and refuses a complete date and a complete date-time on components; that position is reachable through `DateTime(ValueAsDate(partial, FirstDay), …)` and measured there.

**`TimeFromDateTime(source)` and `DateFromDateTime(source)` require a DateTime operand whose declared or derived format carries year, month, day, hour, minute and second**; over the admitted vocabulary only `yyyy-MM-dd'T'HH:mm:ss` does. A valueless source is returned with its not-given or non-relevant reason unchanged.

- **`TimeFromDateTime`** reads the hour, minute and second in the model zone and constructs a Time anchored at 1970-01-01, so downstream Time consumers observe the kept wall clock, not the source date or instant.
- **`DateFromDateTime`** reports the source label's own date components with the time dropped: a stored `2024-06-15T00:30:00` extracts to `2024-06-15`, not the UTC date of the kept instant, `2024-06-14` at a `+0200` model zone. The result is a **Date**: it compares against a Date field, `Today` and another `DateFromDateTime`, and is admitted as a Date-addition operand, while comparing it to `Now` or to a `TimeFromDateTime` result is refused `MVK_INVALID_COMPARE_TO_DATE`.
- **Their source gate.** Across the measured `YearFromDate` and `DateFromDateTime` carriers, a Number, String, Enumeration, Boolean, Confirm, DateRange or Custom operand is refused `MVK_NO_DATE`; the denominator holds no UNKNOWN operand. A temporal declaration whose format lacks the requested component is refused `MVK_WRONG_DATE_FORMAT_FOR_OP` instead, measured by `HoursFromTime(Date)` and `DateFromDateTime(Date)` against admitted component-bearing controls, with the declared format and not the kind deciding. This two-carrier matrix does not establish the other extractors' classes.
- **Repeatable sources.** In the measured `Projects/Choices` to `Projects/Tasks` topology both projections refuse a relative or absolute `Choices*/Stamp` operand with `MVK_NO_WILDCARDS_ALLOWED` and the same path without the star with `MVK_NO_WILDCARD`. This static boundary does not transfer to the separately admitted sibling-star `FirstFilledValue` family.

<a id="temporal-extractor-operands"></a>

**Literal recognition precedes each extractor's own gate.** `DateFromDateTime` and `TimeFromDateTime` accept temporal expressions, `Now` and a complete date-time constant such as `"05.03.2024T10:30:45"` included. A field operand is written bare; bracketing it is a parse failure. Text that parses as no temporal value draws `MVK_INVALID_DATE_STRING`, while a recognized date-only or clock-only literal under either projection draws `MVK_WRONG_DATE_FORMAT_FOR_OP`, and a recognized complete date-time literal is admitted by both. The numeric component extractors instead refuse every recognized direct temporal literal with `MVK_NO_CONST`, even when its kind differs from the extractor's: `HoursFromTime("01.01.2020")` reaches the constant refusal, while `HoursFromTime("2019-01-01")` fails literal recognition first. A nested expression is admitted: `DayFromDate(DateFromDateTime(Now))` and `HoursFromTime(TimeFromDateTime(Now))` are, and so are those forms with the complete date-time constant replacing `Now`. A transformation must keep the distinction between a direct literal and a nested expression at a numeric extractor's immediate operand.

Sources: [composition locus](../docs/sources/temporal-and-message-probes.md#src-value-as-date-locus), [DateTime component completion](../docs/sources/temporal-constant-and-base-year-probes.md#src-datetime-component-completion), [operand family](../docs/sources/computation-placement-and-constant-probes.md#src-temporal-operand-family-is-the-formats-not-the-kinds), [temporal difference gates](../docs/sources/computation-placement-and-constant-probes.md#src-temporal-difference-gates-read-the-format).

### 3.4 Calendar reality

**The constructor's reality test is model-zone-sensitive and uses the legacy hybrid calendar**, not an abstract proleptic-Gregorian date: Kernel 30.8.1 builds a non-lenient Gregorian calendar in the model's `timeZone`, whose default cutover follows Julian rules before the Gregorian transition, and a zone discontinuity can remove a whole local date. So under UTC a construction whose Year component is a field holding 1500 makes 29 February 1500 real on the Julian side, while `Date("30", "12", "2011")` is unreal in `Pacific/Apia`, where that local date was skipped. The zone database is a runtime input the Kernel version alone does not identify; a zone-free proleptic-Gregorian predicate is not equivalent.

Sources: [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), [calendar expression family](../docs/sources/temporal-runtime-fold-probes.md#src-calendar-expression-family).

### 3.5 Reasons and their composition

**A Date- or DateTime-valued operation carries either a concrete value with its calendar and instant identity, or a no-value reason; incomplete (not-given), present-but-unreal and non-relevant or malformed provenance stay distinguishable.** Reason and calendar basis compose through the legal producers:

- **An unreal `Date(...)` carries no date value**: it neither rolls over nor keeps an out-of-range label.
- **Time construction has the same dimensions**: a fixed impossible clock has no payload with fixed provenance, and an empty component no payload with missing provenance. A component of missing provenance whose value is known, such as an hour extracted from a shift whose amount read an empty field, is the missing supplied component of [§3.2](#32-time-and-the-clock-anchor). An unknown-year partially known Date interpretation stays non-relevant rather than neutral absence ([§6.3](#63-valueasdate)).
- **`DateTime(date, time)`** ([§3.3](#33-datetimedate-time-and-the-datetime-projections)): combining a Date and a Time into a nonexistent Berlin spring-gap label yields a clean no-value, whereas resolving that label as a date-time constant raises a computation value failure ([§5](#the-nonexistent-wall-label)). The kept autumn-fold construction chooses the later occurrence, observed by adding one hour to reach 03:30. These are measured on the pinned Berlin profile and do not generalize it to other zones.
- **`DateFromDateTime`, `TimeFromDateTime` and the legal shifts keep the source's no-value reason**, and real `Date(...)` descendants keep the legacy-calendar identity of [§2.7](#27-calendar-basis).
- **Numeric extractors and differences** map an incomplete operand and a present-but-unreal one to the same actual Number `0`, with fillable provenance for the first and fixed for the second, so a fired comparison can be OMISSION for incomplete input and VALUE for unreal input although the amounts agree. They map a non-relevant or malformed operand to UNKNOWN, never to zero.
- **Quarter.** `DayFromDate`, `MonthFromDate`, `QuarterFromDate` and `YearFromDate` are the direct date components; for a real source the quarter is `((month − 1) / 3) + 1` with integer division, and the zero projection of an incomplete or unreal source is `0` for Quarter as for the others.
- **Direct Date `Min`/`Max`** skips a check-relevant valueless operand when another concrete value exists, and a non-relevant operand propagates non-relevance. Operand-list extrema can select their other value while keeping the incomplete-versus-unreal distinction. This consumer admission does not widen the grammar: `YearFromDate(Min(...))` stays refused where the extractor requires a narrower source form ([§2.9](#29-operand-shapes)).
- **Temporal extrema over Time and DateTime.** Operand-list `Min`/`Max` and field-list or starred `MinValue`/`MaxValue` also admit homogeneous TIME operands, or homogeneous full-component DATETIME operands, whose declared formats pass the extremum gate of [§1](#the-temporal-pair-gate). Time selection compares each decoded time-of-day coordinate; DateTime selection compares each resolved physical instant, not its rendered wall label. In both, check-relevant valueless operands are skipped, an all-empty selection has no value, any reached non-relevant operand propagates non-relevance, and an empty, open-declared-tail or encountered-filter source keeps symmetric missing provenance on a selected value. So a seconds-level Time difference stays ordered even when a shorter display omits it, and a selected exact DateTime instant stays distinct from an equal-looking stored value on the other side of a model-zone overlap.

Sources: [composition locus](../docs/sources/temporal-and-message-probes.md#src-value-as-date-locus), [Time component provenance](../docs/sources/temporal-runtime-fold-probes.md#src-time-component-missing-provenance), [calendar expression family](../docs/sources/temporal-runtime-fold-probes.md#src-calendar-expression-family).

### 3.6 `Valid` and `Invalid` over `Date(...)`

```
Invalid(Date(Day, Month, Year))   -- fires on 31.11, 30.02, an unfilled part, …
```

**`Valid(Date(...))` and `Invalid(Date(...))` require at least one immediate component entity**, an index-selected entity included. A field nested inside an extractor does not count: an all-constant or all-extractor construction is refused `MVK_ONLY_CONSTANTS_USED`, in validation and in computation guards alike. This gate does not restrict ordinary scalar Date construction, and it is why such a validity leaf always enables message classification ([§12 §3.1](10-validation-and-polarity.md#31-truth-testing-and-message-classification)).

**Their truth projections are strong-Kleene complements, but one full verdict does not determine the other**, because the construction has reason-bearing no-values:

| Construction | `Valid(Date(...))` | `Invalid(Date(...))` |
|---|---|---|
| all parts present and well-formed, a real date | fires, VALUE | does not fire |
| well-formed, present, but no real date | does not fire | fires, **VALUE** |
| well-formed, some part empty, an all-empty row included | does not fire | fires, **OMISSION** |
| a malformed part | UNKNOWN; the formal error fires instead | UNKNOWN |
| a cause-free non-relevant component | UNKNOWN | UNKNOWN |

- The malformed row is the UNKNOWN/UNKNOWN arm of strong-Kleene complementation, not Boolean false. The non-law is at the full verdict and polarity level: incomplete and unreal constructions both leave `Valid` unfired, but `Invalid` types the first OMISSION and the second VALUE, so `Invalid` is not a unary function of the full `Valid` verdict, and a single empty result for incomplete, unreal and non-relevant constructions cannot serve both.
- In a computation alternative guard either predicate over a non-relevant component falls through to the next alternative; as a common guard it clears the target without poisoning its dependents. A later formally invalid component still wins over earlier non-relevance and poisons the computation and its dependent reads.
- To fire `Invalid` only on a complete but impossible date, prefix `AllFieldsFilled(...)`.

Sources: [recursive Date validity](../docs/sources/temporal-runtime-fold-probes.md#src-recursive-date-validity).

> **Non-normative implementation note.** Use a reason-bearing result such as `real (calendarBasis, date) | incomplete | unreal | unknown` rather than an optional date, and define each validity projection separately.

### 3.7 `Valid` and `Invalid` over a named type

**`Valid(Field, "CustomTypeName")` and `Invalid(Field, "CustomTypeName")` are the other two forms, and no third parses**: a lone field, Date field or not, a third operand after the type name, and any single call other than `Date(...)`, such as `AddDays(...)` or `DayFromDate(...)`, draw `MVK_UNEXPECTED_TOKEN`. The predicate asks whether a String or Enumeration *value* is a valid instance of a named type, not whether a field already declared as that shape is.

**Static admission requires a single non-wildcarded value-validation field whose declared type is String, Enumeration or extensible Enumeration, and a nonempty type name; it does not require the name to be registered.** Each refused arm has its own class:

| Operand | Class |
|---|---|
| a Number, Boolean, Confirm or Custom-declared field | `MVK_NO_STRING_OR_ENUM_OR_EXT_ENUM` |
| a group | `MVK_NO_GROUPS_ALLOWED` |
| a starred operand | `MVK_NO_WILDCARDS_ALLOWED` |
| an unstarred repeatable operand its host does not bind | `MVK_NO_WILDCARD` |

The last two are the confusable pair the DateRange endpoints also carry ([§8.4](#84-construction-and-equality)), with opposite fixes; the read ladder they belong to is [§10 §3.2](08-paths-and-references.md#32-the-field-value-read-)'s.

**At runtime the predicate calls the registered validator on a reached, filled operand, and on nothing else.** Both predicates pass the stored value, so an Enumeration supplies its stored token rather than its display label.

- **With a registered validator**, the two predicates are complementary for a filled value, and neither fires for an empty value.
- **With an unregistered name**, a reached, filled, formally valid operand makes the registry lookup fail inside the condition. In validation that failure aborts the rule through the runtime-failure route of [§12 §3.1](10-validation-and-polarity.md#31-truth-testing-and-message-classification) and becomes one VALUE message; it is not a true leaf, so Boolean composition keeps the failure until the rule's handler, and both standalone polarities therefore report VALUE. Inside `Having` the abort happens before the selected target read, even when that target is malformed, and the resulting message has empty `referenced` and `fillToFix` sets. In a computation precondition the same failure makes both polarities fail with a target-local `berechnungsWertFehler`, clearing the target and poisoning dependent reads.
- **An empty operand, an unreached branch and a formally unavailable operand never reach the lookup.** An empty operand fires neither predicate and, in a computation precondition, clears cleanly; an already formally invalid operand propagates its own invalidity before the lookup. So registration state cannot influence an unspecified value. How the validator is looked up, factory and registry, and how a declared custom field type is validated are [§7 A.3](06-strings-and-enumerations.md#a3-custom-field-type-validation)'s.

Sources: [inbound 2026-10-18](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-18), [`Valid`/`Invalid` operand gates](../docs/sources/static-admission-and-class-probes.md#src-validtype-operand-gates), [Having predicate family](../docs/sources/having-filter-probes.md#src-having-predicate-family), [custom validity route](../docs/sources/evaluation-and-application-routes.md#src-custom-validity-route), [type-validity computation guards](../docs/sources/computation-scheduling-probes.md#src-type-validity-computation-guards).

---

## 4. The Gregorian floor

**Dates before 16 October 1583 are invalid as stored or computed *values*.** The floor is always on and exact:

- it is strictly *before*: `1583-10-15` errors and `1583-10-16` is valid;
- a day-optional value completes its omitted day to `01` before the check ([§6.2](#62-partially-known-dates));
- a stored value is first judged real on the legacy hybrid calendar, so a real label below the floor draws the floor's `datumFalsch` and an unreal one the format's `datumFormatFalsch`: `1500-02-29`, `1300-02-29` and `1582-10-04` draw `datumFalsch`, while `1582-10-05`, `1582-10-14` and `1700-02-29` draw `datumFormatFalsch`;
- a **stored** value below it is the formal error `datumFalsch`, which suppresses referencing rules ([§3 B.1](02-logic-and-formal-errors.md#b1-what-a-formal-error-is)); a **computed** one is ERRORED; a date **range** floors its *start* the same way, with the range's own pair of codes ([§8.1](#81-declaration-and-stored-text)).

⚠ **The floor is not a criterion of the `Date(...)` constructor's reality test** ([§3.4](#34-calendar-reality)): it gates stored and computed values only. Static component admission and the immediate-entity requirement of the validity predicates apply separately. The floor is also distinct from the opt-in pre-1900 check below.

Sources: [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), [calendar expression family](../docs/sources/temporal-runtime-fold-probes.md#src-calendar-expression-family).

### 4.1 The pre-1900 check

**`DateType.youngerThan1900Check` is an opt-in, declaration-owned basic-format check**, independent of Date precision and of the always-on floor. When enabled, a concrete Date strictly before `1900-01-01` is the formal error `datumFalsch`, and `1900-01-01` is valid. Ordinary partial-Date completion and reason preservation happen first, so an unknown-year value stays non-relevant rather than being reclassified as an ancient concrete date. The same declared gate classifies an admitted computed full-Date target ([§11 §4.2](09-computations.md#42-temporal-targets)); a partial-Date computation target is statically refused and adds no runtime case.

**On DATE and DATE_FRAGMENT the check is declarable only where the format carries a year**, and the declaration kinds otherwise differ:

| Declaration | Year-free formats | Year-bearing formats |
|---|---|---|
| DATE | refused at model admission, `MVK_ADDITIONAL_CHECK_INVALID` | admitted |
| DATE_FRAGMENT | as DATE: of the thirteen admitted formats the six year-free ones — `MM`, `MM-dd`, `MMdd`, `ddMM`, `dd.MM.`, `HH:mm:ss` — are refused | the seven year-bearing ones are admitted |
| DATE_RANGE | exempt: all eight admitted `(format, separator)` pairs take the check, the four year-free ones included | admitted |
| TIME, DATE_TIME | the property does not exist on these declarations: injecting it is rejected by the model deserializer, naming the declaration type and the property, before any consistency gate | — |

The Kernel states the refusal in component terms — a date field lacking a year cannot carry the check — not kind terms. So the year co-requirement belongs to the DATE and DATE_FRAGMENT carriers, not to the check: a consumer gates the check on year presence there and must not model it as admitted-and-inert on those two kinds, while one enforcing the requirement on every temporal kind refuses four legal range declarations.

Sources: [inbound 2026-09-08](../docs/sources/inbound-handbacks.md#inbound-2026-09-08), [inbound 2026-09-05c](../docs/sources/inbound-handbacks.md#inbound-2026-09-05c), [inbound 2026-09-21](../docs/sources/inbound-handbacks.md#inbound-2026-09-21-corrections).

### 4.2 Message keys of a stored Date refusal

**A stored Date refusal selects its message key on a finer axis than its code** ([§5](04-numbers-and-decimals.md) describes that axis), by one component reading of the completed text; the format decides, never the kind. The reading runs in this order, and the first step that refuses selects the key:

1. **Syntax.** Text failing the format's digit pattern selects `DATUM_FORMAT`.
2. **Omission, for a partially known Date only** ([§6.2](#62-partially-known-dates)). These keys carry the code `datumFalsch`:

   | Precision | First refusal | Then |
   |---|---|---|
   | `DAY_OPTIONAL` | an unknown month, `DATUM_MONAT_FEHLT` | an unknown year, `DATUM_JAHR_FEHLT` |
   | `MONTH_OPTIONAL` | an unknown month beside a known day, `DATUM_MONATOPTIONAL_TAG_ANGEGEBEN` | an unknown year, `DATUM_JAHR_FEHLT` |
   | `YEAR_OPTIONAL` | an unknown year beside a known month or day, `DATUM_JAHROPTIONAL_MONAT_ODER_TAG_ANGEGEBEN` | an unknown month beside a known day, `DATUM_MONATOPTIONAL_TAG_ANGEGEBEN` |

   The unknown parts then read as `01` (day, month) and `2000` (year) for the steps below, so `DAY_OPTIONAL` `2026-13-00` selects `DATUM_MONAT_FEHLER`.
3. **Calendar reality.** A syntactically sound label the legacy calendar rejects keeps the code `datumFormatFalsch` and is read component by component: a zero component selects `DATUM_FORMAT`; with the pre-1900 check enabled a year below 1900 selects `DATUM_ADDITIONAL_CHECK`, ahead of the month, so `13.13.1850` selects it; a month above 12 selects `DATUM_MONAT_FEHLER`; an exact 29 February `DATUM_FEBRUAR_29_FEHLER`; and every other day `DATUM_TAG_FEHLER`, the cutover gap day `1582-10-10` included.
4. **Position.** A real label fails only as a date, with the code `datumFalsch`: under the enabled pre-1900 check `DATUM_ADDITIONAL_CHECK`, otherwise below the floor `DATUM`.

**The same reading serves every date-bearing format, applied to the completed text.**

- A format without a day — `yyyy`, `yyyy-MM`, `yyyyMM`, `MM` and the clock `HH:mm:ss` — selects `DATUM_FORMAT` for every refusal, month `13` included, and the date keys only for a real date under the pre-1900 check or below the floor.
- The day-bearing `MM-dd`, `MMdd`, `ddMM` and `dd.MM.` are completed with the Base Year, `2000` when none is declared, before the reading, so `02-29` is admitted without a Base Year and selects `DATUM_FEBRUAR_29_FEHLER` under a common one.
- A DateTime label of the declared shape is read by its date half whatever its clock holds: a clock out of range on a sound date selects `DATUM_TAG_FEHLER`, on 29 February or month `13` those keys, and on a zero component `DATUM_FORMAT`. With the pre-1900 check enabled, a malformed date below 1900 selects `DATUM_ADDITIONAL_CHECK` ahead of its month, 29 February and day.

**A DateRange** missing its separator, or not split into two nonempty readable endpoints, selects `DATUM_BEREICH_FORMAT`. An unreal endpoint, the start read first, selects the start or end variant of the month, 29-February and day keys, a zero component the range's format key and the pre-1900 check `DATUM_BEREICH_DATUM_ADDITIONAL_CHECK`; an inverted range selects `DATUM_BEREICH_NICHT_GUELTIG`, and a start below the floor `DATUM_BEREICH_DATUM`.

Measured scope: the three fixed-width complete formats with one separator, the three partial precisions over `yyyy-MM-dd`, a `yyyy-MM-dd` range at `/`, the component-omitting formats, the clock and the date-time format; a Base Year below 1900 is unmeasured.

Sources: [message keys](../docs/sources/domain-ingestion-probes.md#src-date-message-keys-k22), [formal keys, wider](../docs/sources/domain-ingestion-probes.md#src-k22-formal-keys-wider).

---

## 5. Time zones and the sub-day difference

**The model's configured time zone resolves every temporal value, through the legacy `java.util.TimeZone` rules, not `java.time`**, applied at **parse time** to every DATE and DATE_TIME; stored text is converted by a non-lenient `SimpleDateFormat` ([stored temporal text](#stored-temporal-text)). The DM-JSON key is `content.modelConfig.timeZone`; the capitalized `TimeZone` is the internal metamodel key code generation copies it into. An absent key means `UTC`. A plain DATE is midnight in the model zone.

**Which ids are legal is a host input.** The legal set is the host's legacy time-zone id table, versioned with the host exactly as the zone rules are: an explicit id is model-legal exactly when it is the literal `GMT` or `java.util.TimeZone.getTimeZone(id).getID() != "GMT"`. Known IANA ids, `GMT±HH:MM`, `UTC`, `Zulu` and `Etc/UTC` are legal; an empty, unknown or misspelled id, which silently collapses to `GMT`, is refused `MVK_INVALID_TIME_ZONE`.

**The sub-day differences subtract physical instants** ([§2.6](#26-sub-day-arithmetic)). Under `UTC` the wall-clock gap equals the instant gap; under `Europe/Berlin` two date-times straddling a transition differ by their physical elapsed time: `2024-03-31T01:30:00 → 03:30:00` is `DifferenceInHours = 1` across the skipped 02:00 hour, and `2024-10-27T01:30:00 → 03:30:00` is `3` across the repeated hour.

**The non-lenient zone-set parse gives every historical transition these laws:**

- **Every gap is a formal error.** A stored wall time that does not exist, such as `2024-03-31T02:30:00` under Berlin, draws `datumFormatFalsch` — the non-lenient round trip rejects it — and suppresses a referencing rule like any malformed value. It is not rolled forward.
- **Every overlap selects the smaller, after offset.** In an ordinary modern CEST→CET overlap that is CET: `01:30 → 02:30` on `2024-10-27` is `DifferenceInMinutes = 120`, and two stored `02:30` values are instant-equal. In a historical CEMT→CEST overlap the same rule selects CEST, not CET.
- **Date-time comparison is instant-based, and a chained `AddHours`, `AddMinutes` or `AddSeconds` result keeps its exact instant.** `AddHours(01:30 CEST, 1)` lands on the daylight side of the ambiguous hour, so it is not equal to the equal-looking stored `"02:30:00"`, which re-parses on the standard side: the pair is 60 real minutes apart. A rendering-based re-parse loses this; the arithmetic is instant in, instant out. The other consumers of a kept instant are stated with their operators: `DifferenceInDays` and the sub-day differences in [§2.8](#28-reading-operands), the projections in [§3.3](#33-datetimedate-time-and-the-datetime-projections) and the extrema in [§3.5](#35-reasons-and-their-composition).
- **Across a computation join the instant is not carried.** A computation reading another computation's DateTime target reads that target's stored rendering, as the document's own text would be read, so a result on the daylight `02:30` is read on the standard one: `AddHours(00:30, 2)` computed into one field on `2024-10-27` and read by `DifferenceInHours` from `00:30` gives `3`, and a day shift landing on the daylight `02:30` is moved two hours further, to `04:30`.
- **A day-of-month landing assumes the source instant's own offset**, not one chosen from the amount's sign. The nominal target advances the wall label by whole days, keeping clock and millisecond; if the offset in force there differs, the re-fit to it is kept only when it lands on the expected civil date (source date plus amount), not when it merely keeps the raw landing's own date; otherwise the first candidate stands. Witnesses: `2024-10-27T00:30 + 1 day` renders `2024-10-28T00:30` and `2024-03-30T23:30 + 1 day` renders `2024-03-31T23:30`, where the raw-date reading gives `2024-10-27T23:30` and `2024-04-01T00:30`, and `DifferenceInDays` steps through the same landing. The spring-gap separator is a pair, not a roll-forward rule: `2024-03-30T02:30 + 1 day` starts from CET and renders `2024-03-31T01:30`, while `2023-08-31T02:30 + 213 days` starts from CEST, reaches the same gap and renders `2024-03-31T03:30`. A backward landing onto the 1916 `23:00–24:00` gap is the historical control: `1916-05-01T23:30 - 1 day` keeps 30 April and renders `1916-04-30T22:30` CET instead of changing the civil date to 1 May.

Sources: [DateTime join](../docs/sources/computation-scheduling-probes.md#src-datetime-join), [inbound 2026-09-07](../docs/sources/inbound-handbacks.md#inbound-2026-09-07-dispositions), [calendar expression family](../docs/sources/temporal-runtime-fold-probes.md#src-calendar-expression-family).

### The nonexistent wall label

**A wall label the model zone skips has no instant, and each carrier answers it by its own rule:**

| Carrier | Outcome | Owner |
|---|---|---|
| stored DateTime text | `datumFormatFalsch`; the referencing rule is suppressed; not rolled forward | [above](#5-time-zones-and-the-sub-day-difference) |
| `DateTime(date, time)` | a clean no-value | [§3.5](#35-reasons-and-their-composition) |
| a date-time constant at runtime, validation | a runtime failure that fails the rule with one VALUE message | [§12 §3.1](10-validation-and-polarity.md#31-truth-testing-and-message-classification) |
| a date-time constant at runtime, computation | a computation value failure: no value and one addressed `berechnungsWertFehler` per in-capacity target row | [§11 §4.1](09-computations.md#41-temporal-constants) |
| a date-time constant at static admission | admitted under a UTC host default zone, refused `MVK_INVALID_COMPARE_TO_DATE` under a Berlin host default | [§11 §4.1](09-computations.md#41-temporal-constants) |
| `Date(...)` of a skipped whole local date | an unreal Date | [§3.4](#34-calendar-reality) |
| an `AddDays` landing | the source-offset re-fit above, rendering a label on either side of the gap | [above](#5-time-zones-and-the-sub-day-difference) |
| an `AddMonths` or `AddYears` landing | moves to the post-gap label | [§2.7](#27-calendar-basis) |
| `AddHours`, `AddMinutes`, `AddSeconds` | instant arithmetic, resolving no label | [§2.6](#26-sub-day-arithmetic) |
| a stored DATE or DateRange endpoint whose midnight is skipped | not stated | — |

Measured on the pinned Berlin profile; the `Date(...)` row on `Pacific/Apia`.

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

After the final entry, retain its `+3600` offset through the end of 1997. Beginning with 1998, apply the recurring EU rule: offset `+7200` from the last Sunday of March at `01:00Z` inclusive until the last Sunday of October at `01:00Z` exclusive, otherwise `+3600`. The rule has held since 1996; the explicit 1996 and 1997 entries make the table-to-recurrence boundary non-overlapping. For 1980–1995, the table records the historically different last-Sunday-of-September end.

The profile is pinned to that JDK and tzdb release and claims no equivalence to a later one.

Sources: a12-dmkits `BerlinHistoricalTzTest` (the production table against an independent JDK 21.0.11/tzdb2026a 62-pair vector on JVM and Node, before, at and after every transition, every gap and overlap class, both outer regimes, and seeded mutation classes) and `BerlinTransitionOracleDiffTest` (the Groovy-dynamic and generated static Java engines at all 62 transitions against that vector).

> **Non-normative implementation note.** Resolve the model's zone id through a host-supplied versioned profile ([`01-data-model.md`](01-data-model.md)); a staged consumer supporting fewer zones refuses every other legal id before evaluation, and implements the day-landing re-fit separately from month and year resolution.

---

## 6. Date fragments and fragment ranges

### 6.1 Fragments

**A DateFragment is a deliberately imprecise date, and its declaration admits the whole temporal vocabulary** of [the format vocabulary](#the-format-vocabulary), not a narrower fragment-shaped one: measured under its own `formatOfFragment` key, `yyyy-MM-dd`, `dd.MM.yyyy`, `yyyyMMdd`, `HH:mm:ss` and the date-time format are admitted. A complete-date fragment is a complete date, and a clock-declared one a clock value. The completion rules below are measured on the four conventional spellings `MM`, `yyyy`, `yyyy-MM` and `MM-dd`.

- **Fragments are comparable only if both formats include the year or both omit it**, unless the Base Year supplies it ([§1](#the-temporal-pair-gate)). A missing component defaults to `01`.
- **Where an operation needs a concrete Date and the model declares a Base Year, a fragment completes to its earliest concrete date**: a missing month becomes `01`, a missing day `01` and a missing year the Base Year. It then compares, shifts or extracts as a plain date, and its format decides which shifts apply ([§9](#9-datetime-rides-the-date-format-definition--but-the-operand-gates-are-per-operator-)). Without a Base Year each carrier's year is its own row of [the carrier table](#where-a-yearless-value-gets-its-year).

**A fragment-format date range completes its two endpoints asymmetrically**: the start to the interval's earliest date and the end to its latest — a missing month becomes `12` and a missing day the month's last, leap-aware. So a `yyyy` range `2024/2025` denotes `2024-01-01 .. 2025-12-31`.

- With a Base Year, an `MM` range uses day `01` and the leap-aware month end in that year, while an `MM-dd` range uses its stated month and day at both endpoints.
- Without a Base Year, same-profile `MM` and `MM-dd` construction equality and inequality, and construction-versus-stored comparison, stay authorable and distinguish a change to either ordered endpoint; they supply no year-bearing instant.
- Overlap applies [§8.5](#85-overlap-admission)'s uniform-year gate to the whole operand list, so without a Base Year any year-bearing operand beside a yearless stored profile is refused `MVK_DATE_WITH_AND_WITHOUT_YEAR`, and a declared Base Year completes every yearless operand and admits the same list.

Sources: [inbound 2026-09-21](../docs/sources/inbound-handbacks.md#inbound-2026-09-21-corrections), [Base-Year fragment construction](../docs/sources/date-range-construction.md#src-date-range-base-year-fragment-construction).

> **Non-normative implementation note.** Model a fragment as `(present components, format)` with `completeEarliest` and, for range ends, `completeLatest`, kept apart from comparison.

### 6.2 Partially known dates

**A DATE declaration may carry a date precision — `DAY_OPTIONAL`, `MONTH_OPTIONAL` or `YEAR_OPTIONAL`; the default is `FULL` — making it a partially known date whose unspecified components are stored as literal zeros.** Only a DATE declaration carries the property: written onto a TIME or DATE_TIME declaration it is refused by the model deserializer before any check runs. Precision is independent of the declared component set: a `dd.MM.yyyy` declaration exposes all three date components and may still be partially known, so a gate reading components alone cannot see it.

**The zero components form a monotone suffix governed by the precision:**

| Precision | Admits | Example |
|---|---|---|
| `DAY_OPTIONAL` | a full date, or an omitted day | `00.06.2024` |
| `MONTH_OPTIONAL` | additionally an omitted month, only beside an omitted day | `00.00.2024` |
| `YEAR_OPTIONAL` | additionally an omitted year, only beside an omitted month and day | `00.00.0000` |

A lone `0` is never an omission marker; an omitted month beside a present day is invalid, and so is an omitted year beside a present month or day.

**A refused value's formal cause is decided in this order**, and the two thresholds are separable only from the declaration, not from the cause:

1. A **`FULL`** declaration reports any omission marker as the format error `datumFormatFalsch`: an omission is no legal spelling for it.
2. For a declaration that admits omissions, a wrong component width or separator count is the format error.
3. **The omission pattern**: zeros that are not a monotone suffix, or a suffix deeper than the precision admits, are the date error `datumFalsch`. This precedes the reality test: `YEAR_OPTIONAL` `0000-13-00` is the date error.
4. **Reality of the present components** on the earliest completion: an unreal calendar date among them is the format error, an impossible month beside a legally omitted day included, so `DAY_OPTIONAL` `2024-13-00` is the format error rather than an omission failure.
5. **Position**: an admitted shape whose earliest completion falls below the universal floor or the enabled pre-1900 boundary is the date error, so `DAY_OPTIONAL` `1583-10-00` is the date error while `1583-11-00` is admitted.

The message keys follow the same order ([§4.2](#42-message-keys-of-a-stored-date-refusal)).

**An admitted partially known value is filled.** An interval with no point value is still a value, so an implementation storing only the text and reading presence off a parsed value wrongly answers not filled. `FieldFilled` holds and `FieldNotFilled` does not for `2024-06-00` at `DAY_OPTIONAL` and `0000-00-00` at `YEAR_OPTIONAL`, on the validation and the computation arm alike, and `NumberOfFilledFields` counts it, exactly as it counts a component-omitting Date or a DateFragment holding `2024-06`. A value omitting more than its precision admits is the formal failure above and leaves both presence tests unknown. So a required field holding `2024-06-00` raises no `mandatoryField`, a group or a once rule's root holding only it has content, and `FieldValuesNotUnique` compares its stored text, so `2024-06-00` beside a fully known `2024-06-01` is unique although both begin on 1 June. A selecting reader takes the value as its earliest day: `FirstFilledValue` selects `2024-06-00` as `2024-06-01` and `2024-00-00` as `2024-01-01`, directly, starred, over a group and keyed alike, while an omitted year leaves the selection unknown and ends the walk there, as a malformed value does.

**A partially known Date is admitted as an operand only where its operator's gate admits its precision.** Column D of [the operator reference](14-operator-reference.md#temporal-operand-gate) names each operator's precision class:

| Precision class | Admits |
|---|---|
| `any precision` | `FULL` and every partial precision |
| `month-optional` | `FULL`, `DAY_OPTIONAL`, `MONTH_OPTIONAL` |
| `day-optional` | `FULL`, `DAY_OPTIONAL` |
| `full only` | `FULL` |
| `partial only` | every partial precision, not `FULL` |

The refusal's class is that of the gate that asks:

- **The numeric extractor's precision gate** runs before the format gate and Base-Year supplementation and refuses with `MVK_INVALID_DATE_TYPE`, which a Base Year does not waive: `DAY_OPTIONAL` refuses Day, `MONTH_OPTIONAL` Day, Month and Quarter, and `YEAR_OPTIONAL` every date component; every partial precision refuses Hours, Minutes and Seconds. A direct and a key-selected partial field are gated alike. An admitted extractor reads a component that every value of its precision carries, so it reads that stored component and no completion is involved. `DateFromDateTime` and `TimeFromDateTime` ask their own format gate ([§3.3](#33-datetimedate-time-and-the-datetime-projections)) and not this one.
- **A bracketed field-value read** refuses a partially known Date with `MVK_INVALID_DATE_TYPE` wherever it stands ([§10 §3.2](08-paths-and-references.md#32-the-field-value-read-)), so a partial field is not readable as a plain Date operand of a comparison: that is the gap `ValueAsDate` bridges ([§6.3](#63-valueasdate)).
- **The field-list date walk** of `MinValue`, `MaxValue` and `NumberOfDifferentValues` refuses every precision with `MVK_PARTIAL_DATE_NOT_ALLOWED`, while `FieldValuesNotUnique` and `FirstFilledValue` admit every precision. Measured on these five field-list operators. The refusal is asked inside the per-operand date walk, after the duplicate, root and arity gates: a partial leader beside a repeated field reports the duplicate class and one alone the arity class; a partial date and a component mismatch answer by position, so `(DATE, yyyy-MM DATE, partial)` reports `MVK_DATEFORMATS_NOT_COMPATIBLE` and its swap `(DATE, partial, yyyy-MM DATE)` this class; and a list whose leader is not date-like is asked only the kind question, so `MaxValue(Title, ApproxDay)` reports `MVK_NOT_SORTABLE` and `NumberOfDifferentValues(Label, ApproxDay)` `MVK_STRING_ENUM_AND_NON_STRING_ENUM`. The walk reads a group operand's fields: behind a Date leader a group holding a non-date field draws `MVK_DATE_AND_NONDATE`, and one holding `yyyy-MM` Dates `MVK_DATEFORMATS_NOT_COMPATIBLE`.
- **A `DateRange` endpoint** refuses a partial DATE with `MVK_WRONG_DATE_FORMAT_FOR_OP` ([§8.4](#84-construction-and-equality)), and a computation refuses a partial Date target with `MVK_INVALID_DATE_TYPE` ([§11 §4.2](09-computations.md#42-temporal-targets)).
- **The shifts and the differences** refuse a direct partial field with `MVK_INVALID_DATE_TYPE` ahead of their component gates; **the Date argument of `DateTime(...)`** asks its component and year gate first and then refuses a partial field with `MVK_INVALID_DATE_TYPE`, a key-selected one included, before the Time argument is asked: a `MONTH_OPTIONAL` Date argument draws this class beside a clock and beside a complete date in the Time argument alike. The shifts' and differences' order, and the order of `DateTime`'s component gate before its precision gate, are unmeasured.
- **`ValueAsDate`** is the inverse gate: it requires a partially known source and refuses a fully known one with `MVK_INVALID_DATE_TYPE_FOR_OP` ([§6.3](#63-valueasdate)).

Measured scope: the extractor, field-list, bracketed-read, endpoint and `ValueAsDate` gates.

Sources: [partial-Date presence](../docs/sources/temporal-and-message-probes.md#src-partial-date-presence), [partial-Date readers](../docs/sources/temporal-and-message-probes.md#src-partial-date-readers), [inbound 2026-10-02](../docs/sources/inbound-handbacks.md#inbound-2026-10-02-partial-date-readers), [message keys](../docs/sources/domain-ingestion-probes.md#src-date-message-keys-k22), [inbound 2026-09-07](../docs/sources/inbound-handbacks.md#inbound-2026-09-07-dispositions), [inbound 2026-09-23b](../docs/sources/inbound-handbacks.md#inbound-2026-09-23b-entity-list-operand-reads), [inbound 2026-09-26i](../docs/sources/inbound-handbacks.md#inbound-2026-09-26i-expansion-order), [inbound 2026-10-09 extensions](../docs/sources/inbound-handbacks.md#inbound-2026-10-09-extensions), [operand family](../docs/sources/computation-placement-and-constant-probes.md#src-temporal-operand-family-is-the-formats-not-the-kinds), [inbound 2026-10-27](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-27).

### 6.3 `ValueAsDate`

**`ValueAsDate(field, FirstDay|LastDay)` resolves a known-year partially known value to its earliest or latest matching concrete Date**: an omitted day becomes `01` or the leap-aware month end, an omitted month and day January 1 or December 31, and a full value resolves to itself. An omitted year becomes non-relevant before month and day completion, so an enclosing direct comparison evaluates to UNKNOWN rather than an ordinary non-firing emptiness; it is not completed with the formal checker's temporary year 2000.

**`ValueAsDate` is a Date-valued operation.** Beside direct comparisons, the grammar admits it in the special Date-operand positions of Date addition, Date difference and the Date argument of `DateTime(...)`; an extractor does not admit it ([§9.1](#91-what-an-operand-carries)), and neither does `DateTime`'s Time argument. Measured: `AddDays` over it, either slot of `DifferenceInDays` and `DateTime`'s Date argument are admitted, while `YearFromDate` over it and `DateTime`'s Time argument draw `MVK_UNEXPECTED_TOKEN`.

**Its operand is read before it is judged.** An operand inside a repeatable group is admitted exactly when the rule's iteration binds that group; a rule at the parent draws `MVK_NO_WILDCARD`. A starred operand is refused outright, with `MVK_NO_WILDCARDS_ALLOWED` reported at `ValueAsDate` itself rather than at the enclosing comparison, and a group-scope operand is refused as well ([§9](07-repetition-and-iteration.md#3-the-filter-having-the--correlation-and-aggregation)). The unbound-repetition class comes first; then a group draws `MVK_NO_GROUPS_ALLOWED`, whether the rule's iteration, a constant key or a joint parallel iteration addresses it; and a field that is no partially known Date — a Number, a String or a day-number field — draws `MVK_INVALID_DATE_TYPE_FOR_OP`, outside a filter body and inside one, `$`-marked or not. Measured on the direct-comparison carrier; whether the locus verdict transfers to the Date-addition, difference or `DateTime(...)` carriers is unmeasured.

Sources: [`ValueAsDate` locus](../docs/sources/temporal-and-message-probes.md#src-value-as-date-locus), [handback rows 2026-10-23](../docs/sources/model-structure-and-declaration-probes.md#src-handback-rows-2026-10-23) (`value-as-date`), a12-dmkits [KF599](../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf599), [inbound 2026-10-27](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-27).

---

## 7. The point-in-time and reference sources

- **`Today` ignores the time of day**: it truncates the validation instant to midnight **in the model zone**, so under `Europe/Berlin` the day boundary is Berlin midnight, not UTC midnight. It is a date of the `dd.MM.yyyy` shape.
- **`Now` is the raw validation instant**, including any millisecond remainder supplied through `currentDateForTest` or sampled from the wall clock; it is not rounded to authored DateTime precision before a comparison or difference. `Now` is a DATETIME. Ordering (`<`, `<=`, `>`, `>=`) against a DATE or a DATETIME is legal and compares both on the common model-zone timeline, a DATE read at model-zone midnight. Equality and inequality need the other operand to carry a time component, so `Now == PlainDate` and `Now != PlainDate` are refused `MVK_INVALID_COMPARE_TO_DATE` ([§1](#the-temporal-pair-gate)). `Now` is legal as a computation result but unsuitable for stable equality: the generated validation may sample a later instant and disagree at once ([§11 §1](09-computations.md#1-the-ground-rules)).
- **Both read their date on the legacy hybrid calendar**: an instant pinned at `1500-03-10T12:00Z` reads 29 February 1500, and one at `1582-10-14T12:00Z` reads 4 October.
- **`BaseYear` is polymorphic by its typed use.** An explicitly date-typed source receives the Base Year's start (`2020-01-01`); a numeric comparison, an ordinary arithmetic expression or a Number computation receives the fixed scale-0 year number (`2020`); and `StartOfDateRange(BaseYear)` and `EndOfDateRange(BaseYear)` are `01.01` and `31.12` of that year. Its polarity is VALUE. How `BaseYear` meets the comparison walk is [§1](#cross-kind-comparison-classes)'s.

Sources: [inbound 2026-10-21](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-21), [inbound 2026-09-26d constant typing](../docs/sources/inbound-handbacks.md#inbound-2026-09-26d-constant-typing).

> **Non-normative implementation note.** Inject `Today` and `Now` as an explicit point-in-time parameter ([`01-data-model.md`](01-data-model.md)); `BaseYear` is a typed dispatch on model configuration, not a clock read.

---

## 8. Date ranges and overlap

**A date range is an ordered, closed pair of dates; it supports only `==` and `!=`.** A stored DATE_RANGE or a `DateRange(start, end)` construction may stand on either equality side or as a DATE_RANGE computation result; a construction is not admitted as an overlap or bound-extraction argument or nested inside other constructs.

### 8.1 Declaration and stored text

**A DATE_RANGE declaration is admitted for exactly eight `(format, separator)` pairs**: `dd.MM.yyyy` with `-`, `yyyy-MM-dd` with `/`, `yyyy` with `/`, `yyyy-MM` with `/`, `MM` with `/`, `MM-dd` with `/`, `MM` with the empty separator, and `dd.MM` with `-`. Every other pair of the complete candidate grid is refused, separator swaps, every dot separator, every other empty separator and every `yyyyMM` pair included. The allowlist does not by itself establish that every range operation admits every pair. They form five component classes: the complete-date pairs, the `MM` pairs, `MM-dd` with `dd.MM`, `yyyy`, and `yyyy-MM`.

**`interpretationOfYear` may be omitted or set to `FROM` or `TO` on every admitted pair**, year-bearing ones included. An omitted key is the standard interpretation; a present but empty token makes the model illegal at deserialization. The accepted declaration is distinct from the effective runtime format ([§8.2](#82-the-two-stage-runtime-reading)).

**Stored range text has four ordered formal failures:**

1. A token not containing the declared separator: `datumBereichTrennerFehlt`.
2. With the separator present, a split other than two nonempty endpoints, or a lexically or calendrically invalid endpoint: `datumBereichFormatFalsch`.
3. Two valid endpoints with the start after the finish: `datumBereichNichtGueltig`. Equal endpoints are valid.
4. An otherwise ordered range whose formally completed start precedes `1583-10-16`: `datumBereichDatumFalsch`. Formal completion is separate from endpoint completion ([§8.2](#82-the-two-stage-runtime-reading)).

Every failure keeps the physical placement and exact text, makes a reached validation read UNKNOWN and a reached computation read poison.

**An empty declared separator is a real policy, not the absence of a delimiter.** Under the legal `MM` with empty-separator declaration the stored token is split at its midpoint, so `0609` has the endpoints `06` and `09`; it is not split into characters and does not draw `datumBereichTrennerFehlt`. An odd-length token has no midpoint and draws `datumBereichFormatFalsch`: `061`, `06109` and `6` do, while `0609` is admitted.

Sources: [inbound 2026-09-08](../docs/sources/inbound-handbacks.md#inbound-2026-09-08), [shared runtime](../docs/sources/date-range-construction.md#src-date-range-shared-runtime), [inbound 2026-10-27](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-27).

### 8.2 The two-stage runtime reading

**DateRange document input and runtime reads use two stages.** Document conversion first parses the text under the field's own format and separator, a missing month or day defaulting to 1 in the converted Date endpoints. Runtime formatting, formal checking and endpoint reads then use a shared definition selected in declaration order. For interpreted ranges the sharing key distinguishes `FROM` from `TO` and the pre-1900 flag but drops the declared format and separator, and the first field of that class supplies those runtime details; standard ranges keep their format and separator distinct. So reordering declarations can change validity, endpoint values and computed presentation, even when a Base Year is configured.

- **Completion of a shared yearless day-and-month format** uses the declared Base Year, or 2000 when absent. On a wrapping pair, `FROM` anchors the start and moves the finish into the following year, and `TO` anchors the finish and moves the start into the preceding year. Endpoint calendar validity is checked in the placed year: with an effective dotted day-and-month format and Base Year 2020, `01.11-29.02` is valid under `TO` but `datumBereichFormatFalsch` under `FROM`, whose finish would be February 29, 2021. This completion does not generalize to every yearless format: an effective month-only format refuses a wrapping pair with `datumBereichNichtGueltig` under either interpretation, with or without a Base Year.
- **Formal position checking is separate from endpoint completion.** Effective day-and-month formats use the Base Year for the always-on floor and the optional pre-1900 check; effective month-only formats use neither the endpoint's completed year nor the Base Year for them. So both `MM` spellings accept an ordered pair under Base Year 1500 with either flag setting, while still refusing reversed pairs. Day-and-month ranges with the flag refuse Base Year 1899 and accept 1901; their unflagged twins accept both.
- **The two stages also lose components.** With interpreted `dd.MM` declarations first, a later month-only `03/10` input becomes `01.03-01.10` and its end-Day is 1; with interpreted `MM` declarations first that read becomes `03/10`, and positional endpoint completion gives end-Day 31. A later full-Date input can lose its supplied years when rendered through either shared yearless profile, and numeric endpoint reads then return the runtime anchor years. A pre-1900 flag different from the first declaration's creates a separate sharing class. Empty numeric endpoint reads compute 0, and formally invalid sources clear their dependent computations. Raw text that conversion could not decode is checked under the effective runtime format, so even a compact-month declaration can report the shared separator's missing-separator class.
- **A computed DateRange is rendered through the target's shared runtime definition**, and that text is checked before dependent computations consume it. A valid dotted-`FROM` wrapping source copied into a month-only `TO` sharing class therefore produces an errored `11/02` attempt, and a following end-Year computation clears; ordered input writes `03/10`, and the dependent year is 2000 in an unconfigured model. An empty source clears the target and lets the dependent numeric read substitute 0. Formal source poison and target rejection both block the dependent read, but only target rejection keeps the attempted text.

Sources: [shared runtime](../docs/sources/date-range-construction.md#src-date-range-shared-runtime), [inbound 2026-09-08](../docs/sources/inbound-handbacks.md#inbound-2026-09-08).

### 8.3 Bound extraction

**`StartOfDateRange(field)` and `EndOfDateRange(field)` select the stored range's first and second endpoint and expose it as a Date.** Extraction is admitted on every admitted declaration, a yearless profile in a model without a Base Year included; each consumer of the endpoint is gated instead, by the endpoint's resulting format.

- **An uninterpreted range's endpoint keeps the declaration's date components**, and a numeric extractor over it is admitted exactly where that set carries its component — the direct Date field's rule of [§9](#9-datetime-rides-the-date-format-definition--but-the-operand-gates-are-per-operator-), not the comparison consumers' gate below. `MonthFromDate` and `QuarterFromDate` are admitted on `MM`, `MM-dd`, `dd.MM`, `yyyy-MM` and the complete-date profiles; `DayFromDate` on `MM-dd`, `dd.MM` and the complete-date profiles; `YearFromDate` on `yyyy`, `yyyy-MM` and the complete-date profiles in any model, and on every yearless profile once the model declares a Base Year. Every other pairing is refused `MVK_WRONG_DATE_FORMAT_FOR_OP` at the extractor, so `DayFromDate` on an uninterpreted `MM` range stays refused in a configured model.
- **A year interpretation makes the endpoint format a complete date.** An `MM-dd` range with `interpretationOfYear: "FROM"` admits `YearFromDate(EndOfDateRange(...))` without a Base Year, where the uninterpreted twin refuses it; Hours extraction stays refused. Start and end Year and end Day are admitted for both interpretations across all eight profiles, with and without a Base Year. The interpreted endpoint's actual values follow the two-stage reading of [§8.2](#82-the-two-stage-runtime-reading).
- **The selection and its component form one authored operand**, the endpoint alone being no numeric value. It is admitted in a Number computation operation on the same terms as in a validation condition, with the ordinary locus rule deciding the target: a row endpoint computes a field inside its own repeated group, a scalar endpoint either. It is a non-expandable scale-0 Number operation ([§2.1](#21-what-the-operations-produce)).
- **At runtime** the computed value is the selected endpoint's component, an unconfigured yearless range included, whose kept labels are read directly: an unplaced range computes the real number `0` rather than clearing, and a formally invalid range clears the reading computation's target while a sibling computation over a clean operand in the same row still computes its own value. An empty range stays empty. Ordinary formal invalidity makes validation UNKNOWN and poisons computation with the same cause before either endpoint is selected; the validation-scoped required-empty finding is the exception, UNKNOWN in validation and empty in computation.
- **Comparing a selected endpoint with a full Date**, a literal or `Today`, follows the temporal pair gate of [§1](#the-temporal-pair-gate), so only a yearless profile without a Base Year is refused `MVK_INVALID_COMPARE_TO_DATE`, and every year-bearing profile is admitted, the incomplete `yyyy` one included. Comparing two selected endpoints follows the same rule, admitting `MM` against `MM-dd` and refusing `MM` against `yyyy`; at runtime each fragment is first completed by its endpoint position, so a month-only start equals a month-and-day start exactly when that day is the month's first.

**The operand is a non-wildcard, non-category DATE_RANGE field**, direct or selected by a semantic index: `StartOfDateRange(Rows/Window For "k")` and its field-keyed form are admitted, as are a keyed operand of the overlap predicates and of stored range equality, at a nonrepeatable locus, at an iterating one, and when the keyed group is the one iterated. `BaseYear` is the separately typed source of [§7](#7-the-point-in-time-and-reference-sources); a `DateRange(start, end)` construction is not admitted. The refused operand forms are in [§8.4](#84-construction-and-equality)'s table.

Sources: [shared runtime](../docs/sources/date-range-construction.md#src-date-range-shared-runtime), [K22 static batch 2](../docs/sources/group-count-topology.md#src-k22-static-s2).

### 8.4 Construction and equality

**Each `DateRange` endpoint is a bare entity reference**, a literal- or field-keyed semantic-index selection included; a bracketed calculation is illegal there. After that reference gate, **each endpoint is admitted by its declared format alone**: the format must carry at least one date component and no time component, both endpoints must carry the same component set, and the kind takes no part. DATE and DATE_FRAGMENT endpoints may mix, and different lexical spellings are legal when their component sets agree. A TIME- and a DATE_TIME-declared field each carrying `yyyy-MM-dd` are admitted at the start, at the finish and as both endpoints at once, beside the DATE-declared control; a DATE-declared `HH:mm:ss` field, a TIME declared the same, a DATE_TIME declared the date-time format, a Number, a String, a DateRange field, a partial DATE and endpoint formats with different component sets are all refused `MVK_WRONG_DATE_FORMAT_FOR_OP`.

**The reference gate's classes**, measured per carrier ([§10 §3](08-paths-and-references.md#3-the-asterisk-and-) states the read ladder they instantiate):

| Operand | `DateRange` endpoint | `StartOfDateRange`, `EndOfDateRange` |
|---|---|---|
| a starred field | `MVK_NO_WILDCARDS_ALLOWED` | `MVK_NO_WILDCARDS_ALLOWED`, at either locus |
| an unstarred group | `MVK_NO_WILDCARD` | `MVK_NO_WILDCARD` |
| an unstarred repeatable field the rule does not bind | `MVK_NO_WILDCARD` ([§8.7](#87-range-operands-below-a-repeatable-group)) | `MVK_NO_WILDCARD` ([§8.7](#87-range-operands-below-a-repeatable-group)) |
| a starred group, or the rule-context group | `MVK_NO_GROUPS_ALLOWED` | not stated |
| a top-level outer-iteration marker | `MVK_INVALID_OUTER_ITERATION`; admitted inside a `Having` filter that supplies its iteration | not stated |
| `Today`, `BaseYear`, a shift, a date literal | `MVK_UNEXPECTED_TOKEN` | `BaseYear` admitted ([§7](#7-the-point-in-time-and-reference-sources)); others not stated |
| a String literal, a range literal `"2020-01-01/2020-02-01"` included | `MVK_UNEXPECTED_TOKEN` | `MVK_UNEXPECTED_TOKEN` |
| an arity other than two | `MVK_UNEXPECTED_TOKEN` | — |

A String literal also draws `MVK_UNEXPECTED_TOKEN` as any `DateRangesOverlap` operand, in the subject list of `AtLeastOneDateRangeOverlaps`, and in an `In` list that opens with a field; an `In` list that opens with a String literal parses as a literal member list and reaches `MVK_NO_CONST`.

**Equality and inequality additionally require the two resulting ranges to carry the same declared date-component set**; the lexical spelling never enters. A component mismatch between otherwise valid constructions is refused `MVK_INVALID_COMPARE_TO_DATE_RANGE` rather than evaluated by completing the coarser range into the finer one: with a Base Year this admits matching `MM` or matching `MM-dd` constructions but still refuses `MM` beside `yyyy-MM` and `MM-dd` beside a full Date. Mixing those profiles inside one construction is the endpoint gate's `MVK_WRONG_DATE_FORMAT_FOR_OP` instead. Two **stored** DATE_RANGE fields meet the same gate: each of the five component classes' spellings cross freely — `yyyy-MM-dd` against `dd.MM.yyyy`, `MM` with slash against `MM` with the empty separator, `MM-dd` against `dd.MM` — and every pair from two classes is refused, `dd.MM.yyyy` against `dd.MM` included, which shares a separator and differs only in components. The refusal is symmetric in authored order and identical for `==` and `!=`. An admitted pair compares retained identity rather than stored text, so two spellings of one class agree exactly when their resolved endpoints or kept yearless labels agree.

**A fragment endpoint completes by its position** ([§6.1](#61-fragments)): a start to its earliest local date and a finish to its latest, so `yyyy` endpoints become January 1 and December 31, `yyyy-MM` or Base-Year-completed `MM` endpoints span the selected month, and Base-Year-completed `MM-dd` endpoints keep their stated day. The completed local labels are resolved under the model's zone profile, and equality compares both ordered resolved endpoints. These observations establish calendar labels and comparison outcomes, not externally exposed endpoint instants.

Sources: [endpoint reads the format](../docs/sources/computation-placement-and-constant-probes.md#src-daterange-endpoint-reads-the-format), [K22 static batch 2](../docs/sources/group-count-topology.md#src-k22-static-s2), [`yyyy` fragments](../docs/sources/date-range-construction.md#src-date-range-year-fragment-construction), [`yyyy-MM` fragments](../docs/sources/date-range-construction.md#src-date-range-year-month-fragment-construction), [Base-Year fragments](../docs/sources/date-range-construction.md#src-date-range-base-year-fragment-construction).

### 8.5 Overlap admission

**Both overlap operators refuse an operand whose declaration carries an `interpretationOfYear`**, with `MVK_INVALID_DATE_RANGE_FORMAT` against the composite declared format: on either operand side of either operator, under a yearless or a year-bearing profile, with or without a Base Year. It is a property of the declaration, not of the value or its completion; bound extraction and equality admit the same declaration.

**Both operators admit their operands by year class and apply no component-set gate.** Every compared operand must carry the year or none may, and a mix is refused `MVK_DATE_WITH_AND_WITHOUT_YEAR`. The gate reads the whole operand list, not a distinguished pair, so a list of three or more is refused on any mix, and every declared spelling of one yearless component set behaves alike. For `AtLeastOneDateRangeOverlaps` the list is the scalar together with its `In` list, so the gate spans both sides, and a completed fragment is admitted as scalar or as member. A declared Base Year completes each yearless operand and admits every list, `yyyy-MM-dd` beside `MM` included; within one year class differing component sets are admitted outright, unlike the equality gate. A completed yearless operand occupies the Base Year alone, so an exact operand naming another year is disjoint from it, while an exact range spanning into the Base Year meets it.

- **Within one reference's expansion, uniform year-carrying is not enough.** The walk first reduces each reference to its distinct declared format strings and, without a Base Year, refuses a reference expanding to two different strings with `MVK_DATE_WITH_AND_WITHOUT_YEAR` although neither is yearless: on the value-list carrier a group of two ranges declared `dd.MM.yyyy` and `yyyy-MM-dd` is refused where a group sharing one spelling is admitted. The reduction compares format strings, not separators, so a reference expanding to `MM` with slash and `MM` with the empty separator is admitted, and one expanding to `MM-dd` and `dd.MM` is refused; those two cases are unmeasured.
- **Across references only the year question is asked.** An explicitly written pair of two differently spelled dated range fields is admitted — the same two declarations refused through one group reference are admitted when named as two fields — and so is a pair of unrelated top-level range fields at two dated spellings.
- **Two walks run in a fixed order, and only the second has a Base-Year escape.** A per-operand walk asks first whether each expanded field is a DATE_RANGE declaration (`MVK_NO_DATE_RANGE`) and then whether it carries `interpretationOfYear` (`MVK_INVALID_DATE_RANGE_FORMAT`), and it completes before the agreement walk begins: a list both wrong in kind and inconsistent about the year answers with the kind class, and a declared Base Year, which disables the agreement walk, leaves a year-interpreting range refused.

**List admission is ordered per operator.**

- **`DateRangesOverlap`**, after all authored operand reads, checks duplicate or overlapping references, roots, categories, field-only shape, then multiplicity; a sole unstarred field reports `MVK_PARAMSIZE_INVALIDFN`. Its group refusal is asked over the whole list first: a group draws `MVK_NO_GROUPS_ALLOWED` even behind an interpreted field or a field of another kind, and beside a year mix. The kind and interpretation walk and the year agreement follow.
- **`AtLeastOneDateRangeOverlaps`** first checks the subject list for duplicates, roots and a common base type, then requires exactly one unstarred field (`MVK_INVALID_PARAMETER_FOR_DATE_RANGE_COMPARISON`) and value validation. A literal member list then reports `MVK_NO_CONST`. An entity member list is an entity list of its own before it meets the scalar, in the order [§8 B.3](06-strings-and-enumerations.md#b3-the-value-list-quantifiers--per-cell-three-way-classification-) gives the value-list quantifiers: its own repeat, its root, its base type against the scalar's, then a repeat across the two sides, then member value validation, all before the combined kind, interpretation and year gates. So a list naming only a root draws `MVK_ROOT_GROUP_REFERENCED` though the scalar lies inside that root, starred or fixed; `Term In Term, /Lot*` draws `MVK_DUPLICATE_PARAM2` for the containment inside the list rather than the scalar's repeat beside it; `Term In Term, Serial` and `Term In Serial`, over a String `Serial`, draw `MVK_VARYING_TYPES_NOT_ALLOWED`; `Term In Serial, Serial` draws `MVK_DUPLICATE_PARAM1`; and a member of the wrong base type wins over a cross-list duplicate. Beside a scalar carrying `interpretationOfYear`, a root-only list, a repeat in the list and a list of another base type each draw their own class, and only an admissible list reaches `MVK_INVALID_DATE_RANGE_FORMAT`.
- **The scalar slot admits only a scalar, refusing every other form with one class.** A plain star, a `Having`-filtered star, a fixed group, a starred group and a star above a nonrepeatable terminal each draw `MVK_INVALID_PARAMETER_FOR_DATE_RANGE_COMPARISON` in the scalar position, while the identical operand is admitted in the `In` list, so the refusal belongs to the slot. A kind gate answers ahead of it: a group whose expansion mixes kinds draws `MVK_VARYING_TYPES_NOT_ALLOWED` there. So does an operand's read in either slot: an index that cannot be read, `MVK_INDEX_VALUE_INVALID`, answers ahead of the slot gate beside the starred scalar or alone in the `In` list.

An admitted group operand contributes every DATE_RANGE declaration in its recursive subtree, at every instantiated row below the operand's own repetition depth. The combined precedence is measured only where a row is named; the rest is source reading, its wider calibration pending.

Sources: [mixed-year overlap](../docs/sources/date-range-construction.md#src-date-range-mixed-year-overlap), [inbound 2026-09-21](../docs/sources/inbound-handbacks.md#inbound-2026-09-21-corrections), [inbound 2026-09-21b](../docs/sources/inbound-handbacks.md#inbound-2026-09-21b-corrections), [overlap list grid](../docs/sources/group-list-and-capacity-probes.md#src-count-placement-overlap-list-grid), [overlap field-walk order](../docs/sources/group-list-and-capacity-probes.md#src-overlap-field-walk-order), [inbound 2026-09-26h](../docs/sources/inbound-handbacks.md#inbound-2026-09-26h-list-reads).

### 8.6 Overlap evaluation

**The two overlap predicates differ in shape** ⚠:

- **`DateRangesOverlap(op0, op1, …)` is any-pair** among all operands' kept, filled ranges, one growing set: a list-internal pair fires even when a scalar operand is disjoint, and a same-cell self-pair through a scalar plus a star fires on every filled row.
- **`AtLeastOneDateRangeOverlaps(scalar In list…)` is scalar-versus-list**: two list cells overlapping each other do not fire.

For both, intervals are closed, so back-to-back periods sharing a boundary day overlap, and an inverted range (start after end) never overlaps: a stored inverted range is normally refused by its field's formal check and skipped, and the interval relation independently returns false if an inverted pair reaches it. **Without a Base Year, an all-yearless list compares month and day labels directly with no completion**: a month-only endpoint spans day `01` through that month's yearless greatest day, February reaching `29` because no year decides leapness, and both ends stay closed. A configured Base Year makes the stored value itself completable and therefore falsifiable, so `02-29` under Base Year 2023 is `datumBereichFormatFalsch` rather than any overlap verdict. Both accounts are measured on either codegen strategy.

**Validation skips an empty or formally unavailable cell**; polarity depends on the scan:

- **`DateRangesOverlap`** fires **OMISSION** exactly when the scan has processed a kept, filled range from a filter-bearing operand at or before the first overlapping pair, and **VALUE** otherwise. A filtered operand with no kept, filled range does not taint a later firing.
- **`AtLeastOneDateRangeOverlaps`** resolves the scalar first and does not read the list when the scalar is unusable: an empty, malformed or formally unavailable scalar collapses to no fire, and overlaps inside the list cannot rescue it. Otherwise it visits list operands in authored order, each operand's cells in their canonical address order, and stops at the first overlap. It fires **OMISSION** exactly when that first matching list operand carries a filter, **VALUE** otherwise: an earlier filtered but disjoint operand does not taint a later unfiltered match, and a later filtered match cannot change an earlier unfiltered result.
- A group operand expands in declaration-major recursive model order, rows in canonical order; in validation, reordering inside an unfiltered group changes neither truth nor polarity.

**Computation guards keep ordered failure reachability.** Both predicates visit operands in authored order and stop at the first deciding overlap. `DateRangesOverlap` compares each reached filled range with the earlier filled ranges; `AtLeastOneDateRangeOverlaps` reads its scalar first and compares each reached list value with that scalar only. An empty cell is skipped, and an empty or absent scalar makes the latter guard false without reading the list. A reached formally invalid scalar or list value poisons the computing target and every dependent computation reading it, while an invalid value after a deciding overlap stays unread. So an invalid second-row value of the first declared field aborts before an overlapping first-row value of the next field decides. When no later alternative supplies a value, a clean false guard leaves the target empty, which a dependent Number expression may substitute with zero ([§11 §3.1](09-computations.md#31-a-precondition-clear-cascades-as-empty)). Both predicates read fresh computed values under that chapter's scheduling rules.

**A filtered operand uses the computation iterator's one-kept-successor lookahead** ([§9 §3](07-repetition-and-iteration.md#3-the-filter-having-the--correlation-and-aggregation)): the iterator evaluates filters through the next kept row before supplying the current row's range to the search. A dropped row's range is never read; a filter failure in lookahead aborts before the pending range is compared, and the prefetched successor's range stays unread until requested. So, with overlapping first and second rows, an invalid third-row filter can poison the any-pair search while a scalar already overlapping the first row lets the scalar-versus-list search succeed; replacing that filter failure with an invalid range and a healthy filter lets both succeed. They hold in the yearless interval domain too.

Which operator takes which unavailable-read, poison, polarity and filter class is the operator reference's columns V, C, P and F.

Sources: [yearless overlap](../docs/sources/date-range-construction.md#src-date-range-yearless-overlap), [mixed-year overlap](../docs/sources/date-range-construction.md#src-date-range-mixed-year-overlap), [overlap computation guards](../docs/sources/computation-scheduling-probes.md#src-overlap-computation-guards).

### 8.7 Range operands below a repeatable group

**An ordinary unstarred range operand that crosses a repeatable group is governed by the enclosing rule's iteration scope**: with the error field outside that repeated group it is refused `MVK_NO_WILDCARD`, and moving the error field inside the group admits it. This is the rule-locus condition of [§9 §1](07-repetition-and-iteration.md#1-when-a-rule-iterates-and-where-its-error-lands). Measured members: the overlap predicate, stored range equality, an extracted endpoint compared against a fixed Date, a pair of extracted endpoints, a numeric component of an extracted endpoint, and the two-endpoint construction. Other carriers are unmeasured. At the numeric-component carrier this locus gate answers before the component gate: a row operand whose profile lacks the requested component still draws `MVK_NO_WILDCARD` from a non-iterating locus rather than the format class. A filter admits an explicit outer-iteration marker; whether filter context alone admits a crossed-repeatable endpoint is unmeasured.

Sources: [K22 static batch 2](../docs/sources/group-count-topology.md#src-k22-static-s2), [inbound 2026-09-26h](../docs/sources/inbound-handbacks.md#inbound-2026-09-26h-list-reads).

---

## 9. DateTime rides the date-format definition — but the operand gates are PER-OPERATOR ⚠

**A temporal operator admits each operand by the components its declared format carries, and the operator's unit decides which components it needs; neither the declared kind nor an operand's being a DateTime decides.** A DateTime operand is admitted wherever its components satisfy the unit — `AddDays` and `DifferenceInDays` take one, `AddMonths`, `AddYears`, `DifferenceInMonths` and `DifferenceInYears` refuse its time half — and a DATE whose format is `HH:mm:ss` is admitted by the clock extractors. Column D of [the operator reference](14-operator-reference.md#temporal-operand-gate) assigns each operator its component class; this section defines the classes.

### 9.1 What an operand carries

- **A field** carries the letters of its declared format, case-sensitively — `MM` is the month and `mm` the minute — and a format-less declaration its kind's default ([the format vocabulary](#the-format-vocabulary)).
- **An operand with no declaration of its own** carries its kind's default set: `Today`, a date constant and `BaseYear` used as a date a complete date; `Now` and a date-time constant the full stamp; a clock constant the full clock; an omitted-year constant month and day.
- **A derived operand** carries its result's set: a shift its source's set ([§2.1](#21-what-the-operations-produce)); `DateFromDateTime` and `ValueAsDate` a complete date; `TimeFromDateTime` the full clock; `StartOfDateRange` and `EndOfDateRange` the range's own set, or a complete date when the range is year-interpreted ([§8.3](#83-bound-extraction)).
- **`FirstFilledValue`, the temporal extrema and `ValueAsDate`** are refused by the parser in an extraction slot, so they meet no extractor gate.
- **A declared Base Year supplies the year component, and nothing else**, to every class below that names it.

### 9.2 The component classes

| Class | Each operand must carry | Refusal |
|---|---|---|
| `any format` | nothing: every admitted temporal declaration is admitted, with no component gate | — |
| `part d` | `d` | `MVK_WRONG_DATE_FORMAT_FOR_OP` |
| `part M` | `M` | `MVK_WRONG_DATE_FORMAT_FOR_OP` |
| `part y` | `y`, or a declared Base Year | `MVK_WRONG_DATE_FORMAT_FOR_OP` |
| `part H`, `part m`, `part s` | `H`, `m`, `s` respectively | `MVK_WRONG_DATE_FORMAT_FOR_OP` |
| `stamp` | all of `y`, `M`, `d`, `H`, `m`, `s`; over the vocabulary only `yyyy-MM-dd'T'HH:mm:ss` | `MVK_WRONG_DATE_FORMAT_FOR_OP` |
| `step d` | `d` | the step ladder below |
| `step M` | `M`, some date component, no time component | the step ladder below |
| `step y` | `y` or a declared Base Year, some date component, no time component | the step ladder below |
| `step H`, `step m`, `step s` | `H`, `m`, `s` respectively, and some date component | the step ladder below |
| `agreement` | the direct-comparison pair gate | [§1](#the-temporal-pair-gate) |
| `same set` | the temporal extremum gate | [§1](#the-temporal-pair-gate) |
| `positional` | the per-position component forms | [§3.1](#31-date), [§3.2](#32-time-and-the-clock-anchor) |
| `date + clock` | a Date argument with some date component and no time component, carrying `y` or a declared Base Year; a Time argument with a time component and no date component | `MVK_WRONG_DATE_FORMAT_FOR_OP` |
| `range endpoint` | some date component, no time component, the same set at both endpoints | [§8.4](#84-construction-and-equality) |
| `any range` | any admitted DATE_RANGE declaration | [§8.3](#83-bound-extraction) |
| `year class` | the overlap year-class and interpretation gates | [§8.5](#85-overlap-admission) |

**`any format`** is measured on `FieldFilled` and `FieldNotFilled`, which admit a partially known value and the clock-only DATE_TIME declaration below, and on `NumberOfFilledFields`, which counts a component-omitting Date and a DateFragment ([§6.2](#62-partially-known-dates)).

**The extractor classes** (`part …`, `stamp`) ask their gate after the operand's partial-precision gate ([§6.2](#62-partially-known-dates)) and its literal-entry gate ([§3.3](#temporal-extractor-operands)). A non-temporal operand — a Number, String, Enumeration, Boolean, Confirm, DateRange or Custom field — draws `MVK_NO_DATE`, measured on `YearFromDate` and `DateFromDateTime`. Under `part y` the Base Year admits even a pure `HH:mm:ss` operand, which has no date component at all; over a Time value the result is 1970 ([§3.2](#32-time-and-the-clock-anchor)).

**The step ladder.** A shift asks it of its source and a difference of both operands; the first rung that refuses answers:

1. a literal operand that is no temporal value, a literal failing the calendar check included: `MVK_INVALID_DATE_STRING` ([§1](#1-constant-format-and-the-stringdate-literal-ambiguity-));
2. a direct partially known field: `MVK_INVALID_DATE_TYPE` ([§6.2](#62-partially-known-dates));
3. a non-temporal operand: `MVK_INVALID_DATE_FOR_OP`;
4. an operand lacking the unit's component, after a declared Base Year supplies the year: `MVK_WRONG_DATE_FORMAT_FOR_OP`;
5. an operand with no date component: `MVK_INVALID_TIME`;
6. under `step M` and `step y`, an operand with a time component: `MVK_WRONG_DATE_FORMAT_FOR_OP`;
7. for a difference, operands disagreeing about the year after Base-Year supplementation: `MVK_DATE_WITH_AND_WITHOUT_YEAR`. A declared Base Year makes this rung vacuous.

**So a refusal's class depends on the unit and the model, and two units that agree on every admitted operand can answer different codes on a refused one.** A pure clock operand draws `MVK_WRONG_DATE_FORMAT_FOR_OP` at `step d` and `step M` in every model and at `step y` without a Base Year, but `MVK_INVALID_TIME` at `step y` with one, because the Base Year has satisfied rung 4 and rung 5 answers; at `step H` it draws `MVK_INVALID_TIME`. A yearless `dd.MM.` operand is admitted at `step y` with a Base Year and refused `MVK_WRONG_DATE_FORMAT_FOR_OP` without one, and admitted at `step M` in both models when both operands are yearless. A yearless operand beside a dated one draws rung 7's class at `DifferenceInMonths` without a Base Year and is admitted with one, the supplied year removing the mixture. A `yyyy` operand beside a complete date is admitted at `DifferenceInYears` and refused rung 4's class at `DifferenceInMonths` and `DifferenceInDays`, so the component asked is the unit's own. A complete date-time is refused at both completed-period units and admitted by `DifferenceInDays` and the sub-day units, which refuse the pure clock: each family's own missing half draws its own code.

**A DATE_TIME declared with the clock-only format `HH:mm:ss` is fillable and comparable**, and each gate answers it by its class: the `stamp` extractors and the date-component extractors refuse it `MVK_WRONG_DATE_FORMAT_FOR_OP`; the `step H` operations — `AddHours`, `DifferenceInHours` — refuse it `MVK_INVALID_TIME`, needing a date half; a comparison against `Now` refuses it `MVK_INVALID_COMPARE_TO_DATE`; while the `part H`, `part m` and `part s` extractors admit it by their class, measured for `HoursFromTime` and `SecondsFromTime` and unmeasured for `MinutesFromTime` on this carrier. `FieldFilled` and equality against a same-format sibling are admitted, as is every such condition on an ISO-declared sibling. The `stamp` requirement is also why `TimeFromDateTime` refuses a plain Time field: a clock-only format lacks the date half.

Measured scope: the `part` classes on complete dates, clocks and date-times of every kind (`HoursFromTime` on an `HH:mm:ss` DATE, `DayFromDate` refused on `yyyy-MM` and admitted on `yyyy-MM-dd`, `MinutesFromTime` refused on `MM`), on a DATE_FRAGMENT declared `yyyy` (`YearFromDate` admitted, `MonthFromDate` refused), on format-less declarations and on the default-set operands. The `step` classes: the day, month, year and hour differences on the full kind-by-format cross and the Base-Year axis; the minute and second differences at the date-time and clock formats, the rest of their kind-by-format cross unmeasured; the shifts on the calendar, fragment and pure-Time sub-day rows. Rungs 1, 4 before 5 under a Base Year, 4 before 7 (a `MM` operand beside a year-bearing constant draws rung 4's class) and 7 with its Base-Year removal are measured; rungs 2 and 3 are unmeasured. A shift's result set over a non-default source is measured on `AddDays` over a `MM-dd` source, whose year `YearFromDate` refuses `MVK_WRONG_DATE_FORMAT_FOR_OP` without a Base Year; the other shifts over such a source are unmeasured. The `date + clock` component sets and its yearless-source Base-Year requirement are measured. No admitted format carries a day without a month, or one clock letter without the other two, so `step d` and `part d` are not separable from also requiring the month, nor the three clock units from each other.

Sources: [temporal difference gates](../docs/sources/computation-placement-and-constant-probes.md#src-temporal-difference-gates-read-the-format), [Base-Year conditioning](../docs/sources/computation-placement-and-constant-probes.md#src-difference-gate-base-year-conditioning), [operand family](../docs/sources/computation-placement-and-constant-probes.md#src-temporal-operand-family-is-the-formats-not-the-kinds), [yearless anchor](../docs/sources/temporal-constant-and-base-year-probes.md#src-yearless-anchor-is-the-base-year), [calendar expression family](../docs/sources/temporal-runtime-fold-probes.md#src-calendar-expression-family), [inbound 2026-09-21](../docs/sources/inbound-handbacks.md#inbound-2026-09-21-corrections), [inbound 2026-09-21b](../docs/sources/inbound-handbacks.md#inbound-2026-09-21b-corrections), [inbound 2026-10-09 extensions](../docs/sources/inbound-handbacks.md#inbound-2026-10-09-extensions), [cross-kind reads](../docs/sources/temporal-runtime-fold-probes.md#src-cross-kind-temporal-reads), [cross-kind computation reads](../docs/sources/temporal-runtime-fold-probes.md#src-cross-kind-computation-reads), [composition locus](../docs/sources/temporal-and-message-probes.md#src-value-as-date-locus), [inbound 2026-10-27](../docs/sources/inbound-handbacks.md#src-inbound-2026-10-27).

---

## Checklist for §6

- [ ] Every temporal gate and reader asks the declared format's component set, never the kind; admit exactly the thirteen format strings.
- [ ] Stored temporal text converts non-leniently and fails with the two Date codes only; a yearless value takes its year from [its carrier's row](#where-a-yearless-value-gets-its-year).
- [ ] A quoted literal is classified by content alone ([§1](#1-constant-format-and-the-stringdate-literal-ambiguity-)); apply the constant gate's ungrouped-clock exception and the cross-kind walks.
- [ ] `AddMonths` clamps, `AddYears` corrects into leap years; shift amounts truncate and narrow to signed 32 bits; constructed Dates keep their hybrid-calendar identity and instant.
- [ ] Extractions and differences are non-expandable scale-0 Numbers; empty operands give symmetric fillable zero; `DifferenceInDays` steps model-zone calendar days; sub-day differences divide epoch milliseconds, truncated toward zero, order `b − a`.
- [ ] `Valid`/`Invalid` over `Date(...)` have complementary truth but distinct verdicts; over a named type an unregistered name fails the rule.
- [ ] The floor `1583-10-16` gates stored and computed values, not the constructor; the pre-1900 check follows [§4.1](#41-the-pre-1900-check)'s table.
- [ ] Zones resolve through a versioned legacy profile; gaps are formal errors, overlaps take the after offset, sub-day shifts keep their instant, a nonexistent label is answered per carrier.
- [ ] Partial dates: monotone suffix, omission before reality before position, precision classes per gate; `ValueAsDate` bridges them.
- [ ] Ranges: equality by component set, closed intervals, any-pair versus scalar-versus-list overlap.
- [ ] Operand gates are per unit ([§9](#9-datetime-rides-the-date-format-definition--but-the-operand-gates-are-per-operator-)); each operator's class is the operator reference's column D.
