# Kernel conformance coverage

<!-- GENERATED FILE — do not edit by hand. Regenerate with `./scripts/report-conformance-coverage.sh`. -->

**This report is derived, never authoritative.** It reads the Kernel's error catalogs and runtime formal-code constants under `../a12-kernel/`, this repository's owned documents, Lean source, and evidence JSON. Capability status stays in [`IMPLEMENTATION-MAP.md`](IMPLEMENTATION-MAP.md), open obligations in [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md), sequencing in [`PLAN.md`](PLAN.md), and provenance in [`SOURCES.md`](SOURCES.md). When this file and an owner disagree, the owner is right and this file is stale.

The identifier counts come from maximal-identifier extraction intersected with the Kernel vocabulary. `./scripts/report-conformance-coverage.sh --verify` re-derives them by multi-pattern fixed-string whole-word matching and aborts on disagreement. Run it after changing a counting mechanism; it also checks capability record boundaries and gap-shard ownership.

Working-tree counts generated on 2026-11-04; HEAD was `470e51ae`. The vocabulary scans include untracked files under their named roots; the estate inventory uses tracked paths. This is not a measurement of the exact committed revision's bytes.

## Headline

**Replaying 4143 retained Kernel observation rows through Lean, 107668 of the 109292 rule and computation instances Lean admits match the Kernel, 1604 diverge, 0 are not attributable beside a refused computation and 20 fault; [Axis R](#axis-r--population-replay) gives the clusters Lean cannot yet represent.** **Of the 219 construct-by-arm cells the Kernel admits, Lean represents 219 broadly (100%), 0 partially and 0 not at all, as classified on 2026-10-09 at `d55cc5b5+working-tree` in [Axis 0](#axis-0--kernel-constructs-by-arm).** 481 of 491 diagnostic identifiers occur in Lean source (97%); 10 do not.

An occurrence can be a definition, fixture, comment, request, or list of exclusions. It establishes neither implemented behaviour nor a matching Kernel observation. The vocabulary denominator also says nothing about successful evaluation, scheduling, addressing, or combinations of features. Use capability scopes, their retained evidence, and open obligations to assess semantic progress; they do not currently supply a complete behavioural denominator either.

## Terminology

| Term | Meaning in this report |
|---|---|
| Diagnostic identifier / class | A name from the selected Kernel diagnostic catalogs or runtime formal-code constants. Counting its occurrence measures vocabulary coverage. |
| Touched / untouched | A diagnostic name occurs somewhere in the scanned prose, Lean source, or evidence JSON / occurs in none of them. |
| Lean names | Diagnostic names found in Lean source, including comments and fixtures; not a count of implemented or proved behaviours. |
| Capability record (`cap`) | An entry in [the implementation map](IMPLEMENTATION-MAP.md) describing one supported semantic scope, its assurance, and its limits. It need not cover an entire operator or family. |
| Checkpoint | A source or measurement record documenting provenance, findings, and their scope; follow its links to inspect the supporting observations. |
| Checkpoint-citing capabilities (formerly `checkpoint caps`) | Capability records whose text mentions a checkpoint or calibration. This is a record count, not a count of fully calibrated capabilities. |
| Calibration / evidence pending | Calibration compares the executable account with retained Kernel observations for specified cases. An evidence-pending note identifies correspondence still to establish; a capability can have both calibrated and pending parts. |
| Open gap / remaining-work row | A gap is an unresolved semantic topic in [the gap index](SEMANTICS-GAPS.md). A remaining-work row is one entry within a topic; entries vary in size and may overlap. |
| Blocked route | The recorded way to obtain a needed observation cannot currently proceed. This blocks dependent work, not every open gap. |
| Ledger pending / handed-off | Nonterminal cross-project reconciliation states in [the synchronization ledger](A12-DMKITS-SPEC-SYNC-LEDGER.md). Neither state means the claim is accepted or closed. |
| Theory / support / evidence estate | Groups of tracked Lean source counted by nonblank lines: executable semantics, proofs and cases / supporting process and tooling / the evidence subset of support. |
| Capture directory / `inputHash` marker | A directory retaining probe artifacts / an input-identity field in the selected compact observation files. Neither count measures independent semantic cases. |
| Velocity | Changes in the historical table's selected counts. Unchanged counts can accompany semantic progress; the table is not a measure of completed behaviour per hour. |

## Axis 0 — Kernel constructs by arm

The denominator is every construct in a12-dmkits' [operator catalog](../../a12-rulekit/rulekit/src/main/resources/catalog/operators.json), on the validation arm (a rule's error condition) and the computation arm (an operation or its guard). Each cell's level is this repository's judgment in [`CONFORMANCE-CONSTRUCTS.tsv`](CONFORMANCE-CONSTRUCTS.tsv), classified 2026-10-09 at `d55cc5b5+working-tree`: **broad** represents the construct's main authoring forms on that arm across the operand kinds the Kernel admits, with conformance locks; **partial** represents some of them; **absent** has no Lean surface there. A cell is **calibrated** when a retained capture or checkpoint measures the construct on that arm, which for many cells is static admission only, not a runtime value. Constructs compose freely, so a broad cell can still miss a composition no catalog row names.

| | validation | computation | both arms |
|---|---|---|---|
| Constructs | 111 | 111 | |
| Admitted by the Kernel | 111 | 108 | 219 |
| Broad | 111 | 108 | 219 (100%) |
| Partial | 0 | 0 | 0 (0%) |
| Absent | 0 | 0 | 0 (0%) |

Of the admitted cells, 219 are calibrated, 0 are represented without a Kernel observation and 0 are neither represented nor measured; the Kernel refuses 3 constructs on the computation arm.

The open cells group by the shared mechanism that would close them, a construct counted once for each route its gap names; [the conformance economy proposal](CONFORMANCE-ECONOMY-PROPOSAL.md#closing-routes) defines each route:

| constructs | route |
|---|---|
| 33 | `guard` |
| 22 | `temporal-expr` |
| 15 | `having` |
| 11 | `rule-leaf` |
| 8 | `semantic-index` |
| 4 | `banded-rounding` |
| 4 | `string-expr` |
| 3 | `calibration-only` |
| 2 | `family-batch` |
| 2 | `host-regex` |

Remaining effort per construct, estimated at classification: 12 L, 56 M, 43 S (S at most one family batch, M two to four, L a new mechanism).

## Axis R — population replay

The [replay executable](../A12Kernel/ReplayMain.lean) reads each of the 611 retained `kernelProbe` requests with document rows, its DM-JSON model and its documents. It parses every rule condition and computation operation and lowers each onto the checked carriers the theory already has. Each rule and computation is then run and compared with the Kernel's retained artifact.

A rule is compared by the messages it fires: code, pointer and message type. Where those agree, its fired messages' `referenced` and `fillToFix` pointer sets are compared again as a separate references instance. A computation is compared by the Kernel's change projection for its target.

Each instance, one rule or computation on one document row, lands in one tier:

- **match**: the same outcome. A rule that fires on neither side matches too.
- **tier 1**: a different outcome.
- **tier 2**: Lean cannot represent the rule, computation, model or document. The construct column names the construct no carrier admitted, or the carrier whose elaborator refused it.
- **unattributed**: a computation reading, by name, the target of a refused computation, directly or through other computations, so neither its agreement nor its divergence is attributable to it.
- **fault**: Lean admitted the rule or plan but failed running it.
- **absent**: no comparable Kernel observation: none retained, an unreadable artifact or model file, or engines that disagree. These are counted as rows below.

| | rules | computations | rule references | partial rules | computation operand channels |
|---|---|---|---|---|---|
| match | 84152 | 23516 | 83625 | 42065 | 1523 |
| tier 1 | 1026 | 578 | 111 | 9 | 75 |
| tier 2 | 0 | 0 | 56 | 0 | 0 |
| unattributed | 0 | 0 | 0 | 0 | 0 |
| fault | 0 | 20 | 0 | 0 | 0 |

Of the 4143 rows, 172 have no matching row in a retained artifact, and 25 could not be read or prepared as a whole. Matching instances are calibration over this population only; they make no claim about a model the population does not contain.

### Tier-2 clusters

Each cluster is a construct no carrier admits, with its instances and its distinct members (one rule or computation of one request). Clusters are sorted by observed instance count; family priority follows unfinished coverage and delivery cost under [D3](CONFORMANCE-ECONOMY-PROPOSAL.md#d3--build-the-closing-routes-as-keystones-in-cluster-order).

| instances | members | arm | construct |
|---|---|---|---|
| 56 | 2 | references | `References` |
| 11 | 11 | row | `Prepare` |
| 10 | 3 | row | `Document` |
| 4 | 4 | row | `Model` |

### Tier-1 divergences

| request | row | rule or computation | outcomes |
|---|---|---|---|
| `calendar-expressions-2026-10-04/berlin/request.json` | `year-overflow` | `DateDayComp` | lean=[Form/DateDay=errored +10000-01-01] kernel=[Form/DateDay=errored 10000-01-01] |
| `calendar-expressions-2026-10-04/berlin/request.json` | `year-overflow` | `DateMonthComp` | lean=[Form/DateMonth=errored +10000-01-31] kernel=[Form/DateMonth=errored 10000-01-31] |
| `calendar-expressions-2026-10-04/berlin/request.json` | `year-overflow` | `DateYearComp` | lean=[Form/DateYear=errored +10000-12-31] kernel=[Form/DateYear=errored 10000-12-31] |
| `calendar-expressions-2026-10-04/berlin/request.json` | `year-overflow` | `DayThenMonthComp` | lean=[Form/DayThenMonth=errored +10000-02-01] kernel=[Form/DayThenMonth=errored 10000-02-01] |
| `calendar-expressions-2026-10-04/berlin/request.json` | `year-overflow` | `MonthThenDayComp` | lean=[Form/MonthThenDay=errored +10000-02-01] kernel=[Form/MonthThenDay=errored 10000-02-01] |
| `calendar-expressions-2026-10-04/berlin/request.json` | `year-overflow` | `StampDayComp` | lean=[Form/StampDay=errored +10000-01-01T12:30:00] kernel=[Form/StampDay=errored 10000-01-01T12:30:00] |
| `calendar-expressions-2026-10-04/fragment-limits-base-year/request.json` | `overflow` | `YMMonthsComp` | lean=[Form/YMMonths=errored +10000-01] kernel=[Form/YMMonths=errored 10000-01] |
| `calendar-expressions-2026-10-04/fragment-limits-base-year/request.json` | `overflow` | `YMYearsComp` | lean=[Form/YMYears=errored +10000-12] kernel=[Form/YMYears=errored 10000-12] |
| `calendar-expressions-2026-10-04/fragment-limits-base-year/request.json` | `overflow` | `YYearsComp` | lean=[Form/YYears=errored +10000] kernel=[Form/YYears=errored 10000] |
| `calendar-expressions-2026-10-04/fragment-limits-floor-year/request.json` | `overflow` | `YMMonthsComp` | lean=[Form/YMMonths=errored +10000-01] kernel=[Form/YMMonths=errored 10000-01] |
| `calendar-expressions-2026-10-04/fragment-limits-floor-year/request.json` | `overflow` | `YMYearsComp` | lean=[Form/YMYears=errored +10000-12] kernel=[Form/YMYears=errored 10000-12] |
| `calendar-expressions-2026-10-04/fragment-limits-floor-year/request.json` | `overflow` | `YYearsComp` | lean=[Form/YYears=errored +10000] kernel=[Form/YYears=errored 10000] |
| `calendar-expressions-2026-10-04/fragment-limits/request.json` | `overflow` | `YMMonthsComp` | lean=[Form/YMMonths=errored +10000-01] kernel=[Form/YMMonths=errored 10000-01] |
| `calendar-expressions-2026-10-04/fragment-limits/request.json` | `overflow` | `YMYearsComp` | lean=[Form/YMYears=errored +10000-12] kernel=[Form/YMYears=errored 10000-12] |
| `calendar-expressions-2026-10-04/fragment-limits/request.json` | `overflow` | `YYearsComp` | lean=[Form/YYears=errored +10000] kernel=[Form/YYears=errored 10000] |
| `calendar-expressions-2026-10-04/utc/request.json` | `year-overflow` | `DateDayComp` | lean=[Form/DateDay=errored +10000-01-01] kernel=[Form/DateDay=errored 10000-01-01] |
| `calendar-expressions-2026-10-04/utc/request.json` | `year-overflow` | `DateMonthComp` | lean=[Form/DateMonth=errored +10000-01-31] kernel=[Form/DateMonth=errored 10000-01-31] |
| `calendar-expressions-2026-10-04/utc/request.json` | `year-overflow` | `DateYearComp` | lean=[Form/DateYear=errored +10000-12-31] kernel=[Form/DateYear=errored 10000-12-31] |
| `calendar-expressions-2026-10-04/utc/request.json` | `year-overflow` | `DayThenMonthComp` | lean=[Form/DayThenMonth=errored +10000-02-01] kernel=[Form/DayThenMonth=errored 10000-02-01] |
| `calendar-expressions-2026-10-04/utc/request.json` | `year-overflow` | `MonthThenDayComp` | lean=[Form/MonthThenDay=errored +10000-02-01] kernel=[Form/MonthThenDay=errored 10000-02-01] |
| `calendar-expressions-2026-10-04/utc/request.json` | `year-overflow` | `StampDayComp` | lean=[Form/StampDay=errored +10000-01-01T12:30:00] kernel=[Form/StampDay=errored 10000-01-01T12:30:00] |
| `comparison-guards-2026-10-04/request.json` | `bad-empty` | `Form/Rows/AfterGapLeftComp` | lean=[Form/Rows/AfterGapLeft=cleared, Form/Rows[2]/AfterGapLeft=value 1] kernel=[Form/Rows/AfterGapLeft=cleared, Form/Rows[2]/AfterGapLeft=cleared] |
| `comparison-guards-2026-10-04/request.json` | `bad-empty` | `Form/Rows/AfterGapRightComp` | lean=[Form/Rows/AfterGapRight=cleared, Form/Rows[2]/AfterGapRight=value 1] kernel=[Form/Rows/AfterGapRight=cleared, Form/Rows[2]/AfterGapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `bad-empty` | `GapAndFalseComp` | lean=[] kernel=[GapAndFalseComp@Form/GapAndFalse:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `bad-empty` | `GapLeftComp` | lean=[] kernel=[GapLeftComp@Form/GapLeft:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `bad-empty` | `GapLeftComp` | lean=[] kernel=[GapLeftComp@Form/Rows/GapLeft:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `bad-empty` | `GapRightComp` | lean=[] kernel=[GapRightComp@Form/GapRight:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `bad-empty` | `GapRightComp` | lean=[] kernel=[GapRightComp@Form/Rows/GapRight:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `bad-empty` | `GapStampComp` | lean=[] kernel=[GapStampComp@Form/GapStamp:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `bad-empty` | `GapTextComp` | lean=[] kernel=[GapTextComp@Form/GapText:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `bad-empty` | `TrueOrGapComp` | lean=[TrueOrGapComp@Form/TrueOrGap:VALUE_ERROR/ERROR referenced=[Form/N, Form/TrueOrGap, Form/Z1] fillToFix=[]] kernel=[TrueOrGapComp@Form/TrueOrGap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `comparison-guards-2026-10-04/request.json` | `bad-empty` | `call` | lean=[Form/B1:feldJaNeinFalsch, Form/C1:feldJaFalsch, Form/D1:datumFormatFalsch, Form/F1:datumFormatFalsch, Form/R1:datumBereichTrennerFehlt, Form/Rows/B1:feldJaNeinFalsch, Form/Rows/C1:feldJaFalsch, Form/Rows/D1:datumFormatFalsch, Form/Rows/R1:datumBereichTrennerFehlt, Form/Rows/Z1:datumFormatFalsch, Form/Rows[2]/B2:feldJaNeinFalsch, Form/Rows[2]/C2:feldJaFalsch, Form/Rows[2]/D2:datumFormatFalsch, Form/Rows[2]/R2:datumBereichTrennerFehlt, Form/Rows[2]/Z2:datumFormatFalsch, Form/T1:datumFormatFalsch, Form/Y1:datumFormatFalsch, Form/Z1:datumFormatFalsch] kernel=[Form/B1:feldJaNeinFalsch, Form/C1:feldJaFalsch, Form/D1:datumFormatFalsch, Form/F1:datumFormatFalsch, Form/GapLeft:berechnungsWertFehler, Form/R1:datumBereichTrennerFehlt, Form/Rows/B1:feldJaNeinFalsch, Form/Rows/C1:feldJaFalsch, Form/Rows/D1:datumFormatFalsch, Form/Rows/GapLeft:berechnungsWertFehler, Form/Rows/R1:datumBereichTrennerFehlt, Form/Rows/Z1:datumFormatFalsch, Form/Rows[2]/B2:feldJaNeinFalsch, Form/Rows[2]/C2:feldJaFalsch, Form/Rows[2]/D2:datumFormatFalsch, Form/Rows[2]/GapLeft:berechnungsWertFehler, Form/Rows[2]/GapRight:berechnungsWertFehler, Form/Rows[2]/R2:datumBereichTrennerFehlt, Form/Rows[2]/Z2:datumFormatFalsch, Form/T1:datumFormatFalsch, Form/Y1:datumFormatFalsch, Form/Z1:datumFormatFalsch] |
| `comparison-guards-2026-10-04/request.json` | `bad-valid` | `Form/Rows/AfterGapLeftComp` | lean=[Form/Rows/AfterGapLeft=cleared, Form/Rows[2]/AfterGapLeft=value 1] kernel=[Form/Rows/AfterGapLeft=cleared, Form/Rows[2]/AfterGapLeft=cleared] |
| `comparison-guards-2026-10-04/request.json` | `bad-valid` | `Form/Rows/AfterGapRightComp` | lean=[Form/Rows/AfterGapRight=cleared, Form/Rows[2]/AfterGapRight=value 1] kernel=[Form/Rows/AfterGapRight=cleared, Form/Rows[2]/AfterGapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `bad-valid` | `Form/Rows/GapRightComp` | lean=[Form/Rows/GapRight=cleared, Form/Rows[2]/GapRight=value 1] kernel=[Form/Rows/GapRight=cleared, Form/Rows[2]/GapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `bad-valid` | `GapAndFalseComp` | lean=[] kernel=[GapAndFalseComp@Form/GapAndFalse:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `bad-valid` | `GapLeftComp` | lean=[] kernel=[GapLeftComp@Form/GapLeft:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `bad-valid` | `GapLeftComp` | lean=[] kernel=[GapLeftComp@Form/Rows/GapLeft:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `bad-valid` | `GapRightComp` | lean=[GapRightComp@Form/Rows[2]/GapRight:VALUE_ERROR/ERROR] kernel=[GapRightComp@Form/Rows/GapRight:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `bad-valid` | `GapRightComp` | lean=[] kernel=[GapRightComp@Form/GapRight:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `bad-valid` | `GapStampComp` | lean=[] kernel=[GapStampComp@Form/GapStamp:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `bad-valid` | `GapTextComp` | lean=[] kernel=[GapTextComp@Form/GapText:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `bad-valid` | `TrueOrGapComp` | lean=[TrueOrGapComp@Form/TrueOrGap:VALUE_ERROR/ERROR referenced=[Form/N, Form/TrueOrGap, Form/Z1] fillToFix=[]] kernel=[TrueOrGapComp@Form/TrueOrGap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `comparison-guards-2026-10-04/request.json` | `bad-valid` | `call` | lean=[Form/B1:feldJaNeinFalsch, Form/C1:feldJaFalsch, Form/D1:datumFormatFalsch, Form/F1:datumFormatFalsch, Form/R1:datumBereichTrennerFehlt, Form/Rows/B1:feldJaNeinFalsch, Form/Rows/C1:feldJaFalsch, Form/Rows/D1:datumFormatFalsch, Form/Rows/R1:datumBereichTrennerFehlt, Form/Rows/Z1:datumFormatFalsch, Form/Rows[2]/B2:feldJaNeinFalsch, Form/Rows[2]/C2:feldJaFalsch, Form/Rows[2]/D2:datumFormatFalsch, Form/Rows[2]/R2:datumBereichTrennerFehlt, Form/Rows[2]/Z2:datumFormatFalsch, Form/T1:datumFormatFalsch, Form/Y1:datumFormatFalsch, Form/Z1:datumFormatFalsch] kernel=[Form/B1:feldJaNeinFalsch, Form/C1:feldJaFalsch, Form/D1:datumFormatFalsch, Form/F1:datumFormatFalsch, Form/GapLeft:berechnungsWertFehler, Form/R1:datumBereichTrennerFehlt, Form/Rows/B1:feldJaNeinFalsch, Form/Rows/C1:feldJaFalsch, Form/Rows/D1:datumFormatFalsch, Form/Rows/GapLeft:berechnungsWertFehler, Form/Rows/R1:datumBereichTrennerFehlt, Form/Rows/Z1:datumFormatFalsch, Form/Rows[2]/B2:feldJaNeinFalsch, Form/Rows[2]/C2:feldJaFalsch, Form/Rows[2]/D2:datumFormatFalsch, Form/Rows[2]/GapLeft:berechnungsWertFehler, Form/Rows[2]/GapRight:berechnungsWertFehler, Form/Rows[2]/R2:datumBereichTrennerFehlt, Form/Rows[2]/Z2:datumFormatFalsch, Form/T1:datumFormatFalsch, Form/Y1:datumFormatFalsch, Form/Z1:datumFormatFalsch] |
| `comparison-guards-2026-10-04/request.json` | `early` | `AfterGapAndFalseComp` | lean=[Form/AfterGapAndFalse=value 1] kernel=[Form/AfterGapAndFalse=cleared] |
| `comparison-guards-2026-10-04/request.json` | `early` | `Form/AfterGapLeftComp` | lean=[Form/AfterGapLeft=value 1] kernel=[Form/AfterGapLeft=cleared] |
| `comparison-guards-2026-10-04/request.json` | `early` | `Form/AfterGapRightComp` | lean=[Form/AfterGapRight=value 1] kernel=[Form/AfterGapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `early` | `Form/GapRightComp` | lean=[Form/GapRight=value 1] kernel=[Form/GapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `early` | `Form/Rows/AfterGapLeftComp` | lean=[Form/Rows/AfterGapLeft=value 1, Form/Rows[2]/AfterGapLeft=value 1] kernel=[Form/Rows/AfterGapLeft=cleared, Form/Rows[2]/AfterGapLeft=cleared] |
| `comparison-guards-2026-10-04/request.json` | `early` | `Form/Rows/AfterGapRightComp` | lean=[Form/Rows/AfterGapRight=value 1, Form/Rows[2]/AfterGapRight=value 1] kernel=[Form/Rows/AfterGapRight=cleared, Form/Rows[2]/AfterGapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `early` | `Form/Rows/GapRightComp` | lean=[Form/Rows/GapRight=value 1, Form/Rows[2]/GapRight=value 1] kernel=[Form/Rows/GapRight=cleared, Form/Rows[2]/GapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `early` | `GapAndFalseComp` | lean=[] kernel=[GapAndFalseComp@Form/GapAndFalse:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `early` | `GapLeftComp` | lean=[] kernel=[GapLeftComp@Form/GapLeft:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `early` | `GapLeftComp` | lean=[] kernel=[GapLeftComp@Form/Rows/GapLeft:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `early` | `GapRightComp` | lean=[GapRightComp@Form/GapRight:VALUE_ERROR/ERROR referenced=[Form/GapRight, Form/Z1] fillToFix=[]] kernel=[GapRightComp@Form/GapRight:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `comparison-guards-2026-10-04/request.json` | `early` | `GapRightComp` | lean=[GapRightComp@Form/Rows/GapRight:VALUE_ERROR/ERROR, GapRightComp@Form/Rows[2]/GapRight:VALUE_ERROR/ERROR] kernel=[GapRightComp@Form/Rows/GapRight:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `early` | `GapStampComp` | lean=[] kernel=[Form/GapStamp=cleared] |
| `comparison-guards-2026-10-04/request.json` | `early` | `GapStampComp` | lean=[] kernel=[GapStampComp@Form/GapStamp:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `early` | `GapTextComp` | lean=[Form/GapText=value ok] kernel=[Form/GapText=cleared] |
| `comparison-guards-2026-10-04/request.json` | `early` | `GapTextComp` | lean=[GapTextComp@Form/GapText:VALUE_ERROR/ERROR referenced=[Form/GapText, Form/Z1] fillToFix=[]] kernel=[GapTextComp@Form/GapText:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `comparison-guards-2026-10-04/request.json` | `early` | `TrueOrGapComp` | lean=[TrueOrGapComp@Form/TrueOrGap:VALUE_ERROR/ERROR referenced=[Form/N, Form/TrueOrGap, Form/Z1] fillToFix=[]] kernel=[TrueOrGapComp@Form/TrueOrGap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `comparison-guards-2026-10-04/request.json` | `early` | `call` | lean=[] kernel=[Form/GapAndFalse:berechnungsWertFehler, Form/GapLeft:berechnungsWertFehler, Form/GapRight:berechnungsWertFehler, Form/GapStamp:berechnungsWertFehler, Form/GapText:berechnungsWertFehler, Form/Rows/GapLeft:berechnungsWertFehler, Form/Rows/GapRight:berechnungsWertFehler, Form/Rows[2]/GapLeft:berechnungsWertFehler, Form/Rows[2]/GapRight:berechnungsWertFehler] |
| `comparison-guards-2026-10-04/request.json` | `empty` | `AfterGapAndFalseComp` | lean=[Form/AfterGapAndFalse=value 1] kernel=[Form/AfterGapAndFalse=cleared] |
| `comparison-guards-2026-10-04/request.json` | `empty` | `AfterGapStampComp` | lean=[Form/AfterGapStamp=value 1] kernel=[Form/AfterGapStamp=cleared] |
| `comparison-guards-2026-10-04/request.json` | `empty` | `AfterGapTextComp` | lean=[Form/AfterGapText=value 1] kernel=[Form/AfterGapText=cleared] |
| `comparison-guards-2026-10-04/request.json` | `empty` | `Form/AfterGapLeftComp` | lean=[Form/AfterGapLeft=value 1] kernel=[Form/AfterGapLeft=cleared] |
| `comparison-guards-2026-10-04/request.json` | `empty` | `Form/AfterGapRightComp` | lean=[Form/AfterGapRight=value 1] kernel=[Form/AfterGapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `empty` | `Form/Rows/AfterGapLeftComp` | lean=[Form/Rows/AfterGapLeft=value 1, Form/Rows[2]/AfterGapLeft=value 1] kernel=[Form/Rows/AfterGapLeft=cleared, Form/Rows[2]/AfterGapLeft=cleared] |
| `comparison-guards-2026-10-04/request.json` | `empty` | `Form/Rows/AfterGapRightComp` | lean=[Form/Rows/AfterGapRight=value 1, Form/Rows[2]/AfterGapRight=value 1] kernel=[Form/Rows/AfterGapRight=cleared, Form/Rows[2]/AfterGapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `empty` | `GapAndFalseComp` | lean=[] kernel=[GapAndFalseComp@Form/GapAndFalse:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `empty` | `GapLeftComp` | lean=[] kernel=[GapLeftComp@Form/GapLeft:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `empty` | `GapLeftComp` | lean=[] kernel=[GapLeftComp@Form/Rows/GapLeft:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `empty` | `GapRightComp` | lean=[] kernel=[GapRightComp@Form/GapRight:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `empty` | `GapRightComp` | lean=[] kernel=[GapRightComp@Form/Rows/GapRight:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `empty` | `GapStampComp` | lean=[] kernel=[GapStampComp@Form/GapStamp:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `empty` | `GapTextComp` | lean=[] kernel=[GapTextComp@Form/GapText:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `empty` | `TrueOrGapComp` | lean=[TrueOrGapComp@Form/TrueOrGap:VALUE_ERROR/ERROR referenced=[Form/N, Form/TrueOrGap, Form/Z1] fillToFix=[]] kernel=[TrueOrGapComp@Form/TrueOrGap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `comparison-guards-2026-10-04/request.json` | `empty` | `call` | lean=[] kernel=[Form/GapAndFalse:berechnungsWertFehler, Form/GapLeft:berechnungsWertFehler, Form/GapRight:berechnungsWertFehler, Form/GapStamp:berechnungsWertFehler, Form/GapText:berechnungsWertFehler, Form/Rows/GapLeft:berechnungsWertFehler, Form/Rows/GapRight:berechnungsWertFehler, Form/Rows[2]/GapLeft:berechnungsWertFehler, Form/Rows[2]/GapRight:berechnungsWertFehler] |
| `comparison-guards-2026-10-04/request.json` | `empty-bad` | `AfterGapAndFalseComp` | lean=[Form/AfterGapAndFalse=value 1] kernel=[Form/AfterGapAndFalse=cleared] |
| `comparison-guards-2026-10-04/request.json` | `empty-bad` | `AfterGapStampComp` | lean=[Form/AfterGapStamp=value 1] kernel=[Form/AfterGapStamp=cleared] |
| `comparison-guards-2026-10-04/request.json` | `empty-bad` | `AfterGapTextComp` | lean=[Form/AfterGapText=value 1] kernel=[Form/AfterGapText=cleared] |
| `comparison-guards-2026-10-04/request.json` | `empty-bad` | `Form/AfterGapLeftComp` | lean=[Form/AfterGapLeft=value 1] kernel=[Form/AfterGapLeft=cleared] |
| `comparison-guards-2026-10-04/request.json` | `empty-bad` | `Form/AfterGapRightComp` | lean=[Form/AfterGapRight=value 1] kernel=[Form/AfterGapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `empty-bad` | `Form/Rows/AfterGapLeftComp` | lean=[Form/Rows/AfterGapLeft=value 1, Form/Rows[2]/AfterGapLeft=cleared] kernel=[Form/Rows/AfterGapLeft=cleared, Form/Rows[2]/AfterGapLeft=cleared] |
| `comparison-guards-2026-10-04/request.json` | `empty-bad` | `Form/Rows/AfterGapRightComp` | lean=[Form/Rows/AfterGapRight=value 1, Form/Rows[2]/AfterGapRight=cleared] kernel=[Form/Rows/AfterGapRight=cleared, Form/Rows[2]/AfterGapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `empty-bad` | `GapAndFalseComp` | lean=[] kernel=[GapAndFalseComp@Form/GapAndFalse:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `empty-bad` | `GapLeftComp` | lean=[] kernel=[GapLeftComp@Form/GapLeft:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `empty-bad` | `GapLeftComp` | lean=[] kernel=[GapLeftComp@Form/Rows/GapLeft:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `empty-bad` | `GapRightComp` | lean=[] kernel=[GapRightComp@Form/GapRight:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `empty-bad` | `GapRightComp` | lean=[] kernel=[GapRightComp@Form/Rows/GapRight:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `empty-bad` | `GapStampComp` | lean=[] kernel=[GapStampComp@Form/GapStamp:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `empty-bad` | `GapTextComp` | lean=[] kernel=[GapTextComp@Form/GapText:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `empty-bad` | `TrueOrGapComp` | lean=[TrueOrGapComp@Form/TrueOrGap:VALUE_ERROR/ERROR referenced=[Form/N, Form/TrueOrGap, Form/Z1] fillToFix=[]] kernel=[TrueOrGapComp@Form/TrueOrGap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `comparison-guards-2026-10-04/request.json` | `empty-bad` | `call` | lean=[Form/B2:feldJaNeinFalsch, Form/C2:feldJaFalsch, Form/D2:datumFormatFalsch, Form/F2:datumFormatFalsch, Form/R2:datumBereichTrennerFehlt, Form/Rows/B2:feldJaNeinFalsch, Form/Rows/C2:feldJaFalsch, Form/Rows/D2:datumFormatFalsch, Form/Rows/R2:datumBereichTrennerFehlt, Form/Rows/Z2:datumFormatFalsch, Form/Rows[2]/B1:feldJaNeinFalsch, Form/Rows[2]/C1:feldJaFalsch, Form/Rows[2]/D1:datumFormatFalsch, Form/Rows[2]/R1:datumBereichTrennerFehlt, Form/Rows[2]/Z1:datumFormatFalsch, Form/T2:datumFormatFalsch, Form/Y2:datumFormatFalsch, Form/Z2:datumFormatFalsch] kernel=[Form/B2:feldJaNeinFalsch, Form/C2:feldJaFalsch, Form/D2:datumFormatFalsch, Form/F2:datumFormatFalsch, Form/GapAndFalse:berechnungsWertFehler, Form/GapLeft:berechnungsWertFehler, Form/GapRight:berechnungsWertFehler, Form/GapStamp:berechnungsWertFehler, Form/GapText:berechnungsWertFehler, Form/R2:datumBereichTrennerFehlt, Form/Rows/B2:feldJaNeinFalsch, Form/Rows/C2:feldJaFalsch, Form/Rows/D2:datumFormatFalsch, Form/Rows/GapLeft:berechnungsWertFehler, Form/Rows/GapRight:berechnungsWertFehler, Form/Rows/R2:datumBereichTrennerFehlt, Form/Rows/Z2:datumFormatFalsch, Form/Rows[2]/B1:feldJaNeinFalsch, Form/Rows[2]/C1:feldJaFalsch, Form/Rows[2]/D1:datumFormatFalsch, Form/Rows[2]/GapLeft:berechnungsWertFehler, Form/Rows[2]/R1:datumBereichTrennerFehlt, Form/Rows[2]/Z1:datumFormatFalsch, Form/T2:datumFormatFalsch, Form/Y2:datumFormatFalsch, Form/Z2:datumFormatFalsch] |
| `comparison-guards-2026-10-04/request.json` | `equal` | `AfterGapAndFalseComp` | lean=[Form/AfterGapAndFalse=value 1] kernel=[Form/AfterGapAndFalse=cleared] |
| `comparison-guards-2026-10-04/request.json` | `equal` | `Form/AfterGapLeftComp` | lean=[Form/AfterGapLeft=value 1] kernel=[Form/AfterGapLeft=cleared] |
| `comparison-guards-2026-10-04/request.json` | `equal` | `Form/AfterGapRightComp` | lean=[Form/AfterGapRight=value 1] kernel=[Form/AfterGapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `equal` | `Form/GapRightComp` | lean=[Form/GapRight=value 1] kernel=[Form/GapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `equal` | `Form/Rows/AfterGapLeftComp` | lean=[Form/Rows/AfterGapLeft=value 1, Form/Rows[2]/AfterGapLeft=value 1] kernel=[Form/Rows/AfterGapLeft=cleared, Form/Rows[2]/AfterGapLeft=cleared] |
| `comparison-guards-2026-10-04/request.json` | `equal` | `Form/Rows/AfterGapRightComp` | lean=[Form/Rows/AfterGapRight=value 1, Form/Rows[2]/AfterGapRight=value 1] kernel=[Form/Rows/AfterGapRight=cleared, Form/Rows[2]/AfterGapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `equal` | `Form/Rows/GapRightComp` | lean=[Form/Rows/GapRight=value 1, Form/Rows[2]/GapRight=value 1] kernel=[Form/Rows/GapRight=cleared, Form/Rows[2]/GapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `equal` | `GapAndFalseComp` | lean=[] kernel=[GapAndFalseComp@Form/GapAndFalse:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `equal` | `GapLeftComp` | lean=[] kernel=[GapLeftComp@Form/GapLeft:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `equal` | `GapLeftComp` | lean=[] kernel=[GapLeftComp@Form/Rows/GapLeft:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `equal` | `GapRightComp` | lean=[GapRightComp@Form/GapRight:VALUE_ERROR/ERROR referenced=[Form/GapRight, Form/Z1] fillToFix=[]] kernel=[GapRightComp@Form/GapRight:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `comparison-guards-2026-10-04/request.json` | `equal` | `GapRightComp` | lean=[GapRightComp@Form/Rows/GapRight:VALUE_ERROR/ERROR, GapRightComp@Form/Rows[2]/GapRight:VALUE_ERROR/ERROR] kernel=[GapRightComp@Form/Rows/GapRight:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `equal` | `GapStampComp` | lean=[] kernel=[Form/GapStamp=cleared] |
| `comparison-guards-2026-10-04/request.json` | `equal` | `GapStampComp` | lean=[] kernel=[GapStampComp@Form/GapStamp:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `equal` | `GapTextComp` | lean=[Form/GapText=value ok] kernel=[Form/GapText=cleared] |
| `comparison-guards-2026-10-04/request.json` | `equal` | `GapTextComp` | lean=[GapTextComp@Form/GapText:VALUE_ERROR/ERROR referenced=[Form/GapText, Form/Z1] fillToFix=[]] kernel=[GapTextComp@Form/GapText:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `comparison-guards-2026-10-04/request.json` | `equal` | `TrueOrGapComp` | lean=[TrueOrGapComp@Form/TrueOrGap:VALUE_ERROR/ERROR referenced=[Form/N, Form/TrueOrGap, Form/Z1] fillToFix=[]] kernel=[TrueOrGapComp@Form/TrueOrGap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `comparison-guards-2026-10-04/request.json` | `equal` | `call` | lean=[] kernel=[Form/GapAndFalse:berechnungsWertFehler, Form/GapLeft:berechnungsWertFehler, Form/GapRight:berechnungsWertFehler, Form/GapStamp:berechnungsWertFehler, Form/GapText:berechnungsWertFehler, Form/Rows/GapLeft:berechnungsWertFehler, Form/Rows/GapRight:berechnungsWertFehler, Form/Rows[2]/GapLeft:berechnungsWertFehler, Form/Rows[2]/GapRight:berechnungsWertFehler] |
| `comparison-guards-2026-10-04/request.json` | `later` | `AfterGapAndFalseComp` | lean=[Form/AfterGapAndFalse=value 1] kernel=[Form/AfterGapAndFalse=cleared] |
| `comparison-guards-2026-10-04/request.json` | `later` | `Form/AfterGapLeftComp` | lean=[Form/AfterGapLeft=value 1] kernel=[Form/AfterGapLeft=cleared] |
| `comparison-guards-2026-10-04/request.json` | `later` | `Form/AfterGapRightComp` | lean=[Form/AfterGapRight=value 1] kernel=[Form/AfterGapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `later` | `Form/GapRightComp` | lean=[Form/GapRight=value 1] kernel=[Form/GapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `later` | `Form/Rows/AfterGapLeftComp` | lean=[Form/Rows/AfterGapLeft=value 1, Form/Rows[2]/AfterGapLeft=value 1] kernel=[Form/Rows/AfterGapLeft=cleared, Form/Rows[2]/AfterGapLeft=cleared] |
| `comparison-guards-2026-10-04/request.json` | `later` | `Form/Rows/AfterGapRightComp` | lean=[Form/Rows/AfterGapRight=value 1, Form/Rows[2]/AfterGapRight=value 1] kernel=[Form/Rows/AfterGapRight=cleared, Form/Rows[2]/AfterGapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `later` | `Form/Rows/GapRightComp` | lean=[Form/Rows/GapRight=value 1, Form/Rows[2]/GapRight=value 1] kernel=[Form/Rows/GapRight=cleared, Form/Rows[2]/GapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `later` | `GapAndFalseComp` | lean=[] kernel=[GapAndFalseComp@Form/GapAndFalse:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `later` | `GapLeftComp` | lean=[] kernel=[GapLeftComp@Form/GapLeft:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `later` | `GapLeftComp` | lean=[] kernel=[GapLeftComp@Form/Rows/GapLeft:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `later` | `GapRightComp` | lean=[GapRightComp@Form/GapRight:VALUE_ERROR/ERROR referenced=[Form/GapRight, Form/Z1] fillToFix=[]] kernel=[GapRightComp@Form/GapRight:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `comparison-guards-2026-10-04/request.json` | `later` | `GapRightComp` | lean=[GapRightComp@Form/Rows/GapRight:VALUE_ERROR/ERROR, GapRightComp@Form/Rows[2]/GapRight:VALUE_ERROR/ERROR] kernel=[GapRightComp@Form/Rows/GapRight:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `later` | `GapStampComp` | lean=[] kernel=[Form/GapStamp=cleared] |
| `comparison-guards-2026-10-04/request.json` | `later` | `GapStampComp` | lean=[] kernel=[GapStampComp@Form/GapStamp:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `later` | `GapTextComp` | lean=[Form/GapText=value ok] kernel=[Form/GapText=cleared] |
| `comparison-guards-2026-10-04/request.json` | `later` | `GapTextComp` | lean=[GapTextComp@Form/GapText:VALUE_ERROR/ERROR referenced=[Form/GapText, Form/Z1] fillToFix=[]] kernel=[GapTextComp@Form/GapText:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `comparison-guards-2026-10-04/request.json` | `later` | `TrueOrGapComp` | lean=[TrueOrGapComp@Form/TrueOrGap:VALUE_ERROR/ERROR referenced=[Form/N, Form/TrueOrGap, Form/Z1] fillToFix=[]] kernel=[TrueOrGapComp@Form/TrueOrGap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `comparison-guards-2026-10-04/request.json` | `later` | `call` | lean=[] kernel=[Form/GapAndFalse:berechnungsWertFehler, Form/GapLeft:berechnungsWertFehler, Form/GapRight:berechnungsWertFehler, Form/GapStamp:berechnungsWertFehler, Form/GapText:berechnungsWertFehler, Form/Rows/GapLeft:berechnungsWertFehler, Form/Rows/GapRight:berechnungsWertFehler, Form/Rows[2]/GapLeft:berechnungsWertFehler, Form/Rows[2]/GapRight:berechnungsWertFehler] |
| `comparison-guards-2026-10-04/request.json` | `valid-bad` | `AfterGapAndFalseComp` | lean=[Form/AfterGapAndFalse=value 1] kernel=[Form/AfterGapAndFalse=cleared] |
| `comparison-guards-2026-10-04/request.json` | `valid-bad` | `Form/AfterGapLeftComp` | lean=[Form/AfterGapLeft=value 1] kernel=[Form/AfterGapLeft=cleared] |
| `comparison-guards-2026-10-04/request.json` | `valid-bad` | `Form/AfterGapRightComp` | lean=[Form/AfterGapRight=value 1] kernel=[Form/AfterGapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `valid-bad` | `Form/GapRightComp` | lean=[Form/GapRight=value 1] kernel=[Form/GapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `valid-bad` | `Form/Rows/AfterGapLeftComp` | lean=[Form/Rows/AfterGapLeft=value 1, Form/Rows[2]/AfterGapLeft=cleared] kernel=[Form/Rows/AfterGapLeft=cleared, Form/Rows[2]/AfterGapLeft=cleared] |
| `comparison-guards-2026-10-04/request.json` | `valid-bad` | `Form/Rows/AfterGapRightComp` | lean=[Form/Rows/AfterGapRight=value 1, Form/Rows[2]/AfterGapRight=cleared] kernel=[Form/Rows/AfterGapRight=cleared, Form/Rows[2]/AfterGapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `valid-bad` | `Form/Rows/GapRightComp` | lean=[Form/Rows/GapRight=value 1, Form/Rows[2]/GapRight=cleared] kernel=[Form/Rows/GapRight=cleared, Form/Rows[2]/GapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `valid-bad` | `GapAndFalseComp` | lean=[] kernel=[GapAndFalseComp@Form/GapAndFalse:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `valid-bad` | `GapLeftComp` | lean=[] kernel=[GapLeftComp@Form/GapLeft:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `valid-bad` | `GapLeftComp` | lean=[] kernel=[GapLeftComp@Form/Rows/GapLeft:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `valid-bad` | `GapRightComp` | lean=[GapRightComp@Form/GapRight:VALUE_ERROR/ERROR referenced=[Form/GapRight, Form/Z1] fillToFix=[]] kernel=[GapRightComp@Form/GapRight:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `comparison-guards-2026-10-04/request.json` | `valid-bad` | `GapRightComp` | lean=[GapRightComp@Form/Rows/GapRight:VALUE_ERROR/ERROR referenced=[Form/Rows/GapRight, Form/Rows/Z1] fillToFix=[]] kernel=[GapRightComp@Form/Rows/GapRight:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `comparison-guards-2026-10-04/request.json` | `valid-bad` | `GapStampComp` | lean=[] kernel=[Form/GapStamp=cleared] |
| `comparison-guards-2026-10-04/request.json` | `valid-bad` | `GapStampComp` | lean=[] kernel=[GapStampComp@Form/GapStamp:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `valid-bad` | `GapTextComp` | lean=[Form/GapText=value ok] kernel=[Form/GapText=cleared] |
| `comparison-guards-2026-10-04/request.json` | `valid-bad` | `GapTextComp` | lean=[GapTextComp@Form/GapText:VALUE_ERROR/ERROR referenced=[Form/GapText, Form/Z1] fillToFix=[]] kernel=[GapTextComp@Form/GapText:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `comparison-guards-2026-10-04/request.json` | `valid-bad` | `TrueOrGapComp` | lean=[TrueOrGapComp@Form/TrueOrGap:VALUE_ERROR/ERROR referenced=[Form/N, Form/TrueOrGap, Form/Z1] fillToFix=[]] kernel=[TrueOrGapComp@Form/TrueOrGap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `comparison-guards-2026-10-04/request.json` | `valid-bad` | `call` | lean=[Form/B2:feldJaNeinFalsch, Form/C1:feldJaFalsch, Form/C2:feldJaFalsch, Form/D2:datumFormatFalsch, Form/F2:datumFormatFalsch, Form/R2:datumBereichTrennerFehlt, Form/Rows/B2:feldJaNeinFalsch, Form/Rows/C1:feldJaFalsch, Form/Rows/C2:feldJaFalsch, Form/Rows/D2:datumFormatFalsch, Form/Rows/R2:datumBereichTrennerFehlt, Form/Rows/Z2:datumFormatFalsch, Form/Rows[2]/B1:feldJaNeinFalsch, Form/Rows[2]/C1:feldJaFalsch, Form/Rows[2]/C2:feldJaFalsch, Form/Rows[2]/D1:datumFormatFalsch, Form/Rows[2]/R1:datumBereichTrennerFehlt, Form/Rows[2]/Z1:datumFormatFalsch, Form/T2:datumFormatFalsch, Form/Y2:datumFormatFalsch, Form/Z2:datumFormatFalsch] kernel=[Form/B2:feldJaNeinFalsch, Form/C1:feldJaFalsch, Form/C2:feldJaFalsch, Form/D2:datumFormatFalsch, Form/F2:datumFormatFalsch, Form/GapAndFalse:berechnungsWertFehler, Form/GapLeft:berechnungsWertFehler, Form/GapRight:berechnungsWertFehler, Form/GapStamp:berechnungsWertFehler, Form/GapText:berechnungsWertFehler, Form/R2:datumBereichTrennerFehlt, Form/Rows/B2:feldJaNeinFalsch, Form/Rows/C1:feldJaFalsch, Form/Rows/C2:feldJaFalsch, Form/Rows/D2:datumFormatFalsch, Form/Rows/GapLeft:berechnungsWertFehler, Form/Rows/GapRight:berechnungsWertFehler, Form/Rows/R2:datumBereichTrennerFehlt, Form/Rows/Z2:datumFormatFalsch, Form/Rows[2]/B1:feldJaNeinFalsch, Form/Rows[2]/C1:feldJaFalsch, Form/Rows[2]/C2:feldJaFalsch, Form/Rows[2]/D1:datumFormatFalsch, Form/Rows[2]/GapLeft:berechnungsWertFehler, Form/Rows[2]/R1:datumBereichTrennerFehlt, Form/Rows[2]/Z1:datumFormatFalsch, Form/T2:datumFormatFalsch, Form/Y2:datumFormatFalsch, Form/Z2:datumFormatFalsch] |
| `comparison-guards-2026-10-04/request.json` | `zone-before-now` | `AfterGapAndFalseComp` | lean=[Form/AfterGapAndFalse=value 1] kernel=[Form/AfterGapAndFalse=cleared] |
| `comparison-guards-2026-10-04/request.json` | `zone-before-now` | `AfterGapStampComp` | lean=[Form/AfterGapStamp=value 1] kernel=[Form/AfterGapStamp=cleared] |
| `comparison-guards-2026-10-04/request.json` | `zone-before-now` | `AfterGapTextComp` | lean=[Form/AfterGapText=value 1] kernel=[Form/AfterGapText=cleared] |
| `comparison-guards-2026-10-04/request.json` | `zone-before-now` | `Form/AfterGapLeftComp` | lean=[Form/AfterGapLeft=value 1] kernel=[Form/AfterGapLeft=cleared] |
| `comparison-guards-2026-10-04/request.json` | `zone-before-now` | `Form/AfterGapRightComp` | lean=[Form/AfterGapRight=value 1] kernel=[Form/AfterGapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `zone-before-now` | `Form/GapLeftComp` | lean=[Form/GapLeft=value 1] kernel=[Form/GapLeft=cleared] |
| `comparison-guards-2026-10-04/request.json` | `zone-before-now` | `Form/Rows/AfterGapLeftComp` | lean=[Form/Rows/AfterGapLeft=value 1, Form/Rows[2]/AfterGapLeft=value 1] kernel=[Form/Rows/AfterGapLeft=cleared, Form/Rows[2]/AfterGapLeft=cleared] |
| `comparison-guards-2026-10-04/request.json` | `zone-before-now` | `Form/Rows/AfterGapRightComp` | lean=[Form/Rows/AfterGapRight=value 1, Form/Rows[2]/AfterGapRight=value 1] kernel=[Form/Rows/AfterGapRight=cleared, Form/Rows[2]/AfterGapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `zone-before-now` | `Form/Rows/GapRightComp` | lean=[Form/Rows/GapRight=value 1, Form/Rows[2]/GapRight=value 1] kernel=[Form/Rows/GapRight=cleared, Form/Rows[2]/GapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `zone-before-now` | `GapAndFalseComp` | lean=[] kernel=[GapAndFalseComp@Form/GapAndFalse:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `zone-before-now` | `GapLeftComp` | lean=[GapLeftComp@Form/GapLeft:VALUE_ERROR/ERROR referenced=[Form/GapLeft, Form/Z1] fillToFix=[]] kernel=[GapLeftComp@Form/GapLeft:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `comparison-guards-2026-10-04/request.json` | `zone-before-now` | `GapLeftComp` | lean=[] kernel=[GapLeftComp@Form/Rows/GapLeft:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `zone-before-now` | `GapRightComp` | lean=[GapRightComp@Form/Rows/GapRight:VALUE_ERROR/ERROR, GapRightComp@Form/Rows[2]/GapRight:VALUE_ERROR/ERROR] kernel=[GapRightComp@Form/Rows/GapRight:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `zone-before-now` | `GapRightComp` | lean=[] kernel=[GapRightComp@Form/GapRight:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `zone-before-now` | `GapStampComp` | lean=[] kernel=[GapStampComp@Form/GapStamp:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `zone-before-now` | `GapTextComp` | lean=[] kernel=[GapTextComp@Form/GapText:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `zone-before-now` | `TrueOrGapComp` | lean=[TrueOrGapComp@Form/TrueOrGap:VALUE_ERROR/ERROR referenced=[Form/N, Form/TrueOrGap, Form/Z1] fillToFix=[]] kernel=[TrueOrGapComp@Form/TrueOrGap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `comparison-guards-2026-10-04/request.json` | `zone-before-now` | `call` | lean=[] kernel=[Form/GapAndFalse:berechnungsWertFehler, Form/GapLeft:berechnungsWertFehler, Form/GapRight:berechnungsWertFehler, Form/GapStamp:berechnungsWertFehler, Form/GapText:berechnungsWertFehler, Form/Rows/GapLeft:berechnungsWertFehler, Form/Rows/GapRight:berechnungsWertFehler, Form/Rows[2]/GapLeft:berechnungsWertFehler, Form/Rows[2]/GapRight:berechnungsWertFehler] |
| `comparison-guards-2026-10-04/request.json` | `zone-midnight` | `AfterGapAndFalseComp` | lean=[Form/AfterGapAndFalse=value 1] kernel=[Form/AfterGapAndFalse=cleared] |
| `comparison-guards-2026-10-04/request.json` | `zone-midnight` | `AfterGapStampComp` | lean=[Form/AfterGapStamp=value 1] kernel=[Form/AfterGapStamp=cleared] |
| `comparison-guards-2026-10-04/request.json` | `zone-midnight` | `AfterGapTextComp` | lean=[Form/AfterGapText=value 1] kernel=[Form/AfterGapText=cleared] |
| `comparison-guards-2026-10-04/request.json` | `zone-midnight` | `Form/AfterGapLeftComp` | lean=[Form/AfterGapLeft=value 1] kernel=[Form/AfterGapLeft=cleared] |
| `comparison-guards-2026-10-04/request.json` | `zone-midnight` | `Form/AfterGapRightComp` | lean=[Form/AfterGapRight=value 1] kernel=[Form/AfterGapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `zone-midnight` | `Form/GapLeftComp` | lean=[Form/GapLeft=value 1] kernel=[Form/GapLeft=cleared] |
| `comparison-guards-2026-10-04/request.json` | `zone-midnight` | `Form/Rows/AfterGapLeftComp` | lean=[Form/Rows/AfterGapLeft=value 1, Form/Rows[2]/AfterGapLeft=value 1] kernel=[Form/Rows/AfterGapLeft=cleared, Form/Rows[2]/AfterGapLeft=cleared] |
| `comparison-guards-2026-10-04/request.json` | `zone-midnight` | `Form/Rows/AfterGapRightComp` | lean=[Form/Rows/AfterGapRight=value 1, Form/Rows[2]/AfterGapRight=value 1] kernel=[Form/Rows/AfterGapRight=cleared, Form/Rows[2]/AfterGapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `zone-midnight` | `Form/Rows/GapRightComp` | lean=[Form/Rows/GapRight=value 1, Form/Rows[2]/GapRight=value 1] kernel=[Form/Rows/GapRight=cleared, Form/Rows[2]/GapRight=cleared] |
| `comparison-guards-2026-10-04/request.json` | `zone-midnight` | `GapAndFalseComp` | lean=[] kernel=[GapAndFalseComp@Form/GapAndFalse:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `zone-midnight` | `GapLeftComp` | lean=[GapLeftComp@Form/GapLeft:VALUE_ERROR/ERROR referenced=[Form/GapLeft, Form/Z1] fillToFix=[]] kernel=[GapLeftComp@Form/GapLeft:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `comparison-guards-2026-10-04/request.json` | `zone-midnight` | `GapLeftComp` | lean=[] kernel=[GapLeftComp@Form/Rows/GapLeft:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `zone-midnight` | `GapRightComp` | lean=[GapRightComp@Form/Rows/GapRight:VALUE_ERROR/ERROR, GapRightComp@Form/Rows[2]/GapRight:VALUE_ERROR/ERROR] kernel=[GapRightComp@Form/Rows/GapRight:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `zone-midnight` | `GapRightComp` | lean=[] kernel=[GapRightComp@Form/GapRight:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `zone-midnight` | `GapStampComp` | lean=[] kernel=[GapStampComp@Form/GapStamp:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `zone-midnight` | `GapTextComp` | lean=[] kernel=[GapTextComp@Form/GapText:VALUE_ERROR/ERROR] |
| `comparison-guards-2026-10-04/request.json` | `zone-midnight` | `TrueOrGapComp` | lean=[TrueOrGapComp@Form/TrueOrGap:VALUE_ERROR/ERROR referenced=[Form/N, Form/TrueOrGap, Form/Z1] fillToFix=[]] kernel=[TrueOrGapComp@Form/TrueOrGap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `comparison-guards-2026-10-04/request.json` | `zone-midnight` | `call` | lean=[] kernel=[Form/GapAndFalse:berechnungsWertFehler, Form/GapLeft:berechnungsWertFehler, Form/GapRight:berechnungsWertFehler, Form/GapStamp:berechnungsWertFehler, Form/GapText:berechnungsWertFehler, Form/Rows/GapLeft:berechnungsWertFehler, Form/Rows/GapRight:berechnungsWertFehler, Form/Rows[2]/GapLeft:berechnungsWertFehler, Form/Rows[2]/GapRight:berechnungsWertFehler] |
| `compositional-review-2026-10-03/request.json` | `after` | `FirstDependentComp` | lean=[G/FirstDependent=value 2024-03-31T03:30:00] kernel=[G/FirstDependent=cleared] |
| `compositional-review-2026-10-03/request.json` | `after` | `GapComp` | lean=[G/Gap=value 2024-03-31T03:30:00] kernel=[G/Gap=cleared] |
| `compositional-review-2026-10-03/request.json` | `after` | `GapComp` | lean=[GapComp@G/Gap:VALUE_ERROR/ERROR referenced=[G/Gap] fillToFix=[]] kernel=[GapComp@G/Gap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `compositional-review-2026-10-03/request.json` | `after` | `MaxGapComp` | lean=[G/MaxGap=value 2024-03-31T04:00:00] kernel=[G/MaxGap=cleared] |
| `compositional-review-2026-10-03/request.json` | `after` | `MaxGapComp` | lean=[MaxGapComp@G/MaxGap:VALUE_ERROR/ERROR referenced=[G/MaxGap, G/Stamp] fillToFix=[]] kernel=[MaxGapComp@G/MaxGap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `compositional-review-2026-10-03/request.json` | `after` | `MaxGapDepComp` | lean=[G/MaxGapDep=value 2024-03-31T04:00:01] kernel=[G/MaxGapDep=cleared] |
| `compositional-review-2026-10-03/request.json` | `after` | `MinGapComp` | lean=[G/MinGap=value 2024-03-31T03:30:00] kernel=[G/MinGap=cleared] |
| `compositional-review-2026-10-03/request.json` | `after` | `MinGapComp` | lean=[MinGapComp@G/MinGap:VALUE_ERROR/ERROR referenced=[G/MinGap, G/Stamp] fillToFix=[]] kernel=[MinGapComp@G/MinGap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `compositional-review-2026-10-03/request.json` | `after` | `MinGapDepComp` | lean=[G/MinGapDep=value 2024-03-31T03:30:01] kernel=[G/MinGapDep=cleared] |
| `compositional-review-2026-10-03/request.json` | `after` | `MinGapFirstComp` | lean=[G/MinGapFirst=value 2024-03-31T03:30:00] kernel=[G/MinGapFirst=cleared] |
| `compositional-review-2026-10-03/request.json` | `after` | `MinGapFirstComp` | lean=[MinGapFirstComp@G/MinGapFirst:VALUE_ERROR/ERROR referenced=[G/MinGapFirst, G/Stamp] fillToFix=[]] kernel=[MinGapFirstComp@G/MinGapFirst:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `compositional-review-2026-10-03/request.json` | `after` | `MinGapFirstDepComp` | lean=[G/MinGapFirstDep=value 2024-03-31T03:30:01] kernel=[G/MinGapFirstDep=cleared] |
| `compositional-review-2026-10-03/request.json` | `after` | `call` | lean=[] kernel=[G/Gap:berechnungsWertFehler, G/MaxGap:berechnungsWertFehler, G/MinGap:berechnungsWertFehler, G/MinGapFirst:berechnungsWertFehler] |
| `compositional-review-2026-10-03/request.json` | `after` | `gapRule` | lean=[] kernel=[gapRule@G/Stamp:VALUE_ERROR/ERROR] |
| `compositional-review-2026-10-03/request.json` | `after` | `gapThenFalse` | lean=[] kernel=[gapThenFalse@G/Stamp:VALUE_ERROR/ERROR] |
| `compositional-review-2026-10-03/request.json` | `before` | `FirstDependentComp` | lean=[G/FirstDependent=value 2024-03-31T03:30:00] kernel=[G/FirstDependent=cleared] |
| `compositional-review-2026-10-03/request.json` | `before` | `GapComp` | lean=[G/Gap=value 2024-03-31T03:30:00] kernel=[G/Gap=cleared] |
| `compositional-review-2026-10-03/request.json` | `before` | `GapComp` | lean=[GapComp@G/Gap:VALUE_ERROR/ERROR referenced=[G/Gap] fillToFix=[]] kernel=[GapComp@G/Gap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `compositional-review-2026-10-03/request.json` | `before` | `MaxGapComp` | lean=[G/MaxGap=value 2024-03-31T03:30:00] kernel=[G/MaxGap=cleared] |
| `compositional-review-2026-10-03/request.json` | `before` | `MaxGapComp` | lean=[MaxGapComp@G/MaxGap:VALUE_ERROR/ERROR referenced=[G/MaxGap, G/Stamp] fillToFix=[]] kernel=[MaxGapComp@G/MaxGap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `compositional-review-2026-10-03/request.json` | `before` | `MaxGapDepComp` | lean=[G/MaxGapDep=value 2024-03-31T03:30:01] kernel=[G/MaxGapDep=cleared] |
| `compositional-review-2026-10-03/request.json` | `before` | `MinGapComp` | lean=[G/MinGap=value 2024-03-31T01:00:00] kernel=[G/MinGap=cleared] |
| `compositional-review-2026-10-03/request.json` | `before` | `MinGapComp` | lean=[MinGapComp@G/MinGap:VALUE_ERROR/ERROR referenced=[G/MinGap, G/Stamp] fillToFix=[]] kernel=[MinGapComp@G/MinGap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `compositional-review-2026-10-03/request.json` | `before` | `MinGapDepComp` | lean=[G/MinGapDep=value 2024-03-31T01:00:01] kernel=[G/MinGapDep=cleared] |
| `compositional-review-2026-10-03/request.json` | `before` | `MinGapFirstComp` | lean=[G/MinGapFirst=value 2024-03-31T01:00:00] kernel=[G/MinGapFirst=cleared] |
| `compositional-review-2026-10-03/request.json` | `before` | `MinGapFirstComp` | lean=[MinGapFirstComp@G/MinGapFirst:VALUE_ERROR/ERROR referenced=[G/MinGapFirst, G/Stamp] fillToFix=[]] kernel=[MinGapFirstComp@G/MinGapFirst:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `compositional-review-2026-10-03/request.json` | `before` | `MinGapFirstDepComp` | lean=[G/MinGapFirstDep=value 2024-03-31T01:00:01] kernel=[G/MinGapFirstDep=cleared] |
| `compositional-review-2026-10-03/request.json` | `before` | `call` | lean=[] kernel=[G/Gap:berechnungsWertFehler, G/MaxGap:berechnungsWertFehler, G/MinGap:berechnungsWertFehler, G/MinGapFirst:berechnungsWertFehler] |
| `compositional-review-2026-10-03/request.json` | `before` | `gapRule` | lean=[gapRule@G/Stamp:VALUE_ERROR/ERROR referenced=[G/Stamp] fillToFix=[]] kernel=[gapRule@G/Stamp:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `compositional-review-2026-10-03/request.json` | `before` | `gapThenFalse` | lean=[] kernel=[gapThenFalse@G/Stamp:VALUE_ERROR/ERROR] |
| `compositional-review-2026-10-03/request.json` | `empty` | `FirstDependentComp` | lean=[G/FirstDependent=value 2024-03-31T03:30:00] kernel=[G/FirstDependent=cleared] |
| `compositional-review-2026-10-03/request.json` | `empty` | `GapComp` | lean=[G/Gap=value 2024-03-31T03:30:00] kernel=[G/Gap=cleared] |
| `compositional-review-2026-10-03/request.json` | `empty` | `GapComp` | lean=[GapComp@G/Gap:VALUE_ERROR/ERROR referenced=[G/Gap] fillToFix=[]] kernel=[GapComp@G/Gap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `compositional-review-2026-10-03/request.json` | `empty` | `MaxGapComp` | lean=[G/MaxGap=value 2024-03-31T03:30:00] kernel=[G/MaxGap=cleared] |
| `compositional-review-2026-10-03/request.json` | `empty` | `MaxGapComp` | lean=[MaxGapComp@G/MaxGap:OMISSION_ERROR/ERROR] kernel=[MaxGapComp@G/MaxGap:VALUE_ERROR/ERROR] |
| `compositional-review-2026-10-03/request.json` | `empty` | `MaxGapDepComp` | lean=[G/MaxGapDep=value 2024-03-31T03:30:01] kernel=[G/MaxGapDep=cleared] |
| `compositional-review-2026-10-03/request.json` | `empty` | `MinGapComp` | lean=[G/MinGap=value 2024-03-31T03:30:00] kernel=[G/MinGap=cleared] |
| `compositional-review-2026-10-03/request.json` | `empty` | `MinGapComp` | lean=[MinGapComp@G/MinGap:OMISSION_ERROR/ERROR] kernel=[MinGapComp@G/MinGap:VALUE_ERROR/ERROR] |
| `compositional-review-2026-10-03/request.json` | `empty` | `MinGapDepComp` | lean=[G/MinGapDep=value 2024-03-31T03:30:01] kernel=[G/MinGapDep=cleared] |
| `compositional-review-2026-10-03/request.json` | `empty` | `MinGapFirstComp` | lean=[G/MinGapFirst=value 2024-03-31T03:30:00] kernel=[G/MinGapFirst=cleared] |
| `compositional-review-2026-10-03/request.json` | `empty` | `MinGapFirstComp` | lean=[MinGapFirstComp@G/MinGapFirst:OMISSION_ERROR/ERROR] kernel=[MinGapFirstComp@G/MinGapFirst:VALUE_ERROR/ERROR] |
| `compositional-review-2026-10-03/request.json` | `empty` | `MinGapFirstDepComp` | lean=[G/MinGapFirstDep=value 2024-03-31T03:30:01] kernel=[G/MinGapFirstDep=cleared] |
| `compositional-review-2026-10-03/request.json` | `empty` | `call` | lean=[] kernel=[G/Gap:berechnungsWertFehler, G/MaxGap:berechnungsWertFehler, G/MinGap:berechnungsWertFehler, G/MinGapFirst:berechnungsWertFehler] |
| `compositional-review-2026-10-03/request.json` | `empty` | `falseThenGap` | lean=[] kernel=[falseThenGap@G/Stamp:VALUE_ERROR/ERROR] |
| `compositional-review-2026-10-03/request.json` | `empty` | `gapRule` | lean=[] kernel=[gapRule@G/Stamp:VALUE_ERROR/ERROR] |
| `compositional-review-2026-10-03/request.json` | `empty` | `gapThenFalse` | lean=[] kernel=[gapThenFalse@G/Stamp:VALUE_ERROR/ERROR] |
| `compositional-review-2026-10-03/request.json` | `malformed` | `FirstDependentComp` | lean=[G/FirstDependent=value 2024-03-31T03:30:00] kernel=[G/FirstDependent=cleared] |
| `compositional-review-2026-10-03/request.json` | `malformed` | `GapComp` | lean=[G/Gap=value 2024-03-31T03:30:00] kernel=[G/Gap=cleared] |
| `compositional-review-2026-10-03/request.json` | `malformed` | `GapComp` | lean=[GapComp@G/Gap:VALUE_ERROR/ERROR referenced=[G/Gap] fillToFix=[]] kernel=[GapComp@G/Gap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `compositional-review-2026-10-03/request.json` | `malformed` | `MaxGapComp` | lean=[] kernel=[MaxGapComp@G/MaxGap:VALUE_ERROR/ERROR] |
| `compositional-review-2026-10-03/request.json` | `malformed` | `MinGapComp` | lean=[] kernel=[MinGapComp@G/MinGap:VALUE_ERROR/ERROR] |
| `compositional-review-2026-10-03/request.json` | `malformed` | `MinGapFirstComp` | lean=[] kernel=[MinGapFirstComp@G/MinGapFirst:VALUE_ERROR/ERROR] |
| `compositional-review-2026-10-03/request.json` | `malformed` | `call` | lean=[G/Stamp:datumFormatFalsch] kernel=[G/Gap:berechnungsWertFehler, G/MinGapFirst:berechnungsWertFehler, G/Stamp:datumFormatFalsch] |
| `compositional-review-2026-10-03/request.json` | `malformed` | `gapRule` | lean=[] kernel=[gapRule@G/Stamp:VALUE_ERROR/ERROR] |
| `compositional-review-2026-10-03/request.json` | `malformed` | `gapThenFalse` | lean=[] kernel=[gapThenFalse@G/Stamp:VALUE_ERROR/ERROR] |
| `compositional-temporal-disposition-2026-10-03/request.json` | `empty` | `DateGapComp` | lean=[G/DateGap=value 2024-03-31] kernel=[] |
| `compositional-temporal-disposition-2026-10-03/request.json` | `empty` | `DependentComp` | lean=[G/Dependent=value 2024-03-31T03:30:01] kernel=[] |
| `compositional-temporal-disposition-2026-10-03/request.json` | `empty` | `GapComp` | lean=[G/Gap=value 2024-03-31T03:30:00] kernel=[] |
| `compositional-temporal-disposition-2026-10-03/request.json` | `empty` | `NestedGapComp` | lean=[G/NestedGap=value 2024-03-31T04:30:01] kernel=[] |
| `compositional-temporal-disposition-2026-10-03/request.json` | `empty` | `ShiftGapComp` | lean=[G/ShiftGap=value 2024-03-31T03:30:01] kernel=[] |
| `compositional-temporal-disposition-2026-10-03/request.json` | `empty` | `TimeGapComp` | lean=[G/TimeGap=value 03:30:00] kernel=[] |
| `compositional-temporal-disposition-2026-10-03/request.json` | `empty` | `call` | lean=[] kernel=[G/DateGap:berechnungsWertFehler, G/Gap:berechnungsWertFehler, G/NestedGap:berechnungsWertFehler, G/ShiftGap:berechnungsWertFehler, G/TimeGap:berechnungsWertFehler] |
| `compositional-temporal-disposition-2026-10-03/request.json` | `seeded` | `DateGapComp` | lean=[DateGapComp@G/DateGap:VALUE_ERROR/ERROR referenced=[G/DateGap] fillToFix=[]] kernel=[DateGapComp@G/DateGap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `compositional-temporal-disposition-2026-10-03/request.json` | `seeded` | `DateGapComp` | lean=[G/DateGap=value 2024-03-31] kernel=[G/DateGap=cleared] |
| `compositional-temporal-disposition-2026-10-03/request.json` | `seeded` | `DependentComp` | lean=[G/Dependent=value 2024-03-31T03:30:01] kernel=[G/Dependent=cleared] |
| `compositional-temporal-disposition-2026-10-03/request.json` | `seeded` | `GapComp` | lean=[G/Gap=value 2024-03-31T03:30:00] kernel=[G/Gap=cleared] |
| `compositional-temporal-disposition-2026-10-03/request.json` | `seeded` | `GapComp` | lean=[GapComp@G/Gap:VALUE_ERROR/ERROR referenced=[G/Gap] fillToFix=[]] kernel=[GapComp@G/Gap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `compositional-temporal-disposition-2026-10-03/request.json` | `seeded` | `NestedGapComp` | lean=[G/NestedGap=value 2024-03-31T04:30:01] kernel=[G/NestedGap=cleared] |
| `compositional-temporal-disposition-2026-10-03/request.json` | `seeded` | `NestedGapComp` | lean=[NestedGapComp@G/NestedGap:VALUE_ERROR/ERROR referenced=[G/NestedGap] fillToFix=[]] kernel=[NestedGapComp@G/NestedGap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `compositional-temporal-disposition-2026-10-03/request.json` | `seeded` | `ShiftGapComp` | lean=[G/ShiftGap=value 2024-03-31T03:30:01] kernel=[G/ShiftGap=cleared] |
| `compositional-temporal-disposition-2026-10-03/request.json` | `seeded` | `ShiftGapComp` | lean=[ShiftGapComp@G/ShiftGap:VALUE_ERROR/ERROR referenced=[G/ShiftGap] fillToFix=[]] kernel=[ShiftGapComp@G/ShiftGap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `compositional-temporal-disposition-2026-10-03/request.json` | `seeded` | `TimeGapComp` | lean=[G/TimeGap=value 03:30:00] kernel=[G/TimeGap=cleared] |
| `compositional-temporal-disposition-2026-10-03/request.json` | `seeded` | `TimeGapComp` | lean=[TimeGapComp@G/TimeGap:VALUE_ERROR/ERROR referenced=[G/TimeGap] fillToFix=[]] kernel=[TimeGapComp@G/TimeGap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `compositional-temporal-disposition-2026-10-03/request.json` | `seeded` | `call` | lean=[] kernel=[G/DateGap:berechnungsWertFehler, G/Gap:berechnungsWertFehler, G/NestedGap:berechnungsWertFehler, G/ShiftGap:berechnungsWertFehler, G/TimeGap:berechnungsWertFehler] |
| `date-range-interpretation-first-profiles-2026-10-24/request-ioy-mc.json` | `malformed` | `call` | lean=[Form/FF_mc:datumBereichTrennerFehlt, Form/FT_mc:datumBereichTrennerFehlt, Form/LF_dm:datumBereichTrennerFehlt, Form/LF_iso:datumBereichTrennerFehlt, Form/LF_m:datumBereichTrennerFehlt, Form/LT_dm:datumBereichTrennerFehlt, Form/LT_iso:datumBereichTrennerFehlt, Form/LT_m:datumBereichTrennerFehlt] kernel=[Form/FF_mc:datumBereichFormatFalsch, Form/FT_mc:datumBereichFormatFalsch, Form/LF_dm:datumBereichFormatFalsch, Form/LF_iso:datumBereichFormatFalsch, Form/LF_m:datumBereichFormatFalsch, Form/LT_dm:datumBereichFormatFalsch, Form/LT_iso:datumBereichFormatFalsch, Form/LT_m:datumBereichFormatFalsch] |
| `date-range-interpretation-first-profiles-2026-10-24/request-ioy-mc.json` | `ordered` | `CED_FF_mc` | lean=[Form/ED_FF_mc=cleared] kernel=[Form/ED_FF_mc=value 31] |
| `date-range-interpretation-first-profiles-2026-10-24/request-ioy-mc.json` | `ordered` | `CED_FF_mc` | lean=[] kernel=[CED_FF_mc@Form/ED_FF_mc:VALUE_ERROR/ERROR] |
| `date-range-interpretation-first-profiles-2026-10-24/request-ioy-mc.json` | `ordered` | `CED_FT_mc` | lean=[Form/ED_FT_mc=cleared] kernel=[Form/ED_FT_mc=value 31] |
| `date-range-interpretation-first-profiles-2026-10-24/request-ioy-mc.json` | `ordered` | `CED_FT_mc` | lean=[] kernel=[CED_FT_mc@Form/ED_FT_mc:VALUE_ERROR/ERROR] |
| `date-range-interpretation-first-profiles-2026-10-24/request-ioy-mc.json` | `ordered` | `CEY_FF_mc` | lean=[Form/EY_FF_mc=cleared] kernel=[Form/EY_FF_mc=value 2000] |
| `date-range-interpretation-first-profiles-2026-10-24/request-ioy-mc.json` | `ordered` | `CEY_FF_mc` | lean=[] kernel=[CEY_FF_mc@Form/EY_FF_mc:VALUE_ERROR/ERROR] |
| `date-range-interpretation-first-profiles-2026-10-24/request-ioy-mc.json` | `ordered` | `CEY_FT_mc` | lean=[Form/EY_FT_mc=cleared] kernel=[Form/EY_FT_mc=value 2000] |
| `date-range-interpretation-first-profiles-2026-10-24/request-ioy-mc.json` | `ordered` | `CEY_FT_mc` | lean=[] kernel=[CEY_FT_mc@Form/EY_FT_mc:VALUE_ERROR/ERROR] |
| `date-range-interpretation-first-profiles-2026-10-24/request-ioy-mc.json` | `ordered` | `CSM_FF_mc` | lean=[Form/SM_FF_mc=cleared] kernel=[Form/SM_FF_mc=value 3] |
| `date-range-interpretation-first-profiles-2026-10-24/request-ioy-mc.json` | `ordered` | `CSM_FF_mc` | lean=[] kernel=[CSM_FF_mc@Form/SM_FF_mc:VALUE_ERROR/ERROR] |
| `date-range-interpretation-first-profiles-2026-10-24/request-ioy-mc.json` | `ordered` | `CSM_FT_mc` | lean=[Form/SM_FT_mc=cleared] kernel=[Form/SM_FT_mc=value 3] |
| `date-range-interpretation-first-profiles-2026-10-24/request-ioy-mc.json` | `ordered` | `CSM_FT_mc` | lean=[] kernel=[CSM_FT_mc@Form/SM_FT_mc:VALUE_ERROR/ERROR] |
| `date-range-interpretation-first-profiles-2026-10-24/request-ioy-mc.json` | `ordered` | `CSY_FF_mc` | lean=[Form/SY_FF_mc=cleared] kernel=[Form/SY_FF_mc=value 2000] |
| `date-range-interpretation-first-profiles-2026-10-24/request-ioy-mc.json` | `ordered` | `CSY_FF_mc` | lean=[] kernel=[CSY_FF_mc@Form/SY_FF_mc:VALUE_ERROR/ERROR] |
| `date-range-interpretation-first-profiles-2026-10-24/request-ioy-mc.json` | `ordered` | `CSY_FT_mc` | lean=[Form/SY_FT_mc=cleared] kernel=[Form/SY_FT_mc=value 2000] |
| `date-range-interpretation-first-profiles-2026-10-24/request-ioy-mc.json` | `ordered` | `CSY_FT_mc` | lean=[] kernel=[CSY_FT_mc@Form/SY_FT_mc:VALUE_ERROR/ERROR] |
| `date-range-interpretation-first-profiles-2026-10-24/request-ioy-mc.json` | `ordered` | `call` | lean=[Form/FF_mc:datumBereichTrennerFehlt, Form/FT_mc:datumBereichTrennerFehlt] kernel=[] |
| `date-range-interpretation-first-profiles-2026-10-24/request-ioy-mc.json` | `wrapping` | `call` | lean=[Form/FF_mc:datumBereichTrennerFehlt, Form/FT_mc:datumBereichTrennerFehlt, Form/LF_dm:datumBereichNichtGueltig, Form/LF_iso:datumBereichNichtGueltig, Form/LF_m:datumBereichNichtGueltig, Form/LT_dm:datumBereichNichtGueltig, Form/LT_iso:datumBereichNichtGueltig, Form/LT_m:datumBereichNichtGueltig] kernel=[Form/FF_mc:datumBereichNichtGueltig, Form/FT_mc:datumBereichNichtGueltig, Form/LF_dm:datumBereichNichtGueltig, Form/LF_iso:datumBereichNichtGueltig, Form/LF_m:datumBereichNichtGueltig, Form/LT_dm:datumBereichNichtGueltig, Form/LT_iso:datumBereichNichtGueltig, Form/LT_m:datumBereichNichtGueltig] |
| `date-range-list-iso-arity-and-fragment-suffix/req.json` | `mmempty-2nd` | `ETgtComp` | lean=[] kernel=[Dr/ETgt=value 0203] |
| `date-range-list-iso-arity-and-fragment-suffix/req.json` | `mmempty-2nd` | `call` | lean=[Dr/E2:datumBereichTrennerFehlt, Dr/E3:datumBereichTrennerFehlt] kernel=[] |
| `date-range-list-iso-arity-and-fragment-suffix/req.json` | `mmempty-2nd-malformed` | `call` | lean=[Dr/E2:datumBereichTrennerFehlt, Dr/E3:datumBereichTrennerFehlt] kernel=[Dr/E2:datumBereichFormatFalsch] |
| `date-range-list-iso-arity-and-fragment-suffix/req.json` | `mmempty-2nd-then-malformed` | `ETgtComp` | lean=[] kernel=[Dr/ETgt=value 0203] |
| `date-range-list-iso-arity-and-fragment-suffix/req.json` | `mmempty-2nd-then-malformed` | `call` | lean=[Dr/E2:datumBereichTrennerFehlt, Dr/E3:datumBereichTrennerFehlt] kernel=[Dr/E3:datumBereichFormatFalsch] |
| `datetime-constant-zone-split/request.json` | `two-rows` | `GapComp` | lean=[Probe/Rows/Gap=value 2024-03-31T03:30:00, Probe/Rows[2]/Gap=value 2024-03-31T03:30:00] kernel=[] |
| `datetime-constant-zone-split/request.json` | `two-rows` | `call` | lean=[] kernel=[Probe/Rows/Gap:berechnungsWertFehler, Probe/Rows[2]/Gap:berechnungsWertFehler] |
| `datetime-errored-target-2026-10-02/request.json` | `e01-day-past-ceiling` | `DTAComp` | lean=[Mix/DTA=errored +10000-01-02T00:00:00] kernel=[Mix/DTA=errored 10000-01-02T00:00:00] |
| `datetime-errored-target-2026-10-02/request.json` | `e01-day-past-ceiling` | `DTCComp` | lean=[Mix/DTC=errored +10000-01-01T00:00:00] kernel=[Mix/DTC=errored 10000-01-01T00:00:00] |
| `datetime-errored-target-2026-10-02/request.json` | `e02-hour-past-ceiling` | `DTBComp` | lean=[Mix/DTB=errored +10000-01-01T01:00:00] kernel=[Mix/DTB=errored 10000-01-01T01:00:00] |
| `datetime-errored-target-2026-10-02/request.json` | `e02-hour-past-ceiling` | `DTCComp` | lean=[Mix/DTC=errored +10000-01-01T23:00:00] kernel=[Mix/DTC=errored 10000-01-01T23:00:00] |
| `datetime-join-2026-10-02/request-transitions.json` | `d07-fall-back-elapsed` | `HComp` | lean=[Mix/H=value 1] kernel=[Mix/H=value 2] |
| `datetime-join-2026-10-02/request-transitions.json` | `d08-fall-back-calendar` | `DTBComp` | lean=[Mix/DTB=value 2024-10-27T03:30:00] kernel=[Mix/DTB=value 2024-10-27T04:30:00] |
| `datetime-join-2026-10-02/request-transitions.json` | `d08-fall-back-calendar` | `HComp` | lean=[Mix/H=value 26] kernel=[Mix/H=value 27] |
| `datetime-join-2026-10-02/request-transitions.json` | `d10-fall-back-first-occurrence` | `HComp` | lean=[Mix/H=value 2] kernel=[Mix/H=value 3] |
| `datetime-join-2026-10-02/request-transitions.json` | `d11-fall-back-document-text` | `DTBComp` | lean=[Mix/DTB=value 2024-10-27T03:30:00] kernel=[Mix/DTB=value 2024-10-27T04:30:00] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-early` | `CountComp` | lean=[CountComp@Form/Count:OMISSION_ERROR/ERROR] kernel=[CountComp@Form/Count:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-early` | `CountComp` | lean=[Form/Count=value 51] kernel=[Form/Count=cleared] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-early` | `Fill0Comp` | lean=[Fill0Comp@Form/Fill0:OMISSION_ERROR/ERROR] kernel=[Fill0Comp@Form/Fill0:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-early` | `Fill0Comp` | lean=[Form/Fill0=value 1] kernel=[Form/Fill0=cleared] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-early` | `Fill4Comp` | lean=[] kernel=[Fill4Comp@Form/Fill4:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-early` | `Fill6Comp` | lean=[] kernel=[Fill6Comp@Form/Fill6:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-early` | `ResetComp` | lean=[Form/Reset=value 255] kernel=[Form/Reset=cleared] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-early` | `ResetComp` | lean=[ResetComp@Form/Reset:OMISSION_ERROR/ERROR] kernel=[ResetComp@Form/Reset:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-early` | `RowSumComp` | lean=[Form/Outer/RowSum=value 250, Form/Outer[2]/RowSum=value 5] kernel=[Form/Outer/RowSum=value 250, Form/Outer[2]/RowSum=cleared] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-early` | `RowSumComp` | lean=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer[2]/RowSum:OMISSION_ERROR/ERROR] kernel=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer/RowSum:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-early` | `RuleFill0` | lean=[FILL0@Form/Error:OMISSION_ERROR/ERROR] kernel=[FILL0@Form/Error:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-early` | `RuleFill4` | lean=[] kernel=[FILL4@Form/Error:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-early` | `RuleFill6` | lean=[] kernel=[FILL6@Form/Error:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-early` | `SumComp` | lean=[Form/Sum=value 255] kernel=[Form/Sum=cleared] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-early` | `SumComp` | lean=[SumComp@Form/Sum:OMISSION_ERROR/ERROR] kernel=[SumComp@Form/Sum:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-early` | `call` | lean=[] kernel=[Form/Count:berechnungsWertFehler, Form/Fill0:berechnungsWertFehler, Form/Fill4:berechnungsWertFehler, Form/Fill6:berechnungsWertFehler, Form/Outer[2]/RowSum:berechnungsWertFehler, Form/Reset:berechnungsWertFehler, Form/Sum:berechnungsWertFehler] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-late` | `CountComp` | lean=[CountComp@Form/Count:OMISSION_ERROR/ERROR] kernel=[CountComp@Form/Count:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-late` | `CountComp` | lean=[Form/Count=value 1] kernel=[Form/Count=cleared] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-late` | `Fill1Comp` | lean=[] kernel=[Fill1Comp@Form/Fill1:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-late` | `Fill2Comp` | lean=[Fill2Comp@Form/Fill2:OMISSION_ERROR/ERROR] kernel=[Fill2Comp@Form/Fill2:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-late` | `Fill2Comp` | lean=[Form/Fill2=value 1] kernel=[Form/Fill2=cleared] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-late` | `Fill3Comp` | lean=[] kernel=[Fill3Comp@Form/Fill3:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-late` | `Fill5Comp` | lean=[] kernel=[Fill5Comp@Form/Fill5:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-late` | `Fill6Comp` | lean=[Fill6Comp@Form/Fill6:OMISSION_ERROR/ERROR] kernel=[Fill6Comp@Form/Fill6:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-late` | `Fill6Comp` | lean=[Form/Fill6=value 1] kernel=[Form/Fill6=cleared] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-late` | `FirstComp` | lean=[FirstComp@Form/First:OMISSION_ERROR/ERROR] kernel=[FirstComp@Form/First:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-late` | `FirstComp` | lean=[Form/First=value 5] kernel=[Form/First=cleared] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-late` | `ResetComp` | lean=[Form/Reset=value 5] kernel=[Form/Reset=cleared] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-late` | `ResetComp` | lean=[ResetComp@Form/Reset:OMISSION_ERROR/ERROR] kernel=[ResetComp@Form/Reset:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-late` | `RowSumComp` | lean=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=value 5] kernel=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=cleared] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-late` | `RowSumComp` | lean=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer[2]/RowSum:OMISSION_ERROR/ERROR] kernel=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer/RowSum:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-late` | `RuleFill1` | lean=[] kernel=[FILL1@Form/Error:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-late` | `RuleFill2` | lean=[FILL2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FILL2@Form/Error:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-late` | `RuleFill3` | lean=[] kernel=[FILL3@Form/Error:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-late` | `RuleFill5` | lean=[] kernel=[FILL5@Form/Error:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-late` | `RuleFill6` | lean=[FILL6@Form/Error:OMISSION_ERROR/ERROR] kernel=[FILL6@Form/Error:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-late` | `SumComp` | lean=[Form/Sum=value 5] kernel=[Form/Sum=cleared] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-late` | `SumComp` | lean=[SumComp@Form/Sum:OMISSION_ERROR/ERROR] kernel=[SumComp@Form/Sum:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `dense-late` | `call` | lean=[] kernel=[Form/Count:berechnungsWertFehler, Form/Fill1:berechnungsWertFehler, Form/Fill2:berechnungsWertFehler, Form/Fill3:berechnungsWertFehler, Form/Fill5:berechnungsWertFehler, Form/Fill6:berechnungsWertFehler, Form/First:berechnungsWertFehler, Form/Outer[2]/RowSum:berechnungsWertFehler, Form/Reset:berechnungsWertFehler, Form/Sum:berechnungsWertFehler] |
| `field-fill-traversal-2026-10-10/request.json` | `small` | `Fill0Comp` | lean=[] kernel=[Fill0Comp@Form/Fill0:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `small` | `Fill4Comp` | lean=[Fill4Comp@Form/Fill4:OMISSION_ERROR/ERROR] kernel=[Fill4Comp@Form/Fill4:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `small` | `Fill4Comp` | lean=[Form/Fill4=value 1] kernel=[Form/Fill4=cleared] |
| `field-fill-traversal-2026-10-10/request.json` | `small` | `Fill6Comp` | lean=[Fill6Comp@Form/Fill6:OMISSION_ERROR/ERROR] kernel=[Fill6Comp@Form/Fill6:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `small` | `Fill6Comp` | lean=[Form/Fill6=value 1] kernel=[Form/Fill6=cleared] |
| `field-fill-traversal-2026-10-10/request.json` | `small` | `RuleFill0` | lean=[] kernel=[FILL0@Form/Error:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `small` | `RuleFill4` | lean=[FILL4@Form/Error:OMISSION_ERROR/ERROR] kernel=[FILL4@Form/Error:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `small` | `RuleFill6` | lean=[FILL6@Form/Error:OMISSION_ERROR/ERROR] kernel=[FILL6@Form/Error:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `small` | `call` | lean=[] kernel=[Form/Fill0:berechnungsWertFehler, Form/Fill4:berechnungsWertFehler, Form/Fill6:berechnungsWertFehler] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-blank` | `CountComp` | lean=[CountComp@Form/Count:OMISSION_ERROR/ERROR] kernel=[CountComp@Form/Count:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-blank` | `CountComp` | lean=[Form/Count=value 1] kernel=[Form/Count=cleared] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-blank` | `Fill1Comp` | lean=[] kernel=[Fill1Comp@Form/Fill1:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-blank` | `Fill2Comp` | lean=[Fill2Comp@Form/Fill2:OMISSION_ERROR/ERROR] kernel=[Fill2Comp@Form/Fill2:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-blank` | `Fill2Comp` | lean=[Form/Fill2=value 1] kernel=[Form/Fill2=cleared] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-blank` | `Fill3Comp` | lean=[] kernel=[Fill3Comp@Form/Fill3:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-blank` | `Fill5Comp` | lean=[] kernel=[Fill5Comp@Form/Fill5:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-blank` | `Fill6Comp` | lean=[Fill6Comp@Form/Fill6:OMISSION_ERROR/ERROR] kernel=[Fill6Comp@Form/Fill6:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-blank` | `Fill6Comp` | lean=[Form/Fill6=value 1] kernel=[Form/Fill6=cleared] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-blank` | `FirstComp` | lean=[FirstComp@Form/First:OMISSION_ERROR/ERROR] kernel=[FirstComp@Form/First:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-blank` | `FirstComp` | lean=[Form/First=value 5] kernel=[Form/First=cleared] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-blank` | `ResetComp` | lean=[Form/Reset=value 5] kernel=[Form/Reset=cleared] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-blank` | `ResetComp` | lean=[ResetComp@Form/Reset:OMISSION_ERROR/ERROR] kernel=[ResetComp@Form/Reset:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-blank` | `RowSumComp` | lean=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=value 5] kernel=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=cleared] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-blank` | `RowSumComp` | lean=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer[2]/RowSum:OMISSION_ERROR/ERROR] kernel=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer/RowSum:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-blank` | `RuleFill1` | lean=[] kernel=[FILL1@Form/Error:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-blank` | `RuleFill2` | lean=[FILL2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FILL2@Form/Error:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-blank` | `RuleFill3` | lean=[] kernel=[FILL3@Form/Error:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-blank` | `RuleFill5` | lean=[] kernel=[FILL5@Form/Error:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-blank` | `RuleFill6` | lean=[FILL6@Form/Error:OMISSION_ERROR/ERROR] kernel=[FILL6@Form/Error:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-blank` | `SumComp` | lean=[Form/Sum=value 5] kernel=[Form/Sum=cleared] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-blank` | `SumComp` | lean=[SumComp@Form/Sum:OMISSION_ERROR/ERROR] kernel=[SumComp@Form/Sum:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-blank` | `call` | lean=[] kernel=[Form/Count:berechnungsWertFehler, Form/Fill1:berechnungsWertFehler, Form/Fill2:berechnungsWertFehler, Form/Fill3:berechnungsWertFehler, Form/Fill5:berechnungsWertFehler, Form/Fill6:berechnungsWertFehler, Form/First:berechnungsWertFehler, Form/Outer[2]/RowSum:berechnungsWertFehler, Form/Reset:berechnungsWertFehler, Form/Sum:berechnungsWertFehler] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-late` | `Fill1Comp` | lean=[] kernel=[Fill1Comp@Form/Fill1:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-late` | `Fill3Comp` | lean=[] kernel=[Fill3Comp@Form/Fill3:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-late` | `Fill5Comp` | lean=[] kernel=[Fill5Comp@Form/Fill5:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-late` | `FirstComp` | lean=[FirstComp@Form/First:OMISSION_ERROR/ERROR] kernel=[FirstComp@Form/First:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-late` | `FirstComp` | lean=[Form/First=value 5] kernel=[Form/First=cleared] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-late` | `RowSumComp` | lean=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=value 5] kernel=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=cleared] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-late` | `RowSumComp` | lean=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer[2]/RowSum:OMISSION_ERROR/ERROR] kernel=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer/RowSum:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-late` | `RuleFill1` | lean=[] kernel=[FILL1@Form/Error:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-late` | `RuleFill3` | lean=[] kernel=[FILL3@Form/Error:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-late` | `RuleFill5` | lean=[] kernel=[FILL5@Form/Error:VALUE_ERROR/ERROR] |
| `field-fill-traversal-2026-10-10/request.json` | `sparse-late` | `call` | lean=[] kernel=[Form/Fill1:berechnungsWertFehler, Form/Fill3:berechnungsWertFehler, Form/Fill5:berechnungsWertFehler, Form/First:berechnungsWertFehler, Form/Outer[2]/RowSum:berechnungsWertFehler] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-early` | `CountComp` | lean=[Form/Count=value 51] kernel=[] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-early` | `FirstB2` | lean=[FIRSTB2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTB2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-early` | `FirstN2` | lean=[FIRSTN2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTN2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-early` | `FirstR2` | lean=[FIRSTR2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTR2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-early` | `FirstS2` | lean=[FIRSTS2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTS2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-early` | `FirstT2` | lean=[FIRSTT2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTT2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-early` | `OutB2Comp` | lean=[Form/OutB2=value 1] kernel=[Form/OutB2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-early` | `OutB2Comp` | lean=[OutB2Comp@Form/OutB2:OMISSION_ERROR/ERROR] kernel=[OutB2Comp@Form/OutB2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-early` | `OutN2Comp` | lean=[Form/OutN2=value 1] kernel=[Form/OutN2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-early` | `OutN2Comp` | lean=[OutN2Comp@Form/OutN2:OMISSION_ERROR/ERROR] kernel=[OutN2Comp@Form/OutN2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-early` | `OutR2Comp` | lean=[Form/OutR2=value 1] kernel=[Form/OutR2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-early` | `OutR2Comp` | lean=[OutR2Comp@Form/OutR2:OMISSION_ERROR/ERROR] kernel=[OutR2Comp@Form/OutR2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-early` | `OutS2Comp` | lean=[Form/OutS2=value 1] kernel=[Form/OutS2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-early` | `OutS2Comp` | lean=[OutS2Comp@Form/OutS2:OMISSION_ERROR/ERROR] kernel=[OutS2Comp@Form/OutS2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-early` | `OutT2Comp` | lean=[Form/OutT2=value 1] kernel=[Form/OutT2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-early` | `OutT2Comp` | lean=[OutT2Comp@Form/OutT2:OMISSION_ERROR/ERROR] kernel=[OutT2Comp@Form/OutT2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-early` | `ResetComp` | lean=[Form/Reset=value 255] kernel=[] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-early` | `RowSumComp` | lean=[Form/Outer/RowSum=value 250, Form/Outer[2]/RowSum=value 5] kernel=[Form/Outer/RowSum=value 250] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-early` | `SumComp` | lean=[Form/Sum=value 255] kernel=[] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-early` | `call` | lean=[] kernel=[Form/Count:berechnungsWertFehler, Form/OutB2:berechnungsWertFehler, Form/OutN2:berechnungsWertFehler, Form/OutR2:berechnungsWertFehler, Form/OutS2:berechnungsWertFehler, Form/OutT2:berechnungsWertFehler, Form/Outer[2]/RowSum:berechnungsWertFehler, Form/Reset:berechnungsWertFehler, Form/Sum:berechnungsWertFehler] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `CountComp` | lean=[Form/Count=value 1] kernel=[] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `FirstB0` | lean=[FIRSTB0@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTB0@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `FirstB2` | lean=[FIRSTB2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTB2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `FirstComp` | lean=[Form/First=value 5] kernel=[] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `FirstN0` | lean=[FIRSTN0@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTN0@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `FirstN2` | lean=[FIRSTN2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTN2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `FirstR0` | lean=[FIRSTR0@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTR0@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `FirstR2` | lean=[FIRSTR2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTR2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `FirstS0` | lean=[FIRSTS0@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTS0@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `FirstS2` | lean=[FIRSTS2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTS2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `FirstT0` | lean=[FIRSTT0@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTT0@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `FirstT2` | lean=[FIRSTT2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTT2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `OutB0Comp` | lean=[Form/OutB0=value 1] kernel=[Form/OutB0=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `OutB0Comp` | lean=[OutB0Comp@Form/OutB0:OMISSION_ERROR/ERROR] kernel=[OutB0Comp@Form/OutB0:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `OutB2Comp` | lean=[Form/OutB2=value 1] kernel=[Form/OutB2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `OutB2Comp` | lean=[OutB2Comp@Form/OutB2:OMISSION_ERROR/ERROR] kernel=[OutB2Comp@Form/OutB2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `OutN0Comp` | lean=[Form/OutN0=value 1] kernel=[Form/OutN0=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `OutN0Comp` | lean=[OutN0Comp@Form/OutN0:OMISSION_ERROR/ERROR] kernel=[OutN0Comp@Form/OutN0:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `OutN2Comp` | lean=[Form/OutN2=value 1] kernel=[Form/OutN2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `OutN2Comp` | lean=[OutN2Comp@Form/OutN2:OMISSION_ERROR/ERROR] kernel=[OutN2Comp@Form/OutN2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `OutR0Comp` | lean=[Form/OutR0=value 1] kernel=[Form/OutR0=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `OutR0Comp` | lean=[OutR0Comp@Form/OutR0:OMISSION_ERROR/ERROR] kernel=[OutR0Comp@Form/OutR0:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `OutR2Comp` | lean=[Form/OutR2=value 1] kernel=[Form/OutR2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `OutR2Comp` | lean=[OutR2Comp@Form/OutR2:OMISSION_ERROR/ERROR] kernel=[OutR2Comp@Form/OutR2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `OutS0Comp` | lean=[Form/OutS0=value 1] kernel=[Form/OutS0=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `OutS0Comp` | lean=[OutS0Comp@Form/OutS0:OMISSION_ERROR/ERROR] kernel=[OutS0Comp@Form/OutS0:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `OutS2Comp` | lean=[Form/OutS2=value 1] kernel=[Form/OutS2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `OutS2Comp` | lean=[OutS2Comp@Form/OutS2:OMISSION_ERROR/ERROR] kernel=[OutS2Comp@Form/OutS2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `OutT0Comp` | lean=[Form/OutT0=value 1] kernel=[Form/OutT0=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `OutT0Comp` | lean=[OutT0Comp@Form/OutT0:OMISSION_ERROR/ERROR] kernel=[OutT0Comp@Form/OutT0:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `OutT2Comp` | lean=[Form/OutT2=value 1] kernel=[Form/OutT2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `OutT2Comp` | lean=[OutT2Comp@Form/OutT2:OMISSION_ERROR/ERROR] kernel=[OutT2Comp@Form/OutT2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `ResetComp` | lean=[Form/Reset=value 5] kernel=[] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `RowSumComp` | lean=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=value 5] kernel=[Form/Outer/RowSum=value 0] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `SumComp` | lean=[Form/Sum=value 5] kernel=[] |
| `first-filled-traversal-2026-10-10/request.json` | `dense-late` | `call` | lean=[] kernel=[Form/Count:berechnungsWertFehler, Form/First:berechnungsWertFehler, Form/OutB0:berechnungsWertFehler, Form/OutB2:berechnungsWertFehler, Form/OutN0:berechnungsWertFehler, Form/OutN2:berechnungsWertFehler, Form/OutR0:berechnungsWertFehler, Form/OutR2:berechnungsWertFehler, Form/OutS0:berechnungsWertFehler, Form/OutS2:berechnungsWertFehler, Form/OutT0:berechnungsWertFehler, Form/OutT2:berechnungsWertFehler, Form/Outer[2]/RowSum:berechnungsWertFehler, Form/Reset:berechnungsWertFehler, Form/Sum:berechnungsWertFehler] |
| `first-filled-traversal-2026-10-10/request.json` | `invalid-first` | `FirstB2` | lean=[] kernel=[FIRSTB2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `invalid-first` | `FirstN2` | lean=[] kernel=[FIRSTN2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `invalid-first` | `FirstR2` | lean=[] kernel=[FIRSTR2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `invalid-first` | `FirstS2` | lean=[] kernel=[FIRSTS2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `invalid-first` | `FirstT2` | lean=[] kernel=[FIRSTT2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `invalid-first` | `OutB2Comp` | lean=[] kernel=[OutB2Comp@Form/OutB2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `invalid-first` | `OutN2Comp` | lean=[] kernel=[OutN2Comp@Form/OutN2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `invalid-first` | `OutR2Comp` | lean=[] kernel=[OutR2Comp@Form/OutR2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `invalid-first` | `OutS2Comp` | lean=[] kernel=[OutS2Comp@Form/OutS2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `invalid-first` | `OutT2Comp` | lean=[] kernel=[OutT2Comp@Form/OutT2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `invalid-first` | `RowSumComp` | lean=[Form/Outer[2]/RowSum=value 5] kernel=[] |
| `first-filled-traversal-2026-10-10/request.json` | `invalid-first` | `call` | lean=[Form/Outer/Inner/Flag:feldJaNeinFalsch, Form/Outer/Inner/Moment:datumFormatFalsch, Form/Outer/Inner/Range:datumBereichTrennerFehlt, Form/Outer/Inner/Text:stringZuLang, Form/Outer/Inner/V:zahlHatUngueltigeZeichen] kernel=[Form/OutB2:berechnungsWertFehler, Form/OutN2:berechnungsWertFehler, Form/OutR2:berechnungsWertFehler, Form/OutS2:berechnungsWertFehler, Form/OutT2:berechnungsWertFehler, Form/Outer/Inner/Flag:feldJaNeinFalsch, Form/Outer/Inner/Moment:datumFormatFalsch, Form/Outer/Inner/Range:datumBereichTrennerFehlt, Form/Outer/Inner/Text:stringZuLang, Form/Outer/Inner/V:zahlHatUngueltigeZeichen, Form/Outer[2]/RowSum:berechnungsWertFehler] |
| `first-filled-traversal-2026-10-10/request.json` | `large-early` | `FirstB2` | lean=[FIRSTB2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTB2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-early` | `FirstN2` | lean=[FIRSTN2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTN2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-early` | `FirstR2` | lean=[FIRSTR2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTR2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-early` | `FirstS2` | lean=[FIRSTS2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTS2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-early` | `FirstT2` | lean=[FIRSTT2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTT2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-early` | `OutB2Comp` | lean=[Form/OutB2=value 1] kernel=[Form/OutB2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `large-early` | `OutB2Comp` | lean=[OutB2Comp@Form/OutB2:OMISSION_ERROR/ERROR] kernel=[OutB2Comp@Form/OutB2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-early` | `OutN2Comp` | lean=[Form/OutN2=value 1] kernel=[Form/OutN2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `large-early` | `OutN2Comp` | lean=[OutN2Comp@Form/OutN2:OMISSION_ERROR/ERROR] kernel=[OutN2Comp@Form/OutN2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-early` | `OutR2Comp` | lean=[Form/OutR2=value 1] kernel=[Form/OutR2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `large-early` | `OutR2Comp` | lean=[OutR2Comp@Form/OutR2:OMISSION_ERROR/ERROR] kernel=[OutR2Comp@Form/OutR2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-early` | `OutS2Comp` | lean=[Form/OutS2=value 1] kernel=[Form/OutS2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `large-early` | `OutS2Comp` | lean=[OutS2Comp@Form/OutS2:OMISSION_ERROR/ERROR] kernel=[OutS2Comp@Form/OutS2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-early` | `OutT2Comp` | lean=[Form/OutT2=value 1] kernel=[Form/OutT2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `large-early` | `OutT2Comp` | lean=[OutT2Comp@Form/OutT2:OMISSION_ERROR/ERROR] kernel=[OutT2Comp@Form/OutT2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-early` | `RowSumComp` | lean=[Form/Outer/RowSum=value 255, Form/Outer[2]/RowSum=value 5] kernel=[Form/Outer/RowSum=value 255] |
| `first-filled-traversal-2026-10-10/request.json` | `large-early` | `call` | lean=[] kernel=[Form/OutB2:berechnungsWertFehler, Form/OutN2:berechnungsWertFehler, Form/OutR2:berechnungsWertFehler, Form/OutS2:berechnungsWertFehler, Form/OutT2:berechnungsWertFehler, Form/Outer[2]/RowSum:berechnungsWertFehler] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `FirstB0` | lean=[FIRSTB0@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTB0@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `FirstB2` | lean=[FIRSTB2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTB2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `FirstComp` | lean=[Form/First=value 5] kernel=[] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `FirstN0` | lean=[FIRSTN0@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTN0@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `FirstN2` | lean=[FIRSTN2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTN2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `FirstR0` | lean=[FIRSTR0@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTR0@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `FirstR2` | lean=[FIRSTR2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTR2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `FirstS0` | lean=[FIRSTS0@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTS0@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `FirstS2` | lean=[FIRSTS2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTS2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `FirstT0` | lean=[FIRSTT0@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTT0@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `FirstT2` | lean=[FIRSTT2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTT2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `OutB0Comp` | lean=[Form/OutB0=value 1] kernel=[Form/OutB0=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `OutB0Comp` | lean=[OutB0Comp@Form/OutB0:OMISSION_ERROR/ERROR] kernel=[OutB0Comp@Form/OutB0:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `OutB2Comp` | lean=[Form/OutB2=value 1] kernel=[Form/OutB2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `OutB2Comp` | lean=[OutB2Comp@Form/OutB2:OMISSION_ERROR/ERROR] kernel=[OutB2Comp@Form/OutB2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `OutN0Comp` | lean=[Form/OutN0=value 1] kernel=[Form/OutN0=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `OutN0Comp` | lean=[OutN0Comp@Form/OutN0:OMISSION_ERROR/ERROR] kernel=[OutN0Comp@Form/OutN0:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `OutN2Comp` | lean=[Form/OutN2=value 1] kernel=[Form/OutN2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `OutN2Comp` | lean=[OutN2Comp@Form/OutN2:OMISSION_ERROR/ERROR] kernel=[OutN2Comp@Form/OutN2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `OutR0Comp` | lean=[Form/OutR0=value 1] kernel=[Form/OutR0=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `OutR0Comp` | lean=[OutR0Comp@Form/OutR0:OMISSION_ERROR/ERROR] kernel=[OutR0Comp@Form/OutR0:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `OutR2Comp` | lean=[Form/OutR2=value 1] kernel=[Form/OutR2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `OutR2Comp` | lean=[OutR2Comp@Form/OutR2:OMISSION_ERROR/ERROR] kernel=[OutR2Comp@Form/OutR2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `OutS0Comp` | lean=[Form/OutS0=value 1] kernel=[Form/OutS0=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `OutS0Comp` | lean=[OutS0Comp@Form/OutS0:OMISSION_ERROR/ERROR] kernel=[OutS0Comp@Form/OutS0:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `OutS2Comp` | lean=[Form/OutS2=value 1] kernel=[Form/OutS2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `OutS2Comp` | lean=[OutS2Comp@Form/OutS2:OMISSION_ERROR/ERROR] kernel=[OutS2Comp@Form/OutS2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `OutT0Comp` | lean=[Form/OutT0=value 1] kernel=[Form/OutT0=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `OutT0Comp` | lean=[OutT0Comp@Form/OutT0:OMISSION_ERROR/ERROR] kernel=[OutT0Comp@Form/OutT0:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `OutT2Comp` | lean=[Form/OutT2=value 1] kernel=[Form/OutT2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `OutT2Comp` | lean=[OutT2Comp@Form/OutT2:OMISSION_ERROR/ERROR] kernel=[OutT2Comp@Form/OutT2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `RowSumComp` | lean=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=value 5] kernel=[Form/Outer/RowSum=value 0] |
| `first-filled-traversal-2026-10-10/request.json` | `large-late` | `call` | lean=[] kernel=[Form/First:berechnungsWertFehler, Form/OutB0:berechnungsWertFehler, Form/OutB2:berechnungsWertFehler, Form/OutN0:berechnungsWertFehler, Form/OutN2:berechnungsWertFehler, Form/OutR0:berechnungsWertFehler, Form/OutR2:berechnungsWertFehler, Form/OutS0:berechnungsWertFehler, Form/OutS2:berechnungsWertFehler, Form/OutT0:berechnungsWertFehler, Form/OutT2:berechnungsWertFehler, Form/Outer[2]/RowSum:berechnungsWertFehler] |
| `first-filled-traversal-2026-10-10/request.json` | `small` | `CountComp` | lean=[Form/Count=value 3] kernel=[] |
| `first-filled-traversal-2026-10-10/request.json` | `small` | `FirstB2` | lean=[FIRSTB2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTB2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `small` | `FirstN2` | lean=[FIRSTN2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTN2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `small` | `FirstR2` | lean=[FIRSTR2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTR2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `small` | `FirstS2` | lean=[FIRSTS2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTS2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `small` | `FirstT2` | lean=[FIRSTT2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTT2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `small` | `OutB2Comp` | lean=[Form/OutB2=value 1] kernel=[Form/OutB2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `small` | `OutB2Comp` | lean=[OutB2Comp@Form/OutB2:OMISSION_ERROR/ERROR] kernel=[OutB2Comp@Form/OutB2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `small` | `OutN2Comp` | lean=[Form/OutN2=value 1] kernel=[Form/OutN2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `small` | `OutN2Comp` | lean=[OutN2Comp@Form/OutN2:OMISSION_ERROR/ERROR] kernel=[OutN2Comp@Form/OutN2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `small` | `OutR2Comp` | lean=[Form/OutR2=value 1] kernel=[Form/OutR2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `small` | `OutR2Comp` | lean=[OutR2Comp@Form/OutR2:OMISSION_ERROR/ERROR] kernel=[OutR2Comp@Form/OutR2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `small` | `OutS2Comp` | lean=[Form/OutS2=value 1] kernel=[Form/OutS2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `small` | `OutS2Comp` | lean=[OutS2Comp@Form/OutS2:OMISSION_ERROR/ERROR] kernel=[OutS2Comp@Form/OutS2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `small` | `OutT2Comp` | lean=[Form/OutT2=value 1] kernel=[Form/OutT2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `small` | `OutT2Comp` | lean=[OutT2Comp@Form/OutT2:OMISSION_ERROR/ERROR] kernel=[OutT2Comp@Form/OutT2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `small` | `ResetComp` | lean=[Form/Reset=value 15] kernel=[] |
| `first-filled-traversal-2026-10-10/request.json` | `small` | `RowSumComp` | lean=[Form/Outer/RowSum=value 10, Form/Outer[2]/RowSum=value 5] kernel=[Form/Outer/RowSum=value 10] |
| `first-filled-traversal-2026-10-10/request.json` | `small` | `SumComp` | lean=[Form/Sum=value 15] kernel=[] |
| `first-filled-traversal-2026-10-10/request.json` | `small` | `call` | lean=[] kernel=[Form/Count:berechnungsWertFehler, Form/OutB2:berechnungsWertFehler, Form/OutN2:berechnungsWertFehler, Form/OutR2:berechnungsWertFehler, Form/OutS2:berechnungsWertFehler, Form/OutT2:berechnungsWertFehler, Form/Outer[2]/RowSum:berechnungsWertFehler, Form/Reset:berechnungsWertFehler, Form/Sum:berechnungsWertFehler] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `CountComp` | lean=[Form/Count=value 2] kernel=[] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `FirstB0` | lean=[FIRSTB0@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTB0@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `FirstB2` | lean=[FIRSTB2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTB2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `FirstComp` | lean=[Form/First=value 5] kernel=[] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `FirstN0` | lean=[FIRSTN0@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTN0@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `FirstN2` | lean=[FIRSTN2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTN2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `FirstR0` | lean=[FIRSTR0@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTR0@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `FirstR2` | lean=[FIRSTR2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTR2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `FirstS0` | lean=[FIRSTS0@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTS0@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `FirstS2` | lean=[FIRSTS2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTS2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `FirstT0` | lean=[FIRSTT0@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTT0@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `FirstT2` | lean=[FIRSTT2@Form/Error:OMISSION_ERROR/ERROR] kernel=[FIRSTT2@Form/Error:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `OutB0Comp` | lean=[Form/OutB0=value 1] kernel=[Form/OutB0=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `OutB0Comp` | lean=[OutB0Comp@Form/OutB0:OMISSION_ERROR/ERROR] kernel=[OutB0Comp@Form/OutB0:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `OutB2Comp` | lean=[Form/OutB2=value 1] kernel=[Form/OutB2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `OutB2Comp` | lean=[OutB2Comp@Form/OutB2:OMISSION_ERROR/ERROR] kernel=[OutB2Comp@Form/OutB2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `OutN0Comp` | lean=[Form/OutN0=value 1] kernel=[Form/OutN0=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `OutN0Comp` | lean=[OutN0Comp@Form/OutN0:OMISSION_ERROR/ERROR] kernel=[OutN0Comp@Form/OutN0:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `OutN2Comp` | lean=[Form/OutN2=value 1] kernel=[Form/OutN2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `OutN2Comp` | lean=[OutN2Comp@Form/OutN2:OMISSION_ERROR/ERROR] kernel=[OutN2Comp@Form/OutN2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `OutR0Comp` | lean=[Form/OutR0=value 1] kernel=[Form/OutR0=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `OutR0Comp` | lean=[OutR0Comp@Form/OutR0:OMISSION_ERROR/ERROR] kernel=[OutR0Comp@Form/OutR0:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `OutR2Comp` | lean=[Form/OutR2=value 1] kernel=[Form/OutR2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `OutR2Comp` | lean=[OutR2Comp@Form/OutR2:OMISSION_ERROR/ERROR] kernel=[OutR2Comp@Form/OutR2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `OutS0Comp` | lean=[Form/OutS0=value 1] kernel=[Form/OutS0=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `OutS0Comp` | lean=[OutS0Comp@Form/OutS0:OMISSION_ERROR/ERROR] kernel=[OutS0Comp@Form/OutS0:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `OutS2Comp` | lean=[Form/OutS2=value 1] kernel=[Form/OutS2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `OutS2Comp` | lean=[OutS2Comp@Form/OutS2:OMISSION_ERROR/ERROR] kernel=[OutS2Comp@Form/OutS2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `OutT0Comp` | lean=[Form/OutT0=value 1] kernel=[Form/OutT0=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `OutT0Comp` | lean=[OutT0Comp@Form/OutT0:OMISSION_ERROR/ERROR] kernel=[OutT0Comp@Form/OutT0:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `OutT2Comp` | lean=[Form/OutT2=value 1] kernel=[Form/OutT2=cleared] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `OutT2Comp` | lean=[OutT2Comp@Form/OutT2:OMISSION_ERROR/ERROR] kernel=[OutT2Comp@Form/OutT2:VALUE_ERROR/ERROR] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `ResetComp` | lean=[Form/Reset=value 10] kernel=[] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `RowSumComp` | lean=[Form/Outer/RowSum=value 5, Form/Outer[2]/RowSum=value 5] kernel=[] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `SumComp` | lean=[Form/Sum=value 10] kernel=[] |
| `first-filled-traversal-2026-10-10/request.json` | `successor-failure` | `call` | lean=[] kernel=[Form/Count:berechnungsWertFehler, Form/First:berechnungsWertFehler, Form/OutB0:berechnungsWertFehler, Form/OutB2:berechnungsWertFehler, Form/OutN0:berechnungsWertFehler, Form/OutN2:berechnungsWertFehler, Form/OutR0:berechnungsWertFehler, Form/OutR2:berechnungsWertFehler, Form/OutS0:berechnungsWertFehler, Form/OutS2:berechnungsWertFehler, Form/OutT0:berechnungsWertFehler, Form/OutT2:berechnungsWertFehler, Form/Outer/RowSum:berechnungsWertFehler, Form/Outer[2]/RowSum:berechnungsWertFehler, Form/Reset:berechnungsWertFehler, Form/Sum:berechnungsWertFehler] |
| `group-count-multiplicity-2026-10-10/request.json` | `partial-later-empty` | `T4` | lean=[] kernel=[T4@Form/Anchor:VALUE_ERROR/ERROR] |
| `group-count-multiplicity-2026-10-10/request.json` | `partial-later-hidden-filled` | `T4` | lean=[] kernel=[T4@Form/Anchor:VALUE_ERROR/ERROR] |
| `group-count-multiplicity-2026-10-10/request.json` | `partial-later-visible-filled` | `D4` | lean=[] kernel=[D4@Form/Anchor:VALUE_ERROR/ERROR] |
| `group-count-multiplicity-2026-10-10/request.json` | `partial-later-visible-filled` | `L2` | lean=[] kernel=[L2@Form/Anchor:VALUE_ERROR/ERROR] |
| `group-count-multiplicity-2026-10-10/request.json` | `partial-later-visible-filled` | `LR4` | lean=[] kernel=[LR4@Form/Anchor:VALUE_ERROR/ERROR] |
| `group-count-multiplicity-2026-10-10/request.json` | `partial-later-visible-filled` | `M4` | lean=[] kernel=[M4@Form/Anchor:VALUE_ERROR/ERROR] |
| `group-count-multiplicity-2026-10-10/request.json` | `partial-later-visible-filled` | `MR4` | lean=[] kernel=[MR4@Form/Anchor:VALUE_ERROR/ERROR] |
| `group-count-multiplicity-2026-10-10/request.json` | `partial-later-visible-filled` | `RL4` | lean=[] kernel=[RL4@Form/Anchor:VALUE_ERROR/ERROR] |
| `group-count-multiplicity-2026-10-10/request.json` | `partial-later-visible-filled` | `T4` | lean=[] kernel=[T4@Form/Anchor:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `empty-payload` | `GapNowComp` | lean=[Form/GapNow=value 0] kernel=[Form/GapNow=cleared] |
| `having-temporal-constants-2026-10-07/request.json` | `empty-payload` | `GapNowComp` | lean=[GapNowComp@Form/GapNow:OMISSION_ERROR/ERROR] kernel=[GapNowComp@Form/GapNow:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `empty-payload` | `GapNowRComp` | lean=[Form/GapNowR=value 0] kernel=[Form/GapNowR=cleared] |
| `having-temporal-constants-2026-10-07/request.json` | `empty-payload` | `GapNowRComp` | lean=[GapNowRComp@Form/GapNowR:OMISSION_ERROR/ERROR] kernel=[GapNowRComp@Form/GapNowR:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `empty-payload` | `GapNowRRule` | lean=[] kernel=[GapNowR@Form/Error:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `empty-payload` | `GapNowRule` | lean=[] kernel=[GapNow@Form/Error:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `empty-payload` | `GapStampComp` | lean=[Form/GapStamp=value 0] kernel=[Form/GapStamp=cleared] |
| `having-temporal-constants-2026-10-07/request.json` | `empty-payload` | `GapStampComp` | lean=[GapStampComp@Form/GapStamp:OMISSION_ERROR/ERROR] kernel=[GapStampComp@Form/GapStamp:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `empty-payload` | `GapStampRComp` | lean=[Form/GapStampR=value 0] kernel=[Form/GapStampR=cleared] |
| `having-temporal-constants-2026-10-07/request.json` | `empty-payload` | `GapStampRComp` | lean=[GapStampRComp@Form/GapStampR:OMISSION_ERROR/ERROR] kernel=[GapStampRComp@Form/GapStampR:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `empty-payload` | `GapStampRRule` | lean=[] kernel=[GapStampR@Form/Error:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `empty-payload` | `GapStampRule` | lean=[] kernel=[GapStamp@Form/Error:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `empty-payload` | `call` | lean=[] kernel=[Form/GapNow:berechnungsWertFehler, Form/GapNowR:berechnungsWertFehler, Form/GapStamp:berechnungsWertFehler, Form/GapStampR:berechnungsWertFehler] |
| `having-temporal-constants-2026-10-07/request.json` | `malformed-payload` | `GapNowComp` | lean=[Form/GapNow=value 0] kernel=[Form/GapNow=cleared] |
| `having-temporal-constants-2026-10-07/request.json` | `malformed-payload` | `GapNowComp` | lean=[GapNowComp@Form/GapNow:OMISSION_ERROR/ERROR] kernel=[GapNowComp@Form/GapNow:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `malformed-payload` | `GapNowRComp` | lean=[Form/GapNowR=value 0] kernel=[Form/GapNowR=cleared] |
| `having-temporal-constants-2026-10-07/request.json` | `malformed-payload` | `GapNowRComp` | lean=[GapNowRComp@Form/GapNowR:OMISSION_ERROR/ERROR] kernel=[GapNowRComp@Form/GapNowR:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `malformed-payload` | `GapNowRRule` | lean=[] kernel=[GapNowR@Form/Error:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `malformed-payload` | `GapNowRule` | lean=[] kernel=[GapNow@Form/Error:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `malformed-payload` | `GapStampComp` | lean=[GapStampComp@Form/GapStamp:OMISSION_ERROR/ERROR] kernel=[GapStampComp@Form/GapStamp:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `malformed-payload` | `GapStampRComp` | lean=[GapStampRComp@Form/GapStampR:OMISSION_ERROR/ERROR] kernel=[GapStampRComp@Form/GapStampR:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `malformed-payload` | `GapStampRRule` | lean=[] kernel=[GapStampR@Form/Error:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `malformed-payload` | `GapStampRule` | lean=[] kernel=[GapStamp@Form/Error:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `malformed-payload` | `call` | lean=[Form/Rows/D:datumFormatFalsch, Form/Rows/S:datumFormatFalsch, Form/Rows/T:datumFormatFalsch] kernel=[Form/GapNow:berechnungsWertFehler, Form/GapNowR:berechnungsWertFehler, Form/GapStampR:berechnungsWertFehler, Form/Rows/D:datumFormatFalsch, Form/Rows/S:datumFormatFalsch, Form/Rows/T:datumFormatFalsch] |
| `having-temporal-constants-2026-10-07/request.json` | `values` | `GapNowComp` | lean=[Form/GapNow=value 0] kernel=[Form/GapNow=cleared] |
| `having-temporal-constants-2026-10-07/request.json` | `values` | `GapNowComp` | lean=[GapNowComp@Form/GapNow:OMISSION_ERROR/ERROR] kernel=[GapNowComp@Form/GapNow:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `values` | `GapNowRComp` | lean=[Form/GapNowR=value 0] kernel=[Form/GapNowR=cleared] |
| `having-temporal-constants-2026-10-07/request.json` | `values` | `GapNowRComp` | lean=[GapNowRComp@Form/GapNowR:OMISSION_ERROR/ERROR] kernel=[GapNowRComp@Form/GapNowR:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `values` | `GapNowRRule` | lean=[] kernel=[GapNowR@Form/Error:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `values` | `GapNowRule` | lean=[] kernel=[GapNow@Form/Error:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `values` | `GapStampComp` | lean=[Form/GapStamp=value 0] kernel=[Form/GapStamp=cleared] |
| `having-temporal-constants-2026-10-07/request.json` | `values` | `GapStampComp` | lean=[GapStampComp@Form/GapStamp:OMISSION_ERROR/ERROR] kernel=[GapStampComp@Form/GapStamp:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `values` | `GapStampRComp` | lean=[Form/GapStampR=value 0] kernel=[Form/GapStampR=cleared] |
| `having-temporal-constants-2026-10-07/request.json` | `values` | `GapStampRComp` | lean=[GapStampRComp@Form/GapStampR:OMISSION_ERROR/ERROR] kernel=[GapStampRComp@Form/GapStampR:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `values` | `GapStampRRule` | lean=[] kernel=[GapStampR@Form/Error:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `values` | `GapStampRule` | lean=[] kernel=[GapStamp@Form/Error:VALUE_ERROR/ERROR] |
| `having-temporal-constants-2026-10-07/request.json` | `values` | `call` | lean=[] kernel=[Form/GapNow:berechnungsWertFehler, Form/GapNowR:berechnungsWertFehler, Form/GapStamp:berechnungsWertFehler, Form/GapStampR:berechnungsWertFehler] |
| `k22-runtime-r8-2026-10-24/request.json` | `badClock` | `call` | lean=[Form/Clock:datumFormatFalsch, Form/T7:berechnungsWertFehler] kernel=[Form/Clock:datumFormatFalsch, Form/T1:berechnungsWertFehler, Form/T3:berechnungsWertFehler, Form/T7:berechnungsWertFehler] |
| `k22-runtime-r8-2026-10-24/request.json` | `badClock` | `gD` | lean=[Form/T2=value 2] kernel=[Form/T2=cleared] |
| `k22-runtime-r8-2026-10-24/request.json` | `badClock` | `gG` | lean=[Form/T1=value 1] kernel=[Form/T1=cleared] |
| `k22-runtime-r8-2026-10-24/request.json` | `badClock` | `gG` | lean=[gG@Form/T1:VALUE_ERROR/ERROR referenced=[Form/T1] fillToFix=[]] kernel=[gG@Form/T1:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `k22-runtime-r8-2026-10-24/request.json` | `badClock` | `gL` | lean=[] kernel=[gL@Form/T3:VALUE_ERROR/ERROR] |
| `k22-runtime-r8-2026-10-24/request.json` | `badClock` | `gR` | lean=[] kernel=[gR@Form/T4:VALUE_ERROR/ERROR] |
| `k22-runtime-r8-2026-10-24/request.json` | `badClockZeroA` | `call` | lean=[Form/Clock:datumFormatFalsch, Form/T7:berechnungsWertFehler] kernel=[Form/Clock:datumFormatFalsch, Form/T1:berechnungsWertFehler, Form/T3:berechnungsWertFehler, Form/T7:berechnungsWertFehler] |
| `k22-runtime-r8-2026-10-24/request.json` | `badClockZeroA` | `gD` | lean=[Form/T2=value 2] kernel=[Form/T2=cleared] |
| `k22-runtime-r8-2026-10-24/request.json` | `badClockZeroA` | `gG` | lean=[Form/T1=value 1] kernel=[Form/T1=cleared] |
| `k22-runtime-r8-2026-10-24/request.json` | `badClockZeroA` | `gG` | lean=[gG@Form/T1:VALUE_ERROR/ERROR referenced=[Form/T1] fillToFix=[]] kernel=[gG@Form/T1:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `k22-runtime-r8-2026-10-24/request.json` | `badClockZeroA` | `gL` | lean=[] kernel=[gL@Form/T3:VALUE_ERROR/ERROR] |
| `k22-runtime-r8-2026-10-24/request.json` | `badClockZeroA` | `gR` | lean=[] kernel=[gR@Form/T4:VALUE_ERROR/ERROR] |
| `k22-runtime-r8-2026-10-24/request.json` | `goodClock` | `call` | lean=[Form/T5:berechnungsWertFehler, Form/T6:berechnungsWertFehler, Form/T7:berechnungsWertFehler] kernel=[Form/T1:berechnungsWertFehler, Form/T3:berechnungsWertFehler, Form/T4:berechnungsWertFehler, Form/T5:berechnungsWertFehler, Form/T6:berechnungsWertFehler, Form/T7:berechnungsWertFehler] |
| `k22-runtime-r8-2026-10-24/request.json` | `goodClock` | `gD` | lean=[Form/T2=value 2] kernel=[Form/T2=cleared] |
| `k22-runtime-r8-2026-10-24/request.json` | `goodClock` | `gG` | lean=[Form/T1=value 1] kernel=[Form/T1=cleared] |
| `k22-runtime-r8-2026-10-24/request.json` | `goodClock` | `gG` | lean=[gG@Form/T1:VALUE_ERROR/ERROR referenced=[Form/T1] fillToFix=[]] kernel=[gG@Form/T1:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `k22-runtime-r8-2026-10-24/request.json` | `goodClock` | `gL` | lean=[] kernel=[gL@Form/T3:VALUE_ERROR/ERROR] |
| `k22-runtime-r8-2026-10-24/request.json` | `goodClock` | `gR` | lean=[Form/T4=value 1] kernel=[Form/T4=cleared] |
| `k22-runtime-r8-2026-10-24/request.json` | `goodClock` | `gR` | lean=[gR@Form/T4:VALUE_ERROR/ERROR referenced=[Form/Clock, Form/T4] fillToFix=[]] kernel=[gR@Form/T4:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `CountComp` | lean=[CountComp@Form/Count:OMISSION_ERROR/ERROR] kernel=[CountComp@Form/Count:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `CountComp` | lean=[Form/Count=value 51] kernel=[Form/Count=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `NEmpty1Comp` | lean=[Form/NEmpty1=value 1] kernel=[Form/NEmpty1=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `NEmpty1Comp` | lean=[NEmpty1Comp@Form/NEmpty1:OMISSION_ERROR/ERROR] kernel=[NEmpty1Comp@Form/NEmpty1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `NSubjects2Comp` | lean=[] kernel=[NSubjects2Comp@Form/NSubjects2:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `NValues0Comp` | lean=[Form/NValues0=value 1] kernel=[Form/NValues0=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `NValues0Comp` | lean=[NValues0Comp@Form/NValues0:OMISSION_ERROR/ERROR] kernel=[NValues0Comp@Form/NValues0:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `NValues1Comp` | lean=[] kernel=[NValues1Comp@Form/NValues1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `NValues2Comp` | lean=[] kernel=[NValues2Comp@Form/NValues2:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `ResetComp` | lean=[Form/Reset=value 255] kernel=[Form/Reset=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `ResetComp` | lean=[ResetComp@Form/Reset:OMISSION_ERROR/ERROR] kernel=[ResetComp@Form/Reset:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `RowSumComp` | lean=[Form/Outer/RowSum=value 250, Form/Outer[2]/RowSum=value 5] kernel=[Form/Outer/RowSum=value 250, Form/Outer[2]/RowSum=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `RowSumComp` | lean=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer[2]/RowSum:OMISSION_ERROR/ERROR] kernel=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer/RowSum:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `RuleNEmpty1` | lean=[NEMPTY1@Form/Error:OMISSION_ERROR/ERROR] kernel=[NEMPTY1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `RuleNSubjects2` | lean=[] kernel=[NSUBJECTS2@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `RuleNValues0` | lean=[NVALUES0@Form/Error:OMISSION_ERROR/ERROR] kernel=[NVALUES0@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `RuleNValues1` | lean=[] kernel=[NVALUES1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `RuleNValues2` | lean=[] kernel=[NVALUES2@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `RuleTEmpty1` | lean=[TEMPTY1@Form/Error:OMISSION_ERROR/ERROR] kernel=[TEMPTY1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `RuleTSubjects2` | lean=[] kernel=[TSUBJECTS2@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `RuleTValues0` | lean=[TVALUES0@Form/Error:OMISSION_ERROR/ERROR] kernel=[TVALUES0@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `RuleTValues1` | lean=[] kernel=[TVALUES1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `RuleTValues2` | lean=[] kernel=[TVALUES2@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `SumComp` | lean=[Form/Sum=value 255] kernel=[Form/Sum=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `SumComp` | lean=[SumComp@Form/Sum:OMISSION_ERROR/ERROR] kernel=[SumComp@Form/Sum:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `TEmpty1Comp` | lean=[Form/TEmpty1=value 1] kernel=[Form/TEmpty1=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `TEmpty1Comp` | lean=[TEmpty1Comp@Form/TEmpty1:OMISSION_ERROR/ERROR] kernel=[TEmpty1Comp@Form/TEmpty1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `TSubjects2Comp` | lean=[] kernel=[TSubjects2Comp@Form/TSubjects2:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `TValues0Comp` | lean=[Form/TValues0=value 1] kernel=[Form/TValues0=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `TValues0Comp` | lean=[TValues0Comp@Form/TValues0:OMISSION_ERROR/ERROR] kernel=[TValues0Comp@Form/TValues0:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `TValues1Comp` | lean=[] kernel=[TValues1Comp@Form/TValues1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `TValues2Comp` | lean=[] kernel=[TValues2Comp@Form/TValues2:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-early` | `call` | lean=[Form/Bad:zahlHatUngueltigeZeichen] kernel=[Form/Bad:zahlHatUngueltigeZeichen, Form/Count:berechnungsWertFehler, Form/NEmpty1:berechnungsWertFehler, Form/NSubjects2:berechnungsWertFehler, Form/NValues0:berechnungsWertFehler, Form/NValues1:berechnungsWertFehler, Form/NValues2:berechnungsWertFehler, Form/Outer[2]/RowSum:berechnungsWertFehler, Form/Reset:berechnungsWertFehler, Form/Sum:berechnungsWertFehler, Form/TEmpty1:berechnungsWertFehler, Form/TSubjects2:berechnungsWertFehler, Form/TValues0:berechnungsWertFehler, Form/TValues1:berechnungsWertFehler, Form/TValues2:berechnungsWertFehler] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `CountComp` | lean=[CountComp@Form/Count:OMISSION_ERROR/ERROR] kernel=[CountComp@Form/Count:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `CountComp` | lean=[Form/Count=value 1] kernel=[Form/Count=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `FirstComp` | lean=[FirstComp@Form/First:OMISSION_ERROR/ERROR] kernel=[FirstComp@Form/First:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `FirstComp` | lean=[Form/First=value 5] kernel=[Form/First=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `NEmpty1Comp` | lean=[Form/NEmpty1=value 1] kernel=[Form/NEmpty1=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `NEmpty1Comp` | lean=[NEmpty1Comp@Form/NEmpty1:OMISSION_ERROR/ERROR] kernel=[NEmpty1Comp@Form/NEmpty1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `NSubjects0Comp` | lean=[Form/NSubjects0=value 1] kernel=[Form/NSubjects0=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `NSubjects0Comp` | lean=[NSubjects0Comp@Form/NSubjects0:OMISSION_ERROR/ERROR] kernel=[NSubjects0Comp@Form/NSubjects0:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `NSubjects1Comp` | lean=[] kernel=[NSubjects1Comp@Form/NSubjects1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `NSubjects2Comp` | lean=[] kernel=[NSubjects2Comp@Form/NSubjects2:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `NValues0Comp` | lean=[Form/NValues0=value 1] kernel=[Form/NValues0=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `NValues0Comp` | lean=[NValues0Comp@Form/NValues0:OMISSION_ERROR/ERROR] kernel=[NValues0Comp@Form/NValues0:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `NValues1Comp` | lean=[] kernel=[NValues1Comp@Form/NValues1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `NValues2Comp` | lean=[] kernel=[NValues2Comp@Form/NValues2:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `ResetComp` | lean=[Form/Reset=value 5] kernel=[Form/Reset=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `ResetComp` | lean=[ResetComp@Form/Reset:OMISSION_ERROR/ERROR] kernel=[ResetComp@Form/Reset:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `RowSumComp` | lean=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=value 5] kernel=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `RowSumComp` | lean=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer[2]/RowSum:OMISSION_ERROR/ERROR] kernel=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer/RowSum:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `RuleNEmpty1` | lean=[NEMPTY1@Form/Error:OMISSION_ERROR/ERROR] kernel=[NEMPTY1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `RuleNSubjects0` | lean=[NSUBJECTS0@Form/Error:OMISSION_ERROR/ERROR] kernel=[NSUBJECTS0@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `RuleNSubjects1` | lean=[] kernel=[NSUBJECTS1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `RuleNSubjects2` | lean=[] kernel=[NSUBJECTS2@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `RuleNValues0` | lean=[NVALUES0@Form/Error:OMISSION_ERROR/ERROR] kernel=[NVALUES0@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `RuleNValues1` | lean=[] kernel=[NVALUES1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `RuleNValues2` | lean=[] kernel=[NVALUES2@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `RuleTEmpty1` | lean=[TEMPTY1@Form/Error:OMISSION_ERROR/ERROR] kernel=[TEMPTY1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `RuleTSubjects0` | lean=[TSUBJECTS0@Form/Error:OMISSION_ERROR/ERROR] kernel=[TSUBJECTS0@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `RuleTSubjects1` | lean=[] kernel=[TSUBJECTS1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `RuleTSubjects2` | lean=[] kernel=[TSUBJECTS2@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `RuleTValues0` | lean=[TVALUES0@Form/Error:OMISSION_ERROR/ERROR] kernel=[TVALUES0@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `RuleTValues1` | lean=[] kernel=[TVALUES1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `RuleTValues2` | lean=[] kernel=[TVALUES2@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `SumComp` | lean=[Form/Sum=value 5] kernel=[Form/Sum=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `SumComp` | lean=[SumComp@Form/Sum:OMISSION_ERROR/ERROR] kernel=[SumComp@Form/Sum:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `TEmpty1Comp` | lean=[Form/TEmpty1=value 1] kernel=[Form/TEmpty1=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `TEmpty1Comp` | lean=[TEmpty1Comp@Form/TEmpty1:OMISSION_ERROR/ERROR] kernel=[TEmpty1Comp@Form/TEmpty1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `TSubjects0Comp` | lean=[Form/TSubjects0=value 1] kernel=[Form/TSubjects0=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `TSubjects0Comp` | lean=[TSubjects0Comp@Form/TSubjects0:OMISSION_ERROR/ERROR] kernel=[TSubjects0Comp@Form/TSubjects0:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `TSubjects1Comp` | lean=[] kernel=[TSubjects1Comp@Form/TSubjects1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `TSubjects2Comp` | lean=[] kernel=[TSubjects2Comp@Form/TSubjects2:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `TValues0Comp` | lean=[Form/TValues0=value 1] kernel=[Form/TValues0=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `TValues0Comp` | lean=[TValues0Comp@Form/TValues0:OMISSION_ERROR/ERROR] kernel=[TValues0Comp@Form/TValues0:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `TValues1Comp` | lean=[] kernel=[TValues1Comp@Form/TValues1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `TValues2Comp` | lean=[] kernel=[TValues2Comp@Form/TValues2:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-late` | `call` | lean=[Form/Bad:zahlHatUngueltigeZeichen] kernel=[Form/Bad:zahlHatUngueltigeZeichen, Form/Count:berechnungsWertFehler, Form/First:berechnungsWertFehler, Form/NEmpty1:berechnungsWertFehler, Form/NSubjects0:berechnungsWertFehler, Form/NSubjects1:berechnungsWertFehler, Form/NSubjects2:berechnungsWertFehler, Form/NValues0:berechnungsWertFehler, Form/NValues1:berechnungsWertFehler, Form/NValues2:berechnungsWertFehler, Form/Outer[2]/RowSum:berechnungsWertFehler, Form/Reset:berechnungsWertFehler, Form/Sum:berechnungsWertFehler, Form/TEmpty1:berechnungsWertFehler, Form/TSubjects0:berechnungsWertFehler, Form/TSubjects1:berechnungsWertFehler, Form/TSubjects2:berechnungsWertFehler, Form/TValues0:berechnungsWertFehler, Form/TValues1:berechnungsWertFehler, Form/TValues2:berechnungsWertFehler] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `CountComp` | lean=[CountComp@Form/Count:OMISSION_ERROR/ERROR] kernel=[CountComp@Form/Count:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `CountComp` | lean=[Form/Count=value 51] kernel=[Form/Count=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `NEmpty1Comp` | lean=[Form/NEmpty1=value 1] kernel=[Form/NEmpty1=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `NEmpty1Comp` | lean=[NEmpty1Comp@Form/NEmpty1:OMISSION_ERROR/ERROR] kernel=[NEmpty1Comp@Form/NEmpty1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `NSubjects0Comp` | lean=[] kernel=[NSubjects0Comp@Form/NSubjects0:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `NSubjects1Comp` | lean=[Form/NSubjects1=value 1] kernel=[Form/NSubjects1=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `NSubjects1Comp` | lean=[NSubjects1Comp@Form/NSubjects1:OMISSION_ERROR/ERROR] kernel=[NSubjects1Comp@Form/NSubjects1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `NValues0Comp` | lean=[] kernel=[NValues0Comp@Form/NValues0:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `NValues1Comp` | lean=[Form/NValues1=value 1] kernel=[Form/NValues1=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `NValues1Comp` | lean=[NValues1Comp@Form/NValues1:OMISSION_ERROR/ERROR] kernel=[NValues1Comp@Form/NValues1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `NValues2Comp` | lean=[Form/NValues2=value 1] kernel=[Form/NValues2=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `NValues2Comp` | lean=[NValues2Comp@Form/NValues2:OMISSION_ERROR/ERROR] kernel=[NValues2Comp@Form/NValues2:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `ResetComp` | lean=[Form/Reset=value 255] kernel=[Form/Reset=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `ResetComp` | lean=[ResetComp@Form/Reset:OMISSION_ERROR/ERROR] kernel=[ResetComp@Form/Reset:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `RowSumComp` | lean=[Form/Outer/RowSum=value 250, Form/Outer[2]/RowSum=value 5] kernel=[Form/Outer/RowSum=value 250, Form/Outer[2]/RowSum=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `RowSumComp` | lean=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer[2]/RowSum:OMISSION_ERROR/ERROR] kernel=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer/RowSum:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `RuleNEmpty1` | lean=[NEMPTY1@Form/Error:OMISSION_ERROR/ERROR] kernel=[NEMPTY1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `RuleNSubjects0` | lean=[] kernel=[NSUBJECTS0@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `RuleNSubjects1` | lean=[NSUBJECTS1@Form/Error:OMISSION_ERROR/ERROR] kernel=[NSUBJECTS1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `RuleNValues0` | lean=[] kernel=[NVALUES0@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `RuleNValues1` | lean=[NVALUES1@Form/Error:OMISSION_ERROR/ERROR] kernel=[NVALUES1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `RuleNValues2` | lean=[NVALUES2@Form/Error:OMISSION_ERROR/ERROR] kernel=[NVALUES2@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `RuleTEmpty1` | lean=[TEMPTY1@Form/Error:OMISSION_ERROR/ERROR] kernel=[TEMPTY1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `RuleTSubjects0` | lean=[] kernel=[TSUBJECTS0@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `RuleTSubjects1` | lean=[TSUBJECTS1@Form/Error:OMISSION_ERROR/ERROR] kernel=[TSUBJECTS1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `RuleTValues0` | lean=[] kernel=[TVALUES0@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `RuleTValues1` | lean=[TVALUES1@Form/Error:OMISSION_ERROR/ERROR] kernel=[TVALUES1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `RuleTValues2` | lean=[TVALUES2@Form/Error:OMISSION_ERROR/ERROR] kernel=[TVALUES2@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `SumComp` | lean=[Form/Sum=value 255] kernel=[Form/Sum=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `SumComp` | lean=[SumComp@Form/Sum:OMISSION_ERROR/ERROR] kernel=[SumComp@Form/Sum:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `TEmpty1Comp` | lean=[Form/TEmpty1=value 1] kernel=[Form/TEmpty1=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `TEmpty1Comp` | lean=[TEmpty1Comp@Form/TEmpty1:OMISSION_ERROR/ERROR] kernel=[TEmpty1Comp@Form/TEmpty1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `TSubjects0Comp` | lean=[] kernel=[TSubjects0Comp@Form/TSubjects0:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `TSubjects1Comp` | lean=[Form/TSubjects1=value 1] kernel=[Form/TSubjects1=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `TSubjects1Comp` | lean=[TSubjects1Comp@Form/TSubjects1:OMISSION_ERROR/ERROR] kernel=[TSubjects1Comp@Form/TSubjects1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `TValues0Comp` | lean=[] kernel=[TValues0Comp@Form/TValues0:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `TValues1Comp` | lean=[Form/TValues1=value 1] kernel=[Form/TValues1=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `TValues1Comp` | lean=[TValues1Comp@Form/TValues1:OMISSION_ERROR/ERROR] kernel=[TValues1Comp@Form/TValues1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `TValues2Comp` | lean=[Form/TValues2=value 1] kernel=[Form/TValues2=cleared] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `TValues2Comp` | lean=[TValues2Comp@Form/TValues2:OMISSION_ERROR/ERROR] kernel=[TValues2Comp@Form/TValues2:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `dense-outside` | `call` | lean=[Form/Bad:zahlHatUngueltigeZeichen] kernel=[Form/Bad:zahlHatUngueltigeZeichen, Form/Count:berechnungsWertFehler, Form/NEmpty1:berechnungsWertFehler, Form/NSubjects0:berechnungsWertFehler, Form/NSubjects1:berechnungsWertFehler, Form/NValues0:berechnungsWertFehler, Form/NValues1:berechnungsWertFehler, Form/NValues2:berechnungsWertFehler, Form/Outer[2]/RowSum:berechnungsWertFehler, Form/Reset:berechnungsWertFehler, Form/Sum:berechnungsWertFehler, Form/TEmpty1:berechnungsWertFehler, Form/TSubjects0:berechnungsWertFehler, Form/TSubjects1:berechnungsWertFehler, Form/TValues0:berechnungsWertFehler, Form/TValues1:berechnungsWertFehler, Form/TValues2:berechnungsWertFehler] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `CountComp` | lean=[CountComp@Form/Count:OMISSION_ERROR/ERROR] kernel=[CountComp@Form/Count:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `CountComp` | lean=[Form/Count=value 1] kernel=[Form/Count=cleared] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `FirstComp` | lean=[FirstComp@Form/First:OMISSION_ERROR/ERROR] kernel=[FirstComp@Form/First:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `FirstComp` | lean=[Form/First=value 5] kernel=[Form/First=cleared] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `NEmpty1Comp` | lean=[Form/NEmpty1=value 1] kernel=[Form/NEmpty1=cleared] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `NEmpty1Comp` | lean=[NEmpty1Comp@Form/NEmpty1:OMISSION_ERROR/ERROR] kernel=[NEmpty1Comp@Form/NEmpty1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `NSubjects0Comp` | lean=[Form/NSubjects0=value 1] kernel=[Form/NSubjects0=cleared] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `NSubjects0Comp` | lean=[NSubjects0Comp@Form/NSubjects0:OMISSION_ERROR/ERROR] kernel=[NSubjects0Comp@Form/NSubjects0:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `NSubjects1Comp` | lean=[] kernel=[NSubjects1Comp@Form/NSubjects1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `NSubjects2Comp` | lean=[] kernel=[NSubjects2Comp@Form/NSubjects2:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `NValues0Comp` | lean=[Form/NValues0=value 1] kernel=[Form/NValues0=cleared] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `NValues0Comp` | lean=[NValues0Comp@Form/NValues0:OMISSION_ERROR/ERROR] kernel=[NValues0Comp@Form/NValues0:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `NValues1Comp` | lean=[] kernel=[NValues1Comp@Form/NValues1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `NValues2Comp` | lean=[] kernel=[NValues2Comp@Form/NValues2:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `ResetComp` | lean=[Form/Reset=value 5] kernel=[Form/Reset=cleared] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `ResetComp` | lean=[ResetComp@Form/Reset:OMISSION_ERROR/ERROR] kernel=[ResetComp@Form/Reset:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `RowSumComp` | lean=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=value 5] kernel=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=cleared] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `RowSumComp` | lean=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer[2]/RowSum:OMISSION_ERROR/ERROR] kernel=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer/RowSum:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `RuleNEmpty1` | lean=[NEMPTY1@Form/Error:OMISSION_ERROR/ERROR] kernel=[NEMPTY1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `RuleNSubjects0` | lean=[NSUBJECTS0@Form/Error:OMISSION_ERROR/ERROR] kernel=[NSUBJECTS0@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `RuleNSubjects1` | lean=[] kernel=[NSUBJECTS1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `RuleNSubjects2` | lean=[] kernel=[NSUBJECTS2@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `RuleNValues0` | lean=[NVALUES0@Form/Error:OMISSION_ERROR/ERROR] kernel=[NVALUES0@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `RuleNValues1` | lean=[] kernel=[NVALUES1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `RuleNValues2` | lean=[] kernel=[NVALUES2@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `RuleTEmpty1` | lean=[TEMPTY1@Form/Error:OMISSION_ERROR/ERROR] kernel=[TEMPTY1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `RuleTSubjects0` | lean=[TSUBJECTS0@Form/Error:OMISSION_ERROR/ERROR] kernel=[TSUBJECTS0@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `RuleTSubjects1` | lean=[] kernel=[TSUBJECTS1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `RuleTSubjects2` | lean=[] kernel=[TSUBJECTS2@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `RuleTValues0` | lean=[TVALUES0@Form/Error:OMISSION_ERROR/ERROR] kernel=[TVALUES0@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `RuleTValues1` | lean=[] kernel=[TVALUES1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `RuleTValues2` | lean=[] kernel=[TVALUES2@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `SumComp` | lean=[Form/Sum=value 5] kernel=[Form/Sum=cleared] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `SumComp` | lean=[SumComp@Form/Sum:OMISSION_ERROR/ERROR] kernel=[SumComp@Form/Sum:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `TEmpty1Comp` | lean=[Form/TEmpty1=value 1] kernel=[Form/TEmpty1=cleared] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `TEmpty1Comp` | lean=[TEmpty1Comp@Form/TEmpty1:OMISSION_ERROR/ERROR] kernel=[TEmpty1Comp@Form/TEmpty1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `TSubjects0Comp` | lean=[Form/TSubjects0=value 1] kernel=[Form/TSubjects0=cleared] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `TSubjects0Comp` | lean=[TSubjects0Comp@Form/TSubjects0:OMISSION_ERROR/ERROR] kernel=[TSubjects0Comp@Form/TSubjects0:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `TSubjects1Comp` | lean=[] kernel=[TSubjects1Comp@Form/TSubjects1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `TSubjects2Comp` | lean=[] kernel=[TSubjects2Comp@Form/TSubjects2:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `TValues0Comp` | lean=[Form/TValues0=value 1] kernel=[Form/TValues0=cleared] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `TValues0Comp` | lean=[TValues0Comp@Form/TValues0:OMISSION_ERROR/ERROR] kernel=[TValues0Comp@Form/TValues0:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `TValues1Comp` | lean=[] kernel=[TValues1Comp@Form/TValues1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `TValues2Comp` | lean=[] kernel=[TValues2Comp@Form/TValues2:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-blank` | `call` | lean=[Form/Bad:zahlHatUngueltigeZeichen] kernel=[Form/Bad:zahlHatUngueltigeZeichen, Form/Count:berechnungsWertFehler, Form/First:berechnungsWertFehler, Form/NEmpty1:berechnungsWertFehler, Form/NSubjects0:berechnungsWertFehler, Form/NSubjects1:berechnungsWertFehler, Form/NSubjects2:berechnungsWertFehler, Form/NValues0:berechnungsWertFehler, Form/NValues1:berechnungsWertFehler, Form/NValues2:berechnungsWertFehler, Form/Outer[2]/RowSum:berechnungsWertFehler, Form/Reset:berechnungsWertFehler, Form/Sum:berechnungsWertFehler, Form/TEmpty1:berechnungsWertFehler, Form/TSubjects0:berechnungsWertFehler, Form/TSubjects1:berechnungsWertFehler, Form/TSubjects2:berechnungsWertFehler, Form/TValues0:berechnungsWertFehler, Form/TValues1:berechnungsWertFehler, Form/TValues2:berechnungsWertFehler] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `FirstComp` | lean=[FirstComp@Form/First:OMISSION_ERROR/ERROR] kernel=[FirstComp@Form/First:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `FirstComp` | lean=[Form/First=value 5] kernel=[Form/First=cleared] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `NEmpty1Comp` | lean=[Form/NEmpty1=value 1] kernel=[Form/NEmpty1=cleared] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `NEmpty1Comp` | lean=[NEmpty1Comp@Form/NEmpty1:OMISSION_ERROR/ERROR] kernel=[NEmpty1Comp@Form/NEmpty1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `NSubjects1Comp` | lean=[] kernel=[NSubjects1Comp@Form/NSubjects1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `NSubjects2Comp` | lean=[] kernel=[NSubjects2Comp@Form/NSubjects2:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `NValues1Comp` | lean=[] kernel=[NValues1Comp@Form/NValues1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `NValues2Comp` | lean=[] kernel=[NValues2Comp@Form/NValues2:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `RowSumComp` | lean=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=value 5] kernel=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=cleared] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `RowSumComp` | lean=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer[2]/RowSum:OMISSION_ERROR/ERROR] kernel=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer/RowSum:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `RuleNEmpty1` | lean=[NEMPTY1@Form/Error:OMISSION_ERROR/ERROR] kernel=[NEMPTY1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `RuleNSubjects1` | lean=[] kernel=[NSUBJECTS1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `RuleNSubjects2` | lean=[] kernel=[NSUBJECTS2@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `RuleNValues1` | lean=[] kernel=[NVALUES1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `RuleNValues2` | lean=[] kernel=[NVALUES2@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `RuleTEmpty1` | lean=[TEMPTY1@Form/Error:OMISSION_ERROR/ERROR] kernel=[TEMPTY1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `RuleTSubjects1` | lean=[] kernel=[TSUBJECTS1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `RuleTSubjects2` | lean=[] kernel=[TSUBJECTS2@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `RuleTValues1` | lean=[] kernel=[TVALUES1@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `RuleTValues2` | lean=[] kernel=[TVALUES2@Form/Error:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `TEmpty1Comp` | lean=[Form/TEmpty1=value 1] kernel=[Form/TEmpty1=cleared] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `TEmpty1Comp` | lean=[TEmpty1Comp@Form/TEmpty1:OMISSION_ERROR/ERROR] kernel=[TEmpty1Comp@Form/TEmpty1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `TSubjects1Comp` | lean=[] kernel=[TSubjects1Comp@Form/TSubjects1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `TSubjects2Comp` | lean=[] kernel=[TSubjects2Comp@Form/TSubjects2:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `TValues1Comp` | lean=[] kernel=[TValues1Comp@Form/TValues1:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `TValues2Comp` | lean=[] kernel=[TValues2Comp@Form/TValues2:VALUE_ERROR/ERROR] |
| `membership-traversal-2026-10-10/request.json` | `sparse-late` | `call` | lean=[Form/Bad:zahlHatUngueltigeZeichen] kernel=[Form/Bad:zahlHatUngueltigeZeichen, Form/First:berechnungsWertFehler, Form/NEmpty1:berechnungsWertFehler, Form/NSubjects1:berechnungsWertFehler, Form/NSubjects2:berechnungsWertFehler, Form/NValues1:berechnungsWertFehler, Form/NValues2:berechnungsWertFehler, Form/Outer[2]/RowSum:berechnungsWertFehler, Form/TEmpty1:berechnungsWertFehler, Form/TSubjects1:berechnungsWertFehler, Form/TSubjects2:berechnungsWertFehler, Form/TValues1:berechnungsWertFehler, Form/TValues2:berechnungsWertFehler] |
| `message-parameter-rows-2026-10-13/request.json` | `render-grid` | `RMiss` | lean=[RMiss@Kp/Anchor:OMISSION_ERROR/ERROR] kernel=[RMiss@Kp/Anchor:VALUE_ERROR/ERROR] |
| `message-parameter-rows-2026-10-13/request4.json` | `first-row-empty` | `RMiss` | lean=[RMiss@Kp/Anchor:OMISSION_ERROR/ERROR] kernel=[RMiss@Kp/Anchor:VALUE_ERROR/ERROR] |
| `message-parameter-rows-2026-10-13/request4.json` | `first-row-empty` | `RMissK` | lean=[RMissK@Kp/Anchor:OMISSION_ERROR/ERROR] kernel=[RMissK@Kp/Anchor:VALUE_ERROR/ERROR] |
| `message-parameter-rows-2026-10-13/request4.json` | `render-grid` | `RMiss` | lean=[RMiss@Kp/Anchor:OMISSION_ERROR/ERROR] kernel=[RMiss@Kp/Anchor:VALUE_ERROR/ERROR] |
| `message-parameter-rows-2026-10-13/request4.json` | `render-grid` | `RMissK` | lean=[RMissK@Kp/Anchor:OMISSION_ERROR/ERROR] kernel=[RMissK@Kp/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `R_constructed` | lean=[R_constructed@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[R_constructed@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `R_constructedHaving` | lean=[] kernel=[R_constructedHaving@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `R_constructedReverse` | lean=[R_constructedReverse@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[R_constructedReverse@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `R_constructedReverseHaving` | lean=[] kernel=[R_constructedReverseHaving@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `R_direct` | lean=[R_direct@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[R_direct@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `R_directHaving` | lean=[] kernel=[R_directHaving@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `R_directReverse` | lean=[R_directReverse@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[R_directReverse@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `R_directReverseHaving` | lean=[] kernel=[R_directReverseHaving@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `R_shift` | lean=[R_shift@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[R_shift@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `R_shiftHaving` | lean=[] kernel=[R_shiftHaving@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `R_shiftReverse` | lean=[R_shiftReverse@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[R_shiftReverse@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `R_shiftReverseHaving` | lean=[] kernel=[R_shiftReverseHaving@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `call` | lean=[] kernel=[Form/constructed:berechnungsWertFehler, Form/constructedHaving:berechnungsWertFehler, Form/constructedReverse:berechnungsWertFehler, Form/constructedReverseHaving:berechnungsWertFehler, Form/direct:berechnungsWertFehler, Form/directHaving:berechnungsWertFehler, Form/directReverse:berechnungsWertFehler, Form/directReverseHaving:berechnungsWertFehler, Form/shift:berechnungsWertFehler, Form/shiftHaving:berechnungsWertFehler, Form/shiftReverse:berechnungsWertFehler, Form/shiftReverseHaving:berechnungsWertFehler] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `constructedComp` | lean=[Form/constructed=value 0] kernel=[Form/constructed=cleared] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `constructedComp` | lean=[constructedComp@Form/constructed:OMISSION_ERROR/ERROR] kernel=[constructedComp@Form/constructed:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `constructedHavingComp` | lean=[Form/constructedHaving=value 7] kernel=[Form/constructedHaving=cleared] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `constructedHavingComp` | lean=[constructedHavingComp@Form/constructedHaving:OMISSION_ERROR/ERROR] kernel=[constructedHavingComp@Form/constructedHaving:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `constructedReverseComp` | lean=[Form/constructedReverse=value 0] kernel=[Form/constructedReverse=cleared] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `constructedReverseComp` | lean=[constructedReverseComp@Form/constructedReverse:OMISSION_ERROR/ERROR] kernel=[constructedReverseComp@Form/constructedReverse:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `constructedReverseHavingComp` | lean=[Form/constructedReverseHaving=value 7] kernel=[Form/constructedReverseHaving=cleared] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `constructedReverseHavingComp` | lean=[constructedReverseHavingComp@Form/constructedReverseHaving:OMISSION_ERROR/ERROR] kernel=[constructedReverseHavingComp@Form/constructedReverseHaving:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `directComp` | lean=[Form/direct=value 0] kernel=[Form/direct=cleared] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `directComp` | lean=[directComp@Form/direct:OMISSION_ERROR/ERROR] kernel=[directComp@Form/direct:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `directHavingComp` | lean=[Form/directHaving=value 7] kernel=[Form/directHaving=cleared] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `directHavingComp` | lean=[directHavingComp@Form/directHaving:OMISSION_ERROR/ERROR] kernel=[directHavingComp@Form/directHaving:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `directReverseComp` | lean=[Form/directReverse=value 0] kernel=[Form/directReverse=cleared] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `directReverseComp` | lean=[directReverseComp@Form/directReverse:OMISSION_ERROR/ERROR] kernel=[directReverseComp@Form/directReverse:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `directReverseHavingComp` | lean=[Form/directReverseHaving=value 7] kernel=[Form/directReverseHaving=cleared] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `directReverseHavingComp` | lean=[directReverseHavingComp@Form/directReverseHaving:OMISSION_ERROR/ERROR] kernel=[directReverseHavingComp@Form/directReverseHaving:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `shiftComp` | lean=[Form/shift=value 0] kernel=[Form/shift=cleared] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `shiftComp` | lean=[shiftComp@Form/shift:OMISSION_ERROR/ERROR] kernel=[shiftComp@Form/shift:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `shiftHavingComp` | lean=[Form/shiftHaving=value 7] kernel=[Form/shiftHaving=cleared] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `shiftHavingComp` | lean=[shiftHavingComp@Form/shiftHaving:OMISSION_ERROR/ERROR] kernel=[shiftHavingComp@Form/shiftHaving:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `shiftReverseComp` | lean=[Form/shiftReverse=value 0] kernel=[Form/shiftReverse=cleared] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `shiftReverseComp` | lean=[shiftReverseComp@Form/shiftReverse:OMISSION_ERROR/ERROR] kernel=[shiftReverseComp@Form/shiftReverse:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `shiftReverseHavingComp` | lean=[Form/shiftReverseHaving=value 7] kernel=[Form/shiftReverseHaving=cleared] |
| `recursive-difference-effects-2026-10-08/request.json` | `empty` | `shiftReverseHavingComp` | lean=[shiftReverseHavingComp@Form/shiftReverseHaving:OMISSION_ERROR/ERROR] kernel=[shiftReverseHavingComp@Form/shiftReverseHaving:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `R_constructed` | lean=[] kernel=[R_constructed@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `R_constructedHaving` | lean=[R_constructedHaving@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[R_constructedHaving@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `R_constructedReverse` | lean=[] kernel=[R_constructedReverse@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `R_constructedReverseHaving` | lean=[R_constructedReverseHaving@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[R_constructedReverseHaving@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `R_direct` | lean=[] kernel=[R_direct@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `R_directHaving` | lean=[R_directHaving@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[R_directHaving@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `R_directReverse` | lean=[] kernel=[R_directReverse@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `R_directReverseHaving` | lean=[R_directReverseHaving@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[R_directReverseHaving@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `R_shift` | lean=[] kernel=[R_shift@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `R_shiftHaving` | lean=[R_shiftHaving@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[R_shiftHaving@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `R_shiftReverse` | lean=[] kernel=[R_shiftReverse@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `R_shiftReverseHaving` | lean=[R_shiftReverseHaving@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[R_shiftReverseHaving@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `call` | lean=[] kernel=[Form/constructed:berechnungsWertFehler, Form/constructedHaving:berechnungsWertFehler, Form/constructedReverse:berechnungsWertFehler, Form/constructedReverseHaving:berechnungsWertFehler, Form/direct:berechnungsWertFehler, Form/directHaving:berechnungsWertFehler, Form/directReverse:berechnungsWertFehler, Form/directReverseHaving:berechnungsWertFehler, Form/shift:berechnungsWertFehler, Form/shiftHaving:berechnungsWertFehler, Form/shiftReverse:berechnungsWertFehler, Form/shiftReverseHaving:berechnungsWertFehler] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `constructedComp` | lean=[Form/constructed=value 30] kernel=[Form/constructed=cleared] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `constructedComp` | lean=[constructedComp@Form/constructed:VALUE_ERROR/ERROR referenced=[Form/Stamp, Form/constructed] fillToFix=[]] kernel=[constructedComp@Form/constructed:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `constructedHavingComp` | lean=[Form/constructedHaving=value 0] kernel=[Form/constructedHaving=cleared] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `constructedHavingComp` | lean=[constructedHavingComp@Form/constructedHaving:OMISSION_ERROR/ERROR] kernel=[constructedHavingComp@Form/constructedHaving:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `constructedReverseComp` | lean=[Form/constructedReverse=value -30] kernel=[Form/constructedReverse=cleared] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `constructedReverseComp` | lean=[constructedReverseComp@Form/constructedReverse:VALUE_ERROR/ERROR referenced=[Form/Stamp, Form/constructedReverse] fillToFix=[]] kernel=[constructedReverseComp@Form/constructedReverse:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `constructedReverseHavingComp` | lean=[Form/constructedReverseHaving=value 0] kernel=[Form/constructedReverseHaving=cleared] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `constructedReverseHavingComp` | lean=[constructedReverseHavingComp@Form/constructedReverseHaving:OMISSION_ERROR/ERROR] kernel=[constructedReverseHavingComp@Form/constructedReverseHaving:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `directComp` | lean=[Form/direct=value 90] kernel=[Form/direct=cleared] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `directComp` | lean=[directComp@Form/direct:VALUE_ERROR/ERROR referenced=[Form/Stamp, Form/direct] fillToFix=[]] kernel=[directComp@Form/direct:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `directHavingComp` | lean=[Form/directHaving=value 0] kernel=[Form/directHaving=cleared] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `directHavingComp` | lean=[directHavingComp@Form/directHaving:OMISSION_ERROR/ERROR] kernel=[directHavingComp@Form/directHaving:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `directReverseComp` | lean=[Form/directReverse=value -90] kernel=[Form/directReverse=cleared] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `directReverseComp` | lean=[directReverseComp@Form/directReverse:VALUE_ERROR/ERROR referenced=[Form/Stamp, Form/directReverse] fillToFix=[]] kernel=[directReverseComp@Form/directReverse:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `directReverseHavingComp` | lean=[Form/directReverseHaving=value 0] kernel=[Form/directReverseHaving=cleared] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `directReverseHavingComp` | lean=[directReverseHavingComp@Form/directReverseHaving:OMISSION_ERROR/ERROR] kernel=[directReverseHavingComp@Form/directReverseHaving:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `shiftComp` | lean=[Form/shift=value 89] kernel=[Form/shift=cleared] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `shiftComp` | lean=[shiftComp@Form/shift:VALUE_ERROR/ERROR referenced=[Form/Stamp, Form/shift] fillToFix=[]] kernel=[shiftComp@Form/shift:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `shiftHavingComp` | lean=[Form/shiftHaving=value 0] kernel=[Form/shiftHaving=cleared] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `shiftHavingComp` | lean=[shiftHavingComp@Form/shiftHaving:OMISSION_ERROR/ERROR] kernel=[shiftHavingComp@Form/shiftHaving:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `shiftReverseComp` | lean=[Form/shiftReverse=value -89] kernel=[Form/shiftReverse=cleared] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `shiftReverseComp` | lean=[shiftReverseComp@Form/shiftReverse:VALUE_ERROR/ERROR referenced=[Form/Stamp, Form/shiftReverse] fillToFix=[]] kernel=[shiftReverseComp@Form/shiftReverse:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `shiftReverseHavingComp` | lean=[Form/shiftReverseHaving=value 0] kernel=[Form/shiftReverseHaving=cleared] |
| `recursive-difference-effects-2026-10-08/request.json` | `filled` | `shiftReverseHavingComp` | lean=[shiftReverseHavingComp@Form/shiftReverseHaving:OMISSION_ERROR/ERROR] kernel=[shiftReverseHavingComp@Form/shiftReverseHaving:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `R_constructed` | lean=[] kernel=[R_constructed@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `R_constructedHaving` | lean=[R_constructedHaving@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[R_constructedHaving@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `R_constructedReverse` | lean=[] kernel=[R_constructedReverse@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `R_constructedReverseHaving` | lean=[R_constructedReverseHaving@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[R_constructedReverseHaving@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `R_direct` | lean=[] kernel=[R_direct@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `R_directHaving` | lean=[R_directHaving@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[R_directHaving@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `R_directReverse` | lean=[] kernel=[R_directReverse@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `R_directReverseHaving` | lean=[R_directReverseHaving@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[R_directReverseHaving@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `R_shift` | lean=[] kernel=[R_shift@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `R_shiftHaving` | lean=[R_shiftHaving@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[R_shiftHaving@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `R_shiftReverse` | lean=[] kernel=[R_shiftReverse@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `R_shiftReverseHaving` | lean=[R_shiftReverseHaving@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[R_shiftReverseHaving@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `call` | lean=[Form/Rows/Stamp:datumFormatFalsch, Form/Stamp:datumFormatFalsch] kernel=[Form/Rows/Stamp:datumFormatFalsch, Form/Stamp:datumFormatFalsch, Form/constructedReverse:berechnungsWertFehler, Form/constructedReverseHaving:berechnungsWertFehler, Form/directReverse:berechnungsWertFehler, Form/directReverseHaving:berechnungsWertFehler, Form/shiftReverse:berechnungsWertFehler, Form/shiftReverseHaving:berechnungsWertFehler] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `constructedComp` | lean=[] kernel=[constructedComp@Form/constructed:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `constructedHavingComp` | lean=[constructedHavingComp@Form/constructedHaving:OMISSION_ERROR/ERROR] kernel=[constructedHavingComp@Form/constructedHaving:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `constructedReverseComp` | lean=[] kernel=[constructedReverseComp@Form/constructedReverse:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `constructedReverseHavingComp` | lean=[constructedReverseHavingComp@Form/constructedReverseHaving:OMISSION_ERROR/ERROR] kernel=[constructedReverseHavingComp@Form/constructedReverseHaving:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `directComp` | lean=[] kernel=[directComp@Form/direct:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `directHavingComp` | lean=[directHavingComp@Form/directHaving:OMISSION_ERROR/ERROR] kernel=[directHavingComp@Form/directHaving:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `directReverseComp` | lean=[] kernel=[directReverseComp@Form/directReverse:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `directReverseHavingComp` | lean=[directReverseHavingComp@Form/directReverseHaving:OMISSION_ERROR/ERROR] kernel=[directReverseHavingComp@Form/directReverseHaving:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `shiftComp` | lean=[] kernel=[shiftComp@Form/shift:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `shiftHavingComp` | lean=[shiftHavingComp@Form/shiftHaving:OMISSION_ERROR/ERROR] kernel=[shiftHavingComp@Form/shiftHaving:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `shiftReverseComp` | lean=[] kernel=[shiftReverseComp@Form/shiftReverse:VALUE_ERROR/ERROR] |
| `recursive-difference-effects-2026-10-08/request.json` | `malformed` | `shiftReverseHavingComp` | lean=[shiftReverseHavingComp@Form/shiftReverseHaving:OMISSION_ERROR/ERROR] kernel=[shiftReverseHavingComp@Form/shiftReverseHaving:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `call` | lean=[] kernel=[Form/gap:berechnungsWertFehler, Form/gapAmount:berechnungsWertFehler, Form/leftGap:berechnungsWertFehler, Form/rightGap:berechnungsWertFehler] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `gapAmountComp` | lean=[Form/gapAmount=value 23] kernel=[Form/gapAmount=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `gapAmountComp` | lean=[gapAmountComp@Form/gapAmount:VALUE_ERROR/ERROR referenced=[Form/Stamp, Form/gapAmount] fillToFix=[]] kernel=[gapAmountComp@Form/gapAmount:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `gapAmountDepComp` | lean=[Form/gapAmountDep=value 24] kernel=[Form/gapAmountDep=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `gapAmountEq` | lean=[] kernel=[gapAmountEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `gapAmountGt` | lean=[gapAmountGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[Form/Anchor, Form/Stamp] fillToFix=[]] kernel=[gapAmountGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `gapAmountLt` | lean=[] kernel=[gapAmountLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `gapComp` | lean=[Form/gap=value 3] kernel=[Form/gap=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `gapComp` | lean=[gapComp@Form/gap:VALUE_ERROR/ERROR referenced=[Form/gap] fillToFix=[]] kernel=[gapComp@Form/gap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `gapDepComp` | lean=[Form/gapDep=value 4] kernel=[Form/gapDep=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `gapEq` | lean=[] kernel=[gapEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `gapGt` | lean=[gapGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[Form/Anchor] fillToFix=[]] kernel=[gapGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `gapLt` | lean=[] kernel=[gapLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `leftGapComp` | lean=[Form/leftGap=value 3] kernel=[Form/leftGap=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `leftGapComp` | lean=[leftGapComp@Form/leftGap:OMISSION_ERROR/ERROR] kernel=[leftGapComp@Form/leftGap:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `leftGapDepComp` | lean=[Form/leftGapDep=value 4] kernel=[Form/leftGapDep=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `leftGapEq` | lean=[] kernel=[leftGapEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `leftGapGt` | lean=[leftGapGt@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[leftGapGt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `leftGapLt` | lean=[] kernel=[leftGapLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `rightGapComp` | lean=[Form/rightGap=value 3] kernel=[Form/rightGap=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `rightGapComp` | lean=[rightGapComp@Form/rightGap:OMISSION_ERROR/ERROR] kernel=[rightGapComp@Form/rightGap:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `rightGapDepComp` | lean=[Form/rightGapDep=value 4] kernel=[Form/rightGapDep=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `rightGapEq` | lean=[] kernel=[rightGapEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `rightGapGt` | lean=[rightGapGt@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[rightGapGt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `rightGapLt` | lean=[] kernel=[rightGapLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `unrealStampComp` | lean=[Form/unrealStamp=value 3] kernel=[Form/unrealStamp=value 0] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `unrealStampDepComp` | lean=[Form/unrealStampDep=value 4] kernel=[Form/unrealStampDep=value 1] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `unrealStampEq` | lean=[] kernel=[unrealStampEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `amountOnlyEmpty` | `unrealStampLt` | lean=[] kernel=[unrealStampLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `call` | lean=[Form/Clock:datumFormatFalsch] kernel=[Form/Clock:datumFormatFalsch, Form/gap:berechnungsWertFehler, Form/gapAmount:berechnungsWertFehler, Form/leftGap:berechnungsWertFehler] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `gapAmountComp` | lean=[Form/gapAmount=value 23] kernel=[Form/gapAmount=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `gapAmountComp` | lean=[gapAmountComp@Form/gapAmount:VALUE_ERROR/ERROR referenced=[Form/Stamp, Form/gapAmount] fillToFix=[]] kernel=[gapAmountComp@Form/gapAmount:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `gapAmountDepComp` | lean=[Form/gapAmountDep=value 24] kernel=[Form/gapAmountDep=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `gapAmountEq` | lean=[] kernel=[gapAmountEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `gapAmountGt` | lean=[gapAmountGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[Form/Anchor, Form/Stamp] fillToFix=[]] kernel=[gapAmountGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `gapAmountLt` | lean=[] kernel=[gapAmountLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `gapComp` | lean=[Form/gap=value 3] kernel=[Form/gap=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `gapComp` | lean=[gapComp@Form/gap:VALUE_ERROR/ERROR referenced=[Form/gap] fillToFix=[]] kernel=[gapComp@Form/gap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `gapDepComp` | lean=[Form/gapDep=value 4] kernel=[Form/gapDep=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `gapEq` | lean=[] kernel=[gapEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `gapGt` | lean=[gapGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[Form/Anchor] fillToFix=[]] kernel=[gapGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `gapLt` | lean=[] kernel=[gapLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `leftGapComp` | lean=[] kernel=[leftGapComp@Form/leftGap:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `leftGapEq` | lean=[] kernel=[leftGapEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `leftGapGt` | lean=[] kernel=[leftGapGt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `leftGapLt` | lean=[] kernel=[leftGapLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `rightGapComp` | lean=[] kernel=[rightGapComp@Form/rightGap:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `rightGapEq` | lean=[] kernel=[rightGapEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `rightGapGt` | lean=[] kernel=[rightGapGt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `rightGapLt` | lean=[] kernel=[rightGapLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `unrealStampComp` | lean=[Form/unrealStamp=value 3] kernel=[Form/unrealStamp=value 0] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `unrealStampDepComp` | lean=[Form/unrealStampDep=value 4] kernel=[Form/unrealStampDep=value 1] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `unrealStampEq` | lean=[] kernel=[unrealStampEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badClock` | `unrealStampLt` | lean=[] kernel=[unrealStampLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `call` | lean=[Form/Stamp:datumFormatFalsch] kernel=[Form/Stamp:datumFormatFalsch, Form/gap:berechnungsWertFehler, Form/leftGap:berechnungsWertFehler, Form/rightGap:berechnungsWertFehler] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `gapAmountComp` | lean=[] kernel=[gapAmountComp@Form/gapAmount:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `gapAmountEq` | lean=[] kernel=[gapAmountEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `gapAmountGt` | lean=[] kernel=[gapAmountGt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `gapAmountLt` | lean=[] kernel=[gapAmountLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `gapComp` | lean=[Form/gap=value 3] kernel=[Form/gap=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `gapComp` | lean=[gapComp@Form/gap:VALUE_ERROR/ERROR referenced=[Form/gap] fillToFix=[]] kernel=[gapComp@Form/gap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `gapDepComp` | lean=[Form/gapDep=value 4] kernel=[Form/gapDep=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `gapEq` | lean=[] kernel=[gapEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `gapGt` | lean=[gapGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[Form/Anchor] fillToFix=[]] kernel=[gapGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `gapLt` | lean=[] kernel=[gapLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `leftGapComp` | lean=[Form/leftGap=value 8] kernel=[Form/leftGap=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `leftGapComp` | lean=[leftGapComp@Form/leftGap:VALUE_ERROR/ERROR referenced=[Form/Clock, Form/leftGap] fillToFix=[]] kernel=[leftGapComp@Form/leftGap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `leftGapDepComp` | lean=[Form/leftGapDep=value 9] kernel=[Form/leftGapDep=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `leftGapEq` | lean=[] kernel=[leftGapEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `leftGapGt` | lean=[leftGapGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[Form/Anchor, Form/Clock] fillToFix=[]] kernel=[leftGapGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `leftGapLt` | lean=[] kernel=[leftGapLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `rightGapComp` | lean=[Form/rightGap=value 8] kernel=[Form/rightGap=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `rightGapComp` | lean=[rightGapComp@Form/rightGap:VALUE_ERROR/ERROR referenced=[Form/Clock, Form/rightGap] fillToFix=[]] kernel=[rightGapComp@Form/rightGap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `rightGapDepComp` | lean=[Form/rightGapDep=value 9] kernel=[Form/rightGapDep=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `rightGapEq` | lean=[] kernel=[rightGapEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `rightGapGt` | lean=[rightGapGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[Form/Anchor, Form/Clock] fillToFix=[]] kernel=[rightGapGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `rightGapLt` | lean=[] kernel=[rightGapLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `unrealStampComp` | lean=[Form/unrealStamp=value 3] kernel=[Form/unrealStamp=value 0] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `unrealStampDepComp` | lean=[Form/unrealStampDep=value 4] kernel=[Form/unrealStampDep=value 1] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `unrealStampEq` | lean=[] kernel=[unrealStampEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `badStamp` | `unrealStampLt` | lean=[] kernel=[unrealStampLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `call` | lean=[] kernel=[Form/gap:berechnungsWertFehler, Form/gapAmount:berechnungsWertFehler, Form/leftGap:berechnungsWertFehler, Form/rightGap:berechnungsWertFehler] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `gapAmountComp` | lean=[Form/gapAmount=value 0] kernel=[Form/gapAmount=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `gapAmountComp` | lean=[gapAmountComp@Form/gapAmount:OMISSION_ERROR/ERROR] kernel=[gapAmountComp@Form/gapAmount:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `gapAmountDepComp` | lean=[Form/gapAmountDep=value 1] kernel=[Form/gapAmountDep=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `gapAmountEq` | lean=[gapAmountEq@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[gapAmountEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `gapAmountGt` | lean=[gapAmountGt@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[gapAmountGt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `gapAmountLt` | lean=[gapAmountLt@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[gapAmountLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `gapComp` | lean=[Form/gap=value 3] kernel=[Form/gap=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `gapComp` | lean=[gapComp@Form/gap:VALUE_ERROR/ERROR referenced=[Form/gap] fillToFix=[]] kernel=[gapComp@Form/gap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `gapDepComp` | lean=[Form/gapDep=value 4] kernel=[Form/gapDep=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `gapEq` | lean=[] kernel=[gapEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `gapGt` | lean=[gapGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[Form/Anchor] fillToFix=[]] kernel=[gapGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `gapLt` | lean=[] kernel=[gapLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `leftGapComp` | lean=[Form/leftGap=value 3] kernel=[Form/leftGap=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `leftGapComp` | lean=[leftGapComp@Form/leftGap:OMISSION_ERROR/ERROR] kernel=[leftGapComp@Form/leftGap:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `leftGapDepComp` | lean=[Form/leftGapDep=value 4] kernel=[Form/leftGapDep=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `leftGapEq` | lean=[] kernel=[leftGapEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `leftGapGt` | lean=[leftGapGt@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[leftGapGt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `leftGapLt` | lean=[] kernel=[leftGapLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `rightGapComp` | lean=[Form/rightGap=value 3] kernel=[Form/rightGap=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `rightGapComp` | lean=[rightGapComp@Form/rightGap:OMISSION_ERROR/ERROR] kernel=[rightGapComp@Form/rightGap:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `rightGapDepComp` | lean=[Form/rightGapDep=value 4] kernel=[Form/rightGapDep=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `rightGapEq` | lean=[] kernel=[rightGapEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `rightGapGt` | lean=[rightGapGt@Form/Anchor:OMISSION_ERROR/ERROR] kernel=[rightGapGt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `rightGapLt` | lean=[] kernel=[rightGapLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `unrealStampComp` | lean=[Form/unrealStamp=value 3] kernel=[Form/unrealStamp=value 0] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `unrealStampDepComp` | lean=[Form/unrealStampDep=value 4] kernel=[Form/unrealStampDep=value 1] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `unrealStampEq` | lean=[] kernel=[unrealStampEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `empty` | `unrealStampLt` | lean=[] kernel=[unrealStampLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `call` | lean=[] kernel=[Form/gap:berechnungsWertFehler, Form/gapAmount:berechnungsWertFehler, Form/leftGap:berechnungsWertFehler, Form/rightGap:berechnungsWertFehler] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `gapAmountComp` | lean=[Form/gapAmount=value 23] kernel=[Form/gapAmount=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `gapAmountComp` | lean=[gapAmountComp@Form/gapAmount:VALUE_ERROR/ERROR referenced=[Form/Stamp, Form/gapAmount] fillToFix=[]] kernel=[gapAmountComp@Form/gapAmount:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `gapAmountDepComp` | lean=[Form/gapAmountDep=value 24] kernel=[Form/gapAmountDep=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `gapAmountEq` | lean=[] kernel=[gapAmountEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `gapAmountGt` | lean=[gapAmountGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[Form/Anchor, Form/Stamp] fillToFix=[]] kernel=[gapAmountGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `gapAmountLt` | lean=[] kernel=[gapAmountLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `gapComp` | lean=[Form/gap=value 3] kernel=[Form/gap=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `gapComp` | lean=[gapComp@Form/gap:VALUE_ERROR/ERROR referenced=[Form/gap] fillToFix=[]] kernel=[gapComp@Form/gap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `gapDepComp` | lean=[Form/gapDep=value 4] kernel=[Form/gapDep=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `gapEq` | lean=[] kernel=[gapEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `gapGt` | lean=[gapGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[Form/Anchor] fillToFix=[]] kernel=[gapGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `gapLt` | lean=[] kernel=[gapLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `leftGapComp` | lean=[Form/leftGap=value 8] kernel=[Form/leftGap=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `leftGapComp` | lean=[leftGapComp@Form/leftGap:VALUE_ERROR/ERROR referenced=[Form/Clock, Form/leftGap] fillToFix=[]] kernel=[leftGapComp@Form/leftGap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `leftGapDepComp` | lean=[Form/leftGapDep=value 9] kernel=[Form/leftGapDep=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `leftGapEq` | lean=[] kernel=[leftGapEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `leftGapGt` | lean=[leftGapGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[Form/Anchor, Form/Clock] fillToFix=[]] kernel=[leftGapGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `leftGapLt` | lean=[] kernel=[leftGapLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `rightGapComp` | lean=[Form/rightGap=value 8] kernel=[Form/rightGap=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `rightGapComp` | lean=[rightGapComp@Form/rightGap:VALUE_ERROR/ERROR referenced=[Form/Clock, Form/rightGap] fillToFix=[]] kernel=[rightGapComp@Form/rightGap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `rightGapDepComp` | lean=[Form/rightGapDep=value 9] kernel=[Form/rightGapDep=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `rightGapEq` | lean=[] kernel=[rightGapEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `rightGapGt` | lean=[rightGapGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[Form/Anchor, Form/Clock] fillToFix=[]] kernel=[rightGapGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `rightGapLt` | lean=[] kernel=[rightGapLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `unrealStampComp` | lean=[Form/unrealStamp=value 3] kernel=[Form/unrealStamp=value 0] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `unrealStampDepComp` | lean=[Form/unrealStampDep=value 4] kernel=[Form/unrealStampDep=value 1] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `unrealStampEq` | lean=[] kernel=[unrealStampEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `filled` | `unrealStampLt` | lean=[] kernel=[unrealStampLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `call` | lean=[] kernel=[Form/gap:berechnungsWertFehler, Form/gapAmount:berechnungsWertFehler, Form/leftGap:berechnungsWertFehler, Form/rightGap:berechnungsWertFehler] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `gapAmountComp` | lean=[Form/gapAmount=value 23] kernel=[Form/gapAmount=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `gapAmountComp` | lean=[gapAmountComp@Form/gapAmount:VALUE_ERROR/ERROR referenced=[Form/Stamp, Form/gapAmount] fillToFix=[]] kernel=[gapAmountComp@Form/gapAmount:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `gapAmountDepComp` | lean=[Form/gapAmountDep=value 24] kernel=[Form/gapAmountDep=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `gapAmountEq` | lean=[] kernel=[gapAmountEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `gapAmountGt` | lean=[gapAmountGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[Form/Anchor, Form/Stamp] fillToFix=[]] kernel=[gapAmountGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `gapAmountLt` | lean=[] kernel=[gapAmountLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `gapComp` | lean=[Form/gap=value 3] kernel=[Form/gap=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `gapComp` | lean=[gapComp@Form/gap:VALUE_ERROR/ERROR referenced=[Form/gap] fillToFix=[]] kernel=[gapComp@Form/gap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `gapDepComp` | lean=[Form/gapDep=value 4] kernel=[Form/gapDep=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `gapEq` | lean=[] kernel=[gapEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `gapGt` | lean=[gapGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[Form/Anchor] fillToFix=[]] kernel=[gapGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `gapLt` | lean=[] kernel=[gapLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `leftGapComp` | lean=[Form/leftGap=value 8] kernel=[Form/leftGap=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `leftGapComp` | lean=[leftGapComp@Form/leftGap:VALUE_ERROR/ERROR referenced=[Form/Clock, Form/leftGap] fillToFix=[]] kernel=[leftGapComp@Form/leftGap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `leftGapDepComp` | lean=[Form/leftGapDep=value 9] kernel=[Form/leftGapDep=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `leftGapEq` | lean=[] kernel=[leftGapEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `leftGapGt` | lean=[leftGapGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[Form/Anchor, Form/Clock] fillToFix=[]] kernel=[leftGapGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `leftGapLt` | lean=[] kernel=[leftGapLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `rightGapComp` | lean=[Form/rightGap=value 8] kernel=[Form/rightGap=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `rightGapComp` | lean=[rightGapComp@Form/rightGap:VALUE_ERROR/ERROR referenced=[Form/Clock, Form/rightGap] fillToFix=[]] kernel=[rightGapComp@Form/rightGap:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `rightGapDepComp` | lean=[Form/rightGapDep=value 9] kernel=[Form/rightGapDep=cleared] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `rightGapEq` | lean=[] kernel=[rightGapEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `rightGapGt` | lean=[rightGapGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[Form/Anchor, Form/Clock] fillToFix=[]] kernel=[rightGapGt@Form/Anchor:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `rightGapLt` | lean=[] kernel=[rightGapLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `unrealStampComp` | lean=[Form/unrealStamp=value 3] kernel=[Form/unrealStamp=value 0] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `unrealStampDepComp` | lean=[Form/unrealStampDep=value 4] kernel=[Form/unrealStampDep=value 1] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `unrealStampEq` | lean=[] kernel=[unrealStampEq@Form/Anchor:VALUE_ERROR/ERROR] |
| `recursive-temporal-expression-2026-10-04/request-effects.json` | `highHour` | `unrealStampLt` | lean=[] kernel=[unrealStampLt@Form/Anchor:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `all-positive` | `Direct` | lean=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR, Direct@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Direct@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `all-positive` | `FalseAfterOmission` | lean=[FalseAfterOmission@Form/Rows/Flag:VALUE_ERROR/ERROR, FalseAfterOmission@Form/Rows[2]/Flag:VALUE_ERROR/ERROR, FalseAfterOmission@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[FalseAfterOmission@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `all-positive` | `GroupPrefix` | lean=[GroupPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR, GroupPrefix@Form/Rows[2]/Flag:VALUE_ERROR/ERROR, GroupPrefix@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[GroupPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `all-positive` | `Guard` | lean=[Guard@Form/Rows/Stamp:VALUE_ERROR/ERROR, Guard@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Guard@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Guard@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `all-positive` | `NumberGuard` | lean=[NumberGuard@Form/Rows/N:VALUE_ERROR/ERROR, NumberGuard@Form/Rows[2]/N:VALUE_ERROR/ERROR, NumberGuard@Form/Rows[3]/N:VALUE_ERROR/ERROR] kernel=[NumberGuard@Form/Rows/N:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `all-positive` | `NumberPrefix` | lean=[NumberPrefix@Form/Rows/N:VALUE_ERROR/ERROR, NumberPrefix@Form/Rows[2]/N:VALUE_ERROR/ERROR, NumberPrefix@Form/Rows[3]/N:VALUE_ERROR/ERROR] kernel=[NumberPrefix@Form/Rows/N:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `all-positive` | `Prefix` | lean=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR, Prefix@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Prefix@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `all-positive` | `PureGuard` | lean=[PureGuard@Form/Rows/Flag:VALUE_ERROR/ERROR, PureGuard@Form/Rows[2]/Flag:VALUE_ERROR/ERROR, PureGuard@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[PureGuard@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `all-positive` | `PurePrefixWithGroup` | lean=[PurePrefixWithGroup@Form/Rows/Flag:VALUE_ERROR/ERROR, PurePrefixWithGroup@Form/Rows[2]/Flag:VALUE_ERROR/ERROR, PurePrefixWithGroup@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[PurePrefixWithGroup@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `all-positive` | `StringPrefix` | lean=[StringPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR, StringPrefix@Form/Rows[2]/Flag:VALUE_ERROR/ERROR, StringPrefix@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[StringPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `all-positive` | `Unequal` | lean=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR, Unequal@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Unequal@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-first` | `Direct` | lean=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR, Direct@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Direct@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-first` | `FalseAfterOmission` | lean=[FalseAfterOmission@Form/Rows[2]/Flag:VALUE_ERROR/ERROR, FalseAfterOmission@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[FalseAfterOmission@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-first` | `GroupPrefix` | lean=[GroupPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR, GroupPrefix@Form/Rows[2]/Flag:VALUE_ERROR/ERROR, GroupPrefix@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[GroupPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-first` | `Guard` | lean=[Guard@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Guard@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Guard@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-first` | `NumberGuard` | lean=[NumberGuard@Form/Rows[2]/N:VALUE_ERROR/ERROR, NumberGuard@Form/Rows[3]/N:VALUE_ERROR/ERROR] kernel=[NumberGuard@Form/Rows/N:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-first` | `NumberPrefix` | lean=[NumberPrefix@Form/Rows/N:VALUE_ERROR/ERROR, NumberPrefix@Form/Rows[2]/N:VALUE_ERROR/ERROR, NumberPrefix@Form/Rows[3]/N:VALUE_ERROR/ERROR] kernel=[NumberPrefix@Form/Rows/N:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-first` | `Prefix` | lean=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR, Prefix@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Prefix@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-first` | `PureGuard` | lean=[PureGuard@Form/Rows[2]/Flag:VALUE_ERROR/ERROR, PureGuard@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[PureGuard@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-first` | `PurePrefixWithGroup` | lean=[PurePrefixWithGroup@Form/Rows[2]/Flag:VALUE_ERROR/ERROR, PurePrefixWithGroup@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[PurePrefixWithGroup@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-first` | `StringPrefix` | lean=[StringPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR, StringPrefix@Form/Rows[2]/Flag:VALUE_ERROR/ERROR, StringPrefix@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[StringPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-first` | `Unequal` | lean=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR, Unequal@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Unequal@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-last` | `Direct` | lean=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR, Direct@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Direct@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-last` | `FalseAfterOmission` | lean=[FalseAfterOmission@Form/Rows/Flag:VALUE_ERROR/ERROR, FalseAfterOmission@Form/Rows[2]/Flag:VALUE_ERROR/ERROR] kernel=[FalseAfterOmission@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-last` | `GroupPrefix` | lean=[GroupPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR, GroupPrefix@Form/Rows[2]/Flag:VALUE_ERROR/ERROR, GroupPrefix@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[GroupPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-last` | `Guard` | lean=[Guard@Form/Rows/Stamp:VALUE_ERROR/ERROR, Guard@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR] kernel=[Guard@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-last` | `NumberGuard` | lean=[NumberGuard@Form/Rows/N:VALUE_ERROR/ERROR, NumberGuard@Form/Rows[2]/N:VALUE_ERROR/ERROR] kernel=[NumberGuard@Form/Rows/N:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-last` | `NumberPrefix` | lean=[NumberPrefix@Form/Rows/N:VALUE_ERROR/ERROR, NumberPrefix@Form/Rows[2]/N:VALUE_ERROR/ERROR, NumberPrefix@Form/Rows[3]/N:VALUE_ERROR/ERROR] kernel=[NumberPrefix@Form/Rows/N:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-last` | `Prefix` | lean=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR, Prefix@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Prefix@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-last` | `PureGuard` | lean=[PureGuard@Form/Rows/Flag:VALUE_ERROR/ERROR, PureGuard@Form/Rows[2]/Flag:VALUE_ERROR/ERROR] kernel=[PureGuard@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-last` | `PurePrefixWithGroup` | lean=[PurePrefixWithGroup@Form/Rows/Flag:VALUE_ERROR/ERROR, PurePrefixWithGroup@Form/Rows[2]/Flag:VALUE_ERROR/ERROR] kernel=[PurePrefixWithGroup@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-last` | `StringPrefix` | lean=[StringPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR, StringPrefix@Form/Rows[2]/Flag:VALUE_ERROR/ERROR, StringPrefix@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[StringPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-last` | `Unequal` | lean=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR, Unequal@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Unequal@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-middle` | `Direct` | lean=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR, Direct@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Direct@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-middle` | `FalseAfterOmission` | lean=[FalseAfterOmission@Form/Rows/Flag:VALUE_ERROR/ERROR, FalseAfterOmission@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[FalseAfterOmission@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-middle` | `GroupPrefix` | lean=[GroupPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR, GroupPrefix@Form/Rows[2]/Flag:VALUE_ERROR/ERROR, GroupPrefix@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[GroupPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-middle` | `Guard` | lean=[Guard@Form/Rows/Stamp:VALUE_ERROR/ERROR, Guard@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Guard@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-middle` | `NumberGuard` | lean=[NumberGuard@Form/Rows/N:VALUE_ERROR/ERROR, NumberGuard@Form/Rows[3]/N:VALUE_ERROR/ERROR] kernel=[NumberGuard@Form/Rows/N:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-middle` | `NumberPrefix` | lean=[NumberPrefix@Form/Rows/N:VALUE_ERROR/ERROR, NumberPrefix@Form/Rows[2]/N:VALUE_ERROR/ERROR, NumberPrefix@Form/Rows[3]/N:VALUE_ERROR/ERROR] kernel=[NumberPrefix@Form/Rows/N:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-middle` | `Prefix` | lean=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR, Prefix@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Prefix@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-middle` | `PureGuard` | lean=[PureGuard@Form/Rows/Flag:VALUE_ERROR/ERROR, PureGuard@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[PureGuard@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-middle` | `PurePrefixWithGroup` | lean=[PurePrefixWithGroup@Form/Rows/Flag:VALUE_ERROR/ERROR, PurePrefixWithGroup@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[PurePrefixWithGroup@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-middle` | `StringPrefix` | lean=[StringPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR, StringPrefix@Form/Rows[2]/Flag:VALUE_ERROR/ERROR, StringPrefix@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[StringPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `failure-middle` | `Unequal` | lean=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR, Unequal@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Unequal@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `false-all` | `Direct` | lean=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR, Direct@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Direct@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `false-all` | `GroupPrefix` | lean=[GroupPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR, GroupPrefix@Form/Rows[2]/Flag:VALUE_ERROR/ERROR, GroupPrefix@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[GroupPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `false-all` | `NumberPrefix` | lean=[NumberPrefix@Form/Rows/N:VALUE_ERROR/ERROR, NumberPrefix@Form/Rows[2]/N:VALUE_ERROR/ERROR, NumberPrefix@Form/Rows[3]/N:VALUE_ERROR/ERROR] kernel=[NumberPrefix@Form/Rows/N:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `false-all` | `Prefix` | lean=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR, Prefix@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Prefix@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `false-all` | `StringPrefix` | lean=[StringPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR, StringPrefix@Form/Rows[2]/Flag:VALUE_ERROR/ERROR, StringPrefix@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[StringPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `false-all` | `Unequal` | lean=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR, Unequal@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Unequal@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `no-rows` | `Direct` | lean=[] kernel=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `no-rows` | `Prefix` | lean=[] kernel=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `no-rows` | `Unequal` | lean=[] kernel=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `unknown-all` | `Direct` | lean=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR, Direct@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Direct@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `unknown-all` | `GroupPrefix` | lean=[GroupPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR, GroupPrefix@Form/Rows[2]/Flag:VALUE_ERROR/ERROR, GroupPrefix@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[GroupPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `unknown-all` | `NumberPrefix` | lean=[NumberPrefix@Form/Rows/N:VALUE_ERROR/ERROR, NumberPrefix@Form/Rows[2]/N:VALUE_ERROR/ERROR, NumberPrefix@Form/Rows[3]/N:VALUE_ERROR/ERROR] kernel=[NumberPrefix@Form/Rows/N:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `unknown-all` | `Prefix` | lean=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR, Prefix@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Prefix@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `unknown-all` | `StringPrefix` | lean=[StringPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR, StringPrefix@Form/Rows[2]/Flag:VALUE_ERROR/ERROR, StringPrefix@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[StringPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `unknown-all` | `Unequal` | lean=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR, Unequal@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Unequal@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `unknown-first` | `Direct` | lean=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR, Direct@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Direct@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `unknown-first` | `FalseAfterOmission` | lean=[FalseAfterOmission@Form/Rows[2]/Flag:VALUE_ERROR/ERROR, FalseAfterOmission@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[FalseAfterOmission@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `unknown-first` | `GroupPrefix` | lean=[GroupPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR, GroupPrefix@Form/Rows[2]/Flag:VALUE_ERROR/ERROR, GroupPrefix@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[GroupPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `unknown-first` | `Guard` | lean=[Guard@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Guard@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Guard@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `unknown-first` | `NumberGuard` | lean=[NumberGuard@Form/Rows[2]/N:VALUE_ERROR/ERROR, NumberGuard@Form/Rows[3]/N:VALUE_ERROR/ERROR] kernel=[NumberGuard@Form/Rows/N:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `unknown-first` | `NumberPrefix` | lean=[NumberPrefix@Form/Rows/N:VALUE_ERROR/ERROR, NumberPrefix@Form/Rows[2]/N:VALUE_ERROR/ERROR, NumberPrefix@Form/Rows[3]/N:VALUE_ERROR/ERROR] kernel=[NumberPrefix@Form/Rows/N:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `unknown-first` | `Prefix` | lean=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR, Prefix@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Prefix@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `unknown-first` | `PureGuard` | lean=[PureGuard@Form/Rows[2]/Flag:VALUE_ERROR/ERROR, PureGuard@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[PureGuard@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `unknown-first` | `PurePrefixWithGroup` | lean=[PurePrefixWithGroup@Form/Rows[2]/Flag:VALUE_ERROR/ERROR, PurePrefixWithGroup@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[PurePrefixWithGroup@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `unknown-first` | `StringPrefix` | lean=[StringPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR, StringPrefix@Form/Rows[2]/Flag:VALUE_ERROR/ERROR, StringPrefix@Form/Rows[3]/Flag:VALUE_ERROR/ERROR] kernel=[StringPrefix@Form/Rows/Flag:VALUE_ERROR/ERROR] |
| `rule-classification-2026-10-04/request.json` | `unknown-first` | `Unequal` | lean=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR, Unequal@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Unequal@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `all-positive` | `Direct` | lean=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR, Direct@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Direct@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `all-positive` | `Guard` | lean=[Guard@Form/Rows/Stamp:VALUE_ERROR/ERROR, Guard@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Guard@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Guard@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `all-positive` | `Prefix` | lean=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR, Prefix@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Prefix@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `all-positive` | `Unequal` | lean=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR, Unequal@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Unequal@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `blank-first` | `Direct` | lean=[Direct@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Direct@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `blank-first` | `Guard` | lean=[Guard@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Guard@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `blank-first` | `Prefix` | lean=[Prefix@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Prefix@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `blank-first` | `Unequal` | lean=[Unequal@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Unequal@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `failure-first` | `Direct` | lean=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR, Direct@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Direct@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `failure-first` | `Guard` | lean=[Guard@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Guard@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Guard@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `failure-first` | `Prefix` | lean=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR, Prefix@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Prefix@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `failure-first` | `Unequal` | lean=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR, Unequal@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Unequal@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `failure-last` | `Direct` | lean=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR, Direct@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Direct@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `failure-last` | `Guard` | lean=[Guard@Form/Rows/Stamp:VALUE_ERROR/ERROR, Guard@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR] kernel=[Guard@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `failure-last` | `Prefix` | lean=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR, Prefix@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Prefix@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `failure-last` | `Unequal` | lean=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR, Unequal@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Unequal@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `failure-middle` | `Direct` | lean=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR, Direct@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Direct@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `failure-middle` | `Guard` | lean=[Guard@Form/Rows/Stamp:VALUE_ERROR/ERROR, Guard@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Guard@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `failure-middle` | `Prefix` | lean=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR, Prefix@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Prefix@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `failure-middle` | `Unequal` | lean=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR, Unequal@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Unequal@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `no-rows` | `Direct` | lean=[] kernel=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `no-rows` | `Prefix` | lean=[] kernel=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `no-rows` | `Unequal` | lean=[] kernel=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `unknown-first` | `Direct` | lean=[Direct@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Direct@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Direct@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `unknown-first` | `Guard` | lean=[Guard@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Guard@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `unknown-first` | `Prefix` | lean=[Prefix@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Prefix@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Prefix@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `rule-runtime-abort-2026-10-04/request.json` | `unknown-first` | `Unequal` | lean=[Unequal@Form/Rows[2]/Stamp:VALUE_ERROR/ERROR, Unequal@Form/Rows[3]/Stamp:VALUE_ERROR/ERROR] kernel=[Unequal@Form/Rows/Stamp:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `above-threshold` | `FirstComp` | lean=[FirstComp@Form/First:OMISSION_ERROR/ERROR] kernel=[FirstComp@Form/First:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `above-threshold` | `FirstComp` | lean=[Form/First=value 5] kernel=[Form/First=cleared] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `above-threshold` | `PairOverlapComp` | lean=[Form/PairOverlap=value 1] kernel=[Form/PairOverlap=cleared] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `above-threshold` | `PairOverlapComp` | lean=[PairOverlapComp@Form/PairOverlap:OMISSION_ERROR/ERROR] kernel=[PairOverlapComp@Form/PairOverlap:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `above-threshold` | `PairOverlapMonthComp` | lean=[Form/PairOverlapMonth=value 1] kernel=[Form/PairOverlapMonth=cleared] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `above-threshold` | `PairOverlapMonthComp` | lean=[PairOverlapMonthComp@Form/PairOverlapMonth:OMISSION_ERROR/ERROR] kernel=[PairOverlapMonthComp@Form/PairOverlapMonth:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `above-threshold` | `RowSumComp` | lean=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=value 5] kernel=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=cleared] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `above-threshold` | `RowSumComp` | lean=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer[2]/RowSum:OMISSION_ERROR/ERROR] kernel=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer/RowSum:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `above-threshold` | `ValueBoolComp` | lean=[Form/ValueBool=value 52] kernel=[Form/ValueBool=cleared] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `above-threshold` | `ValueBoolComp` | lean=[ValueBoolComp@Form/ValueBool:OMISSION_ERROR/ERROR] kernel=[ValueBoolComp@Form/ValueBool:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `above-threshold` | `ValueNumComp` | lean=[Form/ValueNum=value 52] kernel=[Form/ValueNum=cleared] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `above-threshold` | `ValueNumComp` | lean=[ValueNumComp@Form/ValueNum:OMISSION_ERROR/ERROR] kernel=[ValueNumComp@Form/ValueNum:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `above-threshold` | `ValueTextComp` | lean=[Form/ValueText=value 52] kernel=[Form/ValueText=cleared] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `above-threshold` | `ValueTextComp` | lean=[ValueTextComp@Form/ValueText:OMISSION_ERROR/ERROR] kernel=[ValueTextComp@Form/ValueText:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `above-threshold` | `call` | lean=[] kernel=[Form/First:berechnungsWertFehler, Form/Outer[2]/RowSum:berechnungsWertFehler, Form/PairOverlap:berechnungsWertFehler, Form/PairOverlapMonth:berechnungsWertFehler, Form/ValueBool:berechnungsWertFehler, Form/ValueNum:berechnungsWertFehler, Form/ValueText:berechnungsWertFehler] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `CountComp` | lean=[CountComp@Form/Count:OMISSION_ERROR/ERROR] kernel=[CountComp@Form/Count:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `CountComp` | lean=[Form/Count=value 1] kernel=[Form/Count=cleared] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `FirstComp` | lean=[FirstComp@Form/First:OMISSION_ERROR/ERROR] kernel=[FirstComp@Form/First:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `FirstComp` | lean=[Form/First=value 5] kernel=[Form/First=cleared] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `PairOverlapComp` | lean=[Form/PairOverlap=value 1] kernel=[Form/PairOverlap=cleared] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `PairOverlapComp` | lean=[PairOverlapComp@Form/PairOverlap:OMISSION_ERROR/ERROR] kernel=[PairOverlapComp@Form/PairOverlap:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `PairOverlapMonthComp` | lean=[Form/PairOverlapMonth=value 1] kernel=[Form/PairOverlapMonth=cleared] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `PairOverlapMonthComp` | lean=[PairOverlapMonthComp@Form/PairOverlapMonth:OMISSION_ERROR/ERROR] kernel=[PairOverlapMonthComp@Form/PairOverlapMonth:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `ResetComp` | lean=[Form/Reset=value 5] kernel=[Form/Reset=cleared] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `ResetComp` | lean=[ResetComp@Form/Reset:OMISSION_ERROR/ERROR] kernel=[ResetComp@Form/Reset:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `RowSumComp` | lean=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=value 5] kernel=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=cleared] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `RowSumComp` | lean=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer[2]/RowSum:OMISSION_ERROR/ERROR] kernel=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer/RowSum:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `ScalarOverlapComp` | lean=[Form/ScalarOverlap=value 1] kernel=[Form/ScalarOverlap=cleared] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `ScalarOverlapComp` | lean=[ScalarOverlapComp@Form/ScalarOverlap:OMISSION_ERROR/ERROR] kernel=[ScalarOverlapComp@Form/ScalarOverlap:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `ScalarOverlapMonthComp` | lean=[Form/ScalarOverlapMonth=value 1] kernel=[Form/ScalarOverlapMonth=cleared] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `ScalarOverlapMonthComp` | lean=[ScalarOverlapMonthComp@Form/ScalarOverlapMonth:OMISSION_ERROR/ERROR] kernel=[ScalarOverlapMonthComp@Form/ScalarOverlapMonth:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `SumComp` | lean=[Form/Sum=value 5] kernel=[Form/Sum=cleared] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `SumComp` | lean=[SumComp@Form/Sum:OMISSION_ERROR/ERROR] kernel=[SumComp@Form/Sum:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `ValueBoolComp` | lean=[Form/ValueBool=value 52] kernel=[Form/ValueBool=cleared] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `ValueBoolComp` | lean=[ValueBoolComp@Form/ValueBool:OMISSION_ERROR/ERROR] kernel=[ValueBoolComp@Form/ValueBool:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `ValueNumComp` | lean=[Form/ValueNum=value 52] kernel=[Form/ValueNum=cleared] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `ValueNumComp` | lean=[ValueNumComp@Form/ValueNum:OMISSION_ERROR/ERROR] kernel=[ValueNumComp@Form/ValueNum:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `ValueTextComp` | lean=[Form/ValueText=value 52] kernel=[Form/ValueText=cleared] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `ValueTextComp` | lean=[ValueTextComp@Form/ValueText:OMISSION_ERROR/ERROR] kernel=[ValueTextComp@Form/ValueText:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request-policy.json` | `blank-tail` | `call` | lean=[] kernel=[Form/Count:berechnungsWertFehler, Form/First:berechnungsWertFehler, Form/Outer[2]/RowSum:berechnungsWertFehler, Form/PairOverlap:berechnungsWertFehler, Form/PairOverlapMonth:berechnungsWertFehler, Form/Reset:berechnungsWertFehler, Form/ScalarOverlap:berechnungsWertFehler, Form/ScalarOverlapMonth:berechnungsWertFehler, Form/Sum:berechnungsWertFehler, Form/ValueBool:berechnungsWertFehler, Form/ValueNum:berechnungsWertFehler, Form/ValueText:berechnungsWertFehler] |
| `sparse-filter-traversal-2026-10-10/request.json` | `above-threshold` | `FirstComp` | lean=[FirstComp@Form/First:OMISSION_ERROR/ERROR] kernel=[FirstComp@Form/First:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `above-threshold` | `FirstComp` | lean=[Form/First=value 5] kernel=[Form/First=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `above-threshold` | `RowSumComp` | lean=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=value 5] kernel=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `above-threshold` | `RowSumComp` | lean=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer[2]/RowSum:OMISSION_ERROR/ERROR] kernel=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer/RowSum:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `above-threshold` | `call` | lean=[] kernel=[Form/First:berechnungsWertFehler, Form/Outer[2]/RowSum:berechnungsWertFehler] |
| `sparse-filter-traversal-2026-10-10/request.json` | `at-threshold` | `CountComp` | lean=[CountComp@Form/Count:OMISSION_ERROR/ERROR] kernel=[CountComp@Form/Count:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `at-threshold` | `CountComp` | lean=[Form/Count=value 1] kernel=[Form/Count=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `at-threshold` | `FirstComp` | lean=[FirstComp@Form/First:OMISSION_ERROR/ERROR] kernel=[FirstComp@Form/First:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `at-threshold` | `FirstComp` | lean=[Form/First=value 5] kernel=[Form/First=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `at-threshold` | `ResetComp` | lean=[Form/Reset=value 5] kernel=[Form/Reset=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `at-threshold` | `ResetComp` | lean=[ResetComp@Form/Reset:OMISSION_ERROR/ERROR] kernel=[ResetComp@Form/Reset:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `at-threshold` | `RowSumComp` | lean=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=value 5] kernel=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `at-threshold` | `RowSumComp` | lean=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer[2]/RowSum:OMISSION_ERROR/ERROR] kernel=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer/RowSum:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `at-threshold` | `SumComp` | lean=[Form/Sum=value 5] kernel=[Form/Sum=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `at-threshold` | `SumComp` | lean=[SumComp@Form/Sum:OMISSION_ERROR/ERROR] kernel=[SumComp@Form/Sum:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `at-threshold` | `call` | lean=[] kernel=[Form/Count:berechnungsWertFehler, Form/First:berechnungsWertFehler, Form/Outer[2]/RowSum:berechnungsWertFehler, Form/Reset:berechnungsWertFehler, Form/Sum:berechnungsWertFehler] |
| `sparse-filter-traversal-2026-10-10/request.json` | `below-threshold` | `CountComp` | lean=[CountComp@Form/Count:OMISSION_ERROR/ERROR] kernel=[CountComp@Form/Count:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `below-threshold` | `CountComp` | lean=[Form/Count=value 1] kernel=[Form/Count=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `below-threshold` | `FirstComp` | lean=[FirstComp@Form/First:OMISSION_ERROR/ERROR] kernel=[FirstComp@Form/First:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `below-threshold` | `FirstComp` | lean=[Form/First=value 5] kernel=[Form/First=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `below-threshold` | `ResetComp` | lean=[Form/Reset=value 5] kernel=[Form/Reset=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `below-threshold` | `ResetComp` | lean=[ResetComp@Form/Reset:OMISSION_ERROR/ERROR] kernel=[ResetComp@Form/Reset:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `below-threshold` | `RowSumComp` | lean=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=value 5] kernel=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `below-threshold` | `RowSumComp` | lean=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer[2]/RowSum:OMISSION_ERROR/ERROR] kernel=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer/RowSum:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `below-threshold` | `SumComp` | lean=[Form/Sum=value 5] kernel=[Form/Sum=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `below-threshold` | `SumComp` | lean=[SumComp@Form/Sum:OMISSION_ERROR/ERROR] kernel=[SumComp@Form/Sum:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `below-threshold` | `call` | lean=[] kernel=[Form/Count:berechnungsWertFehler, Form/First:berechnungsWertFehler, Form/Outer[2]/RowSum:berechnungsWertFehler, Form/Reset:berechnungsWertFehler, Form/Sum:berechnungsWertFehler] |
| `sparse-filter-traversal-2026-10-10/request.json` | `explicit-blank` | `CountComp` | lean=[CountComp@Form/Count:OMISSION_ERROR/ERROR] kernel=[CountComp@Form/Count:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `explicit-blank` | `CountComp` | lean=[Form/Count=value 1] kernel=[Form/Count=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `explicit-blank` | `FirstComp` | lean=[FirstComp@Form/First:OMISSION_ERROR/ERROR] kernel=[FirstComp@Form/First:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `explicit-blank` | `FirstComp` | lean=[Form/First=value 5] kernel=[Form/First=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `explicit-blank` | `ResetComp` | lean=[Form/Reset=value 5] kernel=[Form/Reset=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `explicit-blank` | `ResetComp` | lean=[ResetComp@Form/Reset:OMISSION_ERROR/ERROR] kernel=[ResetComp@Form/Reset:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `explicit-blank` | `RowSumComp` | lean=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=value 5] kernel=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `explicit-blank` | `RowSumComp` | lean=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer[2]/RowSum:OMISSION_ERROR/ERROR] kernel=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer/RowSum:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `explicit-blank` | `SumComp` | lean=[Form/Sum=value 5] kernel=[Form/Sum=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `explicit-blank` | `SumComp` | lean=[SumComp@Form/Sum:OMISSION_ERROR/ERROR] kernel=[SumComp@Form/Sum:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `explicit-blank` | `call` | lean=[] kernel=[Form/Count:berechnungsWertFehler, Form/First:berechnungsWertFehler, Form/Outer[2]/RowSum:berechnungsWertFehler, Form/Reset:berechnungsWertFehler, Form/Sum:berechnungsWertFehler] |
| `sparse-filter-traversal-2026-10-10/request.json` | `foreign-prefix` | `CountComp` | lean=[CountComp@Form/Count:OMISSION_ERROR/ERROR] kernel=[CountComp@Form/Count:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `foreign-prefix` | `CountComp` | lean=[Form/Count=value 1] kernel=[Form/Count=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `foreign-prefix` | `FirstComp` | lean=[FirstComp@Form/First:OMISSION_ERROR/ERROR] kernel=[FirstComp@Form/First:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `foreign-prefix` | `FirstComp` | lean=[Form/First=value 5] kernel=[Form/First=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `foreign-prefix` | `ResetComp` | lean=[Form/Reset=value 5] kernel=[Form/Reset=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `foreign-prefix` | `ResetComp` | lean=[ResetComp@Form/Reset:OMISSION_ERROR/ERROR] kernel=[ResetComp@Form/Reset:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `foreign-prefix` | `RowSumComp` | lean=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=value 5] kernel=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `foreign-prefix` | `RowSumComp` | lean=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer[2]/RowSum:OMISSION_ERROR/ERROR] kernel=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer/RowSum:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `foreign-prefix` | `SumComp` | lean=[Form/Sum=value 5] kernel=[Form/Sum=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `foreign-prefix` | `SumComp` | lean=[SumComp@Form/Sum:OMISSION_ERROR/ERROR] kernel=[SumComp@Form/Sum:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `foreign-prefix` | `call` | lean=[] kernel=[Form/Count:berechnungsWertFehler, Form/First:berechnungsWertFehler, Form/Outer[2]/RowSum:berechnungsWertFehler, Form/Reset:berechnungsWertFehler, Form/Sum:berechnungsWertFehler] |
| `sparse-filter-traversal-2026-10-10/request.json` | `initial-search` | `FirstComp` | lean=[FirstComp@Form/First:OMISSION_ERROR/ERROR] kernel=[FirstComp@Form/First:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `initial-search` | `FirstComp` | lean=[Form/First=value 5] kernel=[Form/First=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `initial-search` | `ResetComp` | lean=[Form/Reset=value 0] kernel=[Form/Reset=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `initial-search` | `ResetComp` | lean=[ResetComp@Form/Reset:OMISSION_ERROR/ERROR] kernel=[ResetComp@Form/Reset:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `initial-search` | `RowSumComp` | lean=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=value 5] kernel=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `initial-search` | `RowSumComp` | lean=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer[2]/RowSum:OMISSION_ERROR/ERROR] kernel=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer/RowSum:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `initial-search` | `call` | lean=[] kernel=[Form/First:berechnungsWertFehler, Form/Outer[2]/RowSum:berechnungsWertFehler, Form/Reset:berechnungsWertFehler] |
| `sparse-filter-traversal-2026-10-10/request.json` | `reset-search` | `FirstComp` | lean=[FirstComp@Form/First:OMISSION_ERROR/ERROR] kernel=[FirstComp@Form/First:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `reset-search` | `FirstComp` | lean=[Form/First=value 5] kernel=[Form/First=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `reset-search` | `ResetComp` | lean=[Form/Reset=value 0] kernel=[Form/Reset=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `reset-search` | `ResetComp` | lean=[ResetComp@Form/Reset:OMISSION_ERROR/ERROR] kernel=[ResetComp@Form/Reset:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `reset-search` | `RowSumComp` | lean=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=value 5] kernel=[Form/Outer/RowSum=value 0, Form/Outer[2]/RowSum=cleared] |
| `sparse-filter-traversal-2026-10-10/request.json` | `reset-search` | `RowSumComp` | lean=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer[2]/RowSum:OMISSION_ERROR/ERROR] kernel=[RowSumComp@Form/Outer/RowSum:OMISSION_ERROR/ERROR, RowSumComp@Form/Outer/RowSum:VALUE_ERROR/ERROR] |
| `sparse-filter-traversal-2026-10-10/request.json` | `reset-search` | `call` | lean=[] kernel=[Form/First:berechnungsWertFehler, Form/Outer[2]/RowSum:berechnungsWertFehler, Form/Reset:berechnungsWertFehler] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-clock` | `AfterClockComp` | lean=[Form/AfterClock=cleared] kernel=[Form/AfterClock=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-clock` | `AfterComponentsComp` | lean=[Form/AfterComponents=cleared] kernel=[Form/AfterComponents=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-clock` | `ClockComp` | lean=[ClockComp@Form/OutClock:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-clock` | `ClockComp` | lean=[Form/OutClock=value 2024-03-31T03:00:00] kernel=[Form/OutClock=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-clock` | `ClockNotEqual` | lean=[ClockNotEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-clock` | `ComponentsComp` | lean=[ComponentsComp@Form/OutComponents:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-clock` | `ComponentsComp` | lean=[Form/OutComponents=value 2024-03-31T03:00:00] kernel=[Form/OutComponents=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-clock` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-clock` | `ConstructedMin` | lean=[] kernel=[ConstructedMin@Form/Z:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-clock` | `GapAfterPartialComp` | lean=[Form/OutGapAfterPartial=value 2024-03-01T03:30:00] kernel=[Form/OutGapAfterPartial=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-clock` | `GapAfterPartialComp` | lean=[GapAfterPartialComp@Form/OutGapAfterPartial:VALUE_ERROR/ERROR referenced=[Form/OutGapAfterPartial, Form/P] fillToFix=[]] kernel=[GapAfterPartialComp@Form/OutGapAfterPartial:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-clock` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Z:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-clock` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Z:VALUE_ERROR/ERROR referenced=[Form/P, Form/Z] fillToFix=[]] kernel=[GapAfterPartialNotEqual@Form/Z:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-clock` | `call` | lean=[Form/T:datumFormatFalsch] kernel=[Form/OutGapAfterPartial:berechnungsWertFehler, Form/T:datumFormatFalsch] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-date` | `AfterComponentsComp` | lean=[Form/AfterComponents=cleared] kernel=[Form/AfterComponents=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-date` | `AfterMDComp` | lean=[Form/AfterMD=cleared] kernel=[Form/AfterMD=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-date` | `AfterRangeComp` | lean=[Form/AfterRange=cleared] kernel=[Form/AfterRange=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-date` | `AfterTodayComp` | lean=[Form/AfterToday=cleared] kernel=[Form/AfterToday=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-date` | `ComponentsComp` | lean=[ComponentsComp@Form/OutComponents:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-date` | `ComponentsComp` | lean=[Form/OutComponents=value 2024-03-31T03:00:00] kernel=[Form/OutComponents=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-date` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-date` | `GapAfterPartialComp` | lean=[] kernel=[GapAfterPartialComp@Form/OutGapAfterPartial:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-date` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Z:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-date` | `GapAfterPartialNotEqual` | lean=[] kernel=[GapAfterPartialNotEqual@Form/Z:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-date` | `MDComp` | lean=[Form/OutMD=value 2024-03-31T03:30:00] kernel=[Form/OutMD=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-date` | `MDComp` | lean=[MDComp@Form/OutMD:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-date` | `MDEqual` | lean=[MDEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-date` | `RangeComp` | lean=[Form/OutRange=value 2024-03-31T03:30:00] kernel=[Form/OutRange=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-date` | `RangeComp` | lean=[RangeComp@Form/OutRange:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-date` | `RangeEqual` | lean=[RangeEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-date` | `TodayComp` | lean=[Form/OutToday=value 2024-03-31T03:30:00] kernel=[Form/OutToday=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-date` | `TodayComp` | lean=[TodayComp@Form/OutToday:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `bad-date` | `TodayEqual` | lean=[TodayEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `AfterClockComp` | lean=[Form/AfterClock=cleared] kernel=[Form/AfterClock=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `AfterComponentsComp` | lean=[Form/AfterComponents=cleared] kernel=[Form/AfterComponents=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `AfterFieldsComp` | lean=[Form/AfterFields=cleared] kernel=[Form/AfterFields=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `AfterGivenComp` | lean=[Form/AfterGiven=cleared] kernel=[Form/AfterGiven=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `AfterHourAfterComp` | lean=[Form/AfterHourAfter=cleared] kernel=[Form/AfterHourAfter=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `AfterMDComp` | lean=[Form/AfterMD=cleared] kernel=[Form/AfterMD=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `AfterPartialLastComp` | lean=[Form/AfterPartialLast=cleared] kernel=[Form/AfterPartialLast=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `AfterRangeComp` | lean=[Form/AfterRange=cleared] kernel=[Form/AfterRange=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `AfterTodayComp` | lean=[Form/AfterToday=cleared] kernel=[Form/AfterToday=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `ClockComp` | lean=[ClockComp@Form/OutClock:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `ClockComp` | lean=[Form/OutClock=value 2024-03-31T03:00:00] kernel=[Form/OutClock=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `ClockNotEqual` | lean=[ClockNotEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `ComponentsComp` | lean=[ComponentsComp@Form/OutComponents:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `ComponentsComp` | lean=[Form/OutComponents=value 2024-03-31T03:00:00] kernel=[Form/OutComponents=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `ConstructedMin` | lean=[] kernel=[ConstructedMin@Form/Z:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `FieldsComp` | lean=[FieldsComp@Form/OutFields:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `FieldsComp` | lean=[Form/OutFields=value 2024-03-31T03:30:00] kernel=[Form/OutFields=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `FieldsEqual` | lean=[FieldsEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `GapAfterPartialComp` | lean=[Form/OutGapAfterPartial=value 2024-03-01T03:30:00] kernel=[Form/OutGapAfterPartial=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `GapAfterPartialComp` | lean=[GapAfterPartialComp@Form/OutGapAfterPartial:VALUE_ERROR/ERROR referenced=[Form/OutGapAfterPartial, Form/P] fillToFix=[]] kernel=[GapAfterPartialComp@Form/OutGapAfterPartial:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Z:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Z:VALUE_ERROR/ERROR referenced=[Form/P, Form/Z] fillToFix=[]] kernel=[GapAfterPartialNotEqual@Form/Z:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `GivenComp` | lean=[Form/OutGiven=value 2024-03-31T03:30:00] kernel=[Form/OutGiven=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `GivenComp` | lean=[GivenComp@Form/OutGiven:OMISSION_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `GivenEqual` | lean=[GivenEqual@Form/Z:OMISSION_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `HourAfterComp` | lean=[Form/OutHourAfter=value 2024-03-31T04:30:00] kernel=[Form/OutHourAfter=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `HourAfterComp` | lean=[HourAfterComp@Form/OutHourAfter:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `HourAfterNotEqual` | lean=[HourAfterNotEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `MDComp` | lean=[Form/OutMD=value 2024-03-31T03:30:00] kernel=[Form/OutMD=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `MDComp` | lean=[MDComp@Form/OutMD:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `MDEqual` | lean=[MDEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `PartialLastComp` | lean=[Form/OutPartialLast=value 2024-03-31T03:30:00] kernel=[Form/OutPartialLast=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `PartialLastComp` | lean=[PartialLastComp@Form/OutPartialLast:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `PartialLastEqual` | lean=[PartialLastEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `RangeComp` | lean=[Form/OutRange=value 2024-03-31T03:30:00] kernel=[Form/OutRange=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `RangeComp` | lean=[RangeComp@Form/OutRange:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `RangeEqual` | lean=[RangeEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `TodayComp` | lean=[Form/OutToday=value 2024-03-31T03:30:00] kernel=[Form/OutToday=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `TodayComp` | lean=[TodayComp@Form/OutToday:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `TodayEqual` | lean=[TodayEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-amount` | `call` | lean=[] kernel=[Form/OutGapAfterPartial:berechnungsWertFehler] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-clock` | `GapAfterPartialComp` | lean=[Form/OutGapAfterPartial=value 2024-03-01T03:30:00] kernel=[Form/OutGapAfterPartial=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-clock` | `GapAfterPartialComp` | lean=[GapAfterPartialComp@Form/OutGapAfterPartial:VALUE_ERROR/ERROR referenced=[Form/OutGapAfterPartial, Form/P] fillToFix=[]] kernel=[GapAfterPartialComp@Form/OutGapAfterPartial:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-clock` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Z:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-clock` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Z:VALUE_ERROR/ERROR referenced=[Form/P, Form/Z] fillToFix=[]] kernel=[GapAfterPartialNotEqual@Form/Z:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-clock` | `call` | lean=[] kernel=[Form/OutGapAfterPartial:berechnungsWertFehler] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date` | `AfterComponentsComp` | lean=[Form/AfterComponents=cleared] kernel=[Form/AfterComponents=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date` | `AfterGapAfterPartialComp` | lean=[Form/AfterGapAfterPartial=value 1] kernel=[Form/AfterGapAfterPartial=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date` | `AfterMDComp` | lean=[Form/AfterMD=cleared] kernel=[Form/AfterMD=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date` | `AfterRangeComp` | lean=[Form/AfterRange=cleared] kernel=[Form/AfterRange=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date` | `AfterTodayComp` | lean=[Form/AfterToday=cleared] kernel=[Form/AfterToday=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date` | `ComponentsComp` | lean=[ComponentsComp@Form/OutComponents:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date` | `ComponentsComp` | lean=[Form/OutComponents=value 2024-03-31T03:00:00] kernel=[Form/OutComponents=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date` | `GapAfterPartialComp` | lean=[] kernel=[GapAfterPartialComp@Form/OutGapAfterPartial:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Z:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date` | `GapAfterPartialNotEqual` | lean=[] kernel=[GapAfterPartialNotEqual@Form/Z:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date` | `MDComp` | lean=[Form/OutMD=value 2024-03-31T03:30:00] kernel=[Form/OutMD=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date` | `MDComp` | lean=[MDComp@Form/OutMD:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date` | `MDEqual` | lean=[MDEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date` | `RangeComp` | lean=[Form/OutRange=value 2024-03-31T03:30:00] kernel=[Form/OutRange=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date` | `RangeComp` | lean=[RangeComp@Form/OutRange:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date` | `RangeEqual` | lean=[RangeEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date` | `TodayComp` | lean=[Form/OutToday=value 2024-03-31T03:30:00] kernel=[Form/OutToday=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date` | `TodayComp` | lean=[TodayComp@Form/OutToday:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date` | `TodayEqual` | lean=[TodayEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date` | `call` | lean=[] kernel=[Form/OutGapAfterPartial:berechnungsWertFehler] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date-bad-clock` | `AfterComponentsComp` | lean=[Form/AfterComponents=cleared] kernel=[Form/AfterComponents=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date-bad-clock` | `AfterGapAfterPartialComp` | lean=[Form/AfterGapAfterPartial=value 1] kernel=[Form/AfterGapAfterPartial=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date-bad-clock` | `ComponentsComp` | lean=[ComponentsComp@Form/OutComponents:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date-bad-clock` | `ComponentsComp` | lean=[Form/OutComponents=value 2024-03-31T03:00:00] kernel=[Form/OutComponents=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date-bad-clock` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date-bad-clock` | `GapAfterPartialComp` | lean=[] kernel=[GapAfterPartialComp@Form/OutGapAfterPartial:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date-bad-clock` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Z:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date-bad-clock` | `GapAfterPartialNotEqual` | lean=[] kernel=[GapAfterPartialNotEqual@Form/Z:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `empty-date-bad-clock` | `call` | lean=[Form/T:datumFormatFalsch] kernel=[Form/OutGapAfterPartial:berechnungsWertFehler, Form/T:datumFormatFalsch] |
| `stamp-construction-2026-10-04/berlin/request.json` | `fold` | `AfterComponentsComp` | lean=[Form/AfterComponents=cleared] kernel=[Form/AfterComponents=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `fold` | `AfterMDComp` | lean=[Form/AfterMD=cleared] kernel=[Form/AfterMD=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `fold` | `AfterRangeComp` | lean=[Form/AfterRange=cleared] kernel=[Form/AfterRange=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `fold` | `AfterTodayComp` | lean=[Form/AfterToday=cleared] kernel=[Form/AfterToday=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `fold` | `ComponentsComp` | lean=[ComponentsComp@Form/OutComponents:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `fold` | `ComponentsComp` | lean=[Form/OutComponents=value 2024-03-31T03:00:00] kernel=[Form/OutComponents=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `fold` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `fold` | `GapAfterPartialComp` | lean=[Form/OutGapAfterPartial=value 2024-10-01T03:30:00] kernel=[Form/OutGapAfterPartial=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `fold` | `GapAfterPartialComp` | lean=[GapAfterPartialComp@Form/OutGapAfterPartial:VALUE_ERROR/ERROR referenced=[Form/OutGapAfterPartial, Form/P] fillToFix=[]] kernel=[GapAfterPartialComp@Form/OutGapAfterPartial:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `stamp-construction-2026-10-04/berlin/request.json` | `fold` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Z:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `fold` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Z:VALUE_ERROR/ERROR referenced=[Form/P, Form/Z] fillToFix=[]] kernel=[GapAfterPartialNotEqual@Form/Z:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `stamp-construction-2026-10-04/berlin/request.json` | `fold` | `HourAfterComp` | lean=[Form/OutHourAfter=value 2024-10-27T02:30:00] kernel=[Form/OutHourAfter=value 2024-10-27T03:30:00] |
| `stamp-construction-2026-10-04/berlin/request.json` | `fold` | `MDComp` | lean=[Form/OutMD=value 2024-03-31T03:30:00] kernel=[Form/OutMD=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `fold` | `MDComp` | lean=[MDComp@Form/OutMD:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `fold` | `MDNotEqual` | lean=[MDNotEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `fold` | `RangeComp` | lean=[Form/OutRange=value 2024-03-31T03:30:00] kernel=[Form/OutRange=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `fold` | `RangeComp` | lean=[RangeComp@Form/OutRange:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `fold` | `RangeNotEqual` | lean=[RangeNotEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `fold` | `TodayComp` | lean=[Form/OutToday=value 2024-03-31T03:30:00] kernel=[Form/OutToday=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `fold` | `TodayComp` | lean=[TodayComp@Form/OutToday:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `fold` | `TodayNotEqual` | lean=[TodayNotEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `fold` | `call` | lean=[] kernel=[Form/OutGapAfterPartial:berechnungsWertFehler] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `AfterClockComp` | lean=[Form/AfterClock=cleared] kernel=[Form/AfterClock=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `AfterComponentsComp` | lean=[Form/AfterComponents=cleared] kernel=[Form/AfterComponents=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `AfterFieldsComp` | lean=[Form/AfterFields=cleared] kernel=[Form/AfterFields=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `AfterGivenComp` | lean=[Form/AfterGiven=cleared] kernel=[Form/AfterGiven=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `AfterHourAfterComp` | lean=[Form/AfterHourAfter=cleared] kernel=[Form/AfterHourAfter=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `AfterMDComp` | lean=[Form/AfterMD=cleared] kernel=[Form/AfterMD=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `AfterPartialLastComp` | lean=[Form/AfterPartialLast=cleared] kernel=[Form/AfterPartialLast=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `AfterRangeComp` | lean=[Form/AfterRange=cleared] kernel=[Form/AfterRange=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `AfterTodayComp` | lean=[Form/AfterToday=cleared] kernel=[Form/AfterToday=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `ClockComp` | lean=[ClockComp@Form/OutClock:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `ClockComp` | lean=[Form/OutClock=value 2024-03-31T03:00:00] kernel=[Form/OutClock=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `ClockNotEqual` | lean=[ClockNotEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `ComponentsComp` | lean=[ComponentsComp@Form/OutComponents:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `ComponentsComp` | lean=[Form/OutComponents=value 2024-03-31T03:00:00] kernel=[Form/OutComponents=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `ConstructedMin` | lean=[] kernel=[ConstructedMin@Form/Z:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `FieldsComp` | lean=[FieldsComp@Form/OutFields:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `FieldsComp` | lean=[Form/OutFields=value 2024-03-31T03:30:00] kernel=[Form/OutFields=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `FieldsEqual` | lean=[FieldsEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `GapAfterPartialComp` | lean=[Form/OutGapAfterPartial=value 2024-03-01T03:30:00] kernel=[Form/OutGapAfterPartial=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `GapAfterPartialComp` | lean=[GapAfterPartialComp@Form/OutGapAfterPartial:VALUE_ERROR/ERROR referenced=[Form/OutGapAfterPartial, Form/P] fillToFix=[]] kernel=[GapAfterPartialComp@Form/OutGapAfterPartial:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Z:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Z:VALUE_ERROR/ERROR referenced=[Form/P, Form/Z] fillToFix=[]] kernel=[GapAfterPartialNotEqual@Form/Z:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `GivenComp` | lean=[Form/OutGiven=value 2024-03-31T03:30:00] kernel=[Form/OutGiven=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `GivenComp` | lean=[GivenComp@Form/OutGiven:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `GivenEqual` | lean=[GivenEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `HourAfterComp` | lean=[Form/OutHourAfter=value 2024-03-31T04:30:00] kernel=[Form/OutHourAfter=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `HourAfterComp` | lean=[HourAfterComp@Form/OutHourAfter:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `HourAfterNotEqual` | lean=[HourAfterNotEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `MDComp` | lean=[Form/OutMD=value 2024-03-31T03:30:00] kernel=[Form/OutMD=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `MDComp` | lean=[MDComp@Form/OutMD:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `MDEqual` | lean=[MDEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `PartialLastComp` | lean=[Form/OutPartialLast=value 2024-03-31T03:30:00] kernel=[Form/OutPartialLast=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `PartialLastComp` | lean=[PartialLastComp@Form/OutPartialLast:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `PartialLastEqual` | lean=[PartialLastEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `RangeComp` | lean=[Form/OutRange=value 2024-03-31T03:30:00] kernel=[Form/OutRange=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `RangeComp` | lean=[RangeComp@Form/OutRange:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `RangeEqual` | lean=[RangeEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `TodayComp` | lean=[Form/OutToday=value 2024-03-31T03:30:00] kernel=[Form/OutToday=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `TodayComp` | lean=[TodayComp@Form/OutToday:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `TodayEqual` | lean=[TodayEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `gap` | `call` | lean=[] kernel=[Form/OutGapAfterPartial:berechnungsWertFehler] |
| `stamp-construction-2026-10-04/berlin/request.json` | `ordinary` | `AfterComponentsComp` | lean=[Form/AfterComponents=cleared] kernel=[Form/AfterComponents=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `ordinary` | `ComponentsComp` | lean=[ComponentsComp@Form/OutComponents:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `ordinary` | `ComponentsComp` | lean=[Form/OutComponents=value 2024-03-31T03:00:00] kernel=[Form/OutComponents=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `ordinary` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `ordinary` | `GapAfterPartialComp` | lean=[Form/OutGapAfterPartial=value 2024-02-01T03:30:00] kernel=[Form/OutGapAfterPartial=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `ordinary` | `GapAfterPartialComp` | lean=[GapAfterPartialComp@Form/OutGapAfterPartial:VALUE_ERROR/ERROR referenced=[Form/OutGapAfterPartial, Form/P] fillToFix=[]] kernel=[GapAfterPartialComp@Form/OutGapAfterPartial:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `stamp-construction-2026-10-04/berlin/request.json` | `ordinary` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Z:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `ordinary` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Z:VALUE_ERROR/ERROR referenced=[Form/P, Form/Z] fillToFix=[]] kernel=[GapAfterPartialNotEqual@Form/Z:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `stamp-construction-2026-10-04/berlin/request.json` | `ordinary` | `call` | lean=[] kernel=[Form/OutGapAfterPartial:berechnungsWertFehler] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `AfterClockComp` | lean=[Form/AfterClock=cleared] kernel=[Form/AfterClock=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `AfterComponentsComp` | lean=[Form/AfterComponents=cleared] kernel=[Form/AfterComponents=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `AfterFieldsComp` | lean=[Form/AfterFields=cleared] kernel=[Form/AfterFields=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `AfterGivenComp` | lean=[Form/AfterGiven=cleared] kernel=[Form/AfterGiven=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `AfterHourAfterComp` | lean=[Form/AfterHourAfter=cleared] kernel=[Form/AfterHourAfter=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `AfterMDComp` | lean=[Form/AfterMD=cleared] kernel=[Form/AfterMD=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `AfterRangeComp` | lean=[Form/AfterRange=cleared] kernel=[Form/AfterRange=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `AfterTodayComp` | lean=[Form/AfterToday=cleared] kernel=[Form/AfterToday=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `ClockComp` | lean=[ClockComp@Form/OutClock:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `ClockComp` | lean=[Form/OutClock=value 2024-03-31T03:00:00] kernel=[Form/OutClock=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `ClockNotEqual` | lean=[ClockNotEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `ComponentsComp` | lean=[ComponentsComp@Form/OutComponents:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `ComponentsComp` | lean=[Form/OutComponents=value 2024-03-31T03:00:00] kernel=[Form/OutComponents=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `ConstructedMin` | lean=[] kernel=[ConstructedMin@Form/Z:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `FieldsComp` | lean=[FieldsComp@Form/OutFields:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `FieldsComp` | lean=[Form/OutFields=value 2024-03-31T03:30:00] kernel=[Form/OutFields=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `FieldsEqual` | lean=[FieldsEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `GapAfterPartialComp` | lean=[Form/OutGapAfterPartial=value 2024-01-01T03:30:00] kernel=[Form/OutGapAfterPartial=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `GapAfterPartialComp` | lean=[GapAfterPartialComp@Form/OutGapAfterPartial:VALUE_ERROR/ERROR referenced=[Form/OutGapAfterPartial, Form/P] fillToFix=[]] kernel=[GapAfterPartialComp@Form/OutGapAfterPartial:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Z:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Z:VALUE_ERROR/ERROR referenced=[Form/P, Form/Z] fillToFix=[]] kernel=[GapAfterPartialNotEqual@Form/Z:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `GivenComp` | lean=[Form/OutGiven=value 2024-03-31T03:30:00] kernel=[Form/OutGiven=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `GivenComp` | lean=[GivenComp@Form/OutGiven:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `GivenEqual` | lean=[GivenEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `HourAfterComp` | lean=[Form/OutHourAfter=value 2024-03-31T04:30:00] kernel=[Form/OutHourAfter=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `HourAfterComp` | lean=[HourAfterComp@Form/OutHourAfter:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `HourAfterNotEqual` | lean=[HourAfterNotEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `MDComp` | lean=[Form/OutMD=value 2024-03-31T03:30:00] kernel=[Form/OutMD=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `MDComp` | lean=[MDComp@Form/OutMD:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `MDEqual` | lean=[MDEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `RangeComp` | lean=[Form/OutRange=value 2024-03-31T03:30:00] kernel=[Form/OutRange=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `RangeComp` | lean=[RangeComp@Form/OutRange:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `RangeEqual` | lean=[RangeEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `TodayComp` | lean=[Form/OutToday=value 2024-03-31T03:30:00] kernel=[Form/OutToday=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `TodayComp` | lean=[TodayComp@Form/OutToday:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `TodayEqual` | lean=[TodayEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-month` | `call` | lean=[] kernel=[Form/OutGapAfterPartial:berechnungsWertFehler] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `AfterClockComp` | lean=[Form/AfterClock=cleared] kernel=[Form/AfterClock=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `AfterComponentsComp` | lean=[Form/AfterComponents=cleared] kernel=[Form/AfterComponents=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `AfterFieldsComp` | lean=[Form/AfterFields=cleared] kernel=[Form/AfterFields=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `AfterGapAfterPartialComp` | lean=[Form/AfterGapAfterPartial=value 1] kernel=[Form/AfterGapAfterPartial=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `AfterGivenComp` | lean=[Form/AfterGiven=cleared] kernel=[Form/AfterGiven=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `AfterHourAfterComp` | lean=[Form/AfterHourAfter=cleared] kernel=[Form/AfterHourAfter=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `AfterMDComp` | lean=[Form/AfterMD=cleared] kernel=[Form/AfterMD=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `AfterRangeComp` | lean=[Form/AfterRange=cleared] kernel=[Form/AfterRange=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `AfterTodayComp` | lean=[Form/AfterToday=cleared] kernel=[Form/AfterToday=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `ClockComp` | lean=[ClockComp@Form/OutClock:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `ClockComp` | lean=[Form/OutClock=value 2024-03-31T03:00:00] kernel=[Form/OutClock=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `ClockNotEqual` | lean=[ClockNotEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `ComponentsComp` | lean=[ComponentsComp@Form/OutComponents:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `ComponentsComp` | lean=[Form/OutComponents=value 2024-03-31T03:00:00] kernel=[Form/OutComponents=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `ConstructedMin` | lean=[] kernel=[ConstructedMin@Form/Z:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `FieldsComp` | lean=[FieldsComp@Form/OutFields:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `FieldsComp` | lean=[Form/OutFields=value 2024-03-31T03:30:00] kernel=[Form/OutFields=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `FieldsEqual` | lean=[FieldsEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `GapAfterPartialComp` | lean=[] kernel=[GapAfterPartialComp@Form/OutGapAfterPartial:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Z:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `GapAfterPartialNotEqual` | lean=[] kernel=[GapAfterPartialNotEqual@Form/Z:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `GivenComp` | lean=[Form/OutGiven=value 2024-03-31T03:30:00] kernel=[Form/OutGiven=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `GivenComp` | lean=[GivenComp@Form/OutGiven:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `GivenEqual` | lean=[GivenEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `HourAfterComp` | lean=[Form/OutHourAfter=value 2024-03-31T04:30:00] kernel=[Form/OutHourAfter=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `HourAfterComp` | lean=[HourAfterComp@Form/OutHourAfter:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `HourAfterNotEqual` | lean=[HourAfterNotEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `MDComp` | lean=[Form/OutMD=value 2024-03-31T03:30:00] kernel=[Form/OutMD=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `MDComp` | lean=[MDComp@Form/OutMD:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `MDEqual` | lean=[MDEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `RangeComp` | lean=[Form/OutRange=value 2024-03-31T03:30:00] kernel=[Form/OutRange=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `RangeComp` | lean=[RangeComp@Form/OutRange:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `RangeEqual` | lean=[RangeEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `TodayComp` | lean=[Form/OutToday=value 2024-03-31T03:30:00] kernel=[Form/OutToday=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `TodayComp` | lean=[TodayComp@Form/OutToday:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `TodayEqual` | lean=[TodayEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unknown-year` | `call` | lean=[] kernel=[Form/OutGapAfterPartial:berechnungsWertFehler] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `AfterFieldsComp` | lean=[Form/AfterFields=cleared] kernel=[Form/AfterFields=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `AfterGivenComp` | lean=[Form/AfterGiven=cleared] kernel=[Form/AfterGiven=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `AfterHourAfterComp` | lean=[Form/AfterHourAfter=cleared] kernel=[Form/AfterHourAfter=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `AfterMDComp` | lean=[Form/AfterMD=cleared] kernel=[Form/AfterMD=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `AfterPartialLastComp` | lean=[Form/AfterPartialLast=cleared] kernel=[Form/AfterPartialLast=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `AfterRangeComp` | lean=[Form/AfterRange=cleared] kernel=[Form/AfterRange=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `AfterTodayComp` | lean=[Form/AfterToday=cleared] kernel=[Form/AfterToday=value 1] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `FieldsComp` | lean=[FieldsComp@Form/OutFields:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `FieldsComp` | lean=[Form/OutFields=value 2024-03-31T03:30:00] kernel=[Form/OutFields=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `FieldsEqual` | lean=[FieldsEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `GapAfterPartialComp` | lean=[Form/OutGapAfterPartial=value 2024-03-01T03:30:00] kernel=[Form/OutGapAfterPartial=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `GapAfterPartialComp` | lean=[GapAfterPartialComp@Form/OutGapAfterPartial:VALUE_ERROR/ERROR referenced=[Form/OutGapAfterPartial, Form/P] fillToFix=[]] kernel=[GapAfterPartialComp@Form/OutGapAfterPartial:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Z:VALUE_ERROR/ERROR] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Z:VALUE_ERROR/ERROR referenced=[Form/P, Form/Z] fillToFix=[]] kernel=[GapAfterPartialNotEqual@Form/Z:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `GivenComp` | lean=[Form/OutGiven=value 2024-03-31T03:30:00] kernel=[Form/OutGiven=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `GivenComp` | lean=[GivenComp@Form/OutGiven:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `GivenEqual` | lean=[GivenEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `HourAfterComp` | lean=[Form/OutHourAfter=value 2024-03-31T04:30:00] kernel=[Form/OutHourAfter=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `HourAfterComp` | lean=[HourAfterComp@Form/OutHourAfter:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `HourAfterNotEqual` | lean=[HourAfterNotEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `MDComp` | lean=[Form/OutMD=value 2024-03-31T03:30:00] kernel=[Form/OutMD=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `MDComp` | lean=[MDComp@Form/OutMD:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `MDEqual` | lean=[MDEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `PartialLastComp` | lean=[Form/OutPartialLast=value 2024-03-31T03:30:00] kernel=[Form/OutPartialLast=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `PartialLastComp` | lean=[PartialLastComp@Form/OutPartialLast:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `PartialLastEqual` | lean=[PartialLastEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `RangeComp` | lean=[Form/OutRange=value 2024-03-31T03:30:00] kernel=[Form/OutRange=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `RangeComp` | lean=[RangeComp@Form/OutRange:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `RangeEqual` | lean=[RangeEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `TodayComp` | lean=[Form/OutToday=value 2024-03-31T03:30:00] kernel=[Form/OutToday=cleared] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `TodayComp` | lean=[TodayComp@Form/OutToday:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `TodayEqual` | lean=[TodayEqual@Form/Z:VALUE_ERROR/ERROR] kernel=[] |
| `stamp-construction-2026-10-04/berlin/request.json` | `unreal-clock` | `call` | lean=[] kernel=[Form/OutGapAfterPartial:berechnungsWertFehler] |
| `temporal-row-binding-2026-10-04/bound-berlin/request.json` | `two` | `Min` | lean=[Min@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[Min@Form/Rows/Z:VALUE_ERROR/ERROR, Min@Form/Rows[2]/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `bad-clock` | `ClockNotEqual` | lean=[ClockNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `bad-clock` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `bad-clock` | `ConstructedMin` | lean=[] kernel=[ConstructedMin@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `bad-clock` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `bad-clock` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR referenced=[Form/Rows/P, Form/Rows/Z] fillToFix=[]] kernel=[GapAfterPartialNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `bad-date` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `bad-date` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `bad-date` | `GapAfterPartialNotEqual` | lean=[] kernel=[GapAfterPartialNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `bad-date` | `MDEqual` | lean=[MDEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `bad-date` | `RangeEqual` | lean=[RangeEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `bad-date` | `TodayEqual` | lean=[TodayEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `empty-amount` | `ClockNotEqual` | lean=[ClockNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `empty-amount` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `empty-amount` | `ConstructedMin` | lean=[] kernel=[ConstructedMin@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `empty-amount` | `FieldsEqual` | lean=[FieldsEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `empty-amount` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `empty-amount` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR referenced=[Form/Rows/P, Form/Rows/Z] fillToFix=[]] kernel=[GapAfterPartialNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `empty-amount` | `GivenEqual` | lean=[GivenEqual@Form/Rows/Z:OMISSION_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `empty-amount` | `HourAfterNotEqual` | lean=[HourAfterNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `empty-amount` | `MDEqual` | lean=[MDEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `empty-amount` | `PartialLastEqual` | lean=[PartialLastEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `empty-amount` | `RangeEqual` | lean=[RangeEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `empty-amount` | `TodayEqual` | lean=[TodayEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `empty-clock` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `empty-clock` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR referenced=[Form/Rows/P, Form/Rows/Z] fillToFix=[]] kernel=[GapAfterPartialNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `empty-date` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `empty-date` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `empty-date` | `GapAfterPartialNotEqual` | lean=[] kernel=[GapAfterPartialNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `empty-date` | `MDEqual` | lean=[MDEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `empty-date` | `RangeEqual` | lean=[RangeEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `empty-date` | `TodayEqual` | lean=[TodayEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `empty-date-bad-clock` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `empty-date-bad-clock` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `empty-date-bad-clock` | `GapAfterPartialNotEqual` | lean=[] kernel=[GapAfterPartialNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `fold` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `fold` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `fold` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR referenced=[Form/Rows/P, Form/Rows/Z] fillToFix=[]] kernel=[GapAfterPartialNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `fold` | `MDNotEqual` | lean=[MDNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `fold` | `RangeNotEqual` | lean=[RangeNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `fold` | `TodayNotEqual` | lean=[TodayNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `gap` | `ClockNotEqual` | lean=[ClockNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `gap` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `gap` | `ConstructedMin` | lean=[] kernel=[ConstructedMin@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `gap` | `FieldsEqual` | lean=[FieldsEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `gap` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `gap` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR referenced=[Form/Rows/P, Form/Rows/Z] fillToFix=[]] kernel=[GapAfterPartialNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `gap` | `GivenEqual` | lean=[GivenEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `gap` | `HourAfterNotEqual` | lean=[HourAfterNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `gap` | `MDEqual` | lean=[MDEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `gap` | `PartialLastEqual` | lean=[PartialLastEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `gap` | `RangeEqual` | lean=[RangeEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `gap` | `TodayEqual` | lean=[TodayEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `no-rows` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `no-rows` | `GapAfterPartialNotEqual` | lean=[] kernel=[GapAfterPartialNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `ordinary` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `ordinary` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `ordinary` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR referenced=[Form/Rows/P, Form/Rows/Z] fillToFix=[]] kernel=[GapAfterPartialNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `two-empty` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `two-empty` | `GapAfterPartialNotEqual` | lean=[] kernel=[GapAfterPartialNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `two-values` | `ClockNotEqual` | lean=[ClockNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR, ClockNotEqual@Form/Rows[2]/Z:VALUE_ERROR/ERROR] kernel=[ClockNotEqual@Form/Rows[2]/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `two-values` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR, ComponentsNotEqual@Form/Rows[2]/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `two-values` | `ConstructedMin` | lean=[] kernel=[ConstructedMin@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `two-values` | `FieldsEqual` | lean=[FieldsEqual@Form/Rows/Z:VALUE_ERROR/ERROR, FieldsEqual@Form/Rows[2]/Z:VALUE_ERROR/ERROR] kernel=[FieldsEqual@Form/Rows[2]/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `two-values` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `two-values` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR, GapAfterPartialNotEqual@Form/Rows[2]/Z:VALUE_ERROR/ERROR] kernel=[GapAfterPartialNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `two-values` | `GivenEqual` | lean=[GivenEqual@Form/Rows/Z:VALUE_ERROR/ERROR, GivenEqual@Form/Rows[2]/Z:VALUE_ERROR/ERROR] kernel=[GivenEqual@Form/Rows[2]/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `two-values` | `HourAfterNotEqual` | lean=[HourAfterNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR, HourAfterNotEqual@Form/Rows[2]/Z:VALUE_ERROR/ERROR] kernel=[HourAfterNotEqual@Form/Rows[2]/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `two-values` | `MDEqual` | lean=[MDEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `two-values` | `PartialLastEqual` | lean=[PartialLastEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `two-values` | `RangeEqual` | lean=[RangeEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `two-values` | `TodayEqual` | lean=[TodayEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unknown-month` | `ClockNotEqual` | lean=[ClockNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unknown-month` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unknown-month` | `ConstructedMin` | lean=[] kernel=[ConstructedMin@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unknown-month` | `FieldsEqual` | lean=[FieldsEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unknown-month` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unknown-month` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR referenced=[Form/Rows/P, Form/Rows/Z] fillToFix=[]] kernel=[GapAfterPartialNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unknown-month` | `GivenEqual` | lean=[GivenEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unknown-month` | `HourAfterNotEqual` | lean=[HourAfterNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unknown-month` | `MDEqual` | lean=[MDEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unknown-month` | `RangeEqual` | lean=[RangeEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unknown-month` | `TodayEqual` | lean=[TodayEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unknown-year` | `ClockNotEqual` | lean=[ClockNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unknown-year` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unknown-year` | `ConstructedMin` | lean=[] kernel=[ConstructedMin@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unknown-year` | `FieldsEqual` | lean=[FieldsEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unknown-year` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unknown-year` | `GapAfterPartialNotEqual` | lean=[] kernel=[GapAfterPartialNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unknown-year` | `GivenEqual` | lean=[GivenEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unknown-year` | `HourAfterNotEqual` | lean=[HourAfterNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unknown-year` | `MDEqual` | lean=[MDEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unknown-year` | `RangeEqual` | lean=[RangeEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unknown-year` | `TodayEqual` | lean=[TodayEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unreal-clock` | `FieldsEqual` | lean=[FieldsEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unreal-clock` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unreal-clock` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR referenced=[Form/Rows/P, Form/Rows/Z] fillToFix=[]] kernel=[GapAfterPartialNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unreal-clock` | `GivenEqual` | lean=[GivenEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unreal-clock` | `HourAfterNotEqual` | lean=[HourAfterNotEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unreal-clock` | `MDEqual` | lean=[MDEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unreal-clock` | `PartialLastEqual` | lean=[PartialLastEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unreal-clock` | `RangeEqual` | lean=[RangeEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-1/request.json` | `unreal-clock` | `TodayEqual` | lean=[TodayEqual@Form/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `bad-clock` | `ClockNotEqual` | lean=[ClockNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `bad-clock` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `bad-clock` | `ConstructedMin` | lean=[] kernel=[ConstructedMin@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `bad-clock` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `bad-clock` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR referenced=[Form/Parents/Rows/P, Form/Parents/Rows/Z] fillToFix=[]] kernel=[GapAfterPartialNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `bad-date` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `bad-date` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `bad-date` | `GapAfterPartialNotEqual` | lean=[] kernel=[GapAfterPartialNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `bad-date` | `MDEqual` | lean=[MDEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `bad-date` | `RangeEqual` | lean=[RangeEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `bad-date` | `TodayEqual` | lean=[TodayEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `empty-amount` | `ClockNotEqual` | lean=[ClockNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `empty-amount` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `empty-amount` | `ConstructedMin` | lean=[] kernel=[ConstructedMin@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `empty-amount` | `FieldsEqual` | lean=[FieldsEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `empty-amount` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `empty-amount` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR referenced=[Form/Parents/Rows/P, Form/Parents/Rows/Z] fillToFix=[]] kernel=[GapAfterPartialNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `empty-amount` | `GivenEqual` | lean=[GivenEqual@Form/Parents/Rows/Z:OMISSION_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `empty-amount` | `HourAfterNotEqual` | lean=[HourAfterNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `empty-amount` | `MDEqual` | lean=[MDEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `empty-amount` | `PartialLastEqual` | lean=[PartialLastEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `empty-amount` | `RangeEqual` | lean=[RangeEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `empty-amount` | `TodayEqual` | lean=[TodayEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `empty-clock` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `empty-clock` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR referenced=[Form/Parents/Rows/P, Form/Parents/Rows/Z] fillToFix=[]] kernel=[GapAfterPartialNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `empty-date` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `empty-date` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `empty-date` | `GapAfterPartialNotEqual` | lean=[] kernel=[GapAfterPartialNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `empty-date` | `MDEqual` | lean=[MDEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `empty-date` | `RangeEqual` | lean=[RangeEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `empty-date` | `TodayEqual` | lean=[TodayEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `empty-date-bad-clock` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `empty-date-bad-clock` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `empty-date-bad-clock` | `GapAfterPartialNotEqual` | lean=[] kernel=[GapAfterPartialNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `fold` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `fold` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `fold` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR referenced=[Form/Parents/Rows/P, Form/Parents/Rows/Z] fillToFix=[]] kernel=[GapAfterPartialNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `fold` | `MDNotEqual` | lean=[MDNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `fold` | `RangeNotEqual` | lean=[RangeNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `fold` | `TodayNotEqual` | lean=[TodayNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `gap` | `ClockNotEqual` | lean=[ClockNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `gap` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `gap` | `ConstructedMin` | lean=[] kernel=[ConstructedMin@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `gap` | `FieldsEqual` | lean=[FieldsEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `gap` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `gap` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR referenced=[Form/Parents/Rows/P, Form/Parents/Rows/Z] fillToFix=[]] kernel=[GapAfterPartialNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `gap` | `GivenEqual` | lean=[GivenEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `gap` | `HourAfterNotEqual` | lean=[HourAfterNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `gap` | `MDEqual` | lean=[MDEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `gap` | `PartialLastEqual` | lean=[PartialLastEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `gap` | `RangeEqual` | lean=[RangeEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `gap` | `TodayEqual` | lean=[TodayEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `no-rows` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `no-rows` | `GapAfterPartialNotEqual` | lean=[] kernel=[GapAfterPartialNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `ordinary` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `ordinary` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `ordinary` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR referenced=[Form/Parents/Rows/P, Form/Parents/Rows/Z] fillToFix=[]] kernel=[GapAfterPartialNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `two-empty` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `two-empty` | `GapAfterPartialNotEqual` | lean=[] kernel=[GapAfterPartialNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `two-values` | `ClockNotEqual` | lean=[ClockNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR, ClockNotEqual@Form/Parents/Rows[2]/Z:VALUE_ERROR/ERROR] kernel=[ClockNotEqual@Form/Parents/Rows[2]/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `two-values` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR, ComponentsNotEqual@Form/Parents/Rows[2]/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `two-values` | `ConstructedMin` | lean=[] kernel=[ConstructedMin@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `two-values` | `FieldsEqual` | lean=[FieldsEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR, FieldsEqual@Form/Parents/Rows[2]/Z:VALUE_ERROR/ERROR] kernel=[FieldsEqual@Form/Parents/Rows[2]/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `two-values` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `two-values` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR, GapAfterPartialNotEqual@Form/Parents/Rows[2]/Z:VALUE_ERROR/ERROR] kernel=[GapAfterPartialNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `two-values` | `GivenEqual` | lean=[GivenEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR, GivenEqual@Form/Parents/Rows[2]/Z:VALUE_ERROR/ERROR] kernel=[GivenEqual@Form/Parents/Rows[2]/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `two-values` | `HourAfterNotEqual` | lean=[HourAfterNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR, HourAfterNotEqual@Form/Parents/Rows[2]/Z:VALUE_ERROR/ERROR] kernel=[HourAfterNotEqual@Form/Parents/Rows[2]/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `two-values` | `MDEqual` | lean=[MDEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `two-values` | `PartialLastEqual` | lean=[PartialLastEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `two-values` | `RangeEqual` | lean=[RangeEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `two-values` | `TodayEqual` | lean=[TodayEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unknown-month` | `ClockNotEqual` | lean=[ClockNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unknown-month` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unknown-month` | `ConstructedMin` | lean=[] kernel=[ConstructedMin@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unknown-month` | `FieldsEqual` | lean=[FieldsEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unknown-month` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unknown-month` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR referenced=[Form/Parents/Rows/P, Form/Parents/Rows/Z] fillToFix=[]] kernel=[GapAfterPartialNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unknown-month` | `GivenEqual` | lean=[GivenEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unknown-month` | `HourAfterNotEqual` | lean=[HourAfterNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unknown-month` | `MDEqual` | lean=[MDEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unknown-month` | `RangeEqual` | lean=[RangeEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unknown-month` | `TodayEqual` | lean=[TodayEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unknown-year` | `ClockNotEqual` | lean=[ClockNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unknown-year` | `ComponentsNotEqual` | lean=[ComponentsNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unknown-year` | `ConstructedMin` | lean=[] kernel=[ConstructedMin@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unknown-year` | `FieldsEqual` | lean=[FieldsEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unknown-year` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unknown-year` | `GapAfterPartialNotEqual` | lean=[] kernel=[GapAfterPartialNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unknown-year` | `GivenEqual` | lean=[GivenEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unknown-year` | `HourAfterNotEqual` | lean=[HourAfterNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unknown-year` | `MDEqual` | lean=[MDEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unknown-year` | `RangeEqual` | lean=[RangeEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unknown-year` | `TodayEqual` | lean=[TodayEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unreal-clock` | `FieldsEqual` | lean=[FieldsEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unreal-clock` | `GapAfterPartialEqual` | lean=[] kernel=[GapAfterPartialEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unreal-clock` | `GapAfterPartialNotEqual` | lean=[GapAfterPartialNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR referenced=[Form/Parents/Rows/P, Form/Parents/Rows/Z] fillToFix=[]] kernel=[GapAfterPartialNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR referenced=[] fillToFix=[]] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unreal-clock` | `GivenEqual` | lean=[GivenEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unreal-clock` | `HourAfterNotEqual` | lean=[HourAfterNotEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unreal-clock` | `MDEqual` | lean=[MDEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unreal-clock` | `PartialLastEqual` | lean=[PartialLastEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unreal-clock` | `RangeEqual` | lean=[RangeEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `temporal-row-binding-2026-10-04/stamp-berlin-2/request.json` | `unreal-clock` | `TodayEqual` | lean=[TodayEqual@Form/Parents/Rows/Z:VALUE_ERROR/ERROR] kernel=[] |
| `u02-open-gaps-2026-10-30/request-overlap.json` | `overlap0130` | `P2Comp` | lean=[Mix/P2=value 1] kernel=[Mix/P2=cleared] |
| `u02-open-gaps-2026-10-30/request-overlap.json` | `overlap0130` | `P2Comp` | lean=[P2Comp@Mix/P2:VALUE_ERROR/ERROR] kernel=[] |
| `u02-open-gaps-2026-10-30/request-overlap.json` | `overlap0130` | `P3Comp` | lean=[Mix/P3=cleared] kernel=[Mix/P3=value 1] |
| `u02-open-gaps-2026-10-30/request-overlap.json` | `overlap0130` | `P3Comp` | lean=[] kernel=[P3Comp@Mix/P3:VALUE_ERROR/ERROR] |
| `u02-open-gaps-2026-10-30/request-overlap.json` | `overlap0130` | `v1` | lean=[v1@Mix/DTX:VALUE_ERROR/ERROR] kernel=[] |
| `yearless-shift-anchor-2026-10-30/request-const-2001.json` | `leap` | `c_TC160000` | lean=[Form/TC160000=value 05-23] kernel=[Form/TC160000=value 05-13] |
| `yearless-shift-anchor-2026-10-30/request-const-2001.json` | `leap` | `c_TC200000` | lean=[Form/TC200000=value 11-15] kernel=[Form/TC200000=value 11-06] |
| `yearless-shift-anchor-2026-10-30/request-const-2001.json` | `year-end` | `c_TC160000` | lean=[Form/TC160000=value 05-23] kernel=[Form/TC160000=value 05-13] |
| `yearless-shift-anchor-2026-10-30/request-const-2001.json` | `year-end` | `c_TC200000` | lean=[Form/TC200000=value 11-15] kernel=[Form/TC200000=value 11-06] |
| `yearless-shift-anchor-2026-10-30/request-const.json` | `leap` | `c_TC160000` | lean=[Form/TC160000=value 05-23] kernel=[Form/TC160000=value 05-13] |
| `yearless-shift-anchor-2026-10-30/request-const.json` | `leap` | `c_TC200000` | lean=[Form/TC200000=value 11-15] kernel=[Form/TC200000=value 11-06] |
| `yearless-shift-anchor-2026-10-30/request-const.json` | `year-end` | `c_TC160000` | lean=[Form/TC160000=value 05-23] kernel=[Form/TC160000=value 05-13] |
| `yearless-shift-anchor-2026-10-30/request-const.json` | `year-end` | `c_TC200000` | lean=[Form/TC200000=value 11-15] kernel=[Form/TC200000=value 11-06] |
| `yearless-shift-anchor-2026-10-30/request-cross-2001.json` | `mid-year` | `c_TM160000` | lean=[Form/TM160000=value 05-23] kernel=[Form/TM160000=value 05-13] |
| `yearless-shift-anchor-2026-10-30/request-cross-2001.json` | `mid-year` | `c_TM200000` | lean=[Form/TM200000=value 11-15] kernel=[Form/TM200000=value 11-06] |
| `yearless-shift-anchor-2026-10-30/request-cross-2001.json` | `year-end` | `c_TM160000` | lean=[Form/TM160000=value 12-08] kernel=[Form/TM160000=value 11-28] |
| `yearless-shift-anchor-2026-10-30/request-cross-2001.json` | `year-end` | `c_TM200000` | lean=[Form/TM200000=value 06-02] kernel=[Form/TM200000=value 05-24] |
| `yearless-shift-anchor-2026-10-30/request-cross-2001.json` | `year-end-same` | `c_TM160000` | lean=[Form/TM160000=value 12-07] kernel=[Form/TM160000=value 11-27] |
| `yearless-shift-anchor-2026-10-30/request-cross-2001.json` | `year-end-same` | `c_TM200000` | lean=[Form/TM200000=value 06-01] kernel=[Form/TM200000=value 05-23] |
| `yearless-shift-anchor-2026-10-30/request-cross.json` | `mid-year` | `c_TM160000` | lean=[Form/TM160000=value 05-23] kernel=[Form/TM160000=value 05-13] |
| `yearless-shift-anchor-2026-10-30/request-cross.json` | `mid-year` | `c_TM200000` | lean=[Form/TM200000=value 11-15] kernel=[Form/TM200000=value 11-06] |
| `yearless-shift-anchor-2026-10-30/request-cross.json` | `year-end` | `c_TM160000` | lean=[Form/TM160000=value 12-08] kernel=[Form/TM160000=value 11-28] |
| `yearless-shift-anchor-2026-10-30/request-cross.json` | `year-end` | `c_TM200000` | lean=[Form/TM200000=value 06-02] kernel=[Form/TM200000=value 05-24] |
| `yearless-shift-anchor-2026-10-30/request-cross.json` | `year-end-same` | `c_TM160000` | lean=[Form/TM160000=value 12-07] kernel=[Form/TM160000=value 11-27] |
| `yearless-shift-anchor-2026-10-30/request-cross.json` | `year-end-same` | `c_TM200000` | lean=[Form/TM200000=value 06-01] kernel=[Form/TM200000=value 05-23] |

## Axis 1 — diagnostic vocabulary, with a finite denominator

| | classes | share |
|---|---|---|
| Distinct identifiers in the selected diagnostic catalogs and runtime formal-code constants | 491 | 100% |
| Named in `spec/` or `docs/` prose | 332 | 67% |
| Named in Lean source under `A12Kernel/` | 481 | 97% |
| Named in JSON under `evidence/` | 287 | 58% |
| Touched by any of the three | 486 | 98% |
| **Untouched everywhere** | **5** | **1%** |

Two occurrence checks that may warrant an ownership lookup:

- **Named in evidence JSON but absent from prose: 15.** Inspect the occurrence before treating it as an unaccounted observation.

### Where the untouched classes are

Ordered by count for lookup. Semantic priority remains with the plan and live gaps.

| untouched | catalog | route |
|---|---|---|
| 2 | `_31_1` | runtime formal-error **texts** — a **document** probe (`:adapter:kernelProbe` → `validateFull`); finer than the code below, since art and sign pick the text |
| 1 | `vk_service_errortext_error_messages` | message templates and parameters — the fast `rule check --message` batch route |
| 1 | `vk_parser_error_messages` | condition/DSL static legality — the fast `dmtool rule check` batch route |
| 1 | `vk_parser_common_error_messages` | shared parser diagnostics — the fast `rule check` batch route |

## Axis 2 — admitted behaviour, which no class name reaches

Rendering, arithmetic ordering, computation scheduling, poison timing, and calendar behaviour are not measured by diagnostic vocabulary. This text query counts capability records mentioning a checkpoint or calibration, not how much of each family is calibrated. The checkpoint and evidence-pending sets can overlap.

| | records | share |
|---|---|---|
| Capability records in [`implementation/`](implementation/) | 272 | 100% |
| Citing a Kernel checkpoint or calibration | 147 | 54% |
| Carrying an explicit evidence-pending note | 106 | 38% |

## Axis 3 — open obligation load

| | count |
|---|---|
| Open gap records in [`gaps/`](gaps/), indexed by [`SEMANTICS-GAPS.md`](SEMANTICS-GAPS.md) | 22 |
| `remaining` rows across those gaps | 0 |
| Gaps whose route is **blocked** | 0 |
| Ledger entries `pending` with a12-dmkits | 1 |
| Ledger entries `handed-off` | 0 |

A blocked route stops the work that depends on it. Other ready obligations can continue. Remaining-work entries differ in size and may overlap; their count is not a completion percentage.

## Axis 4 — estate ratio, a standing guard rather than a statistic

[`CLAUDE.md`](../CLAUDE.md#semantic-first-simplification-rule) requires support not to exceed theory, and evidence alone to stay below one third of theory.

| estate | tracked nonblank Lean lines | against theory |
|---|---|---|
| Theory (`Semantics/`, `Elaboration/`, `Proofs/`, `Conformance/`, core types) | 275183 | 100% |
| Support (`Evidence/`, `Reference/`, `Process/`, `Trust/`, drivers) | 64347 | 23% — ceiling 100% |
| Evidence alone | 2415 | 0% — ceiling 33% |

Tracked Lean files in neither estate: 0. A nonzero value means the ratio above measures a subset and the inventory needs review.

## Axis 5 — retained empirical backbone

| | count |
|---|---|
| Retained capture directories under `../evidence/` | 488 |
| `inputHash` markers in `*-obs.json` and `semantic-observations.json` | 767 |

The marker count excludes other observation formats, including runtime `artifact.json` files with `rows` arrays. It is neither a total observation count nor a count of independent behavioural discriminators.

## Velocity

One row is appended when one of the recorded counts changes. Flat vocabulary counts do not indicate stalled semantic work: runtime calibration, proofs, and admitted behaviour can advance without introducing a diagnostic name. Historical rows preserve the counts produced by their then-current queries.

Datetime is HEAD's commit time in ISO 8601 format, including its UTC offset; it is not the report's execution time. The revision is context for working-tree counts, not a claim that every counted byte was committed there.

<!-- velocity-history:start -->
| datetime | revision | touched | Lean names | untouched | checkpoint-citing capabilities | open gaps |
|---|---|---|---|---|---|---|
| 2026-09-07T19:17:22+02:00 | `3db574b1` | 149 | 78 | 292 | 82 | 23 |
| 2026-09-07T20:07:55+02:00 | `0fe98007` | 160 | 78 | 281 | 82 | 23 |
| 2026-09-07T20:15:59+02:00 | `d9079138` | 170 | 78 | 271 | 82 | 23 |
| 2026-09-07T20:24:59+02:00 | `199106fc` | 194 | 92 | 301 | 82 | 23 |
| 2026-09-07T20:36:42+02:00 | `a80be08d` | 202 | 106 | 293 | 83 | 24 |
| 2026-09-07T21:25:22+02:00 | `6eb95a7e` | 300 | 204 | 195 | 83 | 24 |
| 2026-09-07T22:16:10+02:00 | `53d6d3ec` | 313 | 217 | 182 | 83 | 24 |
| 2026-09-07T22:30:39+02:00 | `eb587109` | 314 | 218 | 181 | 83 | 24 |
| 2026-09-07T22:38:00+02:00 | `2716b7cc` | 317 | 220 | 178 | 83 | 24 |
| 2026-09-07T22:43:16+02:00 | `4b6d739f` | 318 | 221 | 177 | 83 | 25 |
| 2026-09-07T22:49:28+02:00 | `77623942` | 336 | 239 | 159 | 84 | 25 |
| 2026-09-07T23:38:57+02:00 | `84dcb0cc` | 371 | 275 | 124 | 85 | 25 |
| 2026-09-08T00:19:13+02:00 | `fcf31f1c` | 375 | 279 | 120 | 86 | 25 |
| 2026-09-08T01:31:14+02:00 | `534c3160` | 387 | 291 | 108 | 87 | 25 |
| 2026-09-08T01:43:17+02:00 | `eaaca020` | 396 | 297 | 99 | 88 | 25 |
| 2026-09-08T01:55:45+02:00 | `74167065` | 403 | 303 | 92 | 89 | 25 |
| 2026-09-08T02:11:12+02:00 | `8b11aa8d` | 415 | 315 | 80 | 90 | 25 |
| 2026-09-08T02:22:27+02:00 | `7e500486` | 420 | 320 | 75 | 91 | 25 |
| 2026-09-08T02:28:53+02:00 | `57293e37` | 429 | 330 | 66 | 92 | 25 |
| 2026-09-08T03:04:37+02:00 | `185d1037` | 431 | 333 | 64 | 93 | 25 |
| 2026-09-08T04:46:36+02:00 | `ab442e98` | 448 | 350 | 47 | 93 | 25 |
| 2026-09-08T04:57:38+02:00 | `ee3e6900` | 452 | 354 | 43 | 94 | 25 |
| 2026-09-08T05:09:40+02:00 | `84fc1dde` | 459 | 361 | 36 | 95 | 25 |
| 2026-09-08T05:15:21+02:00 | `76c62b38` | 467 | 371 | 28 | 96 | 25 |
| 2026-09-08T06:42:57+02:00 | `7f962e56` | 473 | 377 | 22 | 97 | 25 |
| 2026-09-08T07:33:34+02:00 | `43bc7d7a` | 475 | 379 | 20 | 98 | 25 |
| 2026-09-08T07:43:32+02:00 | `29630b55` | 477 | 381 | 18 | 99 | 25 |
| 2026-09-08T07:53:12+02:00 | `8aceedea` | 479 | 383 | 16 | 100 | 25 |
| 2026-09-08T08:04:46+02:00 | `a75240e1` | 482 | 389 | 13 | 101 | 25 |
| 2026-09-08T08:15:13+02:00 | `95b73fdb` | 483 | 392 | 12 | 102 | 25 |
| 2026-09-08T14:31:07+02:00 | `ce0c830f` | 483 | 398 | 12 | 102 | 25 |
| 2026-09-08T14:50:57+02:00 | `fad2419a` | 483 | 405 | 12 | 102 | 25 |
| 2026-09-08T15:00:11+02:00 | `8305375a` | 483 | 410 | 12 | 103 | 25 |
| 2026-09-08T15:10:47+02:00 | `1401d381` | 483 | 415 | 12 | 103 | 25 |
| 2026-09-08T15:18:40+02:00 | `c1bb20aa` | 483 | 419 | 12 | 104 | 25 |
| 2026-09-08T15:40:20+02:00 | `8b1fd94f` | 483 | 426 | 12 | 105 | 25 |
| 2026-09-08T16:11:19+02:00 | `0e22c25a` | 489 | 432 | 6 | 105 | 25 |
| 2026-09-08T16:31:46+02:00 | `c401b5b3` | 489 | 436 | 6 | 105 | 25 |
| 2026-09-08T16:57:26+02:00 | `7da15820` | 489 | 440 | 6 | 105 | 25 |
| 2026-09-08T17:26:37+02:00 | `65e2aaad` | 489 | 444 | 6 | 106 | 25 |
| 2026-09-08T17:34:57+02:00 | `8badcc6a` | 489 | 445 | 6 | 107 | 25 |
| 2026-09-08T17:45:00+02:00 | `9aad52da` | 489 | 447 | 6 | 108 | 25 |
| 2026-09-08T18:07:46+02:00 | `452fd9fb` | 489 | 448 | 6 | 108 | 25 |
| 2026-09-08T18:21:40+02:00 | `ff74d2b8` | 489 | 449 | 6 | 108 | 25 |
| 2026-09-08T18:50:16+02:00 | `176c36ba` | 489 | 450 | 6 | 108 | 25 |
| 2026-09-08T19:44:27+02:00 | `3a457eea` | 489 | 454 | 6 | 108 | 25 |
| 2026-09-08T20:40:25+02:00 | `1a163c9e` | 489 | 455 | 6 | 108 | 25 |
| 2026-09-08T21:01:33+02:00 | `29a705e7` | 489 | 455 | 6 | 107 | 25 |
| 2026-09-08T21:18:34+02:00 | `367e2e71` | 489 | 455 | 6 | 111 | 25 |
| 2026-09-08T23:50:33+02:00 | `e652d91e` | 489 | 455 | 6 | 112 | 24 |
| 2026-09-09T00:03:35+02:00 | `caca1731` | 489 | 455 | 6 | 112 | 23 |
| 2026-09-09T00:32:32+02:00 | `27c48616` | 489 | 455 | 6 | 113 | 23 |
| 2026-09-09T02:01:07+02:00 | `023fbc63` | 489 | 455 | 6 | 114 | 23 |
| 2026-09-09T02:10:04+02:00 | `aa23c313` | 489 | 455 | 6 | 115 | 23 |
| 2026-09-09T02:36:22+02:00 | `32729671` | 489 | 455 | 6 | 116 | 23 |
| 2026-09-21T22:55:36+02:00 | `e19f3a98` | 489 | 455 | 6 | 117 | 23 |
| 2026-09-22T00:41:01+02:00 | `c7573039` | 489 | 455 | 6 | 118 | 23 |
| 2026-09-23T22:35:42+02:00 | `2c2f4c36` | 489 | 455 | 6 | 117 | 23 |
| 2026-09-23T23:20:43+02:00 | `a4a91200` | 489 | 456 | 6 | 117 | 23 |
| 2026-09-23T23:55:50+02:00 | `0b62e75f` | 489 | 456 | 6 | 118 | 23 |
| 2026-09-24T12:30:49+02:00 | `01b2247b` | 489 | 456 | 6 | 120 | 23 |
| 2026-09-24T15:47:41+02:00 | `c113d38a` | 489 | 457 | 6 | 120 | 23 |
| 2026-09-25T01:09:04+02:00 | `74b7f72c` | 489 | 459 | 6 | 120 | 23 |
| 2026-09-26T01:50:27+02:00 | `9230a94c` | 489 | 460 | 6 | 120 | 23 |
| 2026-09-26T04:02:51+02:00 | `93a63757` | 489 | 461 | 6 | 120 | 23 |
| 2026-09-26T07:54:21+02:00 | `933fd2e3` | 489 | 463 | 6 | 120 | 23 |
| 2026-09-26T16:23:26+02:00 | `92f2a974` | 489 | 464 | 6 | 120 | 23 |
| 2026-09-26T18:12:01+02:00 | `0130d527` | 489 | 464 | 6 | 121 | 23 |
| 2026-09-26T20:17:40+02:00 | `2964468f` | 489 | 464 | 6 | 122 | 23 |
| 2026-09-28T23:58:59+02:00 | `a050f150` | 489 | 464 | 6 | 122 | 24 |
| 2026-09-30T22:11:51+02:00 | `8b606e44` | 489 | 466 | 6 | 122 | 24 |
| 2026-10-01T19:53:58+02:00 | `d75f6596` | 489 | 467 | 6 | 122 | 24 |
| 2026-10-01T21:15:06+02:00 | `fd92bdaf` | 489 | 468 | 6 | 122 | 24 |
| 2026-10-01T21:26:08+02:00 | `e066b209` | 489 | 470 | 6 | 123 | 24 |
| 2026-10-02T00:34:38+02:00 | `3135584a` | 489 | 470 | 6 | 125 | 24 |
| 2026-10-02T01:48:13+02:00 | `9e94502f` | 489 | 471 | 6 | 126 | 24 |
| 2026-10-02T14:19:09+02:00 | `04943a90` | 489 | 472 | 6 | 126 | 24 |
| 2026-10-02T14:19:09+02:00 | `04943a90` | 489 | 472 | 6 | 127 | 24 |
| 2026-10-02T17:21:08+02:00 | `f4d27810` | 489 | 472 | 6 | 128 | 24 |
| 2026-10-02T19:19:56+02:00 | `8b40cd7d` | 489 | 472 | 6 | 129 | 24 |
| 2026-10-04T06:36:24+02:00 | `91e13c36` | 489 | 472 | 6 | 130 | 24 |
| 2026-10-05T10:43:03+02:00 | `7fc1aee6` | 489 | 472 | 6 | 131 | 24 |
| 2026-10-06T00:05:27+02:00 | `9cebb1f3` | 489 | 472 | 6 | 132 | 24 |
| 2026-10-06T20:45:10+02:00 | `078577ba` | 489 | 472 | 6 | 133 | 24 |
| 2026-10-07T08:48:03+02:00 | `6ea12b97` | 489 | 472 | 6 | 134 | 24 |
| 2026-10-07T11:59:09+02:00 | `94cce6b1` | 489 | 473 | 6 | 134 | 24 |
| 2026-10-07T17:47:56+02:00 | `5f00012b` | 489 | 473 | 6 | 135 | 24 |
| 2026-10-07T20:22:32+02:00 | `7710eb33` | 489 | 473 | 6 | 136 | 24 |
| 2026-10-08T01:46:57+02:00 | `bd773d1b` | 489 | 473 | 6 | 137 | 24 |
| 2026-10-08T05:05:41+02:00 | `86f814b7` | 489 | 473 | 6 | 138 | 24 |
| 2026-10-08T09:18:24+02:00 | `13e39307` | 489 | 473 | 6 | 139 | 24 |
| 2026-10-08T11:52:27+02:00 | `f524a96c` | 489 | 473 | 6 | 141 | 24 |
| 2026-10-08T13:55:15+02:00 | `4ccd04de` | 489 | 474 | 6 | 141 | 24 |
| 2026-10-08T20:58:59+02:00 | `13593f89` | 489 | 481 | 6 | 121 | 24 |
| 2026-10-09T04:41:58+02:00 | `be100e6b` | 489 | 482 | 6 | 121 | 24 |
| 2026-10-09T07:01:39+02:00 | `d55cc5b5` | 489 | 482 | 6 | 122 | 24 |
| 2026-10-09T09:59:41+02:00 | `1d6b8fb8` | 489 | 482 | 6 | 121 | 24 |
| 2026-10-10T05:52:00+02:00 | `4e9326a0` | 489 | 482 | 6 | 123 | 24 |
| 2026-10-13T00:14:35+02:00 | `03131431` | 489 | 482 | 6 | 124 | 24 |
| 2026-10-13T03:26:44+02:00 | `19017d09` | 489 | 482 | 6 | 125 | 24 |
| 2026-10-13T14:19:56+02:00 | `a4f769ba` | 489 | 482 | 6 | 129 | 23 |
| 2026-10-13T15:26:33+02:00 | `4097253d` | 489 | 482 | 6 | 128 | 23 |
| 2026-10-14T00:18:15+02:00 | `67a8e2f3` | 490 | 484 | 5 | 131 | 22 |
| 2026-10-22T23:42:58+02:00 | `6e6ad094` | 490 | 484 | 5 | 141 | 22 |
| 2026-10-23T15:08:16+02:00 | `7200d3e8` | 490 | 484 | 5 | 142 | 22 |
| 2026-10-25T00:07:47+02:00 | `bb62d125` | 490 | 484 | 5 | 147 | 22 |
| 2026-10-31T04:08:41+01:00 | `8a004a7d` | 490 | 484 | 5 | 148 | 22 |
| 2026-11-04T14:37:41+01:00 | `470e51ae` | 486 | 481 | 5 | 147 | 22 |
<!-- velocity-history:end -->
