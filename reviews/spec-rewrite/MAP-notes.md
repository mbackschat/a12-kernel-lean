# spec/SEMANTICS-MAP rewrite notes

The map is now a declared non-normative summary (plan key `order`): its opening paragraph says every rule it mentions is owned by the linked chapter and that the chapter wins on a difference. Every old normative statement was looked up in the landed chapters; where a chapter states it, the map keeps at most a one-line summary with a link (type-table rows carry an Owner column, invariants and glossary rows a link). Where the old map differed from a chapter, the chapter's account was taken under the run instruction and is listed under "Behavioural decisions" with the chapter sentence that already decides it, as rule 3 asks; no Lean def was needed for any of them. Statements no chapter owns are under "Rules not kept" as map-only. No spec/14 column was needed: the map's only per-operator list (§4 item 3's empty-read overrides) is already spec/14 column N, to which the map now points.

## Findings

- map-1: fixed in §2, DateFragment row: "any format of the shared temporal vocabulary, under `formatOfFragment`", linked to spec/05 §6.1 (`#61-fragments`), which states the whole vocabulary is admitted.
- map-2: fixed in §2, DateRange row: "a declared `(format, separator)` pair, one of eight admitted", linked to spec/05 §8 (§8.1 owns the eight pairs).
- map-3: fixed in §0: the old legend ("observed, not exhaustively pinned", "⚠ trap") is replaced by a table of the vocabulary the chapters use (`Measured scope`, `Measured members … others unmeasured`, `unmeasured`/`not measured`, `source reading`, `no witness known`, `not stated`, ⚠), each with what it binds. Counted in the current chapters: unmeasured 182, not measured 5, source reading 48, no witness 13, not stated 404, Measured scope 61, Measured members 16, ⚠ 19, "not exhaustively pinned" 0, "external evidence pending" 0.
- map-4: fixed. Opening paragraph declares the map non-normative and chapter-wins; §5's lead no longer says "assert them as global laws" but "each restates the linked clause, which owns it"; every invariant links its owning clause rather than `#3-the-taxonomy`; §2 gains an Owner column; the glossary gains a "Defined in" column; §8 no longer calls the map plus a deep dive "the normative route"; §1.5 no longer restates data model §4.3's four placement rows, only names the actions and links the table.
- map-5: fixed in §1.1 (a third bullet naming declaration legality: consistency rules, generation classes, variant filters, with links to data model §1.2–§1.4) and in §3's spec/01 row.
- map-6: fixed in the glossary: "phantom row" now follows data model §2.2 (partial validation only; full validation's declared-slot visits are a separate notion). spec/07 no longer uses "phantom first-row anchor"; its §1.1 table says the uniterated address "is not the partial-validation phantom row", so one term per notion now holds.
- map-7: fixed. The four Lean/implementation directions (old map:63, map:75, map:132, map:138) moved to docs/LEAN-ENCODING-GUIDE.md §1: HIGH added the no-polarity-flag `Rule` bullet; the other three duplicated guide text already there.
- map-8: fixed. §3 lists every chapter in file order, spec/13 (navigation stub) and spec/14 (operator reference) included, one row per taxonomy area; a sentence explains that `§n` follows areas rather than files and which files carry none; "How to read" states the link-label convention (`§n` taxonomy number, "data model §n", "concrete syntax §n", "operator reference"), which removes the "§12" collision. §8 now only gives reading order, so spec/13 is no longer missing there.
- ch02-3 (map half, from 02 notes): fixed in §4 item 1 and the glossary's not-check-relevant row: the third state is "carries a formal finding", which need not be a stored value, and partial-validation non-relevance is a call-local UNKNOWN source, not a cell state (spec/02 B.2).
- ch02-5 (map half, from 02 notes): fixed in §4 item 2 (now "UNKNOWN comes from the data, never from a connective") and the 3VL/Kleene glossary row; "connectives are two-valued" is gone.
- ch03-1 (map half, from 03 notes, map:152 and map:182): fixed in §5's content-gate invariant and the glossary's row-gate row: the four admitting conditions of spec/03 A.4 (composed leaf class, small-side count lift, second root, uniterated repeatable error root), pointing to operator reference column B.
- 07 notes, spec/01 line (ch07-5, map-6): not applicable to this chapter; it edits spec/01, which has landed with the distinction (data model §2.2).
- 05 notes (map-1, map-2) and 01 notes (map-5): applied as above.
- C5 process voice (map:18, map:223, map:229; reported but not verified by the audit): addressed anyway: the confidence chatter, §9's "optional for reading … mandatory when changing" process rule and §10's obligation sentence are gone.
- Implementer feedback (`feedback.md`): no row names SEMANTICS-MAP; nothing to apply.

## Behavioural decisions

Each old map statement below differed from a landed chapter. The map is declared non-normative and the chapter wins (run instruction), so each was resolved by citing the chapter sentence that already decides it; none needed a Lean decision.

1. DateFragment format vocabulary (map-1). Old map:93: "fragment format (`MM`, `yyyy`, `yyyy-MM`, `MM-dd`)". spec/05 §6.1: "its declaration admits the whole temporal vocabulary … not a narrower fragment-shaped one". Taken: spec/05.
2. DateRange separator (map-2). Old map:94: "endpoint format; separator `/`". spec/05 §8.1: "admitted for exactly eight `(format, separator)` pairs", `-` and the empty separator included. Taken: spec/05.
3. DateRange construction endpoints. Old map:94: "`DateRange` construction takes matching-component DATE/DATE_FRAGMENT entity endpoints". spec/05 §8.4: "each endpoint is admitted by its declared format alone … the kind takes no part" (TIME/DATE_TIME `yyyy-MM-dd` admitted). Taken: spec/05.
4. Connectives two-valued (ch02-5). Old map:134: "Connectives (`And`/`Or`) and predicates are two-valued; the third value ('unknown') enters only when an operand reads an invalid cell". spec/02 A.1: "The connectives introduce no truth value of their own"; B.4: `FieldFilled(malformed)` is UNKNOWN. Taken: spec/02.
5. The third state's definition (ch02-3). Old map:132: "a cell can be **not-check-relevant** because of formal invalidity". spec/02 B.2: "while it carries a formal finding … it need not hold a value … Non-relevance under partial validation is not a cell state". Taken: spec/02.
6. Aggregates over an invalid cell. Old map:132: "it is counted as neither filled nor empty, makes aggregates non-evaluable". spec/02 B.2: per consumer class — `all-cells` UNKNOWN, `stop-at-first` only when reached, `skip-invalid` (`FieldValuesNotUnique`) skips. Taken: spec/02 ("an all-cells aggregate over it UNKNOWN").
7. Once-evaluation. Old map:150: "A rule with no iteration-bearing repeatable condition reference evaluates exactly once". spec/07 §1.1: "At most once, anchored at its error entity … subject to the whole-condition content gate". Taken: spec/07 ("at most once").
8. Typed equality. Old map:155: "Typed equality throughout … enums by stored value, dates chronologically — never by stored string." spec/07 §3.6: "`FieldValuesNotUnique` compares a temporal operand's exact stored text"; `RepetitionNotUnique` "the exact stored text". Taken: spec/07 §3.6 (each carrier its own identity).
9. Same treatment of invalid values in both operations. Old map:52: "the same operators, the same treatment of empty and invalid values apply to a rule condition and to a computation's operation". spec/02 B.6: "The two operations treat the third state with opposite temperament". Taken: spec/02.
10. Empty Number in aggregates. Old map:181: "a Number reads a fillable `0` in comparisons/aggregates". spec/03 A.2: "`Sum` / `MaxValue` / `MinValue` drop the empty cell from the fold". Taken: spec/03 (glossary now names the kind default without "aggregates").
11. Time and DateTime "extend Date". Old map:91–92: "**DateTime** (extends Date)", "**Time** (extends Date) … operand for `HoursFromTime`". spec/05: "The format decides, never the kind"; §9: a DATE `HH:mm:ss` is admitted by the clock extractors. Taken: spec/05.
12. DateFragment completion. Old map:93: "completes to a concrete date at evaluation". spec/05 §6.1: "Where an operation needs a concrete Date and the model declares a Base Year, a fragment completes to its earliest concrete date". Taken: spec/05.
13. TypeDefinition legality timing. Old map:96: "legality is the underlying type's, known only after model expansion". data model §5: static admission "still reads type definitions"; a typedef field is its base kind at every gate tested. Taken: spec/01.
14. Compute outcome vocabulary. Old map:188: "per computed cell: **VALUE** …, **CLEARED** …, or **ERRORED**". spec/09 §2: "Each computed instance evaluates to one of five outcomes"; the actions are "derived from the evaluation outcome afterwards". Taken: spec/09.
15. Content gate (ch03-1). Old map:152: "an all-empty instance is evaluated only by a complete condition structurally classified as able to fire on emptiness". spec/03 A.4: four admitting conditions. Taken: spec/03.
16. `Having` consumer. Old map:191: "filters a `*`-path to the rows where a condition holds, before an aggregate consumes it". spec/07 §3: "before an aggregate or quantifier consumes it". Taken: spec/07.
17. Computation write-back. Old map:50: "produce new **values** for computed fields (write-back)". data model §4.3: compute returns a result; `apply` is a separate placement-sensitive step. Taken: spec/01.
18. Date literal shape. Old map:90: "constants are `DD.MM.YYYY`; a string literal matching that format *is* a date". spec/05 §1: the shape must name "a real date of the legacy hybrid calendar"; `"29.02.2023"` is a String. Taken: spec/05 ("naming a real date").
19. Division by zero. Old map:112: "quiet div-by-zero". spec/04 §3: "what that means depends on the consuming construct"; spec/09 §3.2: a domain failure at a Number target emits `berechnungsWertFehler` and poisons. Taken: spec/04 and spec/09 ("consumer-sensitive domain failures").
20. Polarity basis. Old map:138: "each operand tracks 'could this still grow / still shrink' … the enclosing comparison's direction decides". spec/10 §4: "Date/Time/DateTime operands and Strings carry a single *not-given* bit instead". Taken: spec/10 (§4 item 4 adds the not-given bit).

## Unresolved

- None. Host API scope (ch01-11) is settled: data model §2.1 states the host pointer API normatively and data model §5 does not exclude it, so the map no longer calls the host API out of scope.

## Rules not kept

Map-only statements, needing a chapter owner:

- Old map:93, DateFragment row, empty column: "not evaluated". Landed: HIGH places it in spec/03 A.1 in this change (Lean-confirmed, unmeasured); the map cell says **not evaluated** and links spec/03 A.1.
- Old map:94, DateRange row, empty column: "not evaluated". Landed: spec/03 A.1, placed by HIGH in this change (Lean-confirmed, unmeasured); the map cell says **not evaluated** and links spec/03 A.1.
- Old map:95, Custom row, empty column: "as a **string**". Landed: spec/03 A.1, placed by HIGH in this change as an empty Custom value reading as the String kind, so a comparison over it is not evaluated (Lean-confirmed: the Custom kind maps to String and an empty String comparison operand is not evaluated; unmeasured); the map cell says "as a String: not evaluated" and links spec/03 A.1. spec/06 A.3 keeps "an empty … cell is excluded before the oracle is sampled", which the map also keeps.
- Old map:16: "The kernel's Java/host API surface" is out of scope. Dropped: data model §2.1 states the host pointer API normatively and the chapter wins; map §0 now says the host pointer API is not excluded and points to data model §2.1.

Removed or reworded sentences carrying a scope or closing word, with where the content now lives:

- map:8 "The clauses are normative. Clearly labeled **Non-normative implementation notes** … do not own project status or alter the behavioral account." → map "How to read" (notes carry implementation advice only); spec/CLAUDE.md owns the note rule.
- map:15 "Revision chronology does not belong in this semantic map." → dropped as process; spec/CLAUDE.md ("Do not append … review chronology").
- map:16 "These are touched only where they change evaluation (mainly full-vs-partial validation, and the compute→apply→validate flow)." → kept in §0 without the parenthetical examples; data model §5.
- map:17 "a line-by-line port … would be a derivative work … Copy the *mechanism*, never the *expression*." → §0 clean-room bullet keeps the mechanism/expression rule; the legal characterization is project policy (CLAUDE.md), not a semantic rule.
- map:18 "Most are settled behaviour verified against kernel 30.8.1 …; a few carry the caveat *'observed, not exhaustively pinned'* inline." → replaced by §0's vocabulary table (map-3); the Groovy-dynamic anchor and static-Java co-evidence are data model §5.
- map:28 "non-repeatable (occurs at most once)" / "repeatable (an array: zero or more rows, up to a declared `repeatability` bound)" → §1.1; data model §1.
- map:31 "the kernel has no single word for it" → dropped: a negative existential about Kernel vocabulary with no measurement and no rule content; the cell definition is data model §2.
- map:52 "Both are expressed in the **same** language — the same operators, the same treatment of empty and invalid values" → §1.2, corrected (decision 9); spec/09 intro, spec/02 B.6.
- map:56 "A rule has exactly **one** condition slot … There is no 'assert this holds' form." → §1.3; data model §3.1.
- map:63 "A positively-phrased 'requirement' is structurally legal but encodes the opposite rule — a mistake the engine cannot catch." → §1.3 reworded ("admitted like any other, since admission does not decide satisfiability"); spec/02 B.1. Its Lean sentence → docs/LEAN-ENCODING-GUIDE.md §1 (map-7).
- map:67 "only **ERROR** messages make the document invalid" → §1.4; spec/10 §2, data model §4.1.
- map:69 "computed from the data (not fixed per operator)" → §1.4; spec/10 §3–§4.
- map:74 "It guarantees only one direction — it never reports an error that could only be fixed outside the subset — and may skip some checks" → §1.5; data model §4.2.
- map:75 "**Validation never computes first.** … ERRORED empties only an existing target and never creates an absent one, and a source outcome that minted no action preserves destination absence." → §1.5 keeps the first sentence and names the actions; the four placement rows live only in data model §4.3. Its Lean sentence → docs/LEAN-ENCODING-GUIDE.md §1 (map-7).
- map:85 "scale **gates `==`/`!=`** at parse time; ordering is scale-exempt; empty is *ignored* by min/max aggregates" → §2 Number row; spec/04 §1.2, spec/03 A.2.
- map:86 "an unset boolean is neither `== True` nor `== False`" → §2 Boolean row; spec/02 A.3.
- map:88 "there is no empty string (`== \"\"` never holds)" → §2 String row (adds `!= ""`); spec/03 A.1.
- map:94 "only `==`/`!=` (no ordering) … cannot nest in overlap/bound extraction; overlap is inclusive" → §2 DateRange row; spec/05 §8 lead, §8.6 ("intervals are closed").
- map:95 "an empty cell does not invoke the validator" → §2 Custom row; spec/06 A.3.
- map:96 "legality is the underlying type's, known only after model expansion" → §2 TypeDefinition row (decision 13); data model §5.
- map:98 "`[Amount] < 100` **fires** on an empty amount … `[Date] > \"01.01.2022\"` **stays quiet**" → §2 trap paragraph; spec/03 A.1.
- map:104 "Fourteen numbered areas cover the language." → §3 table (fourteen `§n` rows), sentence dropped.
- map:108–121 taxonomy one-liners, rebuilt from the chapters' section headings; phrases with closing words: "no generic `Not`; explicit parens required" → §1 row (spec/02 A.1–A.2); "group-list predicates share one field/group/star-row presence tally" → "fill quantifiers and group scopes" (spec/02 A.4); "quiet div-by-zero" → "consumer-sensitive domain failures" (spec/04 §3); "list-preserving expression-valued `Min`/`Max`; temporal-derived Number sources; staged numeric value functions" → "operand-list `Min`/`Max`, value functions and Number-valued sources" (spec/04 §4.3–§4.5); "anchored Java-Pattern semantics behind a limited two-stage gate" → "pattern admission and execution" (spec/06 A); "ordinary scope comes from compatible condition references, not error placement; negative admission is level-, connective-, operator-, and operand-sensitive …" → "iteration scope from condition references … the negative-condition guard" (spec/07 §1.1, §1.8–§1.10); "starred `..` needs absolute while later named stars remain legal" → "star placement" (spec/08 §1); "rich V2 result, eager formal-operand prepass, and change projections" → "five outcomes and their change actions; the eager formal-operand inventory" (spec/09 §2, §3.3; data model §4.3); "two fixed String-pattern tokens …, whose parameters are split pieces with trailing empty pieces dropped; one-pass opaque replacement" → "field-owned producers" (spec/11 A.13); "barred in compute + filters" → "refused in computations and filters" (spec/11 B.2).
- map:132 "There are at least three semantic cell classifications, not two" → §4 item 1 "three cell states" (spec/02 B.2: "A cell is in one of three states"); "makes aggregates non-evaluable" → decision 6; "suppresses undecided rule branches" → §4 item 2 (spec/02 B.4); "A two-state (`Option Value`) domain cannot express this" → spec/02 B.2 owns it ("why a two-state value domain cannot model the language"), and the Lean sentence → docs/LEAN-ENCODING-GUIDE.md §1 (map-7).
- map:134 "only the *data* is three-valued … **branch-scoped, not rule-scoped**" → §4 item 2 (decision 4); spec/02 intro and B.4.
- map:136 "the count family never counts an empty" → §4 item 3 ("the cell counts never count an empty"); spec/03 A.2 "The count family".
- map:138 "It is not a per-operator constant … Under `And`, omission wins; under `Or`, value wins." → §1.4 and §4 item 4; spec/10 §3–§4. "A faithful engine evaluates *two* things per node" → already in the guide's `Verdict` bullet and trap 4.
- map:140 "so an invalid cell that a given evaluation never actually reads never poisons it. Two documents that differ only in evaluation order can differ in output." → §4 item 5 keeps the first sentence; the second becomes the "order-dependent" heading; spec/09 §3.2 ("read-driven, therefore order-dependent"; "A lowering rewrite can therefore change which of two poisoned field reads is encountered first").
- map:146 "These hold across the whole language; a reimplementation can assert them as global laws." → §5 lead "each restates the linked clause, which owns it" (map-4).
- map:149 "Each negative check is a dedicated predicate … positive/negative pairs cannot be assumed to be full-verdict negations" → §5; spec/02 A.2, spec/05 §3.6.
- map:150 "never placement or the error entity … evaluates exactly once … does not select a level … concrete row 1, while star-bearing `referenced` operands preserve wildcard `0`" → §5 (decision 7; adds the reanchoring exception spec/07 §1.1 states); spec/07 §1.1, data model §3.1 ("A starred *field* retains wildcard `0`").
- map:151 "There is no `[Field At n]`, no neighbour offset … never one to select with; the only row-selection form is the semantic index" → §5; spec/08 §4.
- map:152 "only content-bearing instances evaluate … an all-empty instance is evaluated only by …; Negative-presence predicates and a `CustomCondition` leaf have that property" → §5 (decision 15); spec/03 A.4 measured members, operator reference column B.
- map:153 "A formally invalid cell is UNKNOWN to every predicate, comparison, or aggregate that consumes it; author rules never make a field unevaluable, only formal errors do." → §5 ("every built-in consumer … settles it by its class", decision 6); spec/10 §1, spec/02 B.1.
- map:154 "**Every computation generates an all-alternatives validation rule.**" → §5; spec/09 §1, §6.
- map:155 "Typed equality throughout … never by stored string." → §5 (decision 8); spec/07 §3.6.
- map:163 "This section remains only as the stable bridge" → §6, kept.
- map:173 glossary "cell … The kernel has no single noun for this" → see map:31.
- map:177 glossary "not-check-relevant … built-in reads see UNKNOWN and count it as neither filled nor empty; the computation view is normally poison, with the required-empty exception" → glossary row (decision 5); spec/02 B.2.
- map:178 glossary "formal error … Selected ordinary field constraints and requiredness may carry producer-specific per-locale authored text; … `CustomCondition` is the separate host-SPI exception" → glossary row trimmed to the definition; the template rule is spec/02 B.1 ("for a String pattern, Enumeration value or requiredness check it is the field declaration's own template"), the project code and optional message spec/02 B.1 and spec/06 A.3, the host-SPI exception spec/02 B.1 and §5 here.
- map:179 glossary "Only data is three-valued; connectives are two-valued" → decision 4.
- map:180 glossary "A reached `CustomCondition` owns its Boolean after receiving the formal-invalid set." → dropped from the row; spec/02 B.4 last bullet, and §4 item 1 here.
- map:181 glossary "a Number reads a fillable `0` in comparisons/aggregates" → decision 10.
- map:182 glossary "only fire inside a *content-bearing* instance; an all-empty instance is evaluated only by …, including conditions whose `CustomCondition` branch makes that possible" → glossary row-gate row and §5 (decision 15); spec/03 A.4 (`CustomCondition` a measured `fires on empty` member).
- map:185 glossary "Read-driven, hence **order-dependent**." → glossary poison row; spec/09 §3.2.
- map:187 glossary "an ordinary fitting number padded to the target's minimum fractional digits without a length cap, with a separate warning-suppressed no-fit renderer. What downstream reads, scale-sensitive change detection, and formal checks see." → glossary row keeps "what downstream reads see"; the Number renderer is spec/09 §4.3 and its checklist, change detection spec/09 §3.3 and data model §2, the reduced formal check spec/09 §4.
- map:188 glossary "CLEARED (no value — any stale value wiped)" → decision 14; spec/09 §2.
- map:189 glossary "The error entity must be referenced and scope-compatible but does not introduce levels by itself." → §5 iteration invariant; data model §3.1, spec/07 §1.1, §1.5.
- map:190 glossary "an outer join over index values; an unmatched side reads 'not specified'" → glossary row keeps the outer join; the unmatched side is spec/07 §2 ("binds the unmatched sentinel") and §2.4.
- map:191 glossary "`$` (only inside a filter)" → glossary row; spec/08 §3.6 ("may be written only inside a filter condition").
- map:192 glossary "the only positional-free row lookup; … never by ordinal position" → glossary row; spec/08 §4.
- map:193 glossary "in partial validation, a row in the relevant set that does not physically exist … is still evaluated" → glossary row (map-6); data model §2.2.
- map:194 glossary "global fields are auto-added" → glossary row; data model §4.2, spec/10 §5.1.
- map:195 glossary "a *static* property of the field, checked at parse time" → glossary row ("static"); spec/04 §1.
- map:218 "Read in file order for a first pass. This map plus the relevant deep dive is the normative route" → §8 (map-4).
- map:224 "Verification against source or maintained differentials is optional for reading this specification but mandatory when changing a semantic claim." and "mandatory `.st` review for generated control flow" → dropped as process; repository CLAUDE.md and docs/SOURCES.md own them.
- map:230 "This semantic map deliberately does not snapshot Lean … A semantic fact synchronized here is an implementation obligation, not evidence that Lean already implements or mechanically excludes it." → §10 keeps the pointer; the obligation sentence is process and dropped (spec/CLAUDE.md).

## Other chapters

- spec/03 A.1: HIGH placed the three map-only empty reads there (DateFragment and DateRange not evaluated, Custom read as the String kind and so not evaluated), unmeasured; the map rows link it.
- spec/01 §5 (ch01-11): settled without an edit; §5 does not exclude the host pointer API, which §2.1 states normatively.
- spec/01 lines 5 and 14: they say the glossary, the taxonomy and "the type table" are in SEMANTICS-MAP and that terms such as *cell*, *row* and *not-check-relevant* are "defined there". With the map non-normative, say the map summarises them and that the definitions are data model §2 and spec/02 B.2; keep the `#2-field-types-at-a-glance` link as navigation.
- docs/LEAN-ENCODING-GUIDE.md §1: done by HIGH (map-7).
- Sync ledger: decisions 1–17 adopt sentences landed chapters already state, so they change no chapter; HIGH classifies whether removing the old map's own statements (and the three map-only empty reads, if no chapter takes them in the same change) needs a `SPEC-` entry.

## Anchors

- `#2-field-types-at-a-glance` (linked from spec/01 line 14): §2 heading unchanged.
- `#13-a-rule-states-the-error--and-that-polarity-is-fixed-` (linked from spec/01 line 408): §1.3 heading unchanged.
- `#a12-kernel-validation-language-semantics-mapped-for-a-lean-reimplementation`, `#a12-kernel--validation-language-semantics-mapped-for-a-lean-reimplementation`: explicit anchors kept at the top (no inbound link found).
- `#6-lean-encoding-orientation`: explicit anchor kept in §6 (no inbound link found).
- Every other section heading (§0–§10, §1.1–§1.5) is unchanged, so their generated anchors survive. All links in the new map were checked against the current chapter headings with the repository checker's slug rule: none broken.

## HIGH review (2026-10-27)

- Preservation check: 151 old statements; 110 kept, 1 generalised, 37 declared changes, none lost and three altered, all now declared as decisions 18–20 because each follows its chapter (real-date Date literal, division by zero as a consumer-sensitive domain failure, the not-given bit of temporal and String operands).
- The four map-only rules found owners: the empty DateFragment, DateRange and Custom reads went to spec/03 A.1, marked unmeasured, and the host pointer API stays in scope as data model §2.1 states it. The drafter's Custom cell "an empty String" was corrected to the String kind's not-evaluated read, which the old map and Lean both give.
- spec/01's two lines that called the map the definition site, the evaluator kit's "map first" row and the Kernel 31 proposal's line citation were repointed. The Lean-specific map guidance moved to the encoding guide.
- Behavioural changes ship as SPEC-2026-10-26-30.
