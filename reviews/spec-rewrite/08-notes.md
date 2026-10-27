# spec/08 rewrite — change notes

Draft: [08-new.md](../../spec/08-new.md). Revised operator reference: [14-new08.md](14-new08.md) (column K). The draft keeps every `§n` number and every linked heading; the old §3 bullets became §3.1–§3.6 and §4's lead paragraphs became `####` blocks before the unchanged §4.1–§4.3.

## Findings

- ch08-1: fixed. §4.1 now opens with the parent-scoped index column and one definition of a compromised (not formally available) column by an explicit cell list, without spec/02 B.2 (whose required finding is validation-only): an in-capacity index cell that is empty, duplicated (`uniqueIndex`), formally invalid; over-capacity rows excluded — and a yields table: clean no-match = empty, compromised no-match = UNKNOWN (validation) / poison (computation). §4.2 keeps the phase strictness and points partial validation to spec/10 §5.5. See behavioural decisions 1 and 2.
- ch08-2: fixed. §4.3 states the full eligibility rule taken from spec/07 §2.3 "Selected targets below an indexed group" (ordinary reference keeps physical iteration, authored-syntax identity, deepest error-containing selector, distinct keys keep ordinary iteration, sibling payloads add nothing, target below indexed group, compute overlay) and adds that a runtime failure is not reanchored (spec/10 §3.1 already decides the iterator's first address; Lean `reanchorSelectedError`, `A12Kernel/Elaboration/ValidationRule/Execution.lean`, agrees).
- ch08-3: fixed in the chapter. §3.2 is an ordered gate table for the bracketed read (reader classes and containment, group, star, value gates); §3.3 is a per-parameter outcome table. The measured-carrier lists stay as one "Measured scope" paragraph per subsection rather than moving to `docs/`, because this run writes no repository file and brief rule 8 asks for measured-member statements; moving them to a checkpoint is deferred to HIGH.
- ch08-4: fixed. §3.4 has a category class table (`projected`, `category refused, before repeat`, `category refused, after repeat`, `category refused`), names the three counts (`NumberOfFilledFields`, `NumberOfFilledGroups`, `NumberOfDifferentValues`, confirmed against the archived 2026-09-26b record and the old list), labels the list measured-only, and moves the per-operator membership to spec/14 column K.
- ch08-5: fixed. §4 "The key and the index group" states the star-position rule generally (decision 5); "certain predicates" is replaced by column K's `index refused` cells (`NumberOfFilledGroups`, `RepetitionNotUnique`) plus the filter-body refusal of spec/07 §3.1.
- ch08-8: fixed. §2 gives the condition-side class of a non-matching turning point, `MVK_INVALID_ENTITY`, marked unmeasured (decision 3).
- ch08-9: fixed. Root/fixed-group index: §4 "The key and the index group" (decision 4). Boolean `J`/`N`: the shape table says a Boolean admits exactly `true`/`false` whatever its stored values, refusing the keys `J` and `N` — measured, per the archived 2026-09-26 index-key record (`docs/archived/SOURCES-INBOUND-HANDBACKS-2026-09-25i-THROUGH-2026-09-26.md` at `3831425d`), and Lean `IndexKeyShape` (`.boolean => key == "true" || key == "false"`); not a behavioural change.
- ch08-10: fixed. Old 08:73 is split by responsibility: unquoted keys merged into the §4 lead (deduplicating 08:61), "The literal key's shape, one rule per kind" (table), "Key identity at lookup", the kind-pairing table under "A defective key answers before the operand's gate", selectability and keyed-parent stars into §4.1. §4.3 stays in spec/08 (ten inbound links, spec/07 points into it) with the duplicate-key content under a `####` block and the OpenJDK 21 profile as a scoped normative profile; moving it to spec/01 or spec/11 is left to HIGH.
- ch08-11: fixed. §1 (empty groups) and §3.1 (starred paths) each state their measured scope in one sentence instead of deferring to a checkpoint.
- C5 process voice: fixed. The `[Tier]` history (08:33) is now a plain example; 08:105/08:115 narrative is reworded as measured scope; "Confidence limit" sentences (08:83, 08:85, 08:86) became "Measured …" scope sentences; test-file provenance (08:37) moved to §2's Sources line. Every checkpoint/inbound/a12-dmkits link left the rule sentences for one Sources line per section; KF599/KF602/KF605 map to `src-inbound-2026-10-23`, KF532 to `inbound-2026-10-09-extensions`, KF395/KF405 to `src-field-value-read-predictions`, KF328 to the `R70` sweep row; KF479 and KF351 have no local record and stay as a12-dmkits links in §4's Sources line.
- xc-3: fixed on the spec/08 side. §4.3 says the replaced level would otherwise be pinned to coordinate 1 and links spec/07 §1.1; spec/07's half already landed.
- ch05-14: fixed on the spec/08 side. The read ladder is one general table (§3.2), so spec/05's per-carrier lists can cite `#32-the-field-value-read-`.
- ch05-15: fixed on the spec/08 side. §3.2's gate is stated for every bracketed read, which covers operand-list `Min`/`Max`'s value slots; spec/05's precision table is spec/05's.
- ch06-3: fixed. §3.2 (a bracketed read draws `MVK_INVALID_RAW_TYPE`) and §3.3 (a parameter meets its operator's own gate, with the per-operator raw classes) state both halves.
- ch11-9: not applicable here; spec/11 A.7 already uses the per-kind wording, which matches spec/08 §4's shape table.
- ch12-17: fixed on the spec/08 side. §1 keeps path legality (up-steps, star on `..`); the walk triggers are now a pointer to concrete syntax §3.1 instead of a restatement.
- 12-notes (08:15 relabel): fixed; the link reads "concrete syntax §3.1" with `#31-which-class-a-refused-text-draws`.
- 07-notes (§4.1 compromised; §4.3 eligibility): fixed. 07-notes (take spec/07 §3.1's filter-walk-against-a-key paragraph, ch07-26): not applied — landed spec/07 §3.1 keeps that paragraph with an explicit split ("§10 owns whose filter …; its walk is this chapter's"), so taking it would duplicate; spec/08 §4 "A filter after a key" points to it. Listed under Unresolved.
- 09-notes (define the compromised column once): fixed in §4.1.
- 14-notes, 02/03/04/05/06/10/11-notes: no item names spec/08.
- feedback D row (spec/08 L11, keyword quoting found only here): reader signal; §1 now states quoting as its own rule for every path. Whether the generated rule's `[F]` quotes a keyword segment stays spec/09's inference; no rule added.
- feedback E row (spec/08 L105, host-order addresses): reader signal; §4.3 now says plainly that the cache order or association is an explicit input for duplicate-key addresses and isolates the OpenJDK 21 profile; no rule change.

## Behavioural decisions

1. Validation no-match over a compromised column.
   - Old 08:92: "an *unresolvable no-match* over a column that contains **any** not-check-relevant cell **suppresses** the referencing rule."
   - Old 08:80: "Crucially, a no-match is **empty, never "unknown"**."
   - Taken: a clean no-match is empty; a no-match over a compromised column reads UNKNOWN, which suppresses only by spec/02 B.4's branch-scoped rule (not "the referencing rule" as a whole). Lean `semanticIndexSelected` and `ResolvedSemanticIndexColumn.lookupKey`, `A12Kernel/Semantics/SemanticIndex.lean` (validation: match → observe; no match with `unavailableKey` → `.unknown`; otherwise `.empty`). Already decided for the parallel join by spec/07 §2.3 ("compromises an unresolved column to UNKNOWN") and for a duplicate cell by spec/03's checklist ("a duplicate cell is UNKNOWN in validation").
2. What compromises a column.
   - Old 08:93: "**Compute-side** is **stricter — per column**: any invalid cell in the index column clears every reading computation".
   - Old spec/09:458: "Any invalid cell in the index column — malformed, duplicated or empty — clears every computation reading that parent-scoped column".
   - Taken: any in-capacity index cell that is empty, duplicated (`uniqueIndex`) or formally invalid, stated as an explicit list in either phase; a row beyond declared capacity contributes nothing, marked unmeasured for the semantic index. Lean `CheckedIndexPreliminary.scanIndexRows`, `A12Kernel/Elaboration/CheckedIndexColumn.lean` (skips `addressOverLimit?` rows, records the first finding of each in-capacity index cell as `unavailableKey`, excludes duplicate participants). The over-capacity exclusion is measured only for the parallel join (spec/07 §2.3).
3. A turning point that does not match, in a condition.
   - Old 08:36: "the trailing `Name` merely *names* (and validates) the ancestor landed on — a matching `..Name/rest` resolves exactly like `../rest`." (no class given)
   - Old 11:35 (message side): "a turning point naming another group than the one the walk reaches | `INVALID_ENTITY`"
   - Taken: `MVK_INVALID_ENTITY`, marked unmeasured in a condition. Lean `FlatModel.resolveFieldDeclarationUnchecked` with `GroupPath.matchesTurningPoint`, `A12Kernel/Elaboration/Flat/Model.lean` (throws `.invalidEntity`, projected to `MVK_INVALID_ENTITY`); conformance example in `A12Kernel/Conformance/Elaboration/Static.lean` (`wrongName`).
4. Which group a key addresses; an index on the root or a fixed group.
   - Old 08:64: "An index declared on the root or on a fixed group addresses no repetition."
   - Old 08:70: "the index group, the nearest group on the entity's chain declaring an index field"
   - Taken: the index group is the nearest *repeatable* group on the chain declaring an index field; a chain with none draws `MVK_NO_INDEX_FIELD` (measured on an unindexed chain; a chain whose only index is the root's or a fixed group's is marked unmeasured). Lean `FlatModel.semanticIndexGroupForPath?`, `A12Kernel/Elaboration/SemanticIndex.lean` (filters `repeatableGroupAtLevel?` with an index field; none → `.missingIndexField` → `noIndexField`). spec/11 A.7 states the message-side twin ("the field's nearest enclosing repeatable group that declares an index field").
5. The star-position classes, from two operators to every keyed operand.
   - Old 08:70: "`NumberOfFilledGroups` and `RepetitionNotUnique` instead refuse … and a star draws the class of where it stands against the index group"
   - Old 08:68: "The semantic index is **unsupported** with a star at or above its index group, and with certain predicates"
   - Taken: the rule is general (at the index level `MVK_SEMANTIC_INDEX_AND_WILDCARD`, above `MVK_SEMANTIC_INDEX_BELOW_WILDCARD`, in the key `MVK_SEMANTIC_INDEX_WITH_WILDCARD`, below none). Lean `indexScan`, `A12Kernel/Elaboration/IterationLegality.lean` (a semantic-index level under an outer wildcard → `semanticIndexBelowWildcard`), and `semanticIndexAdmissionRefusal`, `A12Kernel/Elaboration/SemanticIndexAdmission.lean` (starred key → `semanticIndexKeyStarred`; star at the index level → `semanticIndexAndWildcard`, last stage). The old text already used these classes on `Sum` (08:63 `BELOW_WILDCARD`, 08:71 `AND_WILDCARD`, `WITH_WILDCARD`).

## Unresolved

- Lean disagreement, not a decision: §4.3's "deepest error-containing selector whatever the operand order" (moved from spec/07 §2.3) rests on Kernel source reading (`src-selected-error-reanchoring`) and is now marked source reading, unmeasured. Lean `ValidationCondition.uniqueErrorSelection?`, `A12Kernel/Elaboration/ValidationCondition/ErrorSelection.lean`, reanchors only when every selection shares the first one's key and level, and otherwise keeps ordinary iteration. A discriminator would be two error-containing selectors at different depths.
- Old 08:49's "as it does before the substring operators' gates" is kept verbatim in §3.3; the referent is probably `RangeAsString`/`RangeAsNumber`, but the parameter checkpoint records no unstarred-repeatable row inside `RangeAsNumber`, so the table cell stays `not stated`.
- ch07-26 (take spec/07 §3.1's "A filter written after an entity key is walked against the key"): not taken, because landed spec/07 owns the walk explicitly; if HIGH prefers the 07-notes plan, spec/07 deletes the paragraph and spec/08 §4 absorbs it.
- The Lean admission cascade (`semanticIndexAdmissionRefusal`, thirteen ordered stages including `MVK_SEMANTIC_INDEX_NO_FIELD`, `MVK_SEMANTIC_INDEX_WITH_SEMANTIC_INDEX`, `MVK_SEMANTIC_INDEX_WITH_CATEGORY`) orders more defects than spec/08 states; no finding asks for it, so nothing was added.

## Rules not kept

None lost. Every old sentence carrying a scope or closing word that was removed or reworded, with its new home:

- 08:4 "rows are addressed by semantic key, never by position" → intro and §4 heading.
- 08:13 "In every operand gate measured … only the unquoted keyword is the group" → §1 `RuleGroup` paragraph.
- 08:15 "The one combination that *requires* absolute: the `*` may not be attached to a relative `..` step" → §1 "A `*` may not stand on an up-step … must be written absolute".
- 08:16 "An up-step stands only in a relative path's leading run"; "nothing before it is resolved"; "only a prefix that clears its gates reaches the token refusal"; "Up-steps chain only through `/`"; "A message parameter never walks the prefix: every misplaced up-step there draws …" → §1 up-step paragraph and table. "and a `$` mark is measured there as a third" → §1 "where a `$` mark is a third", walk owned by concrete syntax §3.1 (which states the `$` trigger).
- 08:17 "Direct lookup under the declaring group is always attempted; the model-wide fallback requires …" → §2 tiers 1 and 2.
- 08:18 "every operand naming one is refused"; "on every group carrier measured"; "ahead of every list gate"; "The empty-group checkpoint owns the matrix and its limits" → §1 empty-group bullets and its measured-scope sentence.
- 08:24 "exactly two tiers" → §2 lead.
- 08:27 "Only on a miss … over fields only" → §2 tier 2.
- 08:28 "never a silent pick" → §2 tier 2.
- 08:32 "and **never a later segment**; no row measures a path behind an up-step" → §2 "only the first segment … never a later segment; a path behind an up-step is unmeasured".
- 08:34 "There is **no implicit ancestor walk** … reachable only through …"; "with the flag off, the same reference is rejected" → §2 (history sentence dropped, example kept).
- 08:36 "the up-count comes **only** from the `..` tokens" → §2 turning-point paragraph.
- 08:38 test-lock provenance → §2 Sources line.
- 08:40 note "Do not add an implicit ancestor tier; parent lookup requires explicit `..`" → §2 rule plus note "Add no ancestor tier".
- 08:46 "every repeatable group below it in the path must also use `*`" → §3.1 lead.
- 08:47 "A star may land only on a repeatable group"; "draws `MVK_INVALID_WILDCARD` and nothing else"; "measured at every position listed"; "Alone holds per defect, not per condition"; "The starred-path checkpoint owns the matrix" → §3.1 bullets and measured-scope sentence.
- 08:48 "wherever it stands"; "a star on the level the rule iterates is refused too" → §3.2 lead and paragraph under the table.
- 08:49 "The star and group gates are measured on … and the raw and partial-Date gates on those carriers but a filter's body"; the computation-target measured lists → §3.2 measured scope. "An unstarred repeatable level meets the walk first" → §3.4 lead. "The three counts ask it ahead of the list's repeat, and the other carriers measured behind it" → §3.4 class table and measured scope. "not the read's value gates" → §3.3 lead.
- 08:50 measured lists of the repeatable host → §3.5.
- 08:51 "`$` may be used **only inside a filter condition**, and not every reference in the filter may be `$`-marked" → §3.6 "may be written only inside a filter condition" plus pointer to spec/07 §3.1–§3.2 for "some filter reference stay unmarked" (spec/07 §3.2 states "At least one unmarked reference must reach a repeatable level reopened by the filtered operand").
- 08:59 "The language has **no positional row addressing**" → §4 lead.
- 08:61 "cannot stand alone"; "not only a repeatable level"; the measured scope → §4 `CurrentRepetition` paragraph, table and scope sentence.
- 08:62 "The **only row-selection form**" → §4 semantic-index paragraph.
- 08:64 "and only that level"; "each operand gate measured"; "An index declared on the root or on a fixed group addresses no repetition" → §4 "The key and the index group" (decision 4).
- 08:66 "in every selection carrier measured" → §4 defective-key paragraph.
- 08:68 "unsupported with a star at or above its index group, and with certain predicates; a star below the index group is admitted" → §4 star-position bullet, column K `index refused`, filter-body bullet (decision 5).
- 08:70 "No admission verdict transfers to an operator absent from this measured matrix" → §4 "Keyed operand admission" lead and spec/14 K measured scope.
- 08:72 "a string key is a literal and takes none" → §4 "A filter after a key".
- 08:73 "Its digits are ASCII on every index kind"; "a field declaring no fraction admitting none"; "a Confirm key is only `true`"; "the empty key is refused on a String index"; "captured backreferences are unmeasured"; "never a label"; "For every non-Number index field, lookup uses exact internally stored text"; "measured as **UNKNOWN** rather than empty"; "reporting only its own class"; "on both runtime strategies"; "on the pairs measured" → shape table and its bullets, "Key identity at lookup", §4.1 yields table and keyed-parent-star block, kind-pairing paragraph.
- 08:76 "exactly one non-overlapping pass"; "A **Custom** index field tests only its own authored positive minimum and maximum lengths" → String bullets and the Custom row ("meets only …").
- 08:80 "a no-match is **empty, never "unknown"**" → §4.1 "A clean no-match is empty, never UNKNOWN" (decision 1).
- 08:83, 08:86, 08:87 "Confidence limit: …" → "Measured on …" scope sentences in §4.1.
- 08:90 "not to every instance"; "Equal keys in different parents do not collide" → §4.1 column paragraph.
- 08:92–93 per-lookup / per-column sentences → §4.2 (decisions 1 and 2).
- 08:95 note "no match returning `empty` rather than `unknown` or `poison`"; "fail closed on a missing or ambiguous repeatable binding" → §4.2 note.
- 08:99 "one unique semantic-index key"; "Repeated occurrences … do not create competing selections; distinct … do"; "The other error-path coordinates remain unchanged"; "source-derived" → §4.3 lead and eligibility bullets, "Source-derived" scope sentence.
- 08:101 "A literal key contributes no key-field pointer"; "reference membership is not an evaluation trace" → §4.3 reference-collection paragraph.
- 08:103 "replaces only the indexed level"; "the index-field pointer stops at the selected level"; "Unknown pointer coordinates do not change the no-match value semantics" → §4.3.
- 08:105 "refute both first-physical-row and last-physical-row selection"; "an empty or formally invalid field does not contribute in the measured controls"; "physical-row order and an index-column-only fold are insufficient"; "model and document bytes alone do not determine every duplicate message address"; "neither an arbitrary stable tie-breaker nor a claim that every duplicate is ambiguous follows"; "Other host profiles retain separate calibration limits"; "covers String keys, Number payloads, selected groups and lower stars" → §4.3 duplicate-key bullets and measured-scope sentence.
- 08:107 "local to the association being queried"; "must retain all admitted entries" → §4.3 "Uncertainty is local …".
- 08:109 "An empty declared S-value supplies no default"; "Partial validation adds no such association" → §4.3 defaults bullet.
- 08:113 "A concrete index-row selection excludes the other row's association"; "it covers String keys, Number payloads and selected field/group/lower-star references" → §4.3 partial bullet and measured scope.
- 08:115 "a bin that never treeified selects the smallest physical row"; "justified only when all remaining capacity possibilities yield the same association"; "it does not calibrate every capacity or tree history" → §4.3 OpenJDK 21 profile paragraph ("other capacities and tree histories are unmeasured").
- Checklist lines 122–128 → new checklist, each item retained and extended.

Restored after the preservation check (corrections of 2026-10-27):

- S112, old 08:66 "kind meaning base type" → the first draft narrowed it ("Boolean and Confirm keys are not stated"); restored: the pairing table now has Boolean and Confirm rows and states pairing by base type (Boolean vs non-Boolean, Confirm included, inconsistent; Boolean vs Boolean pairs).
- S191, old 08:105 "the retained duplicate controls refute both first-physical-row and last-physical-row selection" → the draft's universal "neither the first nor the last physical row (measured)"; restored to the controls' scope in §4.3.
- S146/S147, old 08:73 line-terminator sentence → the draft attributed the `a\n`/`a\r`/`a\r\n`/length rows to field-valued keys; restored: those rows are literal-key static fit (String bullets), and the field-valued fact (CRLF and LF alias across lookup, uniqueness, join and pointer; lone CR distinct; `src-index-text-normalization`) is stated in "Key identity at lookup".
- S157, old 08:73 "leaves `NoFieldFilled` silent and, over a keyed star or keyed fixed group alike, `NotAllFieldsFilled` too" → the draft extended "keyed star or keyed fixed group" to `NoFieldFilled`; restored to the keyed star for `NoFieldFilled`.
- S61, gate order → the draft ranked the star gate ahead of the value gates while calling that order unmeasured; both now share rank 3.
- Duplicates removed as pointers: keyed-operand admission of indexed fields and groups (now spec/07 §3.5), the static judgment of a `$`-marked read (spec/07 §3.1), the partial no-match sentence of the keyed-group paragraph (spec/10 §5.5, pointed to once in §4.1), the "no verdict transfers" sentence (kept once, in §4 "Keyed operand admission", covering both halves of column K), and §4.1's computation column (computation reads now stated once, in §4.2).

## Other chapters

- spec/14: replace with [14-new08.md](14-new08.md): legend row K, section `### Keyed and category operands` (classes, `n/a` basis, measured scope), a K cell on every row of every operator table (separator rows extended to 16 cells), checklist line. Cells come only from statements in spec/08 §3.4 and §4, spec/06 B.4 (singular value-list subject keyed) and spec/07 §3.5 (`FirstFilledValue` category projection); every other entity-slot cell is `not stated`.
- spec/07 §2.3, "Selected targets below an indexed group" (ch08-2): now stated in spec/08 §4.3; replace the paragraph and its four bullets with a pointer to `08-paths-and-references.md#43-selected-references-in-validation-messages`, keeping only what is join-specific.
- spec/07 §3.1 "A filter written after an entity key …" (ch07-26): no edit unless HIGH moves it (see Unresolved).
- spec/09 §5.4 (09:458) (ch08-1, 09-notes): point "Any invalid cell in the index column — malformed, duplicated or empty —" to spec/08 §4.1's compromised-column definition (`#41-what-a-semantic-index-read-yields`), keeping the per-read-cell poison sentence.
- spec/10 §5.5: "the index column must be formally available" may link `08-paths-and-references.md#41-what-a-semantic-index-read-yields`, where "formally available" is now defined.
- spec/05 (05:426, 05:673, 05:760) and spec/06 (06:71, 06:122, 06:363) and spec/14 (D, F and W basis links): the links to `#3-the-asterisk-and-` still resolve; they may target `#32-the-field-value-read-` (read ladder) or, for parameter classes (06:123's `own class` row), `#33-a-field-named-as-an-operators-parameter` and, for `MVK_NO_ENUMERATION`, `#34-category-reads-and-category-operands`.
- docs/IMPLEMENTATION-MAP.md: name column K's Lean owners: `semanticIndexAdmissionRefusal` (`A12Kernel/Elaboration/SemanticIndexAdmission.lean`), `indexScan` (`A12Kernel/Elaboration/IterationLegality.lean`), and the entity-list category gates raising `categoryNotAllowed` in `A12Kernel/Elaboration/FieldEntityList.lean` and `A12Kernel/Elaboration/FieldEntityAdmission.lean`.
- docs (optional, ch08-3): the measured-carrier paragraphs of §3.2–§3.5 could move to a checkpoint with the spec keeping one scope sentence each.
- spec-sync ledger: decisions 1 and 2 restate the compromised-column rule (1 adopts spec/07 §2.3's UNKNOWN; 2 adds the Lean-derived over-capacity exclusion, marked unmeasured); decisions 3 and 4 add Lean-derived classes marked unmeasured; decision 5 generalizes a measured rule. HIGH classifies which need `SPEC-` entries.

## Anchors

- `#1-absolute-relative-and-short-name-references`: §1 heading, unchanged.
- `#2-bare-name-resolution-order-`: §2 heading, unchanged.
- `#3-the-asterisk-and-`: §3 heading, unchanged; the bracket-read ladder, the star rules and the category rules cited through it now sit in §3.1–§3.4 under it (spec/14's "refuse a starred path", "singular value-list forms refuse a starred subject" and "`GroupFilled`, `GroupNotFilled` refuse a field operand" remain stated in §3.1, §3.2 and §3.4).
- `#4-rows-are-addressed-by-semantic-key-never-by-position-`: §4 heading, unchanged.
- `#41-what-a-semantic-index-read-yields`: §4.1, unchanged; still states the no-match read spec/14's P column cites.
- `#42-per-lookup-validation-vs-per-column-compute`: §4.2, unchanged; still states validation's per-lookup rule spec/09:458 cites.
- `#43-selected-references-in-validation-messages`: §4.3, unchanged; still holds the cache population order spec/07:378 cites and the reanchoring spec/07:35–36 cite.
- New: `#31-where-a-star-may-stand`, `#32-the-field-value-read-`, `#33-a-field-named-as-an-operators-parameter`, `#34-category-reads-and-category-operands` (cited by 14-new08), `#35-reads-from-a-repeatable-or-parallel-host`, `#36-the--marker`, and the `####` anchors `#the-key-and-the-index-group`, `#a-defective-key-answers-before-the-operands-gate`, `#the-literal-keys-shape-one-rule-per-kind`, `#key-identity-at-lookup`, `#keyed-operand-admission` (cited by 14-new08), `#a-filter-after-a-key`, `#duplicate-keys-and-the-index-association-cache`.

## HIGH review (2026-10-27)

- Preservation check: 204 old statements; 184 kept, 6 generalised, 8 declared changes, none lost and five altered defects, all restored: the physical-row selection claim is back to its measured scope, the literal-key and field-valued line-terminator facts are separated again, Boolean and Confirm key pairing by base type is restored, the star and value gates share a rank with their order unmeasured, and the keyed fixed-group scope applies to `NotAllFieldsFilled` only.
- The self-check list held: of 44 scope-bearing rewordings, the check found two whose new home lost scope, both among the restored defects.
- The deepest-selector reanchoring rests on Kernel source reading, and Lean reanchors only when every selection shares one level and key; it is recorded under SG9.
- Behavioural changes ship as SPEC-2026-10-26-28. spec/07 §2.3 owes a pointer to §4.3's eligibility bullets, as Other chapters records.
