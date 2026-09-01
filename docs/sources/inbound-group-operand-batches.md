# Inbound group-operand source checkpoints

Reconciled inbound batches for group operands, entity lists, carrier sweeps, partial relevance, and the group declaration domain. Locally measured probes are split between [`group-and-iteration-probes.md`](group-and-iteration-probes.md) and [`group-list-and-capacity-probes.md`](group-list-and-capacity-probes.md); [`../SOURCES.md`](../SOURCES.md) remains the anchor registry for all three.

### The erroneous list member

<a id="src-erroneous-member-quantifier-undecidable"></a>
#### An erroneous member leaves undecided only the verdicts that needed it, measured locally 2026-08-31 and completed inbound the same day

- `revision`: one `:adapter:kernelProbe` request at a12-dmkits `c2900fe7c91a55e0debd0124f847ee2de0f06186`, the sibling checkout clean before and after with `state: CLEAN` in the artifact. `dmtool` 0.13.0, Kernel `30.8.1` built and runtime, `validateFull` on both codegen strategies, `enginesAgree: true` on all three rows.
- `question`: [`spec/10`](../../spec/10-validation-and-polarity.md) said a field carrying a formal error is not relevant and drew from it that a malformed operand is **dropped from a quantifier's list**, "which is the same answer as treating it as neither filled nor empty". That was source-grounded from the Kernel's business prose and never measured. a12-dmkits reported it contradicted at this revision; a report does not discharge a claim this project wrote into `spec/`, so it was re-derived here.
- `model`: `Quant_DM`, four nonrepeatable Numbers `A`, `B`, `C`, `W`, and six rules all guarded by `FieldFilled(W)` so none fires vacuously: `AllFieldsFilled(A,B,C)`, `NotAllFieldsFilled(A,B,C)`, `NumberOfFilledFields(A,B,C) == 3`, `== 2`, `AtLeastOneFieldFilled(A,B,C)`, and `FieldFilled(A)` as the control.
- `claim`: **all four list quantifiers go silent on the erroneous document, and the three obvious accounts are each excluded by one of them.** With `B` malformed, `AllFieldsFilled`, `NotAllFieldsFilled`, `== 3`, and `== 2` all stay silent. Dropping `B` from the list predicts the universal firing over `A` and `C`; counting it filled predicts `== 3`; counting it empty predicts the negative quantifier and `== 2`. The controls fix the other two rows: all three valid fires the universal and `== 3`, the middle left **empty** fires the negative quantifier and `== 2`.
- `separator`: **`AtLeastOneFieldFilled` fires on the erroneous document**, alongside `FieldFilled(A)` and the malformed cell's own `zahlHatUngueltigeZeichen`. That is the row that makes this three-valued logic rather than an abandoned document or a suppressed rule set: an existential with a *definite* witness stays decidable while a universal over the same list does not. Without it, silence in four rules is equally consistent with the Kernel giving up on the document.
- `not-reached`: this settles the **operand-list** reading only. Whether the Kernel's internal relevant list also excludes the field is a different question, and no observable here distinguishes it.
- `limit`: one malformed converter (a non-numeric Number), one nonrepeatable three-field list, `en_US`, full validation, no repetition. Not measured: an out-of-calendar Date or another converter, a repeatable list, partial validation, and the group-operand quantifiers.
- `bytes`: [`erroneous-member-quantifier/`](../../evidence/kernel-30.8.1/captures/erroneous-member-quantifier/); SHA-256 model `01572cfb9665dfd1e0ad4d418790b38c351f703c45e035f8b308b22e0c04bfca`, request `90d9b751745bb6b47c374a0caeb3e0048b2e206083f0a0e4a8fc543cafbf421f`, artifact `919ac484e797c6f9ac344912112a53e47043a2e3545764369ffc1cf896cbc27e`. A bounded raw calibration capture with no typed consumer: it does not run under `lake test` and establishes neither `L` nor `C` coverage.
- `law-completed`: **the separator above refuted the peer's own wording too.** a12-dmkits had read the behaviour as *an erroneous member suppresses every quantifier over its list*, measured on the same four rules — every one of which needed the erroneous member's state, so no rule in the set sat on the other side of the axis and the account fitted every row while being false.
- `law-completed`: **the corrected law is symmetric and needs a second malformed document to state.** Re-measured at a12-dmkits `11d9d811657c3562299b463f3dc3ece12142c650` over six rules, four documents, two converters, full and partial agreeing cell for cell: a quantifier is decided exactly when the members whose state is **known** already settle it. A known TRUE settles the existential — the row this project contributed — and a known FALSE settles the negation, which needs one erroneous member beside two **empty** ones: `NotAllFieldsFilled` fires there while the existential goes silent. This project's own clause already reproduced all twenty-four cells before it was asked to.
- `local-consequence`: the [validation fill-quantifier cases](../../A12Kernel/Conformance/ValidationFillQuantifier.lean) now lock the four documents as **one table**. Every cell was individually reachable from the single-operator cases that were already there — including both refuting rows — and none of them expressed the law the cells jointly establish, which is exactly what let the wrong account stand in [`spec/10`](../../spec/10-validation-and-polarity.md) for a day.
- `sync`: **inbound, twice.** The contradiction arrived from a12-dmkits' committed and reviewed `c2900fe7c` and the completed law from its `11d9d811`, both re-derived or re-checked here rather than accepted from prose. Neither opens an outbound entry; together they disposition [`SPEC-2026-08-31-05`](../A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-08-31-05) in place.

### Inbound repeatability declaration domain

<a id="src-repeatability-domain-peer-measurement"></a>
#### The kernel's `repeatability` domain is `> 0`, and `1` is admitted, inbound 2026-08-31

- `revision`: a12-dmkits `a6b011140f0de1d19c3d394b02df0fd199a8627f`, its [`GroupRepeatabilityDomainLawsTest`](../../../a12-rulekit/adapter/src/test/java/io/github/mbackschat/a12/dm/adapter/laws/GroupRepeatabilityDomainLawsTest.java). Read here rather than taken on report: the revision is the sibling checkout's `HEAD`, and the test's own expected map carries all nine rows on a declared-repeatable group of its own fixture.
- `question`: this project's [`SPEC-2026-08-31-07`](../A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-08-31-07) stated the domain as a finite integer of **at least two**. The lower bound was never measured against a Kernel gate.
- `claim`: **the domain is `> 0`, and `1` is admitted at both gates.** `2`, `3`, `1`, the text `"2"`, and an absent key are all `ADMITTED`; `0`, `null`, and `-1` draw `MVK_MAX_VALUES_INVALID`; a Boolean `true` is refused by the reader before either gate. **Absence means non-repeatable**, which is the half of this project's clause that stands. A `1` is a non-repeatable group spelled explicitly rather than an error.
- `gate-split`: the reader accepts `null`, `0`, and `-1` **without complaint**; only `checkConsistency` refuses them. The peer's first run used a load-gate oracle and reported every value admitted, which would have arrived here as a clean refutation of the whole entry rather than a correction of its lower bound. Its neighbouring mounted-component test measures the reader and genuinely does find the Kernel tolerant there, so the mistake would have looked corroborated. Name the gate before comparing verdicts.
- `text`: the refusal is emitted **per element** — once for the group and once for every field beneath it — and the domain message has two wordings: `0` and `null` draw *"Only values greater than 0 are allowed."*, a negative draws *"Only values without a sign are allowed."*.
- `defect-source`: the measurement here was sound and the **inference** was not. This project read `≥ 2` off `dmtool group add --repeatable`'s own refusal — an instrument's client-side narrowing — and wrote it as the Kernel's domain ([`LF126`](../LEAN-FINDINGS.md)). The defeater was in this repository the whole time: fourteen retained conformance fixtures across seven modules declare `repeatability := some 1`, every one of which the withdrawn claim made unauthorable.
- `local-consequence`: [`spec/01`](../../spec/01-data-model.md)'s group clause is corrected to `> 0` with the gate split and both wordings, and `RepeatableGroupDecl.repeatability`'s docstring with it. No Lean clause gated on `≥ 2`, so nothing else moved.
- `peer-consequence-corrected`: this project had read the peer's `≥ 2` flag bound as a narrowing "one step stricter than the Kernel", and **that framing is wrong, corrected inbound at reviewed a12-dmkits `8cad1224f86e91c46f0db3573adb4f0fe894a959`.** The two bounds answer different questions: `> 0` is the admitted-integer domain, while `1` is the **non-repeatable encoding** that the Kernel itself reads as not repeatable — starring such a group is refused `MVK_INVALID_WILDCARD`, *"Since 'Plain' is not repeatable, it is not allowed to specify an asterisk"*, against a `repeatability: 3` control that is valid. So `--repeatable 1` would ask for a list the Kernel then refuses to iterate, and the flag's refusal is correct at its own point of use rather than a lag behind the domain.
- `peer-consequence-lesson`: what was genuinely defective is that the bound was stated **without its reason**, which is indistinguishable from a stale one to whoever meets it in `--help`. Both help texts now carry it, verified here at the point of use while authoring an unrelated model. Inbound from a committed reviewed revision, so it opens no outbound entry.
- `sync`: **inbound and already reviewed upstream, so it opens no outbound entry.** It dispositions the existing [`SPEC-2026-08-31-07`](../A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-08-31-07) in place.

### Inbound entity-list group-operand, validator-cardinality, and cleared-value batch

<a id="src-entity-list-group-gates"></a>
#### Entity-list group gates

- `revision`: a12-dmkits `4b244b840e50a8159f6ad966f3def1c44b5b9c75`.
- `route`: real-kernel `checkConsistency` through `KernelLaws.acceptsModel` / `rejectsModel`.
- `test`: [`AggregateGroupOperandLawsTest`](../../../a12-rulekit/src/test/java/io/github/mbackschat/a12/dm/rulekit/validate/laws/AggregateGroupOperandLawsTest.java).
- `claim`: `Sum(/Invoice/Lines*, /Invoice/Lines*/Fees*)` reports `MVK_DUPLICATE_PARAM2`, while repeating the same starred group is admitted; wildcard duplicate skipping applies only to the direct-duplicate arm.
- `claim`: an unstarred repeatable group reports `MVK_NO_WILDCARD` under `Sum` and `NumberOfFilledFields`; the starred form and a nonrepeatable unstarred group are admitted.
- `claim`: expansion kind is carrier-specific: `Sum` reports `MVK_NO_NUMBER`, extrema report `MVK_NOT_SORTABLE`, and `NumberOfDifferentValues` reports `MVK_STRING_ENUM_AND_NON_STRING_ENUM`.
- `scope`: the structural arity, star, and duplicate gates belong to the shared entity-list checker; expansion-kind diagnostics do not transfer between carriers.
- `limit`: the HModel profile has no indirect-overlap witness.
- `limit`: this revision did not measure a star on a nonrepeatable group or `FirstFilledValue`; later checkpoints own those rows.
- `peer-boundary`: the typed builder pre-checks the star gate and delegates expansion-kind and indirect-overlap gates to the Kernel.

#### Validator-cardinality and cleared-value checkpoints

a12-dmkits `73bc4a04b6a7f81e619af261f9263115f4b67106` supplies the kernel oracle behind [`spec/06`](../../spec/06-strings-and-enumerations.md) §A.3's per-**cell** custom-validation cardinality, which until then rested on a single-cell differential plus a peer-internal cache test and therefore could not separate per-cell from per-value. `CustomFieldTypeContextDiffTest.theSameValueInTwoCellsReachesTheValidatorOncePerCell` puts one value in two in-cap rows of a repeatable group with a counting factory and measures two invocations with identical context, two rejections at distinct pointers, and agreement across dynamic Groovy, generated Java, and the interpreter, with the positive control that a value-shaped cache key turns it red at `expected: <2> but was: <1>`.

The peer's own prose had drifted to a per-value wording in five places while its implementation was per-cell, which is why the clause now names the discriminator instead of only the rule.

a12-dmkits `06b84701969979a2e5a2b63de7445a6a1d521473` measures what a **cleared** computed instance carries, now stated in [`09-computations.md` §3.3](../../spec/09-computations.md#33-what-compute-reports): the value accessor reads present and empty for every clear rather than echoing the erased input, so clearedness is a channel-membership fact and a consumer reading that accessor aliases a clear with a computed empty string. `ComputeResultChannelsLawsTest` owns it, and the scope is now **both codegen strategies** at a12-dmkits `a154cd2adbd78c70e2ae101050b5bb3f8f709668`.

The route it took is worth keeping, because it is the cheap half of the discharge rule working in both directions: the first version of that case read the shared dynamic engine alone while the producer's own contract said "for every clear", so this project scoped the local clause to the anchor and returned the mismatch instead of adopting the wider sentence; the peer then measured the second arm rather than narrowing its wording, and both strategies report present-and-empty at the same fixture. The interpreter is not part of this case, so the fact is kernel-strategy-wide and not tri-checked.

### Inbound `FieldValuesNotUnique` group-operand batch

<a id="src-field-values-not-unique-group-admission"></a>
#### Field-values-not-unique group admission

- `revision`: a12-dmkits `7a6092351f112b1857223fb23aeda220fbbe0d95`.
- `kernel`: 30.8.1 under JDK 21.0.12.
- `route`: real-kernel `RuleValidator` / `checkConsistency`.
- `test`: [`FieldValuesNotUniqueAdmissionLawsTest`](../../../a12-rulekit/src/test/java/io/github/mbackschat/a12/dm/rulekit/validate/laws/FieldValuesNotUniqueAdmissionLawsTest.java) and [`AggregateGroupOperandLawsTest`](../../../a12-rulekit/src/test/java/io/github/mbackschat/a12/dm/rulekit/validate/laws/AggregateGroupOperandLawsTest.java), durable peer home `KF173`.
- `claim`: the Kernel admits a nonrepeatable group expanding to two Strings and a starred repeatable group expanding to two same-scale Numbers; equivalent explicit lists pass as controls.
- `claim`: arity reads the authored slot because a single-field group is admitted while that field authored directly reports `MVK_PARAMSIZE_INVALIDN`.
- `claim`: category reads the expansion because a group containing Number and String reports `MVK_VARYING_TYPES_NOT_ALLOWED`.
- `claim`: a star on a nonrepeatable group reports `MVK_INVALID_WILDCARD` against an admitted character-identical unstarred control.
- `integrity`: the unstarred control is asserted equal to the typed renderer's output, excluding a hand-authored spelling difference.
- `limit`: static admission only; no runtime behavior follows.
- `peer-limit`: a12-dmkits' typed `Dsl.fieldValuesNotUnique` still makes this shape type-level unrepresentable under `DG33`.

<a id="src-field-values-not-unique-group-runtime"></a>
#### Field-values-not-unique group runtime

- `revision`: a12-dmkits `e1a7fdd63d98d33173f3ffb4c275e117072d6695` owns the first seven cases.
- `revision`: a12-dmkits `19adb3e5fb5681dee8daf327be690be382e85a30` adds nesting.
- `revision`: a12-dmkits `d0611c01ba0b709e13f25ba2d6f29708205f5a25` adds two stacked repeatable levels and the authored star.
- `revision`: a12-dmkits `b493fb70b3d42e08fe700f1bea41582b5a93172a` adds rule placement.
- `route`: tri-check of dynamic Groovy, generated Java, and the a12-dmkits interpreter; both kernel codegen strategies are measured.
- `test`: [`FieldValuesNotUniqueGroupOperandDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/FieldValuesNotUniqueGroupOperandDiffTest.kt), durable peer home `IF287`.
- `claim`: the group operand contributes one recursive value set across its subtree rather than one direct-child or first-row-only set.
- `claim`: nesting, two stacked repeatable levels, authored-star scope, and rule placement retain that extent.
- `separator`: place the discriminating duplicate in nested row 2; row 1 and a one-row fixture cannot distinguish the wrong extent.
- `limit`: the scope outcome is measured without cause attribution; the source's rejected mechanism predictions do not enter the semantic claim.
- `limit`: these revisions asserted only firing, so they did not measure message multiplicity, anchor, or reference coordinates; later source records own those answers.

<a id="src-number-group-computation-runtime"></a>
#### Number group computation runtime

- `revision`: clean a12-dmkits `3a4025bbfdbd925d7f4c23e519f15ce0e2461b21`; `19adb3e5fb5681dee8daf327be690be382e85a30` is the last revision that changed the retained test's behavior.
- `route`: the existing targeted adapter test passed at the clean revision against Kernel 30.8.1. Every stated row compares dynamic Groovy with the a12-dmkits interpreter; Sum, extrema, recursive extent, poison, and empty identity additionally compare generated Java, while distinct count does not.
- `test`: [`GroupStarValueAggregateDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/GroupStarValueAggregateDiffTest.kt).
- `claim`: starred `Sum(Lines*)` computes `30.75`; `MinValue`, `MaxValue`, and `NumberOfDifferentValues` compute `10.5`, `20.25`, and `2` over the same recursively expanded Number declarations.
- `claim`: starred `Sum(Charges*)` reaches Fee, Tax, and every instantiated nested Extras/Surcharge row; the separating multi-row fixture computes `7.5` across two Charges rows and three nested Extras rows.
- `claim`: a malformed three-fraction Amount clears the computation target, while an empty group computes the Sum identity `0`.
- `separator`: the second nested Extras row and the nested row under the second Charges row distinguish complete recursive expansion from a single-coordinate or first-row traversal.
- `limit`: this retained test authors only starred group operands. Fixed group computation, partial validation, raw-`Document` execution, mixed signedness, and the computation result's internal fillability metadata remain unmeasured; the later [Number group value-count checkpoint](../SOURCES.md#src-number-group-value-count-computation-capacity) owns that separate computation family.
- `sync`: the outcomes match the existing recursive group-extent, aggregate computation, poison, and empty-selection clauses, so no outbound correction follows.

<a id="src-number-group-value-count-computation-capacity"></a>
#### Number group value-count computation capacity

- `revision`: clean a12-dmkits `cd43c249a88874bf5688a45060e208a0dcd20782` with source-shipped dmtool `0.13.0`.
- `route`: structured dmtool authoring persisted `NumberOfValueInFields(10 In Lines*)` as the direct computation of a scale-0 Number target; the source-shipped `:adapter:kernelProbe` task observed `compute` and `validateFull` on dynamic Groovy and generated Java, and read-only `dmtool model compute` independently exercised the a12-dmkits interpreter over the same eight documents.
- `kernel`: 30.8.1 built and runtime; both Kernel strategies agree on every reported runtime channel, and the interpreter returns the same eight computation outcomes.
- `claim`: the two in-capacity rows expand across both Number declarations, producing exact counts `2`, `1`, `0`, and `0` for two matches, one match, two instantiated empty rows, and no rows; an in-capacity malformed cell after an earlier match clears the target.
- `claim`: a third row beyond declared capacity contributes neither a matching value nor malformed-content poison. An over-capacity match alone leaves count `0`, one in-capacity match plus an over-capacity match leaves count `1`, and one in-capacity match plus over-capacity malformed content also leaves count `1`.
- `separator`: the same malformed spelling clears when it is in capacity and does not affect the outcome when it is over capacity, while the Kernel artifact still reports the independent over-repetition findings in messages and `formalErrorsInOperands`.
- `integrity`: request SHA-256 `85cab649cc39f5c69c7f9e5c962f0833a1fd1360946e9b1895670fccc7d383e5`; model SHA-256 `fc94e1392a1543049c4473b55b048721ead9ab68559992046791ef196f4a0b42`; artifact SHA-256 `398bfe23884d6ed5a1661b8c09159de30aa1034750044e8918ca30f5dcf71b23`; producer source state `CLEAN`.
- `limit`: this establishes one terminal single-level starred Number group, two scale-0 declarations, declared capacity two, direct checked-document computation, and exact value/clear outcomes. It establishes the result's extensional content domain, not whether the Kernel omits, classifies, or otherwise suppresses an over-capacity cell internally. Internal fillability, fixed groups, validation, plain starred fields, filters, nested repetition, mixed signedness, token and Boolean groups, and raw-`Document` routes remain outside the measurement.
- `sync`: accepted [`SPEC-2026-08-24-04`](../archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md#spec-2026-08-24-04--numberofvalueinfields-group-computation-ignores-over-capacity-cell-content-for-measured-number-string-and-booleanconfirm-overloads) at reviewed a12-dmkits `975a2e78602eaf26126168cd203bd84738885322`; maintained coverage locks the extensional capacity boundary without asserting internal ordering.

<a id="src-token-group-partial-runtime"></a>
#### Token group partial-validation runtime

- `revision`: clean a12-dmkits `3a4025bbfdbd925d7f4c23e519f15ce0e2461b21`; `9958d69809aa360bb81d35d7de3cebec6dd15d97` added the retained group-specific differential and `726dca09020d78132ee12a9771e2d6a882716160` owns a separate one-field wildcard-versus-concrete orientation case.
- `route`: targeted runs of both retained adapter tests passed at the clean revision, with dynamic Groovy, generated Java, and the a12-dmkits interpreter agreeing against Kernel 30.8.1.
- `test`: [`PartialValidationGroupOperandDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/PartialValidationGroupOperandDiffTest.kt) and [`PartialValidationValueListDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/PartialValidationValueListDiffTest.kt).
- `claim`: partial `NoFieldValueIncludedInValueList(Items* In "A")` over a starred group containing two String declarations matches its explicit `Tag*` plus `Note*` expansion under both wildcard-group relevance and concrete rows 1 and 2.
- `claim`: the wildcard-group and concrete-row relevance shapes produce different results in that group fixture.
- `control`: the separate one-field explicit-star case hardcodes wildcard relevance as firing and concrete-row relevance as silent, but it does not discharge that orientation for the two-declaration group fixture.
- `unverified`: the exact two-declaration group result orientation and the claim that both relevance shapes reach the same cells are not externally measured. Lean locks the chosen wildcard-fired, concrete-unknown account and equal reached-cell counts only as internal executable semantics.
- `limit`: external evidence covers one starred repeatable group, two direct String declarations, two instantiated rows, the fields side of `No`, group-versus-explicit equivalence within each relevance shape, and disagreement between the two shapes. Exact orientation, reached-cell selection, fixed groups, nested declarations, Enumeration projection, other quantifiers, computation, raw-`Document` routes, messages, and references remain unmeasured.
- `sync`: the measured equivalences and shape disagreement are consistent with the existing partial value-list extent and group expansion clauses, so no outbound correction follows.

<a id="src-token-group-value-count-computation-capacity"></a>
#### Token group value-count computation capacity

- `revision`: clean a12-dmkits `cd43c249a88874bf5688a45060e208a0dcd20782` with source-shipped dmtool `0.13.0`.
- `route`: structured dmtool authoring persisted `NumberOfValueInFields("X" In Lines*)` as the direct computation of a scale-0 Number target over a capacity-two repeatable group whose two String declarations each impose maximum length one; the source-shipped `:adapter:kernelProbe` task observed `compute` and `validateFull` on dynamic Groovy and generated Java, and read-only `dmtool model compute` independently exercised the a12-dmkits interpreter over the same eight documents.
- `kernel`: 30.8.1 built and runtime; both Kernel strategies agree on every reported runtime channel, and the interpreter returns the same eight computation outcomes.
- `claim`: the two in-capacity rows expand across both String declarations, producing exact counts `2`, `1`, `0`, and `0` for two matches, one match, two instantiated empty rows, and no rows; an in-capacity overlength String after an earlier match clears the target.
- `claim`: a third row beyond declared capacity contributes neither a matching token nor malformed-content poison. An over-capacity match alone leaves count `0`, one in-capacity match plus an over-capacity match leaves count `1`, and one in-capacity match plus over-capacity malformed content also leaves count `1`.
- `separator`: the same overlength spelling clears when it is in capacity and does not affect the outcome when it is over capacity, while the Kernel artifact still reports the independent over-repetition findings in messages and `formalErrorsInOperands`.
- `integrity`: request SHA-256 `fe88ed525c3258457b803fa3cafaa189187b4212808d9d1c4c6af1845346f96f`; model SHA-256 `6cec2ff3e263edaf388182baa75b541be9962459bb0f89a07cc544fbbb497232`; artifact SHA-256 `2b39b57bdfba32c36c6c68fcd5fd0c5da948211d7ccd79189460e615d9e39b7d`; producer source state `CLEAN`.
- `limit`: this establishes one terminal single-level starred group, two value-validating String declarations, stored projection, declared capacity two, direct checked-document computation, and exact value/clear outcomes. It establishes the result's extensional content domain, not whether the Kernel omits, classifies, or otherwise suppresses an over-capacity cell internally. Internal fillability, fixed groups, validation, plain starred fields, filters, nested repetition, Enumeration/category projection, Boolean groups, and raw-`Document` routes remain outside the measurement.
- `sync`: accepted [`SPEC-2026-08-24-04`](../archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md#spec-2026-08-24-04--numberofvalueinfields-group-computation-ignores-over-capacity-cell-content-for-measured-number-string-and-booleanconfirm-overloads) at reviewed a12-dmkits `975a2e78602eaf26126168cd203bd84738885322`; maintained coverage locks the extensional capacity boundary without asserting internal ordering.

<a id="src-boolean-group-value-count-computation-capacity"></a>
#### Boolean/Confirm group value-count computation capacity

- `revision`: clean a12-dmkits `cd43c249a88874bf5688a45060e208a0dcd20782` with source-shipped dmtool `0.13.0`.
- `route`: structured dmtool authoring persisted `NumberOfValueInFields(True In Lines*)` as the direct computation of a scale-0 Number target over a capacity-two repeatable group containing one Boolean followed by one Confirm declaration; the source-shipped `:adapter:kernelProbe` task observed `compute` and `validateFull` on dynamic Groovy and generated Java, and read-only `dmtool model compute` independently exercised the a12-dmkits interpreter over the same eight documents.
- `kernel`: 30.8.1 built and runtime; both Kernel strategies agree on every reported runtime channel, and the interpreter returns the same eight computation outcomes.
- `claim`: the two in-capacity rows expand across the Boolean and Confirm declarations, producing exact counts `2`, `1`, `0`, and `0` for two matches, one match, two instantiated empty rows, and no rows; malformed in-capacity Boolean content after an earlier match clears the target.
- `claim`: a third row beyond declared capacity contributes neither a matching token nor malformed-content poison. An over-capacity match alone leaves count `0`, one in-capacity match plus an over-capacity match leaves count `1`, and one in-capacity match plus over-capacity malformed content also leaves count `1`.
- `separator`: the same malformed Boolean spelling clears when it is in capacity and does not affect the outcome when it is over capacity, while the Kernel artifact still reports the independent over-repetition findings in messages and `formalErrorsInOperands` for the placed declaration and the row.
- `integrity`: request SHA-256 `3576d472d35e7432e6d0d60000116ba5c8514b7e805ec06acc0e1df20dd391c6`; model SHA-256 `7b5d8b6e7a4f063a7a6d6f3ebced34deae0216a49834e7a2fe20a4c594fe9d23`; artifact SHA-256 `a0c2d29f2834e478541d74547d84aae4e31f8e02711e8c21cea30d00b797e9a0`; producer source state `CLEAN`.
- `limit`: this establishes one terminal single-level starred group, one Boolean followed by one Confirm declaration, constant `True`, declared capacity two, direct checked-document computation, and exact value/clear outcomes. It establishes the result's extensional content domain, not whether the Kernel omits, classifies, or otherwise suppresses an over-capacity cell internally. Internal fillability, constant `False`, other Boolean/Confirm declaration orders or mixes, fixed groups, validation, plain starred fields, filters, nested repetition, and raw-`Document` routes remain outside the measurement.
- `sync`: accepted [`SPEC-2026-08-24-04`](../archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md#spec-2026-08-24-04--numberofvalueinfields-group-computation-ignores-over-capacity-cell-content-for-measured-number-string-and-booleanconfirm-overloads) at reviewed a12-dmkits `975a2e78602eaf26126168cd203bd84738885322`; the maintained Boolean matrix also locks the distinct `feldJaNeinFalsch` and `feldJaFalsch` formal causes and the two over-repetition code kinds. The measured fixture reports one group-level row finding and one field-local context-number finding for each placed over-capacity cell; it does not establish multiplicity for unplaced declarations in the expanded group.

<a id="src-false-boolean-group-value-count-computation-capacity"></a>
#### False Boolean-group value-count computation capacity

- `revision`: clean a12-dmkits `cd43c249a88874bf5688a45060e208a0dcd20782` with source-shipped dmtool `0.13.0`.
- `route`: structured dmtool authoring persisted `NumberOfValueInFields(False In Lines*)` as the direct computation of a scale-0 Number target over a capacity-two repeatable group containing two Boolean declarations; the source-shipped `:adapter:kernelProbe` task observed `compute` and `validateFull` on dynamic Groovy and generated Java, and read-only `dmtool model compute` independently exercised the a12-dmkits interpreter over the same eight documents.
- `kernel`: 30.8.1 built and runtime; both Kernel strategies agree on every reported runtime channel, and the interpreter returns the same eight computation outcomes.
- `claim`: the two in-capacity rows expand across both Boolean declarations, producing exact counts `2`, `1`, `0`, and `0` for two matches, one match, two instantiated empty rows, and no rows; malformed in-capacity Boolean content after an earlier match clears the target.
- `claim`: a third row beyond declared capacity contributes neither a matching token nor malformed-content poison. An over-capacity match alone leaves count `0`, one in-capacity match plus an over-capacity match leaves count `1`, and one in-capacity match plus over-capacity malformed content also leaves count `1`.
- `separator`: the same malformed Boolean spelling clears when it is in capacity and does not affect the outcome when it is over capacity, while the Kernel artifact still reports the independent over-repetition findings in messages and `formalErrorsInOperands` for the placed declaration and the row.
- `integrity`: request SHA-256 `2088d467bd42a8a09aa2d82efacd51d88612110ed0db2b3c2830f8ae28900d71`; model SHA-256 `620a166b0ee9e64f670dfebfec0954b72ecd9efa3a17b56236517842af2a8a69`; artifact SHA-256 `85cf5cf58e2fda8ce04378fc8b34cdaac71862cd97233027af0c100f16f395a1`; producer source state `CLEAN`.
- `limit`: this establishes one terminal single-level starred group, two Boolean declarations, constant `False`, declared capacity two, direct checked-document computation, and exact value/clear outcomes. It establishes the result's extensional content domain, not whether the Kernel omits, classifies, or otherwise suppresses an over-capacity cell internally. Internal fillability, constant `True`, other Boolean/Confirm declaration orders or mixes, fixed groups, validation, plain starred fields, filters, nested repetition, and raw-`Document` routes remain outside the measurement.
- `sync`: accepted [`SPEC-2026-08-24-04`](../archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md#spec-2026-08-24-04--numberofvalueinfields-group-computation-ignores-over-capacity-cell-content-for-measured-number-string-and-booleanconfirm-overloads) at reviewed a12-dmkits `975a2e78602eaf26126168cd203bd84738885322`; the over-repetition channel again exposes the group-level row and field-local context-number code kinds for the placed over-capacity cells, and no evaluator or dmtool surface change was needed. No finding-count rule is inferred for unplaced declarations.

<a id="src-boolean-group-value-count-computation-shape-matrix"></a>
#### Boolean-group value-count computation shape matrix

- `revision`: clean a12-dmkits `cd43c249a88874bf5688a45060e208a0dcd20782` with source-shipped dmtool `0.13.0`.
- `route`: structured dmtool authoring created one seven-computation kind/order/width matrix and one separate three-Boolean `False` capacity model; source-shipped `:adapter:kernelProbe` observed `compute` and `validateFull` on dynamic Groovy and generated Java, and read-only `dmtool model compute` exercised the a12-dmkits interpreter over the same documents.
- `kernel`: 30.8.1 built and runtime; both Kernel strategies agree on every reported runtime channel, and the interpreter returns the same computation outcomes.
- `claim`: `False` over one Boolean returns `1`. `True` returns `1` over one Boolean or one Confirm, `2` over Confirm then Boolean, two Booleans, or two Confirms, and `3` over Boolean then Confirm then Boolean. The result therefore follows the existing constant-specific fieldwise kind gate across the measured kind, order, and width axes rather than requiring the former exact two-declaration orders.
- `claim`: three Boolean declarations under `False` return exact counts `3`, `1`, `0`, and `0` for three matches, one match, two instantiated empty rows, and no rows; malformed content in the third declaration of an in-capacity row after an earlier match clears the target.
- `claim`: a third row beyond declared capacity contributes neither a match in the third declaration nor its malformed-content poison. An over-capacity third-declaration match alone leaves count `0`, one in-capacity match plus that over-capacity match leaves count `1`, and one in-capacity match plus over-capacity malformed third-declaration content also leaves count `1`.
- `separator`: the one-, two-, and three-declaration rows distinguish the fieldwise gate from an exact arity; the Confirm-only, Boolean-only, reversed, and three-member mixed rows distinguish it from a declaration-order rule. Moving the same malformed third Boolean from an in-capacity row to an over-capacity row separates content classification from the computed result domain, while over-repetition findings stay independently visible.
- `integrity`: three-Boolean capacity request SHA-256 `6344b3c10f0135a481f89eea16f1cca2ccfb05ae938d588522ee827ba2fb94c9` model SHA-256 `4ae676389d835708851d0cbde6c03b0e09be27df15f7b981bc1501bb89fc761f` artifact SHA-256 `6a31410c8abca896d67f67189d88fed49caf25d73b44dd445590571e60c69456`. Shape-matrix request SHA-256 `20bc7a04c78f701784c833567f9f03a4f2e819a5801ddb80c8f64613b9fc0d63` model SHA-256 `6de1ebeb45cbdb56466a16730651f31cf8b4e7ad4653943f3884816073418801` artifact SHA-256 `503c65dc09b183dc417275393860f31919cd465c4ffd8434046b78a5d0c887fa` producer source state `CLEAN` before and after both probes.
- `limit`: the shape matrix measures one to three declarations and the capacity matrix measures three Boolean declarations under `False`; arity above three is not separately observed. Both routes use one terminal single-level starred group with no declaration below another repeatable group, capacity two, direct checked-document computation, and exact value/clear outcomes. Internal fillability, fixed groups, partial validation, plain starred fields, filters, nested repetition, and raw-`Document` routes remain outside the measurement.
- `sync`: accepted [`SPEC-2026-08-24-04`](../archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md#spec-2026-08-24-04--numberofvalueinfields-group-computation-ignores-over-capacity-cell-content-for-measured-number-string-and-booleanconfirm-overloads) at reviewed a12-dmkits `975a2e78602eaf26126168cd203bd84738885322`; the maintained kind gate reads each declaration in the group expansion and refuses `False` exactly when that expansion contains Confirm.

<a id="src-boolean-fixed-group-value-count-computation"></a>
#### Boolean fixed-group value-count computation

- `revision`: clean a12-dmkits `cd43c249a88874bf5688a45060e208a0dcd20782` with source-shipped dmtool `0.13.0`.
- `route`: structured dmtool authoring persisted `NumberOfValueInFields(True In TrueFlags)` over a fixed group containing one Boolean and one Confirm declaration and `NumberOfValueInFields(False In FalseFlags)` over a fixed group containing two Boolean declarations; computation readback preserved both exact group operands, the Kernel consistency gate accepted the model, source-shipped `:adapter:kernelProbe` observed `compute` and `validateFull` on dynamic Groovy and generated Java, and read-only `dmtool model compute` exercised the a12-dmkits interpreter over the same four documents.
- `kernel`: 30.8.1 built and runtime; both Kernel strategies return `2`, `1`, and `0` for two matches, one match, and empty input in both computations. With an earlier match followed by malformed Confirm or Boolean content, both targets are absent from computation outcomes and the exact operand formal errors remain reported.
- `separator`: the two-match and one-match rows distinguish group expansion from an empty operand stream or a group path treated as a scalar field. The malformed-after-match row distinguishes formal poison from an ignored group; the empty row is the zero control.
- `peer-correction`: reviewed a12-dmkits `975a2e78602eaf26126168cd203bd84738885322` replaces the wrong `expandGroupStars` call with the already-owned both-shape `expandGroupOperands` path. Both Kernel strategies and the JVM/Node interpreter now agree on `2`, `1`, `0`, and malformed clear; a planted reversal to the former helper is killed by the retained control.
- `validation-extension`: the same reviewed revision measures the separate fill walk. Fixed-group Boolean `NumberOfValueInFields` and `NumberOfFilledFields` use the expanded direct-field extent, so a full two-field group has fixed movement and a firing mismatch is VALUE-typed. `NumberOfFilledGroups` instead counts each authored group as one entity: one half-filled group beside one filled group exhausts the two-group extent. Confirm malformed content reports `feldJaFalsch`, distinct from Boolean `feldJaNeinFalsch`.
- `integrity`: request SHA-256 `1598cbaf316bf5965afa8bb499a819a1ff1c500bdda891a1b5eec6379c92e499`; model SHA-256 `1aa86d6cc0fb5e9660297cf91e821cf8912fed2122f4e1acda77618f3a988d8b`; artifact SHA-256 `0acbdcb4da69f340bebc94091de2569d700f3e71fa2cf892472264e775fac4cf`; documents in request order SHA-256 `d9af4294a3ed88081ea3478c73c2fa12203506885de613be2a6eeb9f91f35cfd`, `835a7ee285617c773612a115dbf88bf74b9721958f11af50d786fc0bc93ae93a`, `f17d7d4ab396fa61c6d898f48e2145e9ae96a1e0af12f8b1ecf102d15fd6d92f`, and `f26e27b4dcc4c5b260a8b1e9f00b58642efb714647accb76a34179f2b157e772`; producer source state `CLEAN` before and after the probe and interpreter replay.
- `limit`: computation establishes two fixed nonrepeatable groups with exactly two direct declarations, the Boolean-plus-Confirm `True` and two-Boolean `False` kind forms, direct checked-document execution, and exact value/clear outcomes. Validation movement is measured for the fixed direct-field extent and fixed group-entity count only. Other arities or kind orders, recursive descendants, fixed groups inside repeatable scope, Enumeration/category projection, and legacy raw-`Document` routes remain outside.
- `sync`: accepted [`SPEC-2026-08-24-05`](../archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md#spec-2026-08-24-05--fixed-boolean-group-numberofvalueinfields-computation-expands-its-direct-fields) at reviewed a12-dmkits `975a2e78602eaf26126168cd203bd84738885322`.

<a id="src-boolean-confirm-constant-computation-targets"></a>
#### Boolean and Confirm constant computation targets

- `revision`: reviewed a12-dmkits `38aeb23b5849b831f8ae6ee09579367e28ce982b`, kernel `30.8.1`.
- `route`: `RuleValidator.check` runs the Kernel consistency checker over four raw `DraftComputation` controls, changing only Boolean versus Confirm target kind and `True` versus `False` operation.
- `claim`: Boolean accepts both constants. Confirm accepts `True` and refuses `False` with `MVK_INVALID_COMPARE_TO_YES`, so the comparison-side confirmation asymmetry also gates computation targets.
- `limit`: static legality for two constants and two target kinds only. Runtime result, placement, preconditions, alternatives, and other Boolean operations remain unmeasured.
- `sync`: inbound observation already implemented and maintained by a12-dmkits; no outbound ledger entry.

<a id="src-token-value-count-group-runtime"></a>
#### Token group value-count runtime

- `revision`: clean a12-dmkits `3a4025bbfdbd925d7f4c23e519f15ce0e2461b21`; `73d44245a0f43a8279d0c1b450c108ab8b924d22` last changed the retained runtime differential and `66457109c32d98c2bfc016c92acc7d4c8000983f` owns the typed starred-group authoring law.
- `route`: the targeted `GroupStarValueInFieldsDiffTest` run passed at the clean revision, with dynamic Groovy, generated Java, and the a12-dmkits interpreter agreeing against Kernel 30.8.1; the source-level law separately checks Kernel admission and exact typed rendering.
- `test`: [`GroupStarValueInFieldsDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/GroupStarValueInFieldsDiffTest.kt) and [`ValueInFieldsGroupOperandLawsTest`](../../../a12-rulekit/src/test/java/io/github/mbackschat/a12/dm/rulekit/validate/laws/ValueInFieldsGroupOperandLawsTest.java).
- `claim`: a starred repeatable String group is admitted as the sole `NumberOfValueInFields` operand, and the typed surface renders that exact group form.
- `claim`: with one `"X"` under declaration `A` in row 1 and one under declaration `B` in row 2, `NumberOfValueInFields("X" In Lines*) >= 2` fires; the explicit `Lines*/A, Lines*/B` control fires on the same fixture.
- `separator`: the internal Lean case locks an exact count of two against the explicit two-star control; an empty, first-row-only, or single-declaration traversal would return a different exact count.
- `limit`: the external row establishes at least two matches, not the internal exact count of two. It covers one terminal starred group, two direct String declarations, two instantiated rows, full validation, stored projection, and one `>= 2` comparison. Lean's treatment of the sole authored group slot as already-many is internal because the upstream fixtures do not distinguish authored-slot arity from expansion-counting arity. This starred-group law explicitly excludes fixed groups; their later separate static admission is owned by [the fixed-group checkpoint](../SOURCES.md#src-token-value-count-fixed-group-admission). Nested groups, Enumeration/category projection, other literals and comparisons, computation, partial validation, malformed cells, messages, and references remain unmeasured here.
- `sync`: this is inbound calibration already committed in a12-dmkits. It closes the starred-group authoring erasure in Lean and creates no outbound ledger request.

<a id="src-token-value-count-fixed-group-admission"></a>
#### Token fixed-group value-count admission

- `revision`: clean a12-dmkits `3a4025bbfdbd925d7f4c23e519f15ce0e2461b21`; `d510684807738aac614e0d596ba6871b4715832a` added the exact fixed-group admission and explicit-field control rows.
- `route`: the targeted `GroupOperandCarrierAdmissionLawsTest` run passed at the clean revision and rechecked every matrix row through the Kernel consistency oracle.
- `test`: [`GroupOperandCarrierAdmissionLawsTest`](../../../a12-rulekit/src/test/java/io/github/mbackschat/a12/dm/rulekit/validate/laws/GroupOperandCarrierAdmissionLawsTest.java).
- `claim`: a fixed nonrepeatable String group is admitted as the sole `NumberOfValueInFields("x" In Contact)` operand, beside an admitted explicit `Contact/Email, Contact/Phone` control.
- `separator`: the fixed group is the only variable between the admitted group row and its two-direct-field control; either refusing ordinary groups or erasing the group form fails the admission row.
- `limit`: this establishes static admission only. The group expands to two String declarations, so this row does not distinguish authored-slot arity from expansion-counting arity and does not establish any runtime count. `RuleGroup`, a fixed group inside repeatable scope, other declaration kinds and literals, computation, partial validation, messages, and references remain outside this observation.
- `sync`: this is inbound calibration already committed in a12-dmkits. It removes Lean's stale fixed-group authoring refusal and creates no outbound ledger request.

<a id="src-filled-field-group-runtime"></a>
#### Filled-field group-count runtime

- `revision`: clean a12-dmkits `3a4025bbfdbd925d7f4c23e519f15ce0e2461b21`; `b4da1c04c7c11c60b51d8fffee4a74b1dbe00d34` added the retained fixed-group rows and `d3f0f42e34ff0800f92dc54e8b9384b5c6ab98d7` added the retained terminal-starred-group rows. Reviewed revision `975a2e78602eaf26126168cd203bd84738885322` adds exact polarity and group-entity controls.
- `route`: the targeted `MultiFieldAggregateDiffTest` and `GroupStarFilledFieldsDiffTest` runs passed together at the clean revision against Kernel 30.8.1. The fixed rows compare dynamic Groovy with the a12-dmkits interpreter; the starred rows compare dynamic Groovy, generated Java, and the interpreter.
- `test`: [`MultiFieldAggregateDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/MultiFieldAggregateDiffTest.kt) and [`GroupStarFilledFieldsDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/GroupStarFilledFieldsDiffTest.kt).
- `fixed-claim`: a fixed nonrepeatable group containing two direct fields is evaluated through that declared field extent. Filling both fields exhausts the extent and makes a firing count comparison VALUE-typed; leaving one empty keeps the available count grow-only. A two-operand `NumberOfFilledGroups(A, B)` instead counts each group as one entity, so a half-filled `A` and filled `B` already exhaust the declared group extent.
- `starred-claim`: a terminal repeatable group containing two String declarations spans both instantiated rows. Four filled descendants across two rows satisfy `>= 3` and do not satisfy `>= 5`; a cell filled only in row 2 satisfies `>= 1`; no group row does not satisfy `>= 1`.
- `separator`: the four-cell fixture distinguishes the complete starred extent from a per-row, row-1-only, or unexpanded group read, and the row-2-only fixture independently rejects the row-1 traversal.
- `internal`: Lean returns the exact fixed counts `0`, `1`, and `2` and starred counts `0`, `1`, and `4`. The retained external comparisons establish the stated threshold outcomes and whole-extent separator, but they do not by themselves establish every exact count or distinguish zero from unavailability in the empty rows.
- `limit`: full validation only, one fixed ordinary field-count group, one fixed two-group entity count, and one terminal starred repeatable group. Mixed field/group operands, nested groups, formal-invalid descendants, partial validation, computation, raw-`Document` execution, messages beyond polarity, and references remain outside.
- `sync`: this is inbound calibration already committed in a12-dmkits and agrees with the canonical recursive group-extent and filled-field-count clauses, so no outbound ledger request follows.

<a id="src-temporal-field-values-not-unique-group-runtime"></a>
#### Temporal field-values-not-unique group runtime

- `revision`: clean a12-dmkits `3a4025bbfdbd925d7f4c23e519f15ce0e2461b21`.
- `route`: source-shipped dmtool 0.13.0 authored and checked one self-contained model, then source-shipped `:adapter:kernelProbe` ran five full-validation rows through dynamic Groovy and generated Java.
- `kernel`: 30.8.1 built and runtime; both strategies agree on every reported channel.
- `claim`: an unstarred fixed group containing one direct Date and two Date declarations in a repeatable subgroup agrees with its explicit direct-plus-two-starred-field control when all five reached texts are distinct, when the direct value duplicates the second row, when two declarations duplicate wholly inside the second row, and when every reached cell is empty.
- `control`: an empty guard leaves both rules silent, so the firing rows do not merely expose unconditional message emission.
- `separator`: the two firing rows place the only duplicate outside a direct-child-only and first-row-only extent; the within-row pair also separates one combined recursive value set from per-declaration scans.
- `integrity`: model SHA-256 `b6d9585aead4c723f27ce2c99135df6ea9d314ab7c2967e04110d4701d82bcc6`; request SHA-256 `40e99b0b275ddd36fe0d8c037d37961bd4098cf5b42c76fbd91fc16e0f00e4ce`; two unchanged runs produced byte-identical artifacts at SHA-256 `6f8d641795af3fb14f4afcabb79c182bc25dd0ad2748a47a9e01c1134f5b8cbe`.
- `limit`: the values use coherent `yyyy-MM-dd` text and decoded Date payloads, so this calibration establishes recursive extent and group-versus-explicit outcome agreement but does not independently discriminate stored-text identity from decoded-value identity.
- `limit`: full validation, one unstarred fixed group, one nested repeatable level, two rows, and verdict only; static diagnostics, starred groups, wider nesting, partial validation, computation, message multiplicity, message addresses, and references are not measured.
- `sync`: the outcomes match the existing recursive group-extent and temporal uniqueness clauses, so no outbound correction follows.

<a id="src-boolean-value-count-group-runtime"></a>
#### Boolean value-count group runtime

- `revision`: clean a12-dmkits `3a4025bbfdbd925d7f4c23e519f15ce0e2461b21`.
- `route`: source-shipped dmtool 0.13.0 authored and checked one self-contained model, structured `rule check` measured the remaining constant-specific kind row, and source-shipped `:adapter:kernelProbe` ran four full-validation rows through dynamic Groovy and generated Java.
- `kernel`: 30.8.1 built and runtime; both strategies agree on every reported runtime channel.
- `claim`: `NumberOfValueInFields(False In group)` over a fixed Boolean/Confirm group is rejected with only `MVK_NO_TYPEYESNO`; `True` over that group and over the fixed Boolean group is admitted.
- `claim`: a fixed Boolean group containing one direct declaration and one declaration in a nested repeatable group counts the same second-row `True` as its explicit direct-plus-starred-field control.
- `claim`: with every instantiated cell filled and the count fixed at one, leaving row 3 uninstantiated under repeatability 3 makes `== 1` fire `OMISSION_ERROR` on both operand forms; instantiating row 3 with `False` flips both to `VALUE_ERROR`, while the identical max-2 fully instantiated pair stays `VALUE_ERROR`.
- `control`: `>= 1` stays `VALUE_ERROR` with the open tail, the all-`False` second-row control emits no count rule, and an empty guard leaves every rule silent.
- `separator`: the max-2 and max-3 groups carry identical instantiated values in one document, so the equality polarity differs only with declared capacity; the explicit controls distinguish group-specific tail loss from a wider count or comparison defect.
- `integrity`: model SHA-256 `fe6fde2f535e221640e7a193273cc0554c9532a332bce9b423e2e346c55108c0`; request SHA-256 `42378774a8328be55e36b4598bbd6da2c0fab316b8dbcc791fa00b13dbc4e301`; two unchanged runs produced byte-identical artifacts at SHA-256 `204931052abb37d64f8ec994f61fcae38347718b4fcd58ea798651242a67307e`.
- `limit`: full validation, `True` runtime identity, one unstarred fixed operand, one finite nested repeatable level, two or three instantiated rows, equality/greater-or-equal polarity, and message type only; starred groups, deeper or unbounded repetition, computation, partial validation, invalid cells, message addresses, and references are not measured.
- `sync`: the outcomes match the existing constant-specific kind, recursive group extent, and declared-tail count clauses, so no outbound correction follows.

#### Group-message checkpoint

a12-dmkits `7df9f5570a1b7f7b4e5bfa5118a6c3521c8db320` then closes the message residual this project raised against that batch, in four further tri-checked cases of the same test, which the peer's amendment now pins correctly and whose case counts identify each revision on their own (7, 11, 17, 19, 23, verified here against the file at each).

A firing over a starred group operand emits exactly one message at the error field's concrete first row, count and address independent of the duplicate's location, on both rule placements and both error-field loci, every firing VALUE. **The separating structure is the reason to trust the count**, and the first two rows would not have carried it: with the error path resolving above the repeatable group, one evaluation over the operand and a per-row evaluation whose two messages collapse onto a single address predict the identical observation. The third row moves the error field inside the rule's own group, which gives the second account two distinct addresses to report at, and it still yields one message; the fourth places the duplicate wholly inside the operand's second row and the anchor stays at the first.

The peer also reports that its prior lock could not have answered this: its tri-check read `any { it.code() == CODE }`, under which one message and two are indistinguishable, so all nineteen earlier rows were structurally blind to the question rather than merely silent on it. Three claim limits, of which the peer's own text states none: every row authors the **starred** form, so the unstarred group operand has no message row; `referenced` membership is untouched; and the reached-`Having` OMISSION contrast is untouched, so VALUE is measured but not separated from its alternative.

The peer flagged its "this matches your starred field form" sentence as a comparison against our prose rather than a measurement, and it is stronger than it thought: our field-form account is independently kernel-locked on its side by `FieldValuesNotUniqueDiffTest.starredDuplicateEmitsOneFirstRowMessageWithItsWildcardReferenceInBothPlacements`, so the two forms agree as two measurements rather than as a measurement checked against text. That is agreement, not a shared mechanism, and the clauses stay separate.

### Inbound group-operand carrier sweep and authored-path wildcard gate

<a id="src-group-carrier-static-admission"></a>
#### Group-carrier static admission

- `revision`: a12-dmkits `57ddd442f2f609b645c0030280662bc96d8ac49c`.
- `route`: source-shipped dmtool 0.13.0 structured `rule check` through the real-kernel consistency oracle.
- `kernel`: 30.8.1 built and runtime.
- `claim`: `FieldValuesNotUnique` admits a nonrepeatable group containing two ordinary Date fields with one persisted `yyyy-MM-dd` format.
- `control`: the equivalent explicit two-Date-field list is admitted in the same six-row matrix.
- `claim`: `NumberOfValueInFields` admits `True` and `False` over a Boolean group and `True` over a Boolean/Confirm group.
- `control`: the equivalent explicit two-Boolean-field list is admitted in the same matrix.
- `claim`: `FirstFilledValue` over a homogeneous two-Confirm fixed group reports only `MVK_NO_BOOLY_ALLOWED`, while a fixed group expanding in ordinary-evaluated-String-then-Number declaration order reports only `MVK_VARYING_TYPES_NOT_ALLOWED`.
- `control`: each fixed group agrees with its explicit two-direct-stored-field expansion in the same order, and both the homogeneous String group and its expansion are admitted.
- `integrity`: the six caller-tagged `FirstFilledValue` observations and rule checks are retained by SHA-256 `2101c57eabac26b38a8c682446acb7de7f967e2adc48182a2f3cf8bd0c52c126` and `f069e60136bf999da56bd6c71fe6bfa6ac826516415b45f3081040953e4727f6`; the persisted model bytes hash to `b11599b1ec2ba33ba4255c5e4166e53a9d0bb3baac95de17bd5b3d615c2a6fd2`, without extending the structured observation claims.
- `limit`: static admission only; no runtime account follows.
- `limit`: `False` over a Boolean/Confirm group is not measured.
- `limit`: the `FirstFilledValue` matrix establishes only the exact fixed-group and equivalent two-direct-stored-field carriers above; raw or custom String policies, reverse order, starred or filtered carriers, wider kind combinations, and wider widths are not projected from it.
- `claim`: `FirstFilledValue(Outer*/FixedNested)` is admitted when `FixedNested` is a nonrepeatable terminal group below the starred repeatable `Outer`; the equivalent two-field expansion is admitted too.
- `claim`: `FirstFilledValue(Outer*/Inner/Value)` reports only `MVK_NO_WILDCARD` when repeatable `Inner` remains unstarred below `Outer*`; `Outer*/Inner*/Value` is admitted.
- `integrity`: the four caller-tagged wildcard observations and rule checks are identified by SHA-256 `d9ef470f1b20a35f4ef9e56dc09455242323d95591da97c205b600d56a360aab` and `795330d630dfc908d5d4faddfdd5e91a8cedbd53a4f2cf1147dbde066da8a139`; the persisted model bytes hash to `f66ce63c80706c25114fc8dff2dfd399e2b487abba27a8a1e32c322fc622636d`, without extending the structured observation claims.
- `limit`: these wildcard rows establish static admission and diagnostic identity for the exact `FirstFilledValue` paths only; no runtime result follows.
- `sync`: these confirmations match existing clauses and create no outbound semantic correction.

<a id="src-group-carrier-duplicate-precedence"></a>
#### Group-carrier duplicate precedence

- `basis-revision`: local dmtool 0.13.0 observations ran from clean a12-dmkits `57ddd442f2f609b645c0030280662bc96d8ac49c`.
- `revision`: reviewed a12-dmkits `2d384c59f18cf9a1019e1e8273f2d8e900f741e0`.
- `route`: source-shipped dmtool 0.13.0 structured `rule check` through the real-kernel consistency oracle.
- `test`: maintained [`FirstFilledValueDuplicatePrecedenceLawsTest`](../../../a12-rulekit/src/test/java/io/github/mbackschat/a12/dm/rulekit/validate/laws/FirstFilledValueDuplicatePrecedenceLawsTest.java), with nine complete-code rows and both exact repair witnesses.
- `kernel`: 30.8.1 built and runtime.
- `claim`: one fixed group is admitted, while the same fixed group authored twice reports only `MVK_DUPLICATE_PARAM1`; the same starred repeatable group authored twice is admitted.
- `claim`: one direct field reports only `MVK_PARAMSIZE_INVALIDN`, two equal direct fields report only `MVK_DUPLICATE_PARAM1`, and a fixed group beside its descendant field reports only `MVK_DUPLICATE_PARAM2`.
- `claim`: every exact non-wildcard field or fixed-group identity shares one authored encounter scan. `(group, field, field, group)` names the field; `(group, group, field, field)` names the group; strict overlap runs only when no exact duplicate exists.
- `integrity`: the eight caller-tagged observations and rule checks are identified by SHA-256 `36f037ae24bfb01d542563f243c1f343e97fcadd5bb8984824f2981bd8a2a152` and `bea84e4282023d0b565d2926697dfc7709a150c42b23bf32e1386d32e5899cbf`; the direct mixed-fault diagnostic was captured twice byte-identically at SHA-256 `2595923d0a74a73f2b10336dbc0e4cef27f4b3d2d6afe57a58846e04e2a51b82`; the persisted model bytes hash to `f66ce63c80706c25114fc8dff2dfd399e2b487abba27a8a1e32c322fc622636d`, without extending the structured observation claims.
- `limit`: static admission and emitted diagnostic identity only; no runtime result, message projection, or behavior outside the exact `FirstFilledValue` carrier follows.
- `sync`: the inbound reviewed discriminator rejects [`SPEC-2026-08-17-01`](../archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md#spec-2026-08-17-01)'s class-priority mechanism while retaining its individual rows; no new outbound request follows.

<a id="src-group-carrier-admission-sweep"></a>
#### Group-carrier admission sweep

- `revision`: a12-dmkits `e233548e2c35a8810454f362f8366cb7d6a0dea0`.
- `route`: real-kernel `rule check`.
- `test`: [`GroupOperandCarrierAdmissionLawsTest`](../../../a12-rulekit/src/test/java/io/github/mbackschat/a12/dm/rulekit/validate/laws/GroupOperandCarrierAdmissionLawsTest.java), durable peer home `KF187`.
- `claim`: group-operand admission is per operator, not per family; two measured pairs disagree within one family.
- `claim`: a Date group against a String value list reports `MVK_ONLY_STRING_ENUM_NUMBER_ALLOWED`, while a String-group control is admitted; this separates expansion type-checking from unconditional group admission.
- `claim`: `MoreThanOneFieldFilled` admits a single-field group while rejecting that field alone with `MVK_PARAMSIZE_INVALIDN`, separating slot arity from expansion cardinality.
- `claim`: `FirstFilledValue` admits a group operand in both repetition shapes; the later [group-carrier static admission](../SOURCES.md#src-group-carrier-static-admission) checkpoint owns its bounded expansion-kind diagnostics.
- `claim`: `Min` distinguishes a starred field's `MVK_NO_WILDCARDS_ALLOWED` from a group's `MVK_NO_GROUPS_ALLOWED`.
- `limit`: a starred group alone cannot separate `Min`'s group and wildcard gates because both accounts report the group class.

#### Authored-path wildcard checkpoint

a12-dmkits `4105b256da528154d1aba851bdc18f96947b3cae`, `d510684807738aac614e0d596ba6871b4715832a`, and `f9f92aaa788221d335538c3f50666da92414b23e` carry the **authored-path wildcard gate**, which is the third gate in the split and the reason `spec/07` now says a group operand and its written-out expansion are two different models. **Three provenance limits travel with it and the first is unresolved.** The cited lock `adapter.MixedScopeStarPreservationTest` **does not exist** at `ebe65be9`, and no file in that tree carries its `Sections*/Answers` fixture, so the three rows themselves were not locatable here; the nearest name present is `MixedScopeFieldFillReadTest`, which is not it.

The three revisions do resolve and their subjects are consistent with the claim, the last two being "keep a group operand a group instead of replaying its expansion" and "read a group operand under the two arms that had none". The clause was therefore recorded as the peer's measurement with its row-level evidence unconfirmed, and that marking is now lifted: the rows are asserted again under a live lock, named at the end of this section. The peer's own converter disclosure is the corroborating half, since it reports five symptoms of having replayed the expansion, including emitting an unstarred nested repeatable level and so producing a condition the kernel rejects from a model it had just read as valid.

<a id="src-group-runtime-and-reference"></a>
#### Group runtime and reference correction

- `revision`: a12-dmkits `bffe9cca65c32125caf304e6b9cec863bbf9d9f3`, range `19adb3e5..af9d14b94ff07922cb63a2a5d5b89c0c9572ecfc`, and `e672da6eebba2342aaa900d5bf133457e378fa19`.
- `route`: adapter differentials assert both kernel codegen strategies equal before comparing the a12-dmkits interpreter.
- `test`: [`NestedGroupFillQuantifierDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/NestedGroupFillQuantifierDiffTest.kt), `GroupScopeFromADeepRuleRowDiffTest`, and `StarredGroupOperandOwnLevelDiffTest`.
- `test`: `ComputeGroupScopeFromADeepRowDiffTest`, `MultiStarDeclaredScanScopeDiffTest`, and [`MinMaxGroupOperandComputeCarrierLawsTest`](../../../a12-rulekit/src/test/java/io/github/mbackschat/a12/dm/rulekit/validate/laws/MinMaxGroupOperandComputeCarrierLawsTest.java).
- `claim`: admitted carriers use the recursive group expansion rather than a carrier-specific direct-child extent.
- `claim`: `FirstFilledValue` encounter order places a filled direct field before nested rows; the later [fixed-group first-filled checkpoint](../SOURCES.md#src-group-first-filled-runtime-order) owns order within the direct and fixed-nested declaration pairs.
- `claim`: the measured fill-quantifier firings distinguish OMISSION while a reached operand cell is empty from VALUE when their relevant expansion is filled.
- `limit`: no operator-independent polarity rule follows; the later [fixed-group first-filled checkpoint](../SOURCES.md#src-group-first-filled-runtime-order) owns `FirstFilledValue`'s empty-prefix versus empty-suffix separator.
- `claim`: an unstarred `/Shipment/Carrier` reference includes `/Shipment[1]/Carrier[1]/Handoffs[0]/Site` and `/Shipment[1]/Carrier[1]/Name`; wildcarding begins at the first repeatable descendant inside the operand.
- `claim`: short revision `c1eb1614` applies the same depth rule to the compared set.
- `separator`: a repeatable level above the operand separates the measured rule from a rule-depth pin and from an entirely unbound resolver.
- `limit`: the source's mechanism hypotheses are excluded; the records establish outcomes and separators only.
- `limit`: a reached-`Having` contrast is not open because a group operand cannot carry that filter on the three measured carriers, established at `2d4dc4beabd2c8375e4b2de14aaff0dd5c88cbaf`.

<a id="src-group-first-filled-runtime-order"></a>
#### Fixed-group first-filled runtime order

- `observation-revision`: clean a12-dmkits `57ddd442f2f609b645c0030280662bc96d8ac49c`, dmtool 0.13.0, built/runtime kernel 30.8.1.
- `lock-revision`: reviewed a12-dmkits `08115206d99bf8417c99dff9a73f9005175ca7d7`.
- `lock`: [`FirstFilledValueGroupOperandDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/FirstFilledValueGroupOperandDiffTest.kt) retains the four rows across dynamic Groovy, generated Java, and the interpreter; [`FirstFilledValueGroupOrderTest`](../../../a12-rulekit/interpreter/src/commonTest/kotlin/io/github/mbackschat/a12/dm/interpreter/FirstFilledValueGroupOrderTest.kt) retains the same matrix on JVM and Node.
- `route`: source-shipped `:adapter:kernelProbe` over one dmtool-authored self-contained model and four canonical documents; dynamic Groovy and static Java agree on every reported channel.
- `claim`: when both fixed-group direct String fields are filled, `FirstFilledValue` selects the field declared first even though its `ZetaDirect` path sorts after `AlphaDirect`; when only the second is filled, it selects the second.
- `claim`: the same declaration-order rule holds for `ZetaNested/Value` before `AlphaNested/Value`; the nested cases report OMISSION with an empty direct prefix, while the direct-both case reports VALUE despite its later empty nested declarations.
- `control`: each second-only row proves that the later declaration is reachable rather than ignored, the two first-filled rules make the selected token externally visible as distinct message codes, and VALUE on direct-both separates empty suffixes from the OMISSION-producing empty prefixes in the other three rows.
- `integrity`: the request has SHA-256 `adefc3b59a79f38eb9aaa5bacb91c12ac74bf8c6a317785db4f3ea36d74fbbd3`; two unchanged runs produced byte-identical artifacts at SHA-256 `a9c702f51df0801319ef01ce27e434b9b98b16228c9c711cf700be2f621f1a49`.
- `integrity`: model SHA-256 `15e4de7a9e26d9b7b18a99a23af6e74f02ffad4dac4762686c9817e30a2d8d16`; document hashes in request order are `8949bca51ece7c5674e40985cafe87bb6c42fc95f10c8672f83159e4531df42b`, `f8363ee52ef1a78130bc98dc458db63d5bc0459d1ca7416d2a1e3da4d0819c06`, `845b15de7d823676df62c0015c8df02bb39c78821343b44e004259bdb37b6c91`, and `e0d764fb2b728c69b2777d24cbf0c01b19684e71212fe87fa9f67bf9e7929ff6`.
- `limit`: fixed nonrepeatable group, direct and fixed nested declarations, full validation, exact selected token, and resulting VALUE/OMISSION only; starred groups, repeatable row order, wider lists, computation, partial validation, and legacy raw-document routes are not measured.
- `sync`: [`SPEC-2026-08-17-02`](../archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md#spec-2026-08-17-02) was accepted as stated at the lock revision.

<a id="src-star-group-first-filled-runtime-order"></a>
#### Starred-group first-filled runtime order

- `observation-revision`: clean a12-dmkits `57ddd442f2f609b645c0030280662bc96d8ac49c`, dmtool 0.13.0, built/runtime kernel 30.8.1.
- `lock-revision`: reviewed a12-dmkits `08115206d99bf8417c99dff9a73f9005175ca7d7`.
- `lock`: [`FirstFilledValueGroupOperandDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/FirstFilledValueGroupOperandDiffTest.kt) retains the six rows across dynamic Groovy, generated Java, and the interpreter; [`FirstFilledValueGroupOrderTest`](../../../a12-rulekit/interpreter/src/commonTest/kotlin/io/github/mbackschat/a12/dm/interpreter/FirstFilledValueGroupOrderTest.kt) retains the same matrix on JVM and Node.
- `prior-lock`: maintained [`FirstFilledValueGroupOperandDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/FirstFilledValueGroupOperandDiffTest.kt) establishes that an unstarred group reaches nested row 2 and visits a direct declaration before nested rows.
- `prior-lock`: maintained [`FirstFilledValueOmittedTailDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/FirstFilledValueOmittedTailDiffTest.kt) establishes no-row fallback polarity for a field star, not a starred group.
- `route`: source-shipped `:adapter:kernelProbe` over one dmtool-authored self-contained model and six canonical documents; dynamic Groovy and static Java agree on every reported channel.
- `claim`: for terminal `Rows*` with direct `First` then `Second`, row 1 `Second = second` and row 2 `First = first` selects `first` with OMISSION; the group stream is declaration-major rather than row-major.
- `claim`: a no-row `Rows*` before one direct fallback selects the fallback with OMISSION; one instantiated empty row gives the same outcome, while an immediate first-row value is VALUE despite later rows and uninstantiated capacity.
- `control`: second-only reaches the later declaration, later-first-only reaches row 2, and the immediate-first row distinguishes an empty prefix from an unread suffix.
- `integrity`: request SHA-256 `8da7f4ebfa04c6df58dbdeb5e5db9157f6f96bf20a2be942e6848da45e7a2eea`; two unchanged runs produced byte-identical artifacts at SHA-256 `67f5a549b80601ab022de127b2fe7b69a606f6ad717f0bcc4edee7fbc6202a8f`; model SHA-256 `005d9357cb105be4195de4d82f24c7077ed7aa0eda9596096bf44d8320aacf41`.
- `integrity`: document hashes in request order are `bf8736afcc211da325a89fc81effa8f9ac338392f9fe7a6c034a8db6bdb6a60b`, `94574f4e190799b734ec48668dcb2a2d0ad1816156c1e8f6ba043bfac547f5c0`, `3a940ddc07627b5fb0359dd573edbb5fead71348891aaa3a983d13fc9610bf56`, `930ebb29a920ed456bd2d7f354489174687944b77a48109d60dc8074c05c6264`, `2fe01b8f534c37b2c7afbe4c4427a693a0a6ed5f0f835a5792754d33d837a69e`, and `284b0b02d9bfc0472259d91f561cd4bf25856640be8d7d8901b49d3852447890`.
- `limit`: terminal single-level starred group, two direct String declarations, full validation, declaration-major selection, VALUE/OMISSION, and one direct fallback only; nested or multi-level stars, outer binding, other mixed lists, computation, partial validation, raw-document routes, and an isolated omitted-tail mechanism are not measured.
- `sync`: [`SPEC-2026-08-17-03`](../archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md#spec-2026-08-17-03) was accepted as stated at the lock revision.

#### Additional carrier-sweep provenance

Three further rows in that sweep are **deliberately not absorbed**, recorded so a later reader does not mistake the omission for an oversight. The `$` outer-marker gate (`MVK_INVALID_OUTER_ITERATION`, universal and filter-only, correcting the peer's own earlier reading that had taken it for a statement about aggregate operands) and the computation-target reference class (`MVK_ERROR_REFERENCE_TO_CALCULATED_FIELD`, whose consequence is that no legal compute spelling of a group-scope-from-a-deep-row discriminator exists, making validation the only carrier that can measure one) are both real static-legality facts that belong to their own clauses rather than to the group-operand paragraph.

**Index-keying is not a gate on the unstarred repeatable group operand; the error field's locus is.** `UnstarredRepeatableGroupIterationLawsTest` compares models differing only in `indexField("Sku")`, retains non-degenerate controls, and establishes identical 24-cell matrices over four field-fill quantifiers, both spellings, and three error-field loci. The two inside-the-group loci agree whether or not the error field is the index field.

**The neighbouring `MVK_NEG_CONDITION_IN_ITERATION` gate is syntactic.** `FieldsNotCollectivelyFilled` is grammatically negative and admitted, while `NumberOfFilledFields(G) < 1` carries no negation and is refused. The refused `< 1` and admitted `<= 0` denote the same predicate because the count cannot fall below zero. The retained nine-cell shape therefore establishes neither a semantic-negation test nor a reconstructed syntactic rule.

**The two gates composed on a nested repeatable then produced a row neither predicts**, locked by `NestedGroupOperandGateLawsTest`: an operand starring an outer level while leaving an inner repeatable level bare is refused in all six of its cells, which a consumer composing the gates separately admits, because each gate alone has no objection. The polarity-adjacent refusal tracks the **iterated** level rather than the operand, and a filter on a group operand is refused outright, so it cannot move either gate on this carrier.

`FirstFilledValueFamilyLawsTest` establishes that the temporal expansion gate reads the **declared format**, not the carrier kind. A DATE declared `yyyy` beside a DATE_FRAGMENT declared `yyyy` is admitted across two kinds, while two DATE fields at differing formats are refused. The fixture retains both separating pairs, so a compatibility table phrased only in kinds is insufficient.

The format rule then gained a witness independent of its closest pair, at `96d0cbedceaa31c89fccf1d978fbd171307de45c` and `e9b3d725bb52bcf6c459b8241710262424def16c`. `DATE` beside `DATE_FRAGMENT` leaves open the objection that the kernel treats those two as one type; `TIME` beside `DATE_TIME` does not, and they can share a declared format exactly because a DateTime may be declared time-only. That pair is admitted at one shared format while two `DATE_TIME` fields at differing formats are refused, and `DATE_RANGE` behaves identically once its allowlisted (format, separator) pair is read as the format, so the rule now covers all five temporal kinds rather than the two that happened to be measured.

[`spec/05`](../../spec/05-dates-and-time.md) owns the time-only DateTime surface. `TimeOnlyDateTimeSurfaceLawsTest` retains its Kernel rows and the essential vacuity control: an all-refusal table is also satisfied by a field that is simply dead.

`NestedGroupOperandGateLawsTest.aGroupOperandAndItsWrittenOutExpansionAreNotInterchangeableSpellings` owns the mixed-scope star-preservation rows: group-operand admission, `MVK_NO_WILDCARD` on the written-out expansion with the inner level unstarred, and the both-levels-starred control.

<a id="src-sum-of-products-owning-group"></a>
#### `SumOfProducts` owning-group and diagnostic matrix, reviewed inbound 2026-08-29

- `revision`: a12-dmkits `a75e6e2dd`; the exact revision and maintained test were reviewed read-only from a clean sibling worktree.
- `route`: [`SumOfProductsLawsTest`](../../../a12-rulekit/src/test/java/io/github/mbackschat/a12/dm/rulekit/validate/laws/SumOfProductsLawsTest.java) runs the Kernel static checker over eleven separating arms.
- `admission-claim`: both fields' immediate owning group must be the same. That group may be fixed below a repeated ancestor, so `Lines*/Packaging/Weight` paired with itself is admitted, while `Lines*/Qty` paired with `Lines*/Packaging/Weight` is refused even though both share `Lines*`.
- `diagnostic-claim`: differing owning groups report `MVK_DIFFERENT_GROUPS`; an unstarred repeatable level or a star above the lowest repeatable level reports `MVK_NO_WILDCARD`; multiple stars report `MVK_WILDCARD_ONLY_AT_LOWEST_LEVEL_ALLOWED`; `Having` reports `MVK_WILDCARD_AT_LOWEST_LEVEL_REQUIRED`; and a path with no repeatable level reports `MVK_REPEATABLE_LEVEL_REQUIRED`.
- `evidence-limit`: static admission and diagnostics only. This revision supplies no runtime observation.
- `local-consequence`: the bounded pair matrix is implemented with exact diagnostic projection under [Number aggregates](../IMPLEMENTATION-MAP.md#cap-number-aggregates); wider aggregate/path shapes remain outside this checkpoint.
- `sync`: inbound correction already committed and reviewed in a12-dmkits; no outbound ledger entry.

<a id="src-count-partial-extent"></a>
#### Direct starred count partial-extent checkpoint

- `revision`: reviewed clean a12-dmkits `cd43c249a88874bf5688a45060e208a0dcd20782`, Kernel 30.8.1.
- `route`: maintained partial-validation differential over one positive two-row `Items*/Qty` document, with exact fired-code assertions on dynamic Groovy, generated Java, and the independent interpreter.
- `test`: [`PartialExtentGateShapeDiffTest.theThreeCountLoopsSelectTheirMeasuredExtentGates`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/PartialExtentGateShapeDiffTest.kt) retains the nine relevance selections; `theCountMatrixControlsReachEachOperator` retains the two-nonmatching, two-empty, and no-row controls.
- `claim`: `NumberOfFilledFields(Items*/Qty)` fires on matrix rows 1, 3, 4, and 5, selecting the reduced-universal field-extent pattern.
- `claim`: `NumberOfFilledGroups(Items*)` fires only on row 4, where a wildcard group accompanies a concrete field identifier, selecting a fifth observable pattern rather than any of the four proposed outcome accounts.
- `claim`: numeric `NumberOfValueInFields(10 In Items*/Qty)` fires on rows 1 through 6, selecting the existential value-list extent; complete concrete enumeration and either one-row selection remain insufficient.
- `control`: two filled nonmatching quantities fire only filled-field and filled-group, two instantiated empty rows fire only filled-group, and no rows fire none on all three engines.
- `mechanism-limit`: the runtime matrix establishes per-operator outcomes. Source inspection establishes that numeric and token `NumberOfValueInFields` share the Kernel loop, but the String/Enumeration overload was not independently exercised by this partial runtime matrix. Nested repeatable levels and a separately represented semantic-root versus physical-root identity remain external evidence pending.
- `local-state`: Lean exposes the two previously missing partial count routes, removes the obsolete uncalibrated one-covering predicate, and reuses the established reduced-universal or existential gate at each measured operand path. Applying the reduced-universal predicate to the group path reproduces the fifth pattern without making descendant field identifiers project upward; this is the local executable account, not an independently isolated Kernel mechanism. `PartialValidationFilledFieldCountResult` and `PartialValidationFilledGroupCountResult` keep unavailable extent distinct from an evaluated count that may itself be formally unknown.
- `sync`: accepted [`EXP-2026-08-24-01`](../archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md#exp-2026-08-24-01--which-partial-validation-extent-gate-do-the-three-non-combiner-count-loops-use); peer [KF209](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf209) owns the Kernel observation and [IF310](../../../a12-rulekit/docs/INTERPRETER-FINDINGS.md#if310) owns the bounded interpreter correction. No outbound follow-up remains.

### Inbound partial-relevance, index-identity, and row-domain correction batch

a12-dmkits clean revision `752054077be62be441b119af14efc97c6baf13d9` contains the maintained routes behind the 2026-08-08 consolidated inbound correction to §§8, 9, and 12.

The partial-relevance extent split begins at `3ce95a05979c1f6c0b5afe83e83607232bb21dbd` and `0dbc7fc8a0c5e65c3ec33f3f867fdb614f5dd7e1`; [`PartialValidationAggregateDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/PartialValidationAggregateDiffTest.kt), [`PartialNestedAggregateDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/PartialNestedAggregateDiffTest.kt), [`PartialNestedWildcardScopeDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/PartialNestedWildcardScopeDiffTest.kt), [`PartialMultiStarScopeDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/PartialMultiStarScopeDiffTest.kt)

[`PartialExtentGateShapeDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/PartialExtentGateShapeDiffTest.kt), [`PartialValidationValueListDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/PartialValidationValueListDiffTest.kt), and [`PartialValueListCellRelevanceDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/PartialValueListCellRelevanceDiffTest.kt) separately retain the all-rows universal gate, the starred value-list existential gate, `SumOfProducts` complete-cross-product gate, first-star binding, per-iteration-row scope, and concrete cell filtering.

[`PartialRuleGateScopeDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/PartialRuleGateScopeDiffTest.kt), [`PartialAtLeastOneScanDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/PartialAtLeastOneScanDiffTest.kt), [`PartialParallelJoinKeyDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/PartialParallelJoinKeyDiffTest.kt), and [`ParallelJoinDuplicateKeyDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/ParallelJoinDuplicateKeyDiffTest.kt) retain iteration-bound error gating, relevance-scoped duplicate compromise, relevant-index join construction and validity, unmatched `-5`, and duplicate exclusion.

The original relevance-scoped duplicate landing is `cb75eb3cdfa8363d3b96ce0acd89592d4d8965c8`.

The same current peer revision carries the wider index and row-domain discriminators rather than inferring them from the partial-validation cases.

[`NumericIndexKeyDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/NumericIndexKeyDiffTest.kt), [`IndexIdentityCustomTypeDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/IndexIdentityCustomTypeDiffTest.kt), [`FirstFilledValueEntitySpecDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/FirstFilledValueEntitySpecDiffTest.kt), and [`SemanticIndexComputeNoMatchDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/SemanticIndexComputeNoMatchDiffTest.kt) retain admission-before-kind-owned identity, collision, selection/join, three-valued presence, authored-pointer identity, descendant-coordinate selection

and computation-overlay payload reads.

[`RepeatableRowContentDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/RepeatableRowContentDiffTest.kt), [`ReferenceDrivenIterationScopeTest`](../../../a12-rulekit/interpreter/src/commonTest/kotlin/io/github/mbackschat/a12/dm/interpreter/ReferenceDrivenIterationScopeTest.kt), and [`RepetitionNotUniqueKeyOrderDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/RepetitionNotUniqueKeyOrderDiffTest.kt) retain V1-to-V2 predecessor padding, recursive implicit validation child row 1 versus concrete-row consumers, and deepest-key-parent RNU iteration independent of authored key order.

These are reviewed inbound corrections already committed in a12-dmkits; they update this repository's canonical clauses and provenance without creating an outbound ledger entry. The partial-extent probes do not establish declared-versus-present completeness, three-or-more-level relevance gates, or skip-versus-UNKNOWN for a non-relevant value-list cell, so those claims remain absent.

### Inbound fixed-group over-limit extent batch

<a id="src-group-operand-capacity-consumer-sweep"></a>
#### Fixed-group over-limit extent across six carriers

- `revision`: a12-dmkits `dd11c9a90`, the short form the peer reported; kernel 30.8.1.
- `route`: tri-engine differential — dynamic-Groovy codegen, static-Java codegen, and the peer interpreter — compared on the complete `code@pointer` message set rather than on the probe rule's presence, so a divergence in the accompanying formal messages cannot pass as agreement.
- `test`: [`GroupOperandOverLimitExtentDiffTest`](../../../a12-rulekit/adapter/src/test/kotlin/io/github/mbackschat/a12/dm/adapter/laws/GroupOperandOverLimitExtentDiffTest.kt).
- `instrument`: the carrier's exact value is read off a **ladder of candidate equalities** (`== 0`, `== 1`, …) and the member that fires is the answer; none firing is reported as `UNAVAILABLE` and two as ambiguous. This makes non-evaluability a first-class observation instead of an inference from two silences, and it is the generalization of the `< 1` negative partner that made the local round decisive.
- `fixture`: a **nonrepeatable** shell group per operand kind — `Notes`, `Flags`, `Amounts` — each owning repeatable descendants capped at 2, so index 3 is over-limit. The operand is therefore the fixed group form throughout.
- `claim`: `NumberOfFilledFields(Notes)` answers `0` when the only filled cell sits over limit and `1` on the in-capacity control, at the outer repetition level and the inner one alike.
- `claim`: `NumberOfValueInFields("KEEP" In Notes)` and `NumberOfValueInFields(True In Flags)` answer `0` over limit and `1` in capacity.
- `claim`: `Sum(Amounts)` answers `5`, `MaxValue(Amounts)` answers `5`, and `NumberOfDifferentValues(Amounts)` answers `1` on a document holding `5` in capacity and `7` over limit; `MinValue(Amounts)` answers `7` on the reversed document, so the extremum is discriminating rather than coincidentally equal.
- `claim`: a malformed cell **in capacity** makes `Sum(Amounts)` `UNAVAILABLE`; the identical malformed cell one index **over limit**, with `5` in capacity, answers `5`.
- `mechanism`: that last pair is what separates *removed from the domain* from *classified unavailable and not counted* — both accounts predict a definite `0` on an only-over-limit document, and they differ exactly where unavailability propagates. An over-limit row is not an excused member of the evaluation domain; it is not in the domain being classified.
- `shape-note`: the counts are decidable on an only-over-limit document, but the aggregates are not: on an empty domain *excluded* and *unavailable* are both candidate-free, so the aggregate rows need a **mixed** document with a value in capacity. The local only-over-limit shape is the right instrument for the counts and blind for the aggregates.
- `agreement`: the peer interpreter agrees on every row, so no peer fix followed; that was not knowable before measuring.
- `limit`: one fixture, `en_US`, bounded repeatability 2, three declared levels only on the String shell, full validation and no partial.
- `limit`: the malformed-in-capacity versus over-limit split is measured on the **fixed** group operand only. Whether a starred carrier shows the same split is unmeasured.
- `limit`: `Sum` over an empty in-capacity domain is not measured, because the mixed document deliberately avoids it; whether that is `0` or unavailable remains open.
- `peer-boundary`: four of the six carriers have no typed factory for an unstarred group operand in the peer's API, so the probe authored raw condition strings. That is a peer type-level erasure over a shape the Kernel admits, recorded there as `DG42`; it constrains the peer's surface, not the Kernel's.

<a id="src-starred-field-operand-peer-reproduction"></a>
#### The starred field operand and the empty-domain zero, reproduced by a12-dmkits, inbound 2026-08-31

- `revision`: a12-dmkits `304440ee60073e4ab43576c66b56ecaa66a56f55`, its `GroupOperandOverLimitExtentDiffTest`. Kernel `30.8.1`, both codegen strategies with the interpreter compared as a third engine and never as the oracle. Read here rather than taken on report: the revision is an ancestor of the peer's head and its test body was inspected.
- `question`: this project measured the starred **field** operand and the corrected empty-domain zero on its own probe and asked the peer to reproduce or refute them ([`SPEC-2026-08-31-11`](../A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-08-31-11)). The peer had named both as gaps in its own estate before the request.
- `claim`: the starred field operand projects to declared capacity across all five carriers on an independent e-commerce fixture — `Sum` 5, `MaxValue` 5, `MinValue` 7 reversed, `NumberOfDifferentValues` 1, `NumberOfValueInFields` 0 reversed — each against its own both-in-capacity control, with the malformed split identical to the group form.
- `claim`: the empty-domain zero holds for the whole aggregate family, on both a never-instantiated domain and one emptied by the capacity projection. Two of the peer's own ladders carried this project's zero-member shortfall and read a value only because their documents happened to be non-empty; their harness now refuses a ladder that cannot express `0`.
- `arm-limit-closed`: the computation arm landed separately at a12-dmkits `981fc9b62`, whose `OverLimitOperandComputeArmDiffTest` drives `compute` and reproduces this project's operand-error-plus-definite-value pair and the `outcomes: []` reading. `304440ee6` measures `validateFull` only — the handback named it for both halves — so the two arms carry two revisions here, each read rather than taken on report.
- `operand-channel`: **the computation's over-repetition channel is measured operand-scoped, which settles the discriminator [SG4](../SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition) recorded.** An over-limit row in a group no computation reads draws nothing, on a row left empty so only the group walk could speak for it; and the scope reaches the operand's whole ancestry, an outer row above capacity two levels up drawing three messages. Both bounds are at `981fc9b62`. This project's own retained bytes already showed the channel differing from validation's — ten findings against zero on one document — so the peer's rows name the rule that difference obeys.
- `pointer-dialect`: the peer's site assignment is pinned as `code@pointer`, but **those addresses are its own house projection and are not kernel address evidence**: both group sites lose their row index while the field site keeps one, which is the collapsing formatter this project measured earlier ([dialect checkpoint](../SOURCES.md#src-message-address-dialects)). The peer states the limit itself. Take the site *assignment* from these rows and the address *spelling* from the kernel-channel record.
- `caution`: the peer reported that assignment before pinning it, having read it off its own implementation, and corrected itself unprompted after measuring. The count and code multiset were measured throughout; one code lands twice, so the multiset alone could not settle which site drew which.
- `local-consequence`: none for the extent rows — the clauses those reproduce were already landed and locked here from this project's own probes, and the value is an independent second estate agreeing on a different fixture and a third engine. The `operand-channel` row is the exception: it is the only part of this batch that was not already represented here, and it landed as [`09-computations.md`](../../spec/09-computations.md) §3.3's channel-scope paragraph and as the [computation over-repetition channel](../IMPLEMENTATION-MAP.md#cap-computation-over-repetition-channel). Inbound, so no outbound entry.
- `corroboration`: two of comparability's three cells are visible in this project's own retained [multiplicity artifact](over-repetition-probes.md#src-over-limit-finding-multiplicity) without a new run, which is why the Lean cases can lock them here rather than cite the peer. Its probe model's computations name `/Probe/ShellDeep`, `/Probe/ShellDeep/Mid*`, and `/Probe/ShellOne` and **none names `/Probe/Tri`**; its two-independent document holds an over-limit row under each and reports eight validation findings against four operand errors, all four under the named one. The **upward** cell has no witness in those bytes and stays the peer's.
- `reach`: **the peer's handback names where this project's claims now sit in text this project cannot watch**, which is the blast radius of any later retraction here. Its `KF58` cites this project's empty-domain retraction as the reason its own claim covers the whole aggregate family rather than `Sum`; its `KF188` cites [`LF114`](../LEAN-FINDINGS.md) as the reason its group-operand extent is measured on a two-field group; and two of its differential tests name this project's ledger entries and both retractions as row provenance. Its report states that no schema description, help text, or public API documentation carries a clause of this project's from that batch. Recorded because a retraction here now has a known set of downstream surfaces rather than an unknown one — the retraction this project issued today had already reached the peer before it was withdrawn.
- `sync`: **inbound and already reviewed upstream, so it opens no outbound entry.** It updates the disposition of the existing [`SPEC-2026-08-31-11`](../A12-DMKITS-SPEC-SYNC-LEDGER.md#spec-2026-08-31-11) in place.

### Reviewed PR #2 static-semantics correction batch, inbound 2026-09-01

The reviewed a12-dmkits integration revision is `b9e7fbdc6b4806e15945bf7f993c04724a83437c`, integrating reviewed PR head `0566dc9086eeb26dc95a564cc07bffb0ae941941` against base `0e8221a6319ee4d949b92c4a14aa4668f13c8fdb`. Each record below was read from that exact integration revision. These are inbound corrections already committed and reviewed in a12-dmkits, so they update canonical clauses and provenance without creating an outbound ledger entry.

<a id="src-pr2-correlated-operand-identity"></a>
#### Correlated direct-operand identity inside `Having`

- `route`: [`AggregateSlotLawsTest`](../../../a12-rulekit/src/test/java/io/github/mbackschat/a12/dm/rulekit/validate/laws/AggregateSlotLawsTest.java), methods `theOuterCorrelationSplitsAnOperandsIdentityInsideAFilter` and `theUnmarkedPairInTheSameFilterIsStillADuplicate`, reaches the real Kernel; [`AggregateCorrelatedOperandTest`](../../../a12-rulekit/src/test/java/io/github/mbackschat/a12/dm/rulekit/dsl/operators/AggregateCorrelatedOperandTest.java) is the typed clean-room lock.
- `claim`: inside `Having`, the authored direct pair `($P, P)` is admitted under `Sum`, `NumberOfFilledFields`, and `NumberOfDifferentValues`, while `(P, P)` reports `MVK_DUPLICATE_PARAM1`. The `$` marker therefore participates in exact operand identity and is not erased before this duplicate decision.
- `limit`: only `$P, P` in that authored order is Kernel-locked by this integration. The reverse order and `($P, $P)` have typed-surface coverage but no Kernel observation here, so the canonical clause does not state their verdict.
- `consequence`: [`spec/07`](../../spec/07-repetition-and-iteration.md) now preserves correlation in the direct-operand identity clause. No runtime aggregation or filter-order claim follows from this static row.

<a id="src-pr2-distinct-count-kind-families"></a>
#### `NumberOfDifferentValues` Custom and DateFragment families

- `route`: [`NumberOfDifferentValuesKindLawsTest`](../../../a12-rulekit/src/test/java/io/github/mbackschat/a12/dm/rulekit/validate/laws/NumberOfDifferentValuesKindLawsTest.java) reaches the real Kernel through the maintained model checker route.
- `claim`: Custom pairs with Custom, String, and stored Enumeration; Custom beside Number reports `MVK_STRING_ENUM_AND_NON_STRING_ENUM`. Two DateFragment operands with the same component set are admitted; DateFragment beside text reports `MVK_DATE_AND_NONDATE`, and two fragments with differing component sets report `MVK_DATEFORMATS_NOT_COMPATIBLE`. These rows place Custom in the existing textual class and DateFragment in the existing date-like class rather than creating new classes.
- `limit`: the rows settle static family admission and the named refusal classes. They do not measure Custom value identity, DateFragment runtime aggregation, or any operator other than `NumberOfDifferentValues`.
- `consequence`: [`spec/07`](../../spec/07-repetition-and-iteration.md) adds the two kinds to the existing families and leaves runtime identity outside the measured boundary.

<a id="src-pr2-semantic-index-carrier-matrix"></a>
#### Semantic-index entity-slot carrier matrix

- `route`: [`SemanticIndexSlotLawsTest`](../../../a12-rulekit/src/test/java/io/github/mbackschat/a12/dm/rulekit/validate/laws/SemanticIndexSlotLawsTest.java), especially `numberOfFilledFieldsAcceptsASemanticIndex`, `anIndexSelectedGroupIsAdmittedInTheCommonEntityList`, and `theSameGroupOperandUnindexedIsRefused`, reaches the real Kernel and retains the negative controls in the same file.
- `claim`: `NumberOfFilledFields` admits index-selected field operands. The common entity list admits an index-selected group under `AllFieldsFilled` and `NoFieldFilled`; the same repeatable group without an index or star reports `MVK_NO_WILDCARD`. `NumberOfFilledGroups` and `RepetitionNotUnique` report `MVK_SEMANTIC_INDEX_NOT_ALLOWED`, and an index below a star reports `MVK_SEMANTIC_INDEX_AND_WILDCARD`.
- `limit`: this is an exact carrier matrix, not a general semantic-index admission rule. The file also measures indexed group refusals in two correlated `FirstFilledValue` filter shapes, but those rows are not promoted into the canonical matrix because the handoff did not request a broader correlated-group clause.
- `consequence`: [`spec/07`](../../spec/07-repetition-and-iteration.md) owns the operator slots and cross-links [`spec/08`](../../spec/08-paths-and-references.md)'s established row-selection semantics.

<a id="src-pr2-rulegroup-semantic-index"></a>
#### `RuleGroup` literal semantic-index suffix

- `route`: [`DirectiveLawsTest`](../../../a12-rulekit/src/test/java/io/github/mbackschat/a12/dm/rulekit/validate/laws/DirectiveLawsTest.java), method `aSemanticIndexSuffixSelectsTheRulesContainingGroup`, reaches the real Kernel; [`RuleGroupEntitySuffixParseTest`](../../../a12-rulekit/interpreter/src/commonTest/kotlin/io/github/mbackschat/a12/dm/interpreter/RuleGroupEntitySuffixParseTest.kt) locks retention and binding of the suffix in the clean-room parser.
- `claim`: `GroupFilled(RuleGroup For "SKU-1")` is admitted when the rule's containing `/Order/Items` group declares `Sku` as its index field. The identical suffix on unindexed `/Order` reaches ordinary semantic-index validation and reports `MVK_NO_INDEX_FIELD`; `RuleGroup*` remains invalid.
- `limit`: the rows establish static selection through the existing semantic-index mechanism. They do not measure selected-row runtime presence, field-valued keys, nested index levels, or any new positional selector.
- `consequence`: [`spec/08`](../../spec/08-paths-and-references.md) now records the suffix on `RuleGroup` and cross-links the containing-group and semantic-index clauses.
